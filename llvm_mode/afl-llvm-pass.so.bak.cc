/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.

 */

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <list>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <json/json.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/CFGPrinter.h"

#if defined(LLVM34)
#include "llvm/DebugInfo.h"
#else
#include "llvm/IR/DebugInfo.h"
#endif

#if defined(LLVM34) || defined(LLVM35) || defined(LLVM36)
#define LLVM_OLD_DEBUG_API
#endif

using namespace llvm;

cl::opt<std::string> DistanceFile(
    "distance",
    cl::desc("Distance file containing the distance of each basic block to the provided targets."),
    cl::value_desc("filename")
);

cl::opt<std::string> TargetsFile(
    "targets",
    cl::desc("Input file containing the target lines of code."),
    cl::value_desc("targets"));

cl::opt<std::string> OutDirectory(
    "outdir",
    cl::desc("Output directory where Ftargets.txt, Fnames.txt, and BBnames.txt are generated."),
    cl::value_desc("outdir"));

char json_path[512];


// enum ValueType {
//   nullValue = 0, ///< 'null' value
//   intValue = 1,      ///< signed integer value
//   uintValue = 2,     ///< unsigned integer value
//   longValue = 3,     ///< signed long value
//   ulongValue = 4,    ///< unsigned long value
//   realValue = 5,     ///< double value
//   stringValue = 6,   ///< UTF-8 string value
//   arrayValue = 7,    ///< array value (ordered list)
//   objectValue = 8    ///< object value (collection of name/value pairs).
// };


// CAFL structs
struct variable
{
    int file_line;
    std::string name;
    Value* llvm_value;
    bool is_ins; // whether is instant number or llvm value
    bool is_struct_var; // is part of struct

    // for data_type, we use json's part, as above
    int type;
};

struct target_info
{
    std::string name;
    std::string file_name;
    std::string function_name;
    std::vector<variable> target_variable;
    int condition_line;
    Json::Value condition;
    int instrumented;
};
struct value_wrap
{
  Value* value;
  std::string name;
};
struct load_wrap
{
  LoadInst* val;
  std::string name;
};



// store temp value in expr()
// std::vector<Value*> expr_val_vector;


std::vector<std::string> split(const std::string& str, const std::string& delim) {
	std::vector<std::string> res;
	if("" == str) return res;
	//先将要切割的字符串从string类型转换为char*类型
	char * strs = new char[str.length() + 1] ; //不要忘了
	strcpy(strs, str.c_str()); 
 
	char * d = new char[delim.length() + 1];
	strcpy(d, delim.c_str());
 
	char *p = strtok(strs, d);
	while(p) {
		std::string s = p; //分割得到的字符串转换为string类型
		res.push_back(s); //存入结果数组
		p = strtok(NULL, d);
	}
 
	return res;
}



namespace llvm {

template<>
struct DOTGraphTraits<Function*> : public DefaultDOTGraphTraits {
  DOTGraphTraits(bool isSimple=true) : DefaultDOTGraphTraits(isSimple) {}

  static std::string getGraphName(Function *F) {
    return "CFG for '" + F->getName().str() + "' function";
  }

  std::string getNodeLabel(BasicBlock *Node, Function *Graph) {
    if (!Node->getName().empty()) {
      return Node->getName().str();
    }

    std::string Str;
    raw_string_ostream OS(Str);

    Node->printAsOperand(OS, false);
    return OS.str();
  }
};

} // namespace llvm

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}






int inst_blocks = 0;

#define RESET   "\033[0m"
#define BLACK   "\033[30m"      /* Black */
#define RED     "\033[31m"      /* Red */
#define GREEN   "\033[32m"      /* Green */
#define YELLOW  "\033[33m"      /* Yellow */
#define BLUE    "\033[34m"      /* Blue */
#define MAGENTA "\033[35m"      /* Magenta */
#define CYAN    "\033[36m"      /* Cyan */
#define WHITE   "\033[37m"      /* White */
#define BOLDBLACK   "\033[1m\033[30m"      /* Bold Black */
#define BOLDRED     "\033[1m\033[31m"      /* Bold Red */
#define BOLDGREEN   "\033[1m\033[32m"      /* Bold Green */
#define BOLDYELLOW  "\033[1m\033[33m"      /* Bold Yellow */
#define BOLDBLUE    "\033[1m\033[34m"      /* Bold Blue */
#define BOLDMAGENTA "\033[1m\033[35m"      /* Bold Magenta */
#define BOLDCYAN    "\033[1m\033[36m"      /* Bold Cyan */
#define BOLDWHITE   "\033[1m\033[37m"      /* Bold White */

void debug_print(char *s){

    printf(YELLOW "%s\n" RESET, s);
}



void red_print(char *s){

  printf( RED "%s" RESET ,s);
}


char AFLCoverage::ID = 0;

/*
 **getValFromName: Get a llvm::Value from variable's name
 *@param target target parsed from Json file
 *@param name variable name in json file
 *@param val value pointer ro store retrived value
 */
int getValFromName(target_info target, std::string name, Value** val){

  std::vector<variable>::const_iterator iter = target.target_variable.begin();

  while(iter!=target.target_variable.end()){

    
    errs()<<"name: "<<name<<"\n";

    if((*iter).name == name){
        errs()<<"(*iter).name: "<<(*iter).name<<"\n";
        debug_print("name are the same");
        
        
        if(val == nullptr){
            printf(RED "val is nullptr in getValFromName\n" RESET);
        }
        *val = (*iter).llvm_value;
        assert(val != nullptr);
        return 1;
    }
    iter++;
  }
  return 0;
}




Value* expr(const target_info target,Json::Value cond,Instruction &I){
  // param1: target info
  // param2: (part of) target condition
  // param3:insert point
  debug_print("enter expr");
  std::string op=cond["op"].asString();
  Json::Value lr_val = cond["lr"];
    Value* left = nullptr;
    Value* right = nullptr;
    static int if_unsigned = 0; // if one variable is unsigned, this is unsigned
    static int if_x64 = 0; // if one variable is 64 bit

    IRBuilder<> builder(&I);
    if(lr_val[0].isMember("r")){
        // the last block.Need to ret
        if(lr_val[0].isMember("l")){
            debug_print("l member present");
            // printf(GREEN "left type is %d\n", lr_val[0]["l"].type());
            if(lr_val[0]["l"].type() == Json::intValue || lr_val[0]["l"].type() ==Json::uintValue){
                
                debug_print("l is int");

                int type = lr_val[0]["l_type"].asInt();
                Value *val_val = nullptr;
#ifdef __x86_64__
                int32_t val_32 = 0;
                int64_t val_64 = 0;
#else
                int32_t val_32 = 0;
#endif
                switch(type){

                    case 0: // null
                    val_val = ConstantInt::get(Type::getInt32Ty(I.getContext()),0);
                    break;

                    case 1: // singed int
                    val_32 = lr_val[0]["l"].asInt();
                    val_val = ConstantInt::get(Type::getInt32Ty(I.getContext()),val_32);
                    break;

                    case 2: // unsigned int
                    val_32 = lr_val[0]["l"].asUInt();
                    val_val = ConstantInt::get(Type::getInt32Ty(I.getContext()),val_64);
                    if_unsigned = 1;
                    break;

                    case 3: // singed long
                    val_64 = lr_val[0]["l"].asInt64();
                    val_val = ConstantInt::get(Type::getInt64Ty(I.getContext()),val_64);
                    if_x64 = 1;
                    break;

                    case 4: // unsigned long
                    val_64 = lr_val[0]["l"].asUInt64();
                    val_val = ConstantInt::get(Type::getInt64Ty(I.getContext()),val_64);
                    if_x64 = 1;
                    if_unsigned = 1;
                    break;

                    case 5:
                    case 6:
                    case 7:
                    case 8:
                    default:
                    break; 



                }

                left = val_val;

                if(left == nullptr)
                    debug_print("left is nullptr");

                assert(left != nullptr);
                debug_print("l member success");
            }
            else if(lr_val[0]["l"].type() == Json::stringValue){
                debug_print("l is string");
                std::string name = lr_val[0]["l"].asString();

                llvm::Type* my_type;
                int type = lr_val[0]["l_type"].asInt();
                switch (type){

                    case 1:
                    case 2:
                    my_type = Type::getInt32Ty(I.getContext());
                    break;

                    case 3:
                    case 4:
                    my_type = Type::getInt64Ty(I.getContext());

                    default:
                    my_type = Type::getInt32Ty(I.getContext());
                    
                }


                if(name.find("@")!=std::string::npos){
                    // something in struct

                    // split the string
                    debug_print("left var is struct");
                    std::vector<std::string> str_vec = split(name,"@");

                    int _place_ = atoi(str_vec[0].c_str());
                    printf(YELLOW "place: %d" RESET, _place_);

                    Value *place = ConstantInt::get(Type::getInt32Ty(I.getContext()),_place_);
                    Value *_struct_;
                    int ret = getValFromName(target,str_vec[1],&_struct_);
                    
                    assert(ret != 0);

                    // if getval returns pointer, dereference it
                    if(isa<AllocaInst>(_struct_)){
                      printf(BLUE "is func arg\n" RESET);
                      _struct_ =  builder.CreateLoad(_struct_);
                    }

                    // get element from struct
                    printf(BLUE "before creategep\n" RESET);
                    left = builder.CreateGEP(_struct_,place);
                    left = builder.CreateLoad(my_type, left);
                    debug_print("left: get from struct success");
                    

                }
                    
                else{
                    printf(YELLOW "before getvalfromname\n" RESET);
                    int ret = getValFromName(target, lr_val[0]["l"].asString(),&left);
                    printf(YELLOW "after getvalfromname\n" RESET);
                    if(ret == 0){
                      printf("error in expr inside.\n");
                }

                
              }
              Value* tmp_left = left;

                // printf(BLUE "left type is: %d\n" RESET, tmp_left->getType()->getTypeID());

                if(isa<AllocaInst>(tmp_left)){

                    left = builder.CreateLoad(tmp_left);
                    debug_print("stack_var found");
                }
              debug_print("l member success");
          }

            if(left == nullptr)
              debug_print("nullptr left in medium");
        }
        if(lr_val[0].isMember("r")){
            if(lr_val[0]["r"].type() == Json::intValue || lr_val[0]["r"].type() == Json::uintValue){
                debug_print("r is int");
                
                int type = lr_val[0]["l_type"].asInt();
                Value *val_val;
                int32_t val_32;
                int64_t val_64;
                switch(type){

                    case 0: // null
                    val_val = ConstantInt::get(Type::getInt32Ty(I.getContext()),0);
                    break;

                    case 1: // singed int
                    val_32 = lr_val[0]["r"].asInt();
                    val_val = ConstantInt::get(Type::getInt32Ty(I.getContext()),val_32);
                    break;

                    case 2: // unsigned int
                    val_32 = lr_val[0]["r"].asUInt();
                    val_val = ConstantInt::get(Type::getInt32Ty(I.getContext()),val_32);
                    if_unsigned = 1;
                    
                    break;

                    case 3: // singed long
                    val_64 = lr_val[0]["r"].asInt64();
                    val_val = ConstantInt::get(Type::getInt64Ty(I.getContext()),val_64);
                    if_x64 = 1;
                    break;

                    case 4: // unsigned long
                    val_64 = lr_val[0]["r"].asUInt64();
                    val_val = ConstantInt::get(Type::getInt64Ty(I.getContext()),val_64);
                    if_x64 = 1;
                    if_unsigned = 1;
                    break;

                    case 5:
                    case 6:
                    case 7:
                    case 8:
                    default:
                    break; 



                }
                right = val_val;

                if(right == nullptr)
                    debug_print("right is nullptr");

                assert(right != nullptr);
                debug_print("r member success");
            }
            else if(lr_val[0]["r"].type() == Json::stringValue){
                debug_print("r is string");
                std::string name = lr_val[0]["r"].asString();

                // judge type
                // llvm::Type* my_type = Type::getInt64Ty(I.getContext());
                llvm::Type* my_type;
                int type = lr_val[0]["r_type"].asInt();
                switch (type){

                    case 1:
                    case 2:
                    my_type = Type::getInt32Ty(I.getContext());
                    break;

                    case 3:
                    case 4:
                    my_type = Type::getInt64Ty(I.getContext());

                    default:
                    my_type = Type::getInt32Ty(I.getContext());
                    
                }



                if(name.find("@")!=std::string::npos){
                    // something in struct
                    debug_print("right var is struct");
                    // split the string
                    std::vector<std::string> str_vec = split(name,"@");

                    int _place_ = atoi(str_vec[0].c_str());
                    printf(YELLOW "place: %d" RESET, _place_);

                    Value *place = ConstantInt::get(Type::getInt32Ty(I.getContext()),_place_);
                    Value *_struct_;
                    int ret = getValFromName(target,str_vec[1],&_struct_);
                    assert(ret != 0);

                    if(isa<AllocaInst>(_struct_)){
                      _struct_ =  builder.CreateLoad(_struct_);
                    }

                    // get element from struct
                    right = builder.CreateGEP(_struct_,place);

                    // judge type:
                    // llvm::LoadInst * CreateLoad(llvm::Type *Ty, llvm::Value *Ptr, const llvm::Twine &Name = "")
                    right = builder.CreateLoad(my_type,right);
                    debug_print("right: get from struct success");

                }
                    
                else{
                  printf(YELLOW "before getvalfromname(right)\n" RESET);
                    int ret = getValFromName(target, lr_val[0]["r"].asString(),&right);
                    printf(YELLOW "after getvalfromname(right)\n" RESET);
                    if(ret == 0){
                      printf("error in expr inside.\n");
                }   
                
              }

              debug_print("right out1");
              Value* tmp_right = right;
                // llvm::Type* ptr_type = Type::getInt64Ty(I.getContext());
                debug_print("right out2");

                // the below statement will cause bugs since value may don't have this attribute
                //printf(BLUE "right type is: %d\n" RESET, tmp_right->getType()->getTypeID());
                // errs()<<*right<<"\n";
                debug_print("right out3");
                // assert(tmp_right!=nullptr);
              
                
                
                if(isa<AllocaInst>(tmp_right)){

                    debug_print("stack_var or pointer found");
                    right = builder.CreateLoad(tmp_right);
                    debug_print("after createload");
                }
              debug_print("r member success");
            }
            
        }

        if(left == nullptr)
            debug_print("nullptr left at last");
        if(right == nullptr)
            debug_print("nullptr right at last");
    }
    else{
        left = expr(target,cond["lr"][0],I);
        right = expr(target,cond["lr"][1],I);

        if(if_x64){
          printf(YELLOW "x64\n" RESET);
            if(!if_unsigned){
              printf(YELLOW "unsigned\n" RESET);
                llvm::Type* my_type = Type::getInt64Ty(I.getContext());
                left = builder.CreateZExt(left,my_type);
                right = builder.CreateZExt(right,my_type);

            }
            else{
              printf(YELLOW "unsigned\n" RESET);
                llvm::Type* my_type = Type::getInt64Ty(I.getContext());
                left = builder.CreateSExt(left,my_type);
                right = builder.CreateSExt(right,my_type);
                printf(BLUE "set unsigned long.\n" RESET);
            }   
        }
        else{
            // x32 signed
            printf(YELLOW "x32\n" RESET);
            llvm::Type* my_type = Type::getInt32Ty(I.getContext());
            if(if_unsigned){
                printf(YELLOW "unsigned\n" RESET);
                left = builder.CreateZExt(left,my_type);
                right = builder.CreateZExt(right,my_type);
            }
        }

    }
    
    // prepare num 0 and 1 with proper type
    Value *zero;
    Value *one;
    Value *big;
    if(if_x64){

        zero = ConstantInt::get(Type::getInt64Ty(I.getContext()),0);
        one = ConstantInt::get(Type::getInt64Ty(I.getContext()),1);
        big = ConstantInt::get(Type::getInt64Ty(I.getContext()),0xffffffff);
    }
    else{

        zero = ConstantInt::get(Type::getInt32Ty(I.getContext()),0);
        one = ConstantInt::get(Type::getInt32Ty(I.getContext()),1);
        big = ConstantInt::get(Type::getInt32Ty(I.getContext()),0xffffffff);
    }




    if(op == "=="){
        debug_print("reach ==");
        Value *sub_result = builder.CreateSub(left,right);
        debug_print("1");
        Value *cmp_result = builder.CreateCmp(ICmpInst::ICMP_SGE,sub_result,zero);
        debug_print("2");
        
        Value* minus_sub_result = builder.CreateSub(zero,sub_result);

        Value *select_result = builder.CreateSelect(cmp_result,sub_result,minus_sub_result);
        debug_print("3");
        inst_blocks+=4;
        return select_result;
    }
    if(op == "!="){
        debug_print("reach !=");

        Value *sub_result = builder.CreateSub(right,left);
        debug_print("1");
        Value *cmp_result = builder.CreateCmp(ICmpInst::ICMP_EQ,sub_result,zero);
        debug_print("2");
        Value *select_result = builder.CreateSelect(cmp_result,big,zero);
        debug_print("3");
        inst_blocks+=3;
        return select_result;
    }
    if(op == ">="){
        debug_print("reach >=");
        errs()<<"insert before"<<I<<"\n";
        

        Value *sub_result = builder.CreateSub(right,left);
        // Instruction *_sub_result = dyn_cast<Instruction>(builder.CreateSub(right,left));
        // _sub_result->setMetadata(I.getModule()->getMDKindID("nosanitize"),MDNode::get(I.getContext(), None));
        debug_print("1");

        Value *cmp_result = builder.CreateICmp(ICmpInst::ICMP_SGT, sub_result,zero);
        // CmpInst* _cmp_result = dyn_cast<CmpInst>(builder.CreateICmp(ICmpInst::ICMP_SGT, sub_result,zero));
        // _cmp_result->setMetadata(I.getModule()->getMDKindID("nosanitize"),MDNode::get(I.getContext(), None));
        debug_print("2");

        Value *select_result = builder.CreateSelect(cmp_result,sub_result,zero);
        // SelectInst *_select_result = dyn_cast<SelectInst>(builder.CreateSelect(cmp_result,sub_result,zero));
        // _select_result->setMetadata(I.getModule()->getMDKindID("nosanitize"),MDNode::get(I.getContext(), None));
        
        debug_print("3");
        // int int_val = 0;
        
        // if(ConstantInt* CI = dyn_cast<ConstantInt>(sub_result)){
        //     debug_print("sub is int");
        //     if(CI->getBitWidth()<=32 ){
        //         int val = CI->getSExtValue();
        //     }
        // }
        inst_blocks+=3;
        return select_result;
        // return zero;
    }
    if(op == ">"){
        debug_print("reach >");

        Value *_sub_result = builder.CreateSub(right,left);
        debug_print("1");
        Value *sub_result = builder.CreateAdd(_sub_result,one);
        debug_print("2");
        Value* cmp_result = builder.CreateICmp(ICmpInst::ICMP_SGT, sub_result,zero);
        debug_print("3");

        Value *select_result = builder.CreateSelect(cmp_result,sub_result,zero);
        debug_print("4");
        inst_blocks+=4;
        return select_result;
    }
    if(op == "<="){
        debug_print("reach <=");
        Value *sub_result = builder.CreateSub(left,right);
        debug_print("1");
        Value* cmp_result = builder.CreateICmp(ICmpInst::ICMP_SGT, sub_result,zero);
        debug_print("2");
        Value *select_result = builder.CreateSelect(cmp_result,sub_result,zero);
        debug_print("3");
        inst_blocks+=3;
        return select_result;
    }
    if(op == "<"){

        debug_print("reach <");

        Value *_sub_result = builder.CreateSub(left,right);
        debug_print("1");
        Value *sub_result = builder.CreateAdd(_sub_result,one);
        debug_print("2");
        Value* cmp_result = builder.CreateICmp(ICmpInst::ICMP_SGT, sub_result,zero);
        debug_print("3");
        Value *select_result = builder.CreateSelect(cmp_result,sub_result,zero);
        debug_print("4");

        inst_blocks+=4;
        return select_result;
    }
    if(op == "&&"){

        debug_print("reach &&");
        Value *add_result = builder.CreateAdd(left,right);
        debug_print("1");
        inst_blocks+=1;
        return add_result;
    }
    if(op == "||"){

        debug_print("reach ||");
        Value *cmp_result = builder.CreateICmp(ICmpInst::ICMP_SGT,left,right);
        debug_print("1");
        Value *result = builder.CreateSelect(cmp_result,right,left);
        debug_print("2");
        inst_blocks+=2;
        return result;
    }
    if(op == "+"){

        debug_print("reach +");
        Value *add_result = builder.CreateAdd(left,right);
        debug_print("1");
        inst_blocks+=1;
        return add_result;
    }
    if(op == "-"){

        debug_print("reach -");
        Value *sub_result = builder.CreateSub(left,right);
        debug_print("1");
        inst_blocks+=1;
        return sub_result;
    }
    if(op == "*"){

        debug_print("reach *");

        // check if it's pointer * or mul
        if(left == nullptr){

            debug_print("\"*\" is pointer");
            return left; // under test

        }
        else{

            debug_print("\"*\" is multiply");
            Value* mul_result = builder.CreateMul(left,right);
            debug_print("1");
            return mul_result;
        }
    }
    if(op == "/"){

        debug_print("reach /");

        if(if_unsigned == 1){

            Value *div_result = builder.CreateUDiv(left,right);
            debug_print("1");
            return div_result;
        }
        else{
          
            Value *div_result = builder.CreateSDiv(left,right);
            debug_print("1");
            return div_result;
        }
        
    }

}



static void getDebugLoc(const Instruction *I, std::string &Filename,
                        unsigned &Line) {
#ifdef LLVM_OLD_DEBUG_API
  DebugLoc Loc = I->getDebugLoc();
  if (!Loc.isUnknown()) {
    DILocation cDILoc(Loc.getAsMDNode(M.getContext()));
    DILocation oDILoc = cDILoc.getOrigLocation();

    Line = oDILoc.getLineNumber();
    Filename = oDILoc.getFilename().str();

    if (filename.empty()) {
      Line = cDILoc.getLineNumber();
      Filename = cDILoc.getFilename().str();
    }
  }
#else
  if (DILocation *Loc = I->getDebugLoc()) {
    Line = Loc->getLine();
    Filename = Loc->getFilename().str();

    if (Filename.empty()) {
      DILocation *oDILoc = Loc->getInlinedAt();
      if (oDILoc) {
        Line = oDILoc->getLine();
        Filename = oDILoc->getFilename().str();
      }
    }
  }
#endif /* LLVM_OLD_DEBUG_API */
}

static bool isBlacklisted(const Function *F) {
  static const SmallVector<std::string, 8> Blacklist = {
    "asan.",
    "llvm.",
    "sancov.",
    "__ubsan_handle_",
    "free",
    "malloc",
    "calloc",
    "realloc"
  };

  for (auto const &BlacklistFunc : Blacklist) {
    if (F->getName().startswith(BlacklistFunc)) {
      return true;
    }
  }

  return false;
}

bool AFLCoverage::runOnModule(Module &M) {

  printf(RED "inside runInModule\n" RESET);

  bool is_aflgo = false;
  bool is_aflgo_preprocessing = false;

  if (!TargetsFile.empty() && !DistanceFile.empty()) {
    FATAL("Cannot specify both '-targets' and '-distance'!");
    return false;
  }

  bool is_mul_target = false;
  int target_index = 0;

  std::list<std::string> targets;
  std::map<std::string, int> bb_to_dis;
  std::vector<std::string> basic_blocks;

  if (!TargetsFile.empty()) {
    printf(GREEN "inside preprocess\n" RESET);

    if (OutDirectory.empty()) {
      FATAL("Provide output directory '-outdir <directory>'");
      return false;
    }

    std::ifstream targetsfile(TargetsFile);
    std::string line;
    while (std::getline(targetsfile, line))
      targets.push_back(line);
    targetsfile.close();

    is_aflgo_preprocessing = true;

  } else if (!DistanceFile.empty()) {

    printf(RED "inside aflgo \n" RESET);

    std::ifstream cf(DistanceFile);
    if (cf.is_open()) {

      std::string line;
      while (getline(cf, line)) {
        if(line.find("@mul_target") != std::string::npos){
            // multiple target
            is_mul_target = true;
        }

        if(!is_mul_target){
            std::size_t pos = line.find(",");
            std::string bb_name = line.substr(0, pos);
            // bb_dis = (int) (100.0 * atof(line.substr(pos + 1, line.length()).c_str()));
            int bb_dis = (int) (10.0 * atof(line.substr(pos + 1, line.length()).c_str()));
            bb_to_dis.emplace(bb_name, bb_dis);
            basic_blocks.push_back(bb_name);
        }else{

            // read until target one, store inside one target
            if(line.find("@target1")){
              
            }
        }
        

      }
      cf.close();

      is_aflgo = true;

    } else {
      FATAL("Unable to find %s.", DistanceFile.c_str());
      return false;
    }

  }

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    if (is_aflgo || is_aflgo_preprocessing)
      SAYF(cCYA "aflgo-llvm-pass (yeah!) " cBRI VERSION cRST " (%s mode)\n",
           (is_aflgo_preprocessing ? "preprocessing" : "distance instrumentation"));
    else
      SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");


  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Default: Not selective */
  char* is_selective_str = getenv("AFLGO_SELECTIVE");
  unsigned int is_selective = 0;

  if (is_selective_str && sscanf(is_selective_str, "%u", &is_selective) != 1)
    FATAL("Bad value of AFLGO_SELECTIVE (must be 0 or 1)");

  char* dinst_ratio_str = getenv("AFLGO_INST_RATIO");
  unsigned int dinst_ratio = 100;

  if (dinst_ratio_str) {

    if (sscanf(dinst_ratio_str, "%u", &dinst_ratio) != 1 || !dinst_ratio ||
        dinst_ratio > 100)
      FATAL("Bad value of AFLGO_INST_RATIO (must be between 1 and 100)");

  }

  memset(json_path,'\x00',sizeof(json_path));
  strcpy(json_path, getenv("JSON_PATH"));
  if(json_path[0]=='\x00' || json_path == NULL){
      FATAL("No json file provided");
  }

    // read from json file, obtain variable info
    std::ifstream ifs(json_path);
    Json::Reader reader; 
    Json::Value root;
    int target_cnt;
    int arch = 0;
    std::vector<int> type_vec; // store bug types
    std::vector<int> var_cnt_vec; // how many variables involved in each condition
    std::vector<target_info> target_vec; // store target info
    std::vector<value_wrap> target_value_vec;
    
    if(reader.parse(ifs,root))
    {
        debug_print("json part first");
        if(!root["targets"].isNull())
        {
            int target_size = root["targets"].size();
            for(int i = 0; i < target_size; i++)
            {
                // i == 0 is metadata block
                if(i == 0)
                {
                    debug_print("json part metadata");
                    Json::Value metadata = root["targets"][i];
                    target_cnt = metadata["count"].asInt();
                    int type_size = metadata["types"].size();
                    for(int j = 0; j<type_size;j++)
                    {
                        
                        if(!strcmp(metadata["types"][j]["type"].asCString(),"stack read"))
                        type_vec.push_back(1);
                        else if(!strcmp(metadata["types"][j]["type"].asCString(),"integer overflow"))
                        type_vec.push_back(5);
                        var_cnt_vec.push_back(metadata["types"][j]["variable_count"].asInt());

                    }
                }
                else
                {
                    debug_print("json part else");
                    // target info block
                    target_info info;
                    info.name = root["targets"][i]["name"].asString();
                    info.file_name = root["targets"][i]["file_name"].asString();
                    info.function_name = root["targets"][i]["function_name"].asString();
                    for(int k = 0; k<var_cnt_vec.size();k++)
                    {
                        
                        for(int l = 0; l < var_cnt_vec[k]; l++)
                        {
                              debug_print("json part l");
                              // puts("here.\n");
                              variable var_temp;
                              var_temp.file_line = root["targets"][i]["variable"][l]["line"].asInt();
                              var_temp.name = root["targets"][i]["variable"][l]["name"].asString();
                              info.target_variable.push_back(var_temp);
                        }
                        
                    }
                    info.condition_line = root["targets"][i]["target_line"].asInt();

                    info.condition = root["targets"][i]["condition"];   
                    info.instrumented = 0;  
                    target_vec.push_back(info);              
                }
            }
        }

        debug_print("json part finish");
    }

    
  // find target variables
  for(auto &F : M){
    int found_target_instr_line = 0;
    int reach_target_function = 0;
    std::string Filename;
    // errs()<<F.getName()<<"\n";
    // errs()<<target_vec[0].function_name<<"\n";

    for(int i = 0; i<target_vec.size();i++){

        
        if(F.getName().contains(target_vec[i].function_name)){
            debug_print("found_variables function");
            printf(GREEN "found_variables function %s \n" RESET, target_vec[i].function_name.c_str());

            
              
              for(int j = 0; j<target_vec[i].target_variable.size();j++){
                printf(RED "j is %d\n" RESET,j);

                for(auto &BB : F) {
                  for(auto &I : BB){
                  unsigned int line;
                  getDebugLoc(&I, Filename, line);

                  if(Filename.empty() || line == 0)
                      continue;

                    if(line == target_vec[i].target_variable[j].file_line){

                      // in real line
                      errs()<<"variable in line"<<line<<"\n";

                      if(isa<CallInst>(I)) {
                          
                          CallInst& ci = cast<CallInst>(I);
                          for(User::op_iterator itr3 = ci.arg_begin(); itr3 != ci.arg_end(); itr3++){

                              Value* value = itr3->get();

                              if(isa<MetadataAsValue>(*value)){

                                Metadata *md = cast<MetadataAsValue>(*value).getMetadata();
                                unsigned char mdid = md->getMetadataID();

                                if(isa<DILocalVariable>(*md)){

                                  DILocalVariable &dil = cast<DILocalVariable>(*md);
                                  errs()<<"variable name is "<<dil.getName().data()<<"\n";

                                  if(!strcmp(dil.getName().data(),target_vec[i].target_variable[j].name.c_str())){

                                    // name are the same
                                      debug_print("name are same");
                                      if(DbgDeclareInst* DbgDec = dyn_cast<DbgDeclareInst>(&I)){
                                          DebugLoc loc = DbgDec->getDebugLoc();
                                          AllocaInst *AI;
                                          Metadata *Meta = cast<MetadataAsValue>(DbgDec->getOperand(0))->getMetadata();

                                          if(isa<ValueAsMetadata>(Meta)){

                                                Value* target_val = cast<ValueAsMetadata>(Meta)->getValue();
                                                AI = cast<AllocaInst>(target_val);

                                                errs()<< *AI <<"\n";

                                                debug_print("found same variable");
                                                target_vec[i].target_variable[j].llvm_value = target_val;
                                                debug_print("statement is ");
                                                errs()<<I<<"\n";
                                                target_vec[i].target_variable[j].is_ins = true;

                                          }
                                  }
                              }
                          }



                      }

                }    
              }
            }
          }      
        }
      }
    }
  }
}








  /* Instrument all the things! */

  int inst_blocks = 0;

  if (is_aflgo_preprocessing) {

    std::ofstream bbnames(OutDirectory + "/BBnames.txt", std::ofstream::out | std::ofstream::app);
    std::ofstream bbcalls(OutDirectory + "/BBcalls.txt", std::ofstream::out | std::ofstream::app);
    std::ofstream fnames(OutDirectory + "/Fnames.txt", std::ofstream::out | std::ofstream::app);
    std::ofstream ftargets(OutDirectory + "/Ftargets.txt", std::ofstream::out | std::ofstream::app);

    /* Create dot-files directory */
    std::string dotfiles(OutDirectory + "/dot-files");
    if (sys::fs::create_directory(dotfiles)) {
      FATAL("Could not create directory %s.", dotfiles.c_str());
    }

    for (auto &F : M) {

      bool has_BBs = false;
      std::string funcName = F.getName().str();

      /* Black list of function names */
      if (isBlacklisted(&F)) {
        continue;
      }

      bool is_target = false;
      for (auto &BB : F) {

        std::string bb_name("");
        std::string filename;
        unsigned line;

        for (auto &I : BB) {
          getDebugLoc(&I, filename, line);

          /* Don't worry about external libs */
          static const std::string Xlibs("/usr/");
          if (filename.empty() || line == 0 || !filename.compare(0, Xlibs.size(), Xlibs))
            continue;

          if (bb_name.empty()) {

            std::size_t found = filename.find_last_of("/\\");
            if (found != std::string::npos)
              filename = filename.substr(found + 1);

            bb_name = filename + ":" + std::to_string(line);
          }

          if (!is_target) {
              for (auto &target : targets) {
                std::size_t found = target.find_last_of("/\\");
                if (found != std::string::npos)
                  target = target.substr(found + 1);

                std::size_t pos = target.find_last_of(":");
                std::string target_file = target.substr(0, pos);
                unsigned int target_line = atoi(target.substr(pos + 1).c_str());

                if (!target_file.compare(filename) && target_line == line)
                  is_target = true;

              }
            }

            if (auto *c = dyn_cast<CallInst>(&I)) {

              std::size_t found = filename.find_last_of("/\\");
              if (found != std::string::npos)
                filename = filename.substr(found + 1);

              if (auto *CalledF = c->getCalledFunction()) {
                if (!isBlacklisted(CalledF))
                  bbcalls << bb_name << "," << CalledF->getName().str() << "\n";
              }
            }
        }

        if (!bb_name.empty()) {

          BB.setName(bb_name + ":");
          if (!BB.hasName()) {
            std::string newname = bb_name + ":";
            Twine t(newname);
            SmallString<256> NameData;
            StringRef NameRef = t.toStringRef(NameData);
            MallocAllocator Allocator;
            BB.setValueName(ValueName::Create(NameRef, Allocator));
          }

          bbnames << BB.getName().str() << "\n";
          has_BBs = true;

#ifdef AFLGO_TRACING
          auto *TI = BB.getTerminator();
          IRBuilder<> Builder(TI);

          Value *bbnameVal = Builder.CreateGlobalStringPtr(bb_name);
          Type *Args[] = {
              Type::getInt8PtrTy(M.getContext()) //uint8_t* bb_name
          };
          FunctionType *FTy = FunctionType::get(Type::getVoidTy(M.getContext()), Args, false);
          Constant *instrumented = M.getOrInsertFunction("llvm_profiling_call", FTy);
          Builder.CreateCall(instrumented, {bbnameVal});
#endif

        }
      }

      if (has_BBs) {
        /* Print CFG */
        std::string cfgFileName = dotfiles + "/cfg." + funcName + ".dot";
        std::error_code EC;
        raw_fd_ostream cfgFile(cfgFileName, EC, sys::fs::F_None);
        if (!EC) {
          WriteGraph(cfgFile, &F, true);
        }

        if (is_target)
          ftargets << F.getName().str() << "\n";
        fnames << F.getName().str() << "\n";
      }
    }

  } else {
    /* Distance instrumentation */
    // assert(is_aflgo == true);

    LLVMContext &C = M.getContext();
    IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
    IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
    IntegerType *Int64Ty = IntegerType::getInt64Ty(C);

#ifdef __x86_64__
    IntegerType *LargestType = Int64Ty;
    ConstantInt *MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 8);
#else
    IntegerType *LargestType = Int32Ty;
    ConstantInt *MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 4);
#endif
    ConstantInt *MapDistLoc = ConstantInt::get(LargestType, MAP_SIZE);
    ConstantInt *TotalDataDist;
    TotalDataDist = ConstantInt::get(LargestType, MAP_SIZE + 16);

    
    ConstantInt *One = ConstantInt::get(LargestType, 1);
    ConstantInt *Zero = ConstantInt::get(LargestType, 0);
    ConstantInt *Big = ConstantInt::get(LargestType, 0x7fffffff);

    /* Get globals for the SHM region and the previous location. Note that
       __afl_prev_loc is thread-local. */

    GlobalVariable *AFLMapPtr =
        new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                           GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

    GlobalVariable *AFLPrevLoc = new GlobalVariable(
        M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
        0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

    for (auto &F : M) {

      int distance = -1;

      for (auto &BB : F) {

        distance = -1;

        if (is_aflgo) {

          std::string bb_name;
          for (auto &I : BB) {
            std::string filename;
            unsigned line;
            getDebugLoc(&I, filename, line);

            if (filename.empty() || line == 0)
              continue;
            std::size_t found = filename.find_last_of("/\\");
            if (found != std::string::npos)
              filename = filename.substr(found + 1);

            bb_name = filename + ":" + std::to_string(line);
            break;
          }

          if (!bb_name.empty()) {

            if (find(basic_blocks.begin(), basic_blocks.end(), bb_name) == basic_blocks.end()) {

              if (is_selective)
                continue;

            } else {

              /* Find distance for BB */

              if (AFL_R(100) < dinst_ratio) {
                std::map<std::string,int>::iterator it;
                for (it = bb_to_dis.begin(); it != bb_to_dis.end(); ++it)
                  if (it->first.compare(bb_name) == 0)
                    distance = it->second;

              }
            }
          }
        }

        BasicBlock::iterator IP = BB.getFirstInsertionPt();
        IRBuilder<> IRB(&(*IP));

        if (AFL_R(100) >= inst_ratio) continue;

        /* Make up cur_loc */

        unsigned int cur_loc = AFL_R(MAP_SIZE);

        ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

        /* Load prev_loc */

        LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
        PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

        /* Load SHM pointer */

        LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
        MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *MapPtrIdx =
            IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

        /* Update bitmap */

        LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
        Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
        IRB.CreateStore(Incr, MapPtrIdx)
           ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        /* Set prev_loc to cur_loc >> 1 */

        StoreInst *Store =
            IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
        Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        

        if (distance >= 0) {

          ConstantInt *Distance =
              ConstantInt::get(LargestType, (unsigned) distance);

          /* Add distance to shm[MAPSIZE] */

          Value *MapDistPtr = IRB.CreateBitCast(
              IRB.CreateGEP(MapPtr, MapDistLoc), LargestType->getPointerTo());
          LoadInst *MapDist = IRB.CreateLoad(MapDistPtr);
          MapDist->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));





          /* for the smallest distance , if current is smaller, store it*/

          // first set to zero, I can't find the place to initialize the area to a large number
          Value *cmp_zero = IRB.CreateCmp(CmpInst::ICMP_EQ, Zero, MapDist);
          Value *pre_select = IRB.CreateSelect(cmp_zero,Big,MapDist);
          IRB.CreateStore(pre_select, MapDistPtr)
              ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));


          MapDist = IRB.CreateLoad(MapDistPtr);
          MapDist->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
          Value* cmp_result = IRB.CreateCmp(CmpInst::ICMP_ULT, Distance, MapDist);
          Value* dist_store = IRB.CreateSelect(cmp_result, Distance, MapDist);
          IRB.CreateStore(dist_store, MapDistPtr)
              ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));




          // Value *IncrDist = IRB.CreateAdd(MapDist, Distance);
          // IRB.CreateStore(IncrDist, MapDistPtr)
          //     ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          /* Increase count at shm[MAPSIZE + (4 or 8)] */

          // need a flag for data initiating to zero

          Value *MapCntPtr = IRB.CreateBitCast(
              IRB.CreateGEP(MapPtr, MapCntLoc), LargestType->getPointerTo());
          LoadInst *MapCnt = IRB.CreateLoad(MapCntPtr);
          MapCnt->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          Value *IncrCnt = IRB.CreateAdd(MapCnt, One);
          IRB.CreateStore(IncrCnt, MapCntPtr)
              ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        }


        /* if not traced to, store as zero */
          Value *DataDistPtr = IRB.CreateBitCast(IRB.CreateGEP(MapPtr, TotalDataDist),LargestType->getPointerTo());
          //printf(RED "before load\n" RESET);
          LoadInst *Datadist_ = IRB.CreateLoad(DataDistPtr);
          Datadist_->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          //printf(RED "after load\n" RESET);

          Value *cmp = IRB.CreateCmp(CmpInst::ICMP_EQ,Datadist_,Zero);
          Value *restore = IRB.CreateSelect(cmp,Big,Datadist_);
          IRB.CreateStore(restore,DataDistPtr)->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));





        inst_blocks++;

      }
    }


  // third instrumentation: find target variables and do expr()
  for (auto &F : M){

    

    std::string Filename;
    unsigned int line;
    int found_target_file = 0;
    if(isBlacklisted(&F)){
        continue;
    }

    for (auto &BB : F) {

      // do instrument, and expr() in CAFL
      for(auto &I : BB){

          

          int found_target_func = 0;
          int iter = 0;

          getDebugLoc(&I,Filename,line);

          //printf(YELLOW "line: %d, target_vec[iter].condition_line: %d\n" RESET , line, target_vec[iter].condition_line);
          if(line != target_vec[iter].condition_line){
              continue; // continue to another instruction
          }

          // errs()<<"Filename: "<<Filename<<"\n";
          // errs()<<"target_vec[0].file_name:"<<target_vec[0].file_name<<"\n";

          // printf(BLUE "found target!!!\n" RESET);
          
          if(Filename.find(target_vec[0].file_name) != std::string::npos){
              found_target_file = 1;
              size_t index = Filename.find(target_vec[0].file_name);
              if(index != 0){
                  if(Filename.c_str()[index-1] != '/')
                      found_target_file = 0;
                      //printf(BLUE "reset found_target!!!\n" RESET);
              }
          }

          


          if(found_target_file == 1 && line == target_vec[iter].condition_line && target_vec[iter].instrumented == 0){


              // maybe many instructions exist in this line
              // but we only need to instrument once!
              debug_print("target location");
              IRBuilder<> IRB(&I);
              IRB.SetInsertPoint(&I);
              LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
              MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

              assert(line == target_vec[iter].condition_line);
              debug_print("reach expr");
              printf(YELLOW "reach expr" RESET);
              
              Value *retval = expr(target_vec[iter],target_vec[iter].condition, I);
              // retval is val needs to be stored

              debug_print("after expr()");

              // store into global variable
              Value *DatadistAll = IRB.CreateBitCast(
                  IRB.CreateGEP(MapPtr, TotalDataDist),Int32Ty->getPointerTo()
              );
              
              debug_print("GEP global variable");
              // LoadInst *DataDistPtr = IRB.CreateLoad(Int64Ty,DatadistAll);
              // DataDistPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));


              IRB.CreateStore(retval,DatadistAll)
            ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
            debug_print("STORE global variable");
            target_vec[iter].instrumented = 1;
            debug_print("should finish");
            break;

          }

          else{
              // not target function
              break; 

          }
          

      }

    }
    
  }

    
  }

  /* Say something nice. */

  if (!is_aflgo_preprocessing && !be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%, dist. ratio %u%%).",
             inst_blocks,
             getenv("AFL_HARDEN")
             ? "hardened"
             : ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN"))
               ? "ASAN/MSAN" : "non-hardened"),
             inst_ratio, dinst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
