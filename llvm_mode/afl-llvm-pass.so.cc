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
#include <set>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"


#include "llvm/IR/CFG.h"

using namespace llvm;

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


char AFLCoverage::ID = 0;


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

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

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  std::ofstream func;
  func.open("FuncInfo.txt", std::ofstream::out | std::ofstream::app);
  std::map<BasicBlock *, unsigned int> block_afl_map;
  std::vector<BasicBlock *> entryblocks;
  unsigned int total_bb_num = 0;

  /* Instrument all the things! */
  int inst_blocks = 0;
  int func_num = 0;
  std::cout << "Funcinfo functions : \n";
  for (auto &F : M){
    int bb_num = 0;
    std::cout << F.getName().str() << " ";
    if (!F.empty()){
      entryblocks.push_back(&F.getEntryBlock());
    }
    //std::cout << "entry block : " << &F.getEntryBlock() << "\n";
    for (auto BB = F.begin() ; BB != F.end() ; BB++) {
      BasicBlock::iterator IP = (*BB).getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;
      bb_num ++;
      total_bb_num ++;

      /* Make up cur_loc */
      unsigned int cur_loc = AFL_R(MAP_SIZE);
      block_afl_map.insert(std::make_pair(&(*BB), cur_loc));  //hack to get BB's id

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

      inst_blocks++;
    }
    std::cout << "BB num : " << bb_num << "\n";
    if (bb_num >= 1) {func_num++;}
  }

  //func << func_num << "\n";

  for (auto &F : M) {
    std::set<unsigned int> ids;
    for (auto &BB : F) {
      unsigned int cur_loc = block_afl_map.find(&BB) -> second;
      for (succ_iterator succs = succ_begin(&BB); succs != succ_end(&BB); succs++){
        unsigned int next_loc = block_afl_map.find(*succs) -> second;
        unsigned int branch_id = (cur_loc >> 1) ^ next_loc;
        ids.insert(branch_id);
      }
      TerminatorInst * BBt = BB.getTerminator();
      if (BBt->getNumSuccessors() == 0){
        if (BBt->isExceptional()){
        } else if (isa<ReturnInst>(BBt)){
          for(auto eB = entryblocks.begin(); eB != entryblocks.end(); eB++){
            auto search = block_afl_map.find(*eB);
            unsigned int next_loc = 0;
            if (search == block_afl_map.end()){
              std::cout << "can't find in block afl map\n";
              continue;
            } else {
              next_loc = block_afl_map.find(*eB) -> second;
            }
            unsigned int branch_id = (cur_loc >> 1) ^ next_loc;
            ids.insert(branch_id);
          }
        } else if (isa<IndirectBrInst>(BBt)) {
          //std::cout << "indirect branch : no successor \n";
        } else if (isa<UnreachableInst> (BBt)) {
          //std::cout << "unreachable : no successor\n";
        } else {
          //std::cout << "Warning : no successor?\n";
        }
      }
    }
    if (ids.size() > 0){
      func << ids.size() << ":" <<  F.getName().str() << "\n";
      for (auto id= ids.begin(); id!=ids.end(); id++){
        func << *id << "\n";
      }
    }
  }
  func.close();

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

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
