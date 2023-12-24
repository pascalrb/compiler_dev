#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm-c/Core.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Analysis/InstructionSimplify.h"

#include "llvm/Transforms/Utils/Local.h"  //isInstructionTriviallyDead()
//#include "/ece566/projects/p2/C/dominance.h"

using namespace llvm;

static void CommonSubexpressionElimination(Module *M);

static void summarize(Module *M);
static void print_csv_file(std::string outputfile);

static cl::opt<std::string>
        InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
        OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
        Mem2Reg("mem2reg",
                cl::desc("Perform memory to register promotion before CSE."),
                cl::init(false));

static cl::opt<bool>
        NoCSE("no-cse",
              cl::desc("Do not perform CSE Optimization."),
              cl::init(false));

static cl::opt<bool>
        Verbose("verbose",
                    cl::desc("Verbose stats."),
                    cl::init(false));

static cl::opt<bool>
        NoCheck("no",
                cl::desc("Do not check for valid IR."),
                cl::init(false));

static llvm::Statistic CSEDead = {"", "CSEDead", "CSE found dead instructions"};
static llvm::Statistic CSEElim = {"", "CSEElim", "CSE redundant instructions"};
static llvm::Statistic CSESimplify = {"", "CSESimplify", "CSE simplified instructions"};
static llvm::Statistic CSELdElim = {"", "CSELdElim", "CSE redundant loads"};
static llvm::Statistic CSEStore2Load = {"", "CSEStore2Load", "CSE forwarded store to load"};
static llvm::Statistic CSEStElim = {"", "CSEStElim", "CSE redundant stores"};

Function *Current=NULL;
DominatorTreeBase<BasicBlock,false> *DT=NULL;
DominatorTreeBase<BasicBlock,true> *PDT=NULL;
LoopInfoBase<BasicBlock,Loop> *LI=NULL;

int main(int argc, char **argv) {
    // Parse command line arguments
    cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

    // Handle creating output files and shutting down properly
    llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.
    LLVMContext Context;

    // LLVM idiom for constructing output file.
    std::unique_ptr<ToolOutputFile> Out;
    std::string ErrorInfo;
    std::error_code EC;
    Out.reset(new ToolOutputFile(OutputFilename.c_str(), EC,
                                 sys::fs::OF_None));

    EnableStatistics();

    // Read in module
    SMDiagnostic Err;
    std::unique_ptr<Module> M;
    M = parseIRFile(InputFilename, Err, Context);

    // If errors, fail
    if (M.get() == 0)
    {
        Err.print(argv[0], errs());
        return 1;
    }

    // If requested, do some early optimizations
    if (Mem2Reg)
    {
        legacy::PassManager Passes;
        Passes.add(createPromoteMemoryToRegisterPass());
        Passes.run(*M.get());
    }

    if (!NoCSE) {
        CommonSubexpressionElimination(M.get());
    }

    // Collect statistics on Module
    summarize(M.get());
    print_csv_file(OutputFilename);

    if (Verbose)
        PrintStatistics(errs());

    // Verify integrity of Module, do this by default
    if (!NoCheck)
    {
        legacy::PassManager Passes;
        Passes.add(createVerifierPass());
        Passes.run(*M.get());
    }

    // Write final bitcode
    WriteBitcodeToFile(*M.get(), Out->os());
    Out->keep();

    return 0;
}

static llvm::Statistic nFunctions = {"", "Functions", "number of functions"};
static llvm::Statistic nInstructions = {"", "Instructions", "number of instructions"};
static llvm::Statistic nLoads = {"", "Loads", "number of loads"};
static llvm::Statistic nStores = {"", "Stores", "number of stores"};

static void summarize(Module *M) {
    for (auto i = M->begin(); i != M->end(); i++) {
        if (i->begin() != i->end()) {
            nFunctions++;
        }

        for (auto j = i->begin(); j != i->end(); j++) {
            for (auto k = j->begin(); k != j->end(); k++) {
                Instruction &I = *k;
                nInstructions++;
                if (isa<LoadInst>(&I)) {
                    nLoads++;
                } else if (isa<StoreInst>(&I)) {
                    nStores++;
                }
            }
        }
    }
}

static void print_csv_file(std::string outputfile)
{
    std::ofstream stats(outputfile + ".stats");
    auto a = GetStatistics();
    for (auto p : a) {
        stats << p.first.str() << "," << p.second << std::endl;
    }
    stats.close();
}


void UpdateDominators(Function *F)
{
  if (Current != F)
    {
        Current = F;

        if (DT==NULL)
        {
            DT = new DominatorTreeBase<BasicBlock,false>();
            PDT = new DominatorTreeBase<BasicBlock,true>();
            if (LI==NULL)
                LI = new LoopInfoBase<BasicBlock,Loop>();
        }
      
        DT->recalculate(*F);
        PDT->recalculate(*F);

        LI->analyze(*DT);
    }
}

BasicBlock* FirstDomChild(BasicBlock *BB)
{
  UpdateDominators(BB->getParent());
  DomTreeNodeBase<BasicBlock> *Node = DT->getNode(BB);

  if(Node==NULL)
    return NULL;

  DomTreeNodeBase<BasicBlock>::iterator it = Node->begin();
  if (it!=Node->end())
    return (*it)->getBlock();
  return NULL;
}

BasicBlock* NextDomChild(BasicBlock *BB, BasicBlock *Child)
{
  UpdateDominators(BB->getParent());
  DomTreeNodeBase<BasicBlock> *Node = DT->getNode(BB);
  DomTreeNodeBase<BasicBlock>::iterator it,end;

  bool next=false;
  for(it=Node->begin(),end=Node->end(); it!=end; it++)
    if (next)
      return (*it)->getBlock();
    else if (*it==DT->getNode(Child))
      next=true;

  return NULL;
}

void CSEElimRecursion(BasicBlock *BB, Instruction &I1){

    BasicBlock *child = FirstDomChild(BB);

    // this while() check acts as recusion base case
    // as well as a checker for when all immediate children of BB have been processed
    while(child){

        CSEElimRecursion(child, I1);

        //check common subexpression
        auto domBBInst_iter = child->begin();
        while(domBBInst_iter != child->end()){
            Instruction &I2 = *domBBInst_iter;
            
            if(I1.isIdenticalTo(&I2)){          // same opcode
                                                // same type (not operands)
                                                // same number of operands
                                                // same operands order
                if(Value* val = dyn_cast<Value>(&I1)){
                    CSEElim++;
                    I2.replaceAllUsesWith(val);

                    domBBInst_iter++;
                    I2.eraseFromParent();
                    continue;
                }
            }
            domBBInst_iter++;
        }
        child = NextDomChild(BB, child);
    }
}

static void CommonSubexpressionElimination(Module * M) {

    for (auto func_iter = M->begin(); func_iter != M->end(); func_iter++) {
        //llvm::Module::iterator = FunctionListType::iterator

        for (auto bb_iter = func_iter->begin(); bb_iter != func_iter->end(); bb_iter++) {
            //llvm::BasicBlock
            BasicBlock &BB = *bb_iter;
            
            auto instr1_iter = bb_iter->begin();
            bool erasedInst1;
            while(instr1_iter != bb_iter->end()){
                //llvm::Instruction
                erasedInst1 = false;
                Instruction &I1 = *instr1_iter;

                //OPT 0 - Eliminate dead instructions
                if(isInstructionTriviallyDead(&I1)){
                    CSEDead++;

                    //update iter 
                    instr1_iter++;

                    I1.eraseFromParent();
                    continue; //TODO: might need to move this to process Opt 1-3
                }

                //OPT 1a - Simplifying instructions
                Value *val = SimplifyInstruction(&I1, M->getDataLayout());
                if(val){ 
                    CSESimplify++;
                    I1.replaceAllUsesWith(val);

                    //update iter 
                    instr1_iter++;
                    //erase original instruction
                    I1.eraseFromParent();
                    continue;
                }

                //OPT 1b - Common Subexpression Elimination 
                // FIXME: Currently passing at 17.59/20
                //  suspecting the following line is better but for some gets 0/20
                //  if(I1.isBinaryOp() || I1.isBitwiseLogicOp() || I1.isUnaryOp()){

                if(!I1.mayWriteToMemory() && !I1.mayReadFromMemory() && 
                        /*!I1.isAtomic() &&*/ !I1.isTerminator() && !I1.isVolatile()){
                
                    CSEElimRecursion(&BB, I1);
                }


                //OPT 2 - Eliminating redundant loads (within same basic block)
                if(isa<LoadInst>(&I1)){
                    auto redundLd_iter = instr1_iter;
                    redundLd_iter++;
                    
                    while(redundLd_iter != bb_iter->end()){
                        Instruction &I2 = *redundLd_iter;

                        if(isa<LoadInst>(&I2) && !I2.isVolatile()){
                            LoadInst* l1 = dyn_cast<LoadInst>(&I1);
                            LoadInst* l2 = dyn_cast<LoadInst>(&I2);
                            Value * val1 = l1->getPointerOperand(); //getOperand(0)
                            Value * val2 = l2->getPointerOperand();
                            if (val1 == val2){ 

                                if(I1.getType() == I2.getType()){
                                    if(Value* val = dyn_cast<Value>(&I1)){
                                        CSELdElim++;
                                        I2.replaceAllUsesWith(val);

                                        redundLd_iter++;
                                        I2.eraseFromParent();
                                        continue;
                                    }
                                }
                            }
                        }
                        if(isa<StoreInst>(&I2)){
                            break;
                        }
                        redundLd_iter++;
                    }
                }
                
                //OPT 3 - Eliminating redundant stores (and loads)
                if(isa<StoreInst>(&I1)){
                    auto instr2_iter = instr1_iter;
                    instr2_iter++;
                    
                    while(instr2_iter != bb_iter->end()){
                        Instruction &I2 = *instr2_iter;

                        //Store to Load
                        if(isa<LoadInst>(&I2) && !I2.isVolatile()){
                            StoreInst* st_p = dyn_cast<StoreInst>(&I1);
                            LoadInst* ld_p  = dyn_cast<LoadInst>(&I2);
                            Value * stAddrVal = st_p->getPointerOperand(); //getOperand(1)
                            Value * ldAddrVal = ld_p->getPointerOperand(); //getOperand(0)
                            if (stAddrVal == ldAddrVal){ 

                                if(st_p->getValueOperand()->getType() == I2.getType()){
                                    CSEStore2Load++;
                                    I2.replaceAllUsesWith(st_p->getValueOperand());

                                    instr2_iter++;
                                    I2.eraseFromParent();
                                    continue;
                                }
                            }
                        }

                        //redundant stores
                        // .isSameOperationAs()
                        if(isa<StoreInst>(&I2) && !I2.isVolatile()){
                            StoreInst* st_p = dyn_cast<StoreInst>(&I1);
                            StoreInst* st2_p  = dyn_cast<StoreInst>(&I2);
                            Value * stAddrVal = st_p->getPointerOperand();      //getOperand(1)
                            Value * st2AddrVal = st2_p->getPointerOperand();    //getOperand(1)
                            
                            if (stAddrVal == st2AddrVal){ 

                                if(st_p->getValueOperand()->getType() == st2_p->getValueOperand()->getType()){
                                    CSEStElim++;

                                    instr1_iter++;
                                    erasedInst1 = true;
                                    I1.eraseFromParent();
                                    break;
                                }
                            }
                        }
                        if(isa<StoreInst>(&I2) || isa<LoadInst>(&I2) || I2.mayHaveSideEffects()){
                            break;
                        }

                        instr2_iter++;
                    }
                }
                if(!erasedInst1){
                    instr1_iter++;
                }
            }
        }
    }
}

