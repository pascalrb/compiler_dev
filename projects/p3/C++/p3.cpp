#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <unordered_map>

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
#include "llvm/Analysis/CallGraph.h"
//#include "llvm/Analysis/AnalysisManager.h"

#include "llvm/IR/LLVMContext.h"

#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Pass.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/SourceMgr.h"
#include <memory>

using namespace llvm;

static void DoInlining(Module *);

static void summarize(Module *M);

static void print_csv_file(std::string outputfile);

static cl::opt<std::string>
        InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
        OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
        InlineHeuristic("inline-heuristic",
              cl::desc("Use student's inlining heuristic."),
              cl::init(false));

static cl::opt<bool>
        InlineConstArg("inline-require-const-arg",
              cl::desc("Require function call to have at least one constant argument."),
              cl::init(false));

static cl::opt<int>
        InlineFunctionSizeLimit("inline-function-size-limit",
              cl::desc("Biggest size of function to inline."),
              cl::init(1000000000));

static cl::opt<int>
        InlineGrowthFactor("inline-growth-factor",
              cl::desc("Largest allowed program size increase factor (e.g. 2x)."),
              cl::init(20));


static cl::opt<bool>
        NoInline("no-inline",
              cl::desc("Do not perform inlining."),
              cl::init(false));


static cl::opt<bool>
        NoPreOpt("no-preopt",
              cl::desc("Do not perform pre-inlining optimizations."),
              cl::init(false));

static cl::opt<bool>
        NoPostOpt("no-postopt",
              cl::desc("Do not perform post-inlining optimizations."),
              cl::init(false));

static cl::opt<bool>
        Verbose("verbose",
                    cl::desc("Verbose stats."),
                    cl::init(false));

static cl::opt<bool>
        NoCheck("no",
                cl::desc("Do not check for valid IR."),
                cl::init(false));


static llvm::Statistic nInstrBeforeOpt = {"", "nInstrBeforeOpt", "number of instructions"};
static llvm::Statistic nInstrBeforeInline = {"", "nInstrPreInline", "number of instructions"};
static llvm::Statistic nInstrAfterInline = {"", "nInstrAfterInline", "number of instructions"};
static llvm::Statistic nInstrPostOpt = {"", "nInstrPostOpt", "number of instructions"};


static void countInstructions(Module *M, llvm::Statistic &nInstr) {
  for (auto i = M->begin(); i != M->end(); i++) {
    for (auto j = i->begin(); j != i->end(); j++) {
      for (auto k = j->begin(); k != j->end(); k++) {
	      nInstr++;
      }
    }
  }
}


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

    countInstructions(M.get(),nInstrBeforeOpt);
    
    if (!NoPreOpt) {
      legacy::PassManager Passes;
      Passes.add(createPromoteMemoryToRegisterPass());    
      Passes.add(createEarlyCSEPass());
      Passes.add(createSCCPPass());
      Passes.add(createAggressiveDCEPass());
      Passes.add(createVerifierPass());
      Passes.run(*M);  
    }

    countInstructions(M.get(),nInstrBeforeInline);    

    if (!NoInline) {
        DoInlining(M.get());
    }

    countInstructions(M.get(),nInstrAfterInline);
    
    if (!NoPostOpt) {
      legacy::PassManager Passes;
      Passes.add(createPromoteMemoryToRegisterPass());    
      Passes.add(createEarlyCSEPass());
      Passes.add(createSCCPPass());
      Passes.add(createAggressiveDCEPass());
      Passes.add(createVerifierPass());
      Passes.run(*M);  
    }

    countInstructions(M.get(),nInstrPostOpt);
    
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

static llvm::Statistic Inlined = {"", "Inlined", "Inlined a call."};
static llvm::Statistic ConstArg = {"", "ConstArg", "Call has a constant argument."};
static llvm::Statistic SizeReq = {"", "SizeReq", "Call meets size requirement."};
static llvm::Statistic AdLibHeuristic = {"", "AdLibHeuristic", "Call meets personal heuristic requirement."};

#include "llvm/Transforms/Utils/Cloning.h"

// Function to perform function inlining
static void DoInlining(Module *M) {

  Inlined = 0;
  ConstArg = 0;
  SizeReq = 0;
  AdLibHeuristic = 0;

  std::map<std::string, std::vector<CallInst*> > funcCallsToInline;
  int initialInstrCount = 0;

  //Traversing the entire program, adding function calls to inline into a worklist
  for (auto func_iter = M->begin(); func_iter != M->end(); func_iter++) {
    //llvm::Module::iterator = FunctionListType::iterator

    for (auto bb_iter = func_iter->begin(); bb_iter != func_iter->end(); bb_iter++) {
      //llvm::BasicBlock

      for (auto instr_iter = bb_iter->begin(); instr_iter != bb_iter->end(); instr_iter++) {
        //llvm::Instruction
        initialInstrCount++;

        Instruction &I = *instr_iter;

        CallInst *CI = dyn_cast<CallInst>(&I);
        if(CI){
          Function *F = CI->getCalledFunction();
          if (F) {
            InlineFunctionInfo IFI; 

            InlineResult IR = isInlineViable(*F);   
            if (IR.isSuccess()) {
              funcCallsToInline[F->getName().str()].push_back(CI);
            }
          }
        }
      }
    }
  }

  // Traversing the worklist, performing the inlining
  InlineFunctionInfo IFI;
  int inlineCalleeSize;
  int currentProgramSize = initialInstrCount;
  int growthFactorProgramSizeLimit;
  bool constPresent;
  int growthFactorLim = 3;
  int numOfCallsToFunc = 7; /* based on data gathered, most funcs 
                               get called less than 7 times, 
                               the exceptions >20, sometimes >50 */ 
  int funcBodySizeMax1 = 75;
  int funcBodySizeMax2 = 200; 

  std::map<std::string, std::vector<CallInst*> >:: iterator funcCallsToInline_it;
  for(funcCallsToInline_it = funcCallsToInline.begin(); funcCallsToInline_it != funcCallsToInline.end(); funcCallsToInline_it++){


    if(InlineHeuristic){
    //Ad Libitum heuristic 
      growthFactorProgramSizeLimit = initialInstrCount * growthFactorLim;

      for(int i = 0; i < funcCallsToInline_it->second.size(); i++){
        Function *Callee = funcCallsToInline_it->second[i]->getCalledFunction();
        inlineCalleeSize = Callee->getInstructionCount();

        constPresent = false;

        //always inline if there is a constant in the func argument, while 
        // we're still below the growth factor limit
        for (auto &Arg : funcCallsToInline_it->second[i]->args()) {
          if(isa<Constant>(&Arg)){
            if((currentProgramSize + inlineCalleeSize) <= growthFactorProgramSizeLimit){
              InlineFunction(*funcCallsToInline_it->second[i], IFI);

              currentProgramSize += inlineCalleeSize;              
              AdLibHeuristic++;
              Inlined++;
              constPresent = true;
              break;
            }
          }
        }if (!constPresent){
          //if none of func's argument is a constant, do further checks before inlining 

          if(funcCallsToInline_it->second.size() < numOfCallsToFunc){
            // if the function doesn't get called that often 

            if(inlineCalleeSize < funcBodySizeMax2){
              if((currentProgramSize + inlineCalleeSize) <= growthFactorProgramSizeLimit){
                InlineFunction(*funcCallsToInline_it->second[i], IFI);

                currentProgramSize += inlineCalleeSize;              
                AdLibHeuristic++;
                Inlined++;
              }
            }
          }else{
            if(inlineCalleeSize < funcBodySizeMax1){
              if((currentProgramSize + inlineCalleeSize) <= growthFactorProgramSizeLimit){
                InlineFunction(*funcCallsToInline_it->second[i], IFI);

                currentProgramSize += inlineCalleeSize;              
                AdLibHeuristic++;
                Inlined++;
              }
            }
          }
        }
      }

    }else{
      //basic inling support
      growthFactorProgramSizeLimit = initialInstrCount * InlineGrowthFactor; 

      for(int i = 0; i < funcCallsToInline_it->second.size(); i++){
        Function *Callee = funcCallsToInline_it->second[i]->getCalledFunction();
        inlineCalleeSize = Callee->getInstructionCount();

        if(inlineCalleeSize < InlineFunctionSizeLimit){
          if((currentProgramSize + inlineCalleeSize) <= growthFactorProgramSizeLimit){
            if(InlineConstArg){

              for (auto &Arg : funcCallsToInline_it->second[i]->args()) {
                if(isa<Constant>(&Arg)){
                  InlineFunction(*funcCallsToInline_it->second[i], IFI);
                  currentProgramSize += inlineCalleeSize;

                  ConstArg++;
                  Inlined++;

                  break;
                }
              }

            }else{
              InlineFunction(*funcCallsToInline_it->second[i], IFI);
              currentProgramSize += inlineCalleeSize;

              SizeReq++;
              Inlined++;
            }
          }
        }
      }
    }
  }
}
