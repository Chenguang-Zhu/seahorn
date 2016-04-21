/* 
 * Instrument a program to add null dereference checks
 */

#include "seahorn/Transforms/Instrumentation/NullCheck.hh"

#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"

#include "avy/AvyDebug.h"

namespace seahorn
{
  using namespace llvm;
 
  char NullCheck::ID = 0;

  void NullCheck::insertNullCheck (Value *Ptr, 
                                   IRBuilder<> B,
                                   Instruction* I) {

     B.SetInsertPoint (I);    
     Value* isNull = B.CreateIsNull (Ptr);
     isNull->setName ("null_check");

     if (Constant* C = dyn_cast<Constant> (isNull)) {
       if (ConstantInt* CI = dyn_cast<ConstantInt> (C)) {
         if (CI == ConstantInt::getFalse (B.getContext ())) {
           LOG ("null-check",
                errs () << "Memory access is trivially safe\n";);
           
           TrivialChecks++;
         }
         else if (CI == ConstantInt::getTrue (B.getContext ())) {
           LOG ("null-check",
                errs () << "Memory access is trivially unsafe\n";);
           
           TrivialChecks++;
         }
       }
     }

     
     // Attach debug information to the new instruction
     if (Instruction* isNullI = dyn_cast<Instruction> (isNull)) {
       isNullI->setDebugLoc (I->getDebugLoc ());
       LOG ("null-check",
            errs () << "Added " << *isNullI << "\n";);
       ChecksAdded++;
     }

     TerminatorInst* ThenTerm = nullptr;
     TerminatorInst* ElseTerm = nullptr;

     SplitBlockAndInsertIfThenElse(isNull, I, &ThenTerm, &ElseTerm);

     assert (ThenTerm);

     // ThenTerm is always a BranchInst so this cast should never fail
     BranchInst *BI = cast<BranchInst> (ThenTerm);

     BasicBlock* ErrorBB = createErrorBlock (*I->getParent ()->getParent (), B);
     BI->setSuccessor(0, ErrorBB);
  }

  BasicBlock* NullCheck::createErrorBlock (Function &F, IRBuilder<> B) {
  
    BasicBlock* errBB = BasicBlock::Create(B.getContext (), "NullError", &F);
    B.SetInsertPoint (errBB);    
    CallInst * CI = B.CreateCall (ErrorFn);
    B.CreateUnreachable ();
    
    // update call graph
    if (CG) {
      auto f1 = CG->getOrInsertFunction (&F);
      auto f2 = CG->getOrInsertFunction (ErrorFn);
        f1->addCalledFunction (CallSite (CI), f2);
    }
    return errBB;
  }

  bool NullCheck::runOnFunction (Function &F)
  {
    if (F.isDeclaration ()) return false;

    // We instrument every address only once per basic block
    SmallSet<Value*, 16> TempsToInstrument;
    std::vector<Instruction*> Worklist;
    for (auto&BB : F)  {
      TempsToInstrument.clear();
      for (auto &i: BB) {
        Instruction *I = &i;
        if (isa<LoadInst>(I)) {
          // We've seen this temp in the current BB.
          if (!TempsToInstrument.insert(I).second) continue;  
          Worklist.push_back (I);
        } else if (isa<StoreInst>(I)) {
          // We've seen this temp in the current BB.
          if (!TempsToInstrument.insert(I).second) continue;  
          Worklist.push_back (I);
        }
      }
    }

    LLVMContext &ctx = F.getContext ();
    IRBuilder<> B (ctx);

    bool change = false;    
    for (auto I: Worklist) {
      Value *Ptr = nullptr;
      if (auto *LI = dyn_cast<LoadInst>(I)) {
        Ptr = LI->getPointerOperand();
      } else if (auto *SI = dyn_cast<StoreInst>(I)) {
        Ptr = SI->getPointerOperand();
      }

      // Dereferencing a pointer so we insert a check if the pointer
      // is null
      if (Ptr) {
        insertNullCheck (Ptr, B, I);

        // Add extra memory safety assumption that successful
        // load/store imply validity of their arguments.
        if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(Ptr)) {
          if (gep->isInBounds() && gep->getPointerAddressSpace() == 0) {
            Value* base = gep->getPointerOperand ();
            B.SetInsertPoint (I);
            auto It = B.GetInsertPoint();
            ++It;
            B.SetInsertPoint(I->getParent(), It);
            CallInst* CI = B.CreateCall(AssumeFn, B.CreateIsNotNull(base));
            CI->setDebugLoc (I->getDebugLoc ());
            // update call graph
            if (CG) {
              auto f1 = CG->getOrInsertFunction (&F);
              auto f2 = CG->getOrInsertFunction (AssumeFn);
              f1->addCalledFunction (CallSite (CI), f2);
            }
          }
        }
        change = true;
      }
    }
    return change;
  }

  bool NullCheck::runOnModule (llvm::Module &M) {

    if (M.begin () == M.end ()) return false;
      
    // Get call graph
    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
    if (cgwp) CG = &cgwp->getCallGraph ();

    LLVMContext &ctx = M.getContext ();

    AttrBuilder B;

    AttributeSet as = AttributeSet::get (ctx, 
                                         AttributeSet::FunctionIndex,
                                         B);

    AssumeFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.assume", 
                                as,
                                Type::getVoidTy (ctx),
                                Type::getInt1Ty (ctx),
                                NULL));

    B.addAttribute (Attribute::NoReturn);
    B.addAttribute (Attribute::ReadNone);
    ErrorFn = dyn_cast<Function> (M.getOrInsertFunction ("verifier.error",
                                                         as,
                                                         Type::getVoidTy (ctx), NULL));


    bool change = false;
    for (Function &F : M) {
      change |= runOnFunction (F); 
    }

    errs () << "-- Inserted " << ChecksAdded << " null dereference checks " 
            << " (skipped " << TrivialChecks << " trivial checks).\n";

    return change;
  }
    
  void NullCheck::getAnalysisUsage (llvm::AnalysisUsage &AU) const  {
    AU.setPreservesAll ();
    AU.addRequired<CallGraphWrapperPass> ();
    AU.addPreserved<CallGraphWrapperPass> ();
  } 


}

static llvm::RegisterPass<seahorn::NullCheck> 
X ("null-check", "Insert null dereference checks");
   

