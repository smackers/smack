//===------------ TypeChecks.cpp - Insert runtime type checks -------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass inserts checks to enforce type safety during runtime.
//
//===----------------------------------------------------------------------===//

#include "assistDS/TypeChecks.h"
#include "llvm/Constants.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Module.h"
#include "llvm/Assembly/Writer.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Intrinsics.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/ADT/Statistic.h"

#include <set>
#include <vector>
#include <deque>

using namespace llvm;

char TypeChecks::ID = 0;

static RegisterPass<TypeChecks> 
TC("typechecks", "Insert runtime type checks", false, true);

// Pass statistics
STATISTIC(numLoadChecks,  "Number of Load Insts that need type checks");
STATISTIC(numStoreChecks, "Number of Store Insts that need type checks");
STATISTIC(numTypes, "Number of Types used in the module");

namespace {
  static cl::opt<bool> EnablePointerTypeChecks("enable-ptr-type-checks",
         cl::desc("Distinguish pointer types in loads"),
         cl::Hidden,
         cl::init(false));
  static cl::opt<bool> DisablePtrCmpChecks("no-ptr-cmp-checks",
         cl::desc("Dont instrument cmp statements"),
         cl::Hidden,
         cl::init(false));
  static cl::opt<bool> TrackAllLoads("track-all-loads",
         cl::desc("Check at all loads irrespective of use"),
         cl::Hidden,
         cl::init(false));
}

static int tagCounter = 0;
static Type *VoidTy = 0;
static Type *Int8Ty = 0;
static Type *Int32Ty = 0;
static Type *Int64Ty = 0;
static PointerType *VoidPtrTy = 0;

static Type *TypeTagTy = 0;
static Type *TypeTagPtrTy = 0;

static Constant *One = 0;
static Constant *Zero = 0;

static Constant *RegisterArgv;
static Constant *RegisterEnvp;

static Constant *trackGlobal;
static Constant *trackStoreInst;
static Constant *trackStringInput;
static Constant *trackArray;

static Constant *trackInitInst;
static Constant *trackUnInitInst;

static Constant *getTypeTag;
static Constant *checkTypeInst;

static Constant *copyTypeInfo;
static Constant *setTypeInfo;

static Constant *setVAInfo;
static Constant *copyVAInfo;
static Constant *checkVAArg;

unsigned int TypeChecks::getTypeMarker(Type * Ty) {
  if(!EnablePointerTypeChecks) {
    if(Ty->isPointerTy()) {
      Ty = VoidPtrTy;
    }
  }
  if(UsedTypes.find(Ty) == UsedTypes.end())
    UsedTypes[Ty] = UsedTypes.size();

  assert((UsedTypes.size() < 254) && "Too many types found. Not enough metadata bits");
  return UsedTypes[Ty];
}

unsigned int TypeChecks::getTypeMarker(Value *V) {
  return getTypeMarker(V->getType());
}

unsigned int TypeChecks::getSize(Type *Ty) {
  return TD->getTypeStoreSize(Ty);
}

Constant *TypeChecks::getSizeConstant(Type *Ty) {
  return (ConstantInt::get(Int64Ty, getSize(Ty)));
}

static Constant *getTagCounter() {
  return ConstantInt::get(Int32Ty, tagCounter++);
}

Constant *TypeChecks::getTypeMarkerConstant(Value * V) {
  return ConstantInt::get(TypeTagTy, getTypeMarker(V));
}

Constant *TypeChecks::getTypeMarkerConstant(Type *T) {
  return ConstantInt::get(TypeTagTy, getTypeMarker(T));
}

static inline Value *
castTo (Value * V, Type * Ty, std::string Name, Instruction * InsertPt) {
  //
  // Don't bother creating a cast if it's already the correct type.
  //
  if (V->getType() == Ty)
    return V;

  //
  // If it's a constant, just create a constant expression.
  //
  if (Constant * C = dyn_cast<Constant>(V)) {
    Constant * CE = ConstantExpr::getZExtOrBitCast (C, Ty);
    return CE;
  }

  //
  // Otherwise, insert a cast instruction.
  //
  return CastInst::CreateZExtOrBitCast (V, Ty, Name, InsertPt);
}

bool TypeChecks::runOnModule(Module &M) {
  bool modified = false; // Flags whether we modified the module.
  bool transformIndirectCalls = true;

  TD = &getAnalysis<DataLayout>();
  addrAnalysis = &getAnalysis<AddressTakenAnalysis>();

  // Create the necessary prototypes
  VoidTy = IntegerType::getVoidTy(M.getContext());
  Int8Ty = IntegerType::getInt8Ty(M.getContext());
  Int32Ty = IntegerType::getInt32Ty(M.getContext());
  Int64Ty = IntegerType::getInt64Ty(M.getContext());
  VoidPtrTy = PointerType::getUnqual(Int8Ty);

  TypeTagTy = Int8Ty;
  TypeTagPtrTy = PointerType::getUnqual(TypeTagTy);

  One = ConstantInt::get(Int64Ty, 1);
  Zero = ConstantInt::get(Int64Ty, 0);

  // Add prototypes for the dynamic type checking functions
  initRuntimeCheckPrototypes(M);

  UsedTypes.clear(); // Reset if run multiple times.
  VAArgFunctions.clear();
  ByValFunctions.clear();
  AddressTakenFunctions.clear();

  // Only works for whole program analysis
  Function *MainF = M.getFunction("main");
  if (MainF == 0 || MainF->isDeclaration()) {
    assert(0 && "No main function found");
    return false;
  }

  // Insert the shadow initialization function.
  modified |= initShadow(M);

  // Record argv/envp
  modified |= visitMain(M, *MainF);

  // Recognize special cases
  for (Module::iterator MI = M.begin(), ME = M.end(); MI != ME; ++MI) {
    Function &F = *MI;
    if(F.isDeclaration()) {
      if(addrAnalysis->hasAddressTaken(&F))
        transformIndirectCalls = false;

      continue;
    }

    std::string name = F.getName();
    if (strncmp(name.c_str(), "tc.", 3) == 0) continue;
    if (strncmp(name.c_str(), "main", 4) == 0) continue;

    // Iterate and find all byval functions
    bool hasByValArg = false;
    for (Function::arg_iterator I = F.arg_begin(); I != F.arg_end(); ++I) {
      if (I->hasByValAttr()) {
        hasByValArg = true;
        break;
      }
    }
    if(hasByValArg) {
      ByValFunctions.push_back(&F);
    }

    // Iterate and find all address taken functions
    if(addrAnalysis->hasAddressTaken(&F)) {
      AddressTakenFunctions.push_back(&F);
    }

    // Iterate and find all varargs functions
    if(F.isVarArg()) {
      VAArgFunctions.push_back(&F);
      continue;
    }
  }

  // Modify all byval functions
  while(!ByValFunctions.empty()) {
    Function *F = ByValFunctions.back();
    ByValFunctions.pop_back();
    modified |= visitByValFunction(M, *F);
  }

  // Modify all the var arg functions
  while(!VAArgFunctions.empty()) {
    Function *F = VAArgFunctions.back();
    VAArgFunctions.pop_back();
    assert(F->isVarArg());
    modified |= visitVarArgFunction(M, *F);
  }

  // Modify all the address taken functions
  if(transformIndirectCalls) {
    while(!AddressTakenFunctions.empty()) {
      Function *F = AddressTakenFunctions.back();
      AddressTakenFunctions.pop_back();
      if(F->isVarArg())
        continue;
      visitAddressTakenFunction(M, *F);
    }
  }

  for (Module::iterator MI = M.begin(), ME = M.end(); MI != ME; ++MI) {
    Function &F = *MI;
    if(F.isDeclaration())
      continue;
    DominatorTree & DT = getAnalysis<DominatorTree>(F);
    std::deque<DomTreeNode *> Worklist;
    Worklist.push_back (DT.getRootNode());
    while(Worklist.size()) {
      DomTreeNode * Node = Worklist.front();
      Worklist.pop_front();
      BasicBlock *BB = Node->getBlock();
      for (BasicBlock::iterator bi = BB->begin(); bi != BB->end(); ++bi) {
        Instruction &I = *bi;
        if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
          modified |= visitStoreInst(M, *SI);
        } else if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
          modified |= visitLoadInst(M, *LI);
        } else if (CallInst *CI = dyn_cast<CallInst>(&I)) {
          modified |= visitCallInst(M, *CI);
        } else if (InvokeInst *II = dyn_cast<InvokeInst>(&I)) {
          modified |= visitInvokeInst(M, *II);
        } else if (AllocaInst *AI = dyn_cast<AllocaInst>(&I)) {
          modified |= visitAllocaInst(M, *AI);
        } else if (VAArgInst *VI = dyn_cast<VAArgInst>(&I)) {
          modified |= visitVAArgInst(M, *VI);
        }
      }
      Worklist.insert(Worklist.end(), Node->begin(), Node->end());
    }

    // Loop over all of the instructions in the function,
    // adding instrumentation where needed.
    /*for (inst_iterator II = inst_begin(F), IE = inst_end(F); II != IE;++II) {
      Instruction &I = *II;
      if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
        modified |= visitStoreInst(M, *SI);
      } else if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
        modified |= visitLoadInst(M, *LI);
      } else if (CallInst *CI = dyn_cast<CallInst>(&I)) {
        modified |= visitCallInst(M, *CI);
      } else if (InvokeInst *II = dyn_cast<InvokeInst>(&I)) {
        modified |= visitInvokeInst(M, *II);
      } else if (AllocaInst *AI = dyn_cast<AllocaInst>(&I)) {
        modified |= visitAllocaInst(M, *AI);
      } else if (VAArgInst *VI = dyn_cast<VAArgInst>(&I)) {
        modified |= visitVAArgInst(M, *VI);
      }
    }*/
  }

  // visit all the indirect call sites
  if(transformIndirectCalls) {
    std::set<Instruction*>::iterator II = IndCalls.begin();
    for(; II != IndCalls.end();) {
      Instruction *I = *II++;
      modified |= visitIndirectCallSite(M,I);
    }
  }

  // visit all the uses of the address taken functions and var arg functions and modify if
  // not being passed to external code
  std::map<Function *, Function * >::iterator FI = IndFunctionsMap.begin(), FE = IndFunctionsMap.end();
  for(;FI!=FE;++FI) {
    Function *F = FI->first;

    Constant *CNew = ConstantExpr::getBitCast(FI->second, F->getType());

    std::set<User *> toReplace;
    for(Function::use_iterator User = F->use_begin();
        User != F->use_end();++User) {
      toReplace.insert(*User);
    }
    for(std::set<llvm::User *>::iterator userI = toReplace.begin(); userI != toReplace.end(); ++userI) {
      llvm::User * user = *userI;
      if(Constant *C = dyn_cast<Constant>(user)) {
        if(!isa<GlobalValue>(C)) {
          bool changeUse = true;
          for(Value::use_iterator II = user->use_begin();
              II != user->use_end(); II++) {
            if(CallInst *CI = dyn_cast<CallInst>(*II))
              if(CI->getCalledFunction()) {
                if(CI->getCalledFunction()->isDeclaration())
                  changeUse = false;
              }
          }
          if(!changeUse)
            continue;
          std::vector<Use *> ReplaceWorklist;
          for (User::op_iterator use = user->op_begin();
               use != user->op_end();
               ++use) {
            if (use->get() == F) {
              ReplaceWorklist.push_back (use);
            }
          }

          //
          // Do replacements in the worklist.
          // Special case for ContantArray(triggered by 253.perl)
          // ConstantArray::replaceUsesOfWithOnConstant, replace all uses
          // in that constant, unlike the other versions, which  only
          // replace the use specified in ReplaceWorklist.
          //
          if(isa<ConstantArray>(C)) {
              C->replaceUsesOfWithOnConstant(F, CNew, ReplaceWorklist[0]);
          } else {
            for (unsigned index = 0; index < ReplaceWorklist.size(); ++index) {
              C->replaceUsesOfWithOnConstant(F, CNew, ReplaceWorklist[index]);
            }
          }
          continue;
        }
      }
      if(CallInst *CI = dyn_cast<CallInst>(user)) {
        if(CI->getCalledFunction()) {
          if(CI->getCalledFunction()->isDeclaration())
            continue;
        }
      }
      user->replaceUsesOfWith(F, CNew);
    }
  }

  // remove redundant checks, caused due to insturmenting uses of loads
  // Remove a check if it is dominated by another check for the same instruction
  optimizeChecks(M);

  // add a global that contains the mapping from metadata to strings
  addTypeMap(M);

  // Update stats
  numTypes += UsedTypes.size();

  return modified;
}

void TypeChecks::initRuntimeCheckPrototypes(Module &M) {

  RegisterArgv = M.getOrInsertFunction("trackArgvType",
                                       VoidTy,
                                       Int32Ty, /*argc */
                                       VoidPtrTy->getPointerTo(),/*argv*/
                                       NULL);

  RegisterEnvp = M.getOrInsertFunction("trackEnvpType",
                                       VoidTy,
                                       VoidPtrTy->getPointerTo(),/*envp*/
                                       NULL);

  trackGlobal = M.getOrInsertFunction("trackGlobal",
                                      VoidTy,
                                      VoidPtrTy,/*ptr*/
                                      TypeTagTy,/*type*/
                                      Int64Ty,/*size*/
                                      Int32Ty,/*tag*/
                                      NULL);

  trackArray = M.getOrInsertFunction("trackArray",
                                     VoidTy,
                                     VoidPtrTy,/*ptr*/
                                     Int64Ty,/*size*/
                                     Int64Ty,/*count*/
                                     Int32Ty,/*tag*/
                                     NULL);

  trackInitInst = M.getOrInsertFunction("trackInitInst",
                                        VoidTy,
                                        VoidPtrTy,/*ptr*/
                                        Int64Ty,/*size*/
                                        Int32Ty,/*tag*/
                                        NULL);

  trackUnInitInst = M.getOrInsertFunction("trackUnInitInst",
                                          VoidTy,
                                          VoidPtrTy,/*ptr*/
                                          Int64Ty,/*size*/
                                          Int32Ty,/*tag*/
                                          NULL);

  trackStoreInst = M.getOrInsertFunction("trackStoreInst",
                                         VoidTy,
                                         VoidPtrTy,/*ptr*/
                                         TypeTagTy,/*type*/
                                         Int64Ty,/*size*/
                                         Int32Ty,/*tag*/
                                         NULL);
  getTypeTag = M.getOrInsertFunction("getTypeTag",
                                     VoidTy,
                                     VoidPtrTy, /*ptr*/
                                     Int64Ty, /*size*/
                                     TypeTagPtrTy, /*dest for type tag*/
                                     Int32Ty, /*tag*/
                                     NULL);
  checkTypeInst = M.getOrInsertFunction("checkType",
                                        VoidTy,
                                        TypeTagTy,/*type*/
                                        Int64Ty,/*size*/
                                        TypeTagPtrTy,/*ptr to metadata*/
                                        VoidPtrTy,/*ptr*/
                                        Int32Ty,/*tag*/
                                        NULL);
  setTypeInfo = M.getOrInsertFunction("setTypeInfo",
                                      VoidTy,
                                      VoidPtrTy,/*dest ptr*/
                                      TypeTagPtrTy,/*metadata*/
                                      Int64Ty,/*size*/
                                      TypeTagTy,
                                      VoidPtrTy, /*src ptr*/
                                      Int32Ty,/*tag*/
                                      NULL);
  copyTypeInfo = M.getOrInsertFunction("copyTypeInfo",
                                       VoidTy,
                                       VoidPtrTy,/*dest ptr*/
                                       VoidPtrTy,/*src ptr*/
                                       Int64Ty,/*size*/
                                       Int32Ty,/*tag*/
                                       NULL);
  trackStringInput = M.getOrInsertFunction("trackStringInput",
                                           VoidTy,
                                           VoidPtrTy,
                                           Int32Ty,
                                           NULL);
  setVAInfo = M.getOrInsertFunction("setVAInfo",
                                    VoidTy,
                                    VoidPtrTy,/*va_list ptr*/
                                    Int64Ty,/*total num of elements in va_list */
                                    TypeTagPtrTy,/*ptr to metadta*/
                                    Int32Ty,/*tag*/
                                    NULL);
  copyVAInfo = M.getOrInsertFunction("copyVAInfo",
                                     VoidTy,
                                     VoidPtrTy,/*dst va_list*/
                                     VoidPtrTy,/*src va_list */
                                     Int32Ty,/*tag*/
                                     NULL);
  checkVAArg = M.getOrInsertFunction("checkVAArgType",
                                     VoidTy,
                                     VoidPtrTy,/*va_list ptr*/
                                     TypeTagTy,/*type*/
                                     Int32Ty,/*tag*/
                                     NULL);

}

// Delete checks, if it is dominated by another check for the same value.
// We might get multiple checks on a path, if there are multiple uses of
// a load inst.

void TypeChecks::optimizeChecks(Module &M) {
  for (Module::iterator MI = M.begin(), ME = M.end(); MI != ME; ++MI) {
    Function &F = *MI;
    if(F.isDeclaration())
      continue;
    DominatorTree & DT = getAnalysis<DominatorTree>(F);
    std::deque<DomTreeNode *> Worklist;
    Worklist.push_back (DT.getRootNode());
    while(Worklist.size()) {
      DomTreeNode * Node = Worklist.front();
      Worklist.pop_front();
      BasicBlock *BB = Node->getBlock();
      for (BasicBlock::iterator bi = BB->begin(); bi != BB->end(); ++bi) {
        CallInst *CI = dyn_cast<CallInst>(bi);
        if(!CI)
          continue;
        if(CI->getCalledFunction() != checkTypeInst)
          continue;
        std::list<Instruction *>toDelete;
        for(Value::use_iterator User = CI->getOperand(3)->use_begin(); User != CI->getOperand(3)->use_end(); ++User) {
          CallInst *CI2 = dyn_cast<CallInst>(*User);
          if(!CI2)
            continue;
          if(CI2 == CI)
            continue;
          // Check that they are refering to the same pointer
          if(CI->getOperand(4) != CI2->getOperand(4))
            continue;
          // Check that they are using the same metadata for comparison.
          if(CI->getOperand(3) != CI2->getOperand(3))
            continue;
          if(!DT.dominates(CI, CI2))
            continue;
          // if CI, dominates CI2, delete CI2
          toDelete.push_back(CI2);
        }
        while(!toDelete.empty()) {
          Instruction *I = toDelete.back();
          toDelete.pop_back();
          I->eraseFromParent();
        }
      }
      Worklist.insert(Worklist.end(), Node->begin(), Node->end());
    }
  }
  for (Module::iterator MI = M.begin(), ME = M.end(); MI != ME; ++MI) {
    Function &F = *MI;
    if(F.isDeclaration())
      continue;
    DominatorTree & DT = getAnalysis<DominatorTree>(F);
    LoopInfo & LI = getAnalysis<LoopInfo>(F);
    std::deque<DomTreeNode *> Worklist;
    Worklist.push_back (DT.getRootNode());
    while(Worklist.size()) {
      DomTreeNode * Node = Worklist.front();
      Worklist.pop_front();
      Worklist.insert(Worklist.end(), Node->begin(), Node->end());
      BasicBlock *BB = Node->getBlock();
      Loop *L = LI.getLoopFor(BB);
      if(!L)
        continue;
      if(!L->getLoopPreheader())
        continue;
      for (BasicBlock::iterator bi = BB->begin(); bi != BB->end(); ) {
        CallInst *CI = dyn_cast<CallInst>(bi++);
        if(!CI)
          continue;
        if(CI->getCalledFunction() != checkTypeInst)
          continue;
        bool hoist = true;
        // The instruction is loop invariant if all of its operands are loop-invariant
        for (unsigned i = 1, e = CI->getNumOperands(); i != e; ++i)
          if (!L->isLoopInvariant(CI->getOperand(i)))
            hoist = false;

        if(hoist) {
          CI->removeFromParent();
          L->getLoopPreheader()->getInstList().insert(L->getLoopPreheader()->getTerminator(), CI);
        }
      }
    }
  }
}

// add a global that has the metadata -> typeString mapping
void TypeChecks::addTypeMap(Module &M) {

  // Declare the type of the global
  ArrayType*  AType = ArrayType::get(VoidPtrTy, UsedTypes.size() + 1);
  std::vector<Constant *> Values;
  Values.reserve(UsedTypes.size() + 1);

  // Declare indices useful for creating a GEP
  std::vector<Constant *> Indices;
  Indices.push_back(ConstantInt::get(Int32Ty,0));
  Indices.push_back(ConstantInt::get(Int32Ty,0));

  // Add an entry for uninitialized(Type Number = 0)

  Constant *CA = ConstantDataArray::getString(M.getContext(),
                                              "UNINIT", true);
  GlobalVariable *GV = new GlobalVariable(M, 
                                          CA->getType(),
                                          true,
                                          GlobalValue::ExternalLinkage,
                                          CA,
                                          "");
  GV->setInitializer(CA);
  Constant *C = ConstantExpr::getGetElementPtr(GV,Indices);
  Values[0] = C;

  // For each used type, create a new entry. 
  // Also add these strings to the Values list
  std::map<Type*, unsigned int >::iterator TI = UsedTypes.begin(),
    TE = UsedTypes.end(); 
  for(;TI!=TE; ++TI) {
    std::string *type = new std::string();
    llvm::raw_string_ostream *test = new llvm::raw_string_ostream(*type);

    *test << TI->first;
    //WriteTypeSymbolic(*test, TI->first, &M);
    Constant *CA = ConstantDataArray::getString(M.getContext(),
                                                test->str(), true);
    GlobalVariable *GV = new GlobalVariable(M, 
                                            CA->getType(),
                                            true,
                                            GlobalValue::ExternalLinkage,
                                            CA,
                                            "");
    GV->setInitializer(CA);
    Constant *C = ConstantExpr::getGetElementPtr(GV, Indices);
    Values[TI->second]= C;
  }

  new GlobalVariable(M, 
                     AType,
                     true,
                     GlobalValue::ExternalLinkage,
                     ConstantArray::get(AType,Values),
                     "typeNames"
                    );
}

// For each address taken function, create a clone
// that takes 2 extra arguments(same as a var arg function).
// Modify call sites.
bool TypeChecks::visitAddressTakenFunction(Module &M, Function &F) {
  // Clone function
  // 1. Create the new argument types vector
  std::vector<Type*> TP;
  TP.push_back(Int64Ty); // for count
  TP.push_back(VoidPtrTy); // for MD
  for(Function::arg_iterator I = F.arg_begin(); I !=F.arg_end(); ++I) {
    TP.push_back(I->getType());
  }

  // 2. Create the new function prototype
  FunctionType *NewFTy = FunctionType::get(F.getReturnType(),
                                                 TP,
                                                 false);
  Function *NewF = Function::Create(NewFTy,
                                    GlobalValue::InternalLinkage,
                                    F.getName().str() + ".mod",
                                    &M);

  // 3. Set the mapping for the args
  Function::arg_iterator NI = NewF->arg_begin();
  ValueToValueMapTy ValueMap;
  NI->setName("TotalCount");
  NI++;
  NI->setName("MD");
  NI++;
  for(Function::arg_iterator II = F.arg_begin(); 
      NI!=NewF->arg_end(); ++II, ++NI) {
    // Each new argument maps to the argument in the old function
    // For each of these also copy attributes
    ValueMap[II] = NI;
    NI->setName(II->getName());
    NI->addAttr(F.getAttributes().getParamAttributes(II->getArgNo()+1));
  }

  // 4. Copy over attributes for the function
  NewF->setAttributes(NewF->getAttributes()
                      .addAttr(M.getContext(), 0, F.getAttributes().getRetAttributes()));
  NewF->setAttributes(NewF->getAttributes()
                      .addAttr(M.getContext(), ~0, F.getAttributes().getFnAttributes()));

  // 5. Perform the cloning
  SmallVector<ReturnInst*, 100>Returns;
  // TODO: Review the boolean flag here
  CloneFunctionInto(NewF, &F, ValueMap, true, Returns);
  // Store in the map of original -> cloned function
  IndFunctionsMap[&F] = NewF;

  std::vector<Instruction *>toDelete;
  // Find all uses of the function
  for(Value::use_iterator ui = F.use_begin(), ue = F.use_end();
      ui != ue;++ui)  {
    if(InvokeInst *II = dyn_cast<InvokeInst>(*ui)) {
      if(II->getCalledValue()->stripPointerCasts() != &F)
        continue;
      std::vector<Value *> Args;
      inst_iterator InsPt = inst_begin(II->getParent()->getParent());
      unsigned int i;
      unsigned int NumArgs = II->getNumOperands() - 3;
      Value *NumArgsVal = ConstantInt::get(Int32Ty, NumArgs);
      AllocaInst *AI = new AllocaInst(TypeTagTy, NumArgsVal, "", &*InsPt);
      // set the metadata for the varargs in AI
      for(i = 3; i <II->getNumOperands(); i++) {
        Value *Idx[1];
        Idx[0] = ConstantInt::get(Int32Ty, i - 3 );
        // For each vararg argument, also add its type information
        GetElementPtrInst *GEP = GetElementPtrInst::CreateInBounds(AI,Idx, "", II);
        Constant *C = getTypeMarkerConstant(II->getOperand(i));
        new StoreInst(C, GEP, II);
      }

      // As the first argument pass the number of var_arg arguments
      Args.push_back(ConstantInt::get(Int64Ty, NumArgs));
      Args.push_back(AI);
      for(i = 3 ;i < II->getNumOperands(); i++) {
        // Add the original argument
        Args.push_back(II->getOperand(i));
      }

      // Create the new call
      InvokeInst *II_New = InvokeInst::Create(NewF,
                                              II->getNormalDest(),
                                              II->getUnwindDest(),
                                              Args,
                                              "", II);
      II->replaceAllUsesWith(II_New);
      toDelete.push_back(II);
    }
    // Check for call sites
    else if(CallInst *CI = dyn_cast<CallInst>(*ui)) {
      if(CI->getCalledValue()->stripPointerCasts() != &F)
        continue;
      std::vector<Value *> Args;
      unsigned int i;
      unsigned int NumArgs = CI->getNumOperands() - 1;
      inst_iterator InsPt = inst_begin(CI->getParent()->getParent());
      Value *NumArgsVal = ConstantInt::get(Int32Ty, NumArgs);
      AllocaInst *AI = new AllocaInst(TypeTagTy, NumArgsVal, "", &*InsPt);
      // set the metadata for the varargs in AI
      for(i = 1; i <CI->getNumOperands(); i++) {
        Value *Idx[1];
        Idx[0] = ConstantInt::get(Int32Ty, i - 1 );
        // For each vararg argument, also add its type information
        GetElementPtrInst *GEP = GetElementPtrInst::CreateInBounds(AI,Idx, "", CI);
        Constant *C = getTypeMarkerConstant(CI->getOperand(i));
        new StoreInst(C, GEP, CI);
      }

      // As the first argument pass the number of var_arg arguments
      Args.push_back(ConstantInt::get(Int64Ty, NumArgs));
      Args.push_back(AI);
      for(i = 1 ;i < CI->getNumOperands(); i++) {
        // Add the original argument
        Args.push_back(CI->getOperand(i));
      }

      // Create the new call
      CallInst *CI_New = CallInst::Create(NewF, Args, "", CI);
      CI->replaceAllUsesWith(CI_New);
      toDelete.push_back(CI);
    }
  }
  while(!toDelete.empty()) {
    Instruction *I = toDelete.back();
    toDelete.pop_back();
    I->eraseFromParent();
  }

  return true;
}

// Transform Variable Argument functions, by also passing
// the relavant metadata info
bool TypeChecks::visitVarArgFunction(Module &M, Function &F) {
  if(F.hasInternalLinkage()) {
    return visitInternalVarArgFunction(M, F);
  }

  // create internal clone
  ValueToValueMapTy VMap;
  Function *F_clone = CloneFunction(&F, VMap, false);
  F_clone->setName(F.getName().str() + "internal");
  F.setLinkage(GlobalValue::InternalLinkage);
  F.getParent()->getFunctionList().push_back(F_clone);
  F.replaceAllUsesWith(F_clone);
  return visitInternalVarArgFunction(M, *F_clone);
}

// each vararg function is modified so that the first
// argument is the number of arguments passed in,
// and the second is a pointer to a metadata array, 
// containing type information for each of the arguments

// These are read and stored at the beginning of the function.

// We keep a counter for the number of arguments accessed
// from the va_list(Counter). It is incremented and 
// checked on every va_arg access. It is initialized to zero.
// It is also reset to zero on a call to va_start.

// Similiarly we check type on every va_arg access.

// Aside from this, this function also transforms all
// callsites of the var_arg function.

bool TypeChecks::visitInternalVarArgFunction(Module &M, Function &F) {

  // Clone function
  // 1. Create the new argument types vector
  std::vector<Type*> TP;
  TP.push_back(Int64Ty); // for count
  TP.push_back(TypeTagPtrTy); // for MD
  for(Function::arg_iterator I = F.arg_begin(); I !=F.arg_end(); ++I) {
    TP.push_back(I->getType());
  }

  // 2. Create the new function prototype
  FunctionType *NewFTy = FunctionType::get(F.getReturnType(),
                                                 TP,
                                                 true);
  Function *NewF = Function::Create(NewFTy,
                                    GlobalValue::InternalLinkage,
                                    F.getName().str() + ".vararg",
                                    &M);

  // 3. Set the mapping for the args
  Function::arg_iterator NI = NewF->arg_begin();
  ValueToValueMapTy ValueMap;
  NI->setName("TotalArgCount");
  NI++;
  NI->setName("MD");
  NI++;
  for(Function::arg_iterator II = F.arg_begin(); 
      NI!=NewF->arg_end(); ++II, ++NI) {
    // Each new argument maps to the argument in the old function
    // For each of these also copy attributes
    ValueMap[II] = NI;
    NI->setName(II->getName());
    NI->addAttr(F.getAttributes().getParamAttributes(II->getArgNo()+1));
  }

  // 4. Copy over attributes for the function
  NewF->setAttributes(NewF->getAttributes()
                      .addAttr(M.getContext(), 0, F.getAttributes().getRetAttributes()));
  NewF->setAttributes(NewF->getAttributes()
                      .addAttr(M.getContext(), ~0, F.getAttributes().getFnAttributes()));

  // 5. Perform the cloning
  SmallVector<ReturnInst*, 100>Returns;
  // TODO: Review the boolean flag here
  CloneFunctionInto(NewF, &F, ValueMap, true, Returns);


  // Store the information
  inst_iterator InsPt = inst_begin(NewF);
  Function::arg_iterator NII = NewF->arg_begin();
  // Subtract the number of initial arguments
  Constant *InitialArgs = ConstantInt::get(Int64Ty, F.arg_size());
  Instruction *NewValue = BinaryOperator::Create(BinaryOperator::Sub,
                                                 NII,
                                                 InitialArgs,
                                                 "varargs",
                                                 &*InsPt);
  NII++;

  // Increment by the number of Initial Args, so as to not read the metadata
  //for those.
  Value *Idx[1];
  Idx[0] = InitialArgs;
  // For each vararg argument, also add its type information
  GetElementPtrInst *GEP = GetElementPtrInst::CreateInBounds(NII,Idx, "", &*InsPt);
  // visit all VAStarts and initialize the counter
  for (Function::iterator B = NewF->begin(), FE = NewF->end(); B != FE; ++B) {
    for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE;I++) {
      CallInst *CI = dyn_cast<CallInst>(I);
      if(!CI)
        continue;
      Function *CalledF = dyn_cast<Function>(CI->getCalledFunction());
      if(!CalledF)
        continue;
      if(!CalledF->isIntrinsic())
        continue;
      if(CalledF->getIntrinsicID() != Intrinsic::vastart) 
        continue;
      // Reinitialize the counter
      Value *BCI = castTo(CI->getArgOperand(0), VoidPtrTy, "", CI);
      std::vector<Value *> Args;
      Args.push_back(BCI);
      Args.push_back(NewValue);
      Args.push_back(GEP);
      Args.push_back(getTagCounter());
      CallInst::Create(setVAInfo, Args, "", CI);
    }
  }

  // Find all va_copy calls
  for (Function::iterator B = NewF->begin(), FE = NewF->end(); B != FE; ++B) {
    for (BasicBlock::iterator I = B->begin(), BE = B->end(); I != BE;I++) {
      CallInst *CI = dyn_cast<CallInst>(I);
      if(!CI)
        continue;
      Function *CalledF = dyn_cast<Function>(CI->getCalledFunction());
      if(!CalledF)
        continue;
      if(!CalledF->isIntrinsic())
        continue;
      if(CalledF->getIntrinsicID() != Intrinsic::vacopy) 
        continue;
      Value *BCI_Src = castTo(CI->getArgOperand(1), VoidPtrTy, "", CI);
      Value *BCI_Dest = castTo(CI->getArgOperand(0), VoidPtrTy, "", CI);
      std::vector<Value *> Args;
      Args.push_back(BCI_Dest);
      Args.push_back(BCI_Src);
      Args.push_back(getTagCounter());
      CallInst::Create(copyVAInfo, Args, "", CI);
    }
  }

  std::vector<Instruction *>toDelete;
  // Find all uses of the function
  for(Value::use_iterator ui = F.use_begin(), ue = F.use_end();
      ui != ue;ui ++)  {

    // Check for call sites
    if(InvokeInst *II = dyn_cast<InvokeInst>(*ui)) {
      std::vector<Value *> Args;
      inst_iterator InsPt = inst_begin(II->getParent()->getParent());
      unsigned int i;
      unsigned int NumArgs = II->getNumOperands() - 3;
      Value *NumArgsVal = ConstantInt::get(Int32Ty, NumArgs);
      AllocaInst *AI = new AllocaInst(TypeTagTy, NumArgsVal, "", &*InsPt);
      // set the metadata for the varargs in AI
      for(i = 3; i <II->getNumOperands(); i++) {
        Value *Idx[1];
        Idx[0] = ConstantInt::get(Int32Ty, i - 3 );
        // For each vararg argument, also add its type information
        GetElementPtrInst *GEP = GetElementPtrInst::CreateInBounds(AI, Idx, "", II);
        Constant *C = getTypeMarkerConstant(II->getOperand(i));
        new StoreInst(C, GEP, II);
      }

      // As the first argument pass the number of var_arg arguments
      Args.push_back(ConstantInt::get(Int64Ty, NumArgs));
      Args.push_back(AI);
      for(i = 3 ;i < II->getNumOperands(); i++) {
        // Add the original argument
        Args.push_back(II->getOperand(i));
      }

      // Create the new call
      InvokeInst *II_New = InvokeInst::Create(NewF, 
                                              II->getNormalDest(),
                                              II->getUnwindDest(),
                                              Args,
                                              "", II);
      II->replaceAllUsesWith(II_New);
      toDelete.push_back(II);
    } else if (CallInst *CI = dyn_cast<CallInst>(*ui)) {
      std::vector<Value *> Args;
      inst_iterator InsPt = inst_begin(CI->getParent()->getParent());
      unsigned int i;
      unsigned int NumArgs = CI->getNumArgOperands();
      Value *NumArgsVal = ConstantInt::get(Int32Ty, NumArgs);
      AllocaInst *AI = new AllocaInst(TypeTagTy, NumArgsVal, "", &*InsPt);
      // set the metadata for the varargs in AI
      for(i = 0; i <CI->getNumArgOperands(); i++) {
        Value *Idx[1];
        Idx[0] = ConstantInt::get(Int32Ty, i);
        // For each vararg argument, also add its type information
        GetElementPtrInst *GEP = GetElementPtrInst::CreateInBounds(AI,Idx, "", CI);
        Constant *C = getTypeMarkerConstant(CI->getArgOperand(i));
        new StoreInst(C, GEP, CI);
      }

      // As the first argument pass the number of var_arg arguments
      Args.push_back(ConstantInt::get(Int64Ty, NumArgs));
      Args.push_back(AI);
      for(i = 0 ;i < CI->getNumArgOperands(); i++) {
        // Add the original argument
        Args.push_back(CI->getArgOperand(i));
      }

      // Create the new call
      CallInst *CI_New = CallInst::Create(NewF, Args, "", CI);
      CI->replaceAllUsesWith(CI_New);
      toDelete.push_back(CI);
    }
  }
  while(!toDelete.empty()) {
    Instruction *I = toDelete.back();
    toDelete.pop_back();
    I->eraseFromParent();
  }
  IndFunctionsMap[&F] = NewF;
  return true;
}

bool TypeChecks::visitByValFunction(Module &M, Function &F) {

  // For internal functions
  //   Replace with a function with a a new function with no byval attr.
  //   Add an explicity copy in the function
  //   Also update all the call sites.

  // For external functions
  //  Create an internal clone (treated same as internal functions)
  //  Modify the original function
  //  To assume that the metadata for the byval arguments is TOP 

  if(F.hasInternalLinkage()) {
    visitInternalByValFunction(M, F);
  } else {
    // create internal clone
    ValueToValueMapTy VMap;
    Function *F_clone = CloneFunction(&F, VMap, false);
    F_clone->setName(F.getName().str() + "internal");
    F.setLinkage(GlobalValue::InternalLinkage);
    F.getParent()->getFunctionList().push_back(F_clone);
    F.replaceAllUsesWith(F_clone);
    visitInternalByValFunction(M, *F_clone);
    visitExternalByValFunction(M, F);
  }
  return true;
}

bool TypeChecks::visitInternalByValFunction(Module &M, Function &F) {

  // for every byval argument
  // add an alloca, a load, and a store inst
  Instruction * InsertBefore = &(F.getEntryBlock().front());
  for (Function::arg_iterator I = F.arg_begin(); I != F.arg_end(); ++I) {
    if (!I->hasByValAttr())
      continue;
    assert(I->getType()->isPointerTy());
    Type *ETy = (cast<PointerType>(I->getType()))->getElementType();
    AllocaInst *AI = new AllocaInst(ETy, "", InsertBefore);
    // Do this before adding the load/store pair, so that those uses are not replaced.
    I->replaceAllUsesWith(AI);
    LoadInst *LI = new LoadInst(I, "", InsertBefore);
    new StoreInst(LI, AI, InsertBefore);
  }

  // Update the call sites
  std::vector<Instruction *>toDelete;
  for(Value::use_iterator ui = F.use_begin(), ue = F.use_end();
      ui != ue; ui++)  {
    // Check that F is the called value
    if(InvokeInst *II = dyn_cast<InvokeInst>(*ui)) {
      if(II->getCalledFunction() == &F) {
        SmallVector<Value*, 8> Args;
        SmallVector<AttributeWithIndex, 8> AttributesVec;

        // Get the initial attributes of the call
        AttrListPtr CallPAL = II->getAttributes();
        Attributes RAttrs = CallPAL.getRetAttributes();
        Attributes FnAttrs = CallPAL.getFnAttributes();

        if (RAttrs.hasAttributes())
          AttributesVec.push_back(AttributeWithIndex::get(0, RAttrs));

        Function::arg_iterator NI = F.arg_begin();
        for(unsigned j =3;j<II->getNumOperands();j++, NI++) {
          // Add the original argument
          Args.push_back(II->getOperand(j));
          // If there are attributes on this argument, copy them to the correct 
          // position in the AttributesVec
          //FIXME: copy the rest of the attributes.
          if(NI->hasByValAttr()) 
            continue;
          Attributes Attrs = CallPAL.getParamAttributes(j);
          if (Attrs.hasAttributes()) {
            AttributesVec.push_back(AttributeWithIndex::get(j, Attrs));
          }
        }

        // Create the new attributes vec.
        if (FnAttrs.hasAttributes())
          AttributesVec.push_back(AttributeWithIndex::get(~0, FnAttrs));

        AttrListPtr NewCallPAL = AttrListPtr::get(F.getContext(),
                                                  AttributesVec);


        // Create the substitute call
        InvokeInst *CallI = InvokeInst::Create(&F,
                                               II->getNormalDest(),
                                               II->getUnwindDest(),
                                               Args,
                                               "", II);

        CallI->setCallingConv(II->getCallingConv());
        CallI->setAttributes(NewCallPAL);
        II->replaceAllUsesWith(CallI);
        toDelete.push_back(II);

      }
    } else if(CallInst *CI = dyn_cast<CallInst>(*ui)) {
      if(CI->getCalledFunction() == &F) {
        SmallVector<Value*, 8> Args;
        SmallVector<AttributeWithIndex, 8> AttributesVec;

        // Get the initial attributes of the call
        AttrListPtr CallPAL = CI->getAttributes();
        Attributes RAttrs = CallPAL.getRetAttributes();
        Attributes FnAttrs = CallPAL.getFnAttributes();

        if (RAttrs.hasAttributes())
          AttributesVec.push_back(AttributeWithIndex::get(0, RAttrs));

        Function::arg_iterator II = F.arg_begin();
        for(unsigned j =1;j<CI->getNumOperands();j++, II++) {
          // Add the original argument
          Args.push_back(CI->getOperand(j));
          // If there are attributes on this argument, copy them to the correct 
          // position in the AttributesVec
          //FIXME: copy the rest of the attributes.
          if(II->hasByValAttr()) 
            continue;
          Attributes Attrs = CallPAL.getParamAttributes(j);
          if (Attrs.hasAttributes()) {
            AttributesVec.push_back(AttributeWithIndex::get(j, Attrs));
          }
        }

        // Create the new attributes vec.
        if (FnAttrs.hasAttributes())
          AttributesVec.push_back(AttributeWithIndex::get(~0, FnAttrs));

        AttrListPtr NewCallPAL = AttrListPtr::get(F.getContext(),
                                                  AttributesVec);

        // Create the substitute call
        CallInst *CallI = CallInst::Create(&F,
                                           Args,
                                           "", CI);

        CallI->setCallingConv(CI->getCallingConv());
        CallI->setAttributes(NewCallPAL);
        CI->replaceAllUsesWith(CallI);
        toDelete.push_back(CI);
      }
    }
  }
  while(!toDelete.empty()) {
    Instruction *I = toDelete.back();
    toDelete.pop_back();
    I->eraseFromParent();
  }

  // remove the byval attribute from the function
  AttrBuilder B;
  B.addAttribute(Attributes::ByVal);
  for (Function::arg_iterator I = F.arg_begin(); I != F.arg_end(); ++I) {
    if (!I->hasByValAttr())
      continue;
    I->removeAttr(Attributes::get(M.getContext(), B));
  }
  return true;
}

bool TypeChecks::visitExternalByValFunction(Module &M, Function &F) {
  // A list of the byval arguments that we are setting metadata for
  typedef SmallVector<Value *, 4> RegisteredArgTy;
  RegisteredArgTy registeredArguments;
  for (Function::arg_iterator I = F.arg_begin(); I != F.arg_end(); ++I) {
    if (I->hasByValAttr()) {
      assert (isa<PointerType>(I->getType()));
      PointerType * PT = cast<PointerType>(I->getType());
      Type * ET = PT->getElementType();
      Value * AllocSize = ConstantInt::get(Int64Ty, TD->getTypeAllocSize(ET));
      Instruction * InsertPt = &(F.getEntryBlock().front());
      Value *BCI = castTo(I, VoidPtrTy, "", InsertPt);
      std::vector<Value *> Args;
      Args.push_back(BCI);
      Args.push_back(AllocSize);
      Args.push_back(getTagCounter());
      // Set the metadata for the byval argument to TOP/Initialized
      CallInst::Create(trackInitInst, Args, "", InsertPt);
      registeredArguments.push_back(&*I);
    }
  }

  // Find all basic blocks which terminate the function.
  std::set<BasicBlock *> exitBlocks;
  for (inst_iterator I = inst_begin(&F), E = inst_end(&F); I != E; ++I) {
    if (isa<ReturnInst>(*I) || isa<ResumeInst>(*I)) {
      exitBlocks.insert(I->getParent());
    }
  }

  // At each function exit, insert code to set the metadata as uninitialized.
  for (std::set<BasicBlock*>::const_iterator BI = exitBlocks.begin(),
       BE = exitBlocks.end();
       BI != BE; ++BI) {
    for (RegisteredArgTy::const_iterator I = registeredArguments.begin(),
         E = registeredArguments.end();
         I != E; ++I) {
      SmallVector<Value *, 2> args;
      Instruction * Pt = &((*BI)->back());
      PointerType * PT = cast<PointerType>((*I)->getType());
      Type * ET = PT->getElementType();
      Value * AllocSize = ConstantInt::get(Int64Ty, TD->getTypeAllocSize(ET));
      Value *BCI = castTo(*I, VoidPtrTy, "", Pt);
      std::vector<Value *> Args;
      Args.push_back(BCI);
      Args.push_back(AllocSize);
      Args.push_back(getTagCounter());
      CallInst::Create(trackUnInitInst, Args, "", Pt);
    }
  }
  return true;
}

// Print the types found in the module. If the optional Module parameter is
// passed in, then the types are printed symbolically if possible, using the
// symbol table from the module.
void TypeChecks::print(raw_ostream &OS, const Module *M) const {
  OS << "Types in use by this module:\n";
  std::map<Type *,unsigned int>::const_iterator I = UsedTypes.begin(), 
    E = UsedTypes.end();
  for (; I != E; ++I) {
    OS << "  ";
    OS << I->first;
    // WriteTypeSymbolic(OS, I->first, M);
    OS << " : " << I->second;
    OS << '\n';
  }

  OS << "\nNumber of types: " << UsedTypes.size() << '\n';
}

// Initialize the shadow memory which contains the 1:1 mapping.
bool TypeChecks::initShadow(Module &M) {
  // Create the call to the runtime initialization function and place it before the store instruction.

  Constant * RuntimeCtor = M.getOrInsertFunction("tc.init", VoidTy, NULL);
  Constant * InitFn = M.getOrInsertFunction("shadowInit", VoidTy, NULL);

  //RuntimeCtor->setDoesNotThrow();
  //RuntimeCtor->setLinkage(GlobalValue::InternalLinkage);

  BasicBlock *BB = BasicBlock::Create(M.getContext(), "entry", cast<Function>(RuntimeCtor));
  CallInst::Create(InitFn, "", BB);

  Instruction *InsertPt = ReturnInst::Create(M.getContext(), BB); 

  // record all globals
  for (Module::global_iterator I = M.global_begin(), E = M.global_end();
       I != E; ++I) {
    if(I->use_empty())
      continue;
    if(I->getName().str() == "stderr" ||
       I->getName().str() == "stdout" ||
       I->getName().str() == "stdin" ||
       I->getName().str() == "optind" ||
       I->getName().str() == "optarg") {
      // assume initialized
      Value *BCI = castTo(I, VoidPtrTy, "", InsertPt);
      std::vector<Value *> Args;
      Args.push_back(BCI);
      Args.push_back(getSizeConstant(I->getType()->getElementType()));
      Args.push_back(getTagCounter());
      CallInst::Create(trackInitInst, Args, "", InsertPt);
      continue;
    } 
    if(!I->hasInitializer())
      continue;
    SmallVector<Value*,8>index;
    index.push_back(Zero);
    visitGlobal(M, *I, I->getInitializer(), *InsertPt, index);
  }
  //
  // Insert the run-time ctor into the ctor list.
  //
  std::vector<Constant *> CtorInits;
  CtorInits.push_back (ConstantInt::get (Int32Ty, 65535));
  CtorInits.push_back (RuntimeCtor);
  Constant * RuntimeCtorInit=ConstantStruct::getAnon(M.getContext(),CtorInits, false);

  //
  // Get the current set of static global constructors and add the new ctor
  // to the list.
  //
  std::vector<Constant *> CurrentCtors;
  GlobalVariable * GVCtor = M.getNamedGlobal ("llvm.global_ctors");
  if (GVCtor) {
    if (Constant * C = GVCtor->getInitializer()) {
      for (unsigned index = 0; index < C->getNumOperands(); ++index) {
        CurrentCtors.push_back (cast<Constant>(C->getOperand (index)));
      }
    }

    //
    // Rename the global variable so that we can name our global
    // llvm.global_ctors.
    //
    GVCtor->setName ("removed");
  }

  //
  // The ctor list seems to be initialized in different orders on different
  // platforms, and the priority settings don't seem to work.  Examine the
  // module's platform string and take a best guess to the order.
  //
  if (M.getTargetTriple().find ("linux") == std::string::npos)
    CurrentCtors.insert (CurrentCtors.begin(), RuntimeCtorInit);
  else
    CurrentCtors.push_back (RuntimeCtorInit);

  //
  // Create a new initializer.
  //
  ArrayType * AT = ArrayType::get (RuntimeCtorInit-> getType(),
                                   CurrentCtors.size());
  Constant * NewInit=ConstantArray::get (AT, CurrentCtors);

  //
  // Create the new llvm.global_ctors global variable and replace all uses of
  // the old global variable with the new one.
  //
  new GlobalVariable (M,
                      NewInit->getType(),
                      false,
                      GlobalValue::AppendingLinkage,
                      NewInit,
                      "llvm.global_ctors");


  return true;
}

  bool TypeChecks::visitMain(Module &M, Function &MainFunc) {
    if(MainFunc.arg_size() < 2)
      // No need to register
      return false;

    Function::arg_iterator AI = MainFunc.arg_begin();
    Value *Argc = AI;
    Value *Argv = ++AI;

    Instruction *InsertPt = MainFunc.front().begin();
    std::vector<Value *> fargs;
    fargs.push_back (Argc);
    fargs.push_back (Argv);
    CallInst::Create (RegisterArgv, fargs, "", InsertPt);

    if(MainFunc.arg_size() < 3)
      return true;

    Value *Envp = ++AI;
    std::vector<Value*> Args;
    Args.push_back(Envp);
    CallInst::Create(RegisterEnvp, Args, "", InsertPt);
    return true;
  }

bool TypeChecks::visitGlobal(Module &M, GlobalVariable &GV, 
                             Constant *C, Instruction &I, SmallVector<Value *,8> Indices) {

  if(ConstantArray *CA = dyn_cast<ConstantArray>(C)) {
    Type * ElementType = CA->getType()->getElementType();
    // Create the type entry for the first element
    // using recursive creation till we get to the base types
    Indices.push_back(ConstantInt::get(Int64Ty,0));
    visitGlobal(M, GV, CA->getOperand(0), I, Indices);
    Indices.pop_back();
    GetElementPtrInst *GEP = GetElementPtrInst::CreateInBounds(&GV, Indices, "", &I);

    Value *BCI = castTo(GEP, VoidPtrTy, "", &I);

    // Copy the type metadata for the first element
    // over for the rest of the elements.
    std::vector<Value *> Args;
    Args.push_back(BCI);
    Args.push_back(getSizeConstant(ElementType));
    Args.push_back(ConstantInt::get(Int64Ty, CA->getNumOperands()));
    Args.push_back(getTagCounter());
    CallInst::Create(trackArray, Args, "", &I);
  }
  else if(ConstantStruct *CS = dyn_cast<ConstantStruct>(C)) {
    // Create metadata for each field of the struct
    // at the correct offset.
    const StructLayout *SL = TD->getStructLayout(cast<StructType>(CS->getType()));
    for (unsigned i = 0, e = CS->getNumOperands(); i != e; ++i) {
      if (SL->getElementOffset(i) < SL->getSizeInBytes()) {
        Constant * ConstElement = cast<Constant>(CS->getOperand(i));
        Indices.push_back(ConstantInt::get(Int32Ty, i));
        visitGlobal(M, GV, ConstElement, I, Indices);
        Indices.pop_back();
      }
    }
  } else if(ConstantAggregateZero *CAZ = dyn_cast<ConstantAggregateZero>(C)) {
    // Similiar to having an initializer with all values NULL
    // Must set metadata, similiar to the previous 2 cases.
    Type *Ty = CAZ->getType();
    if(ArrayType * ATy = dyn_cast<ArrayType>(Ty)) {
      Type * ElementType = ATy->getElementType();
      Indices.push_back(ConstantInt::get(Int64Ty,0));
      visitGlobal(M, GV, Constant::getNullValue(ElementType), I, Indices);
      Indices.pop_back();
      GetElementPtrInst *GEP = GetElementPtrInst::CreateInBounds(&GV, Indices, "", &I);

      Value *BCI = castTo(GEP, VoidPtrTy, "", &I);
      std::vector<Value *> Args;
      Args.push_back(BCI);
      Args.push_back(getSizeConstant(ElementType));
      Args.push_back(ConstantInt::get(Int64Ty, ATy->getNumElements()));
      Args.push_back(getTagCounter());
      CallInst::Create(trackArray, Args, "", &I);
    } else if(StructType *STy = dyn_cast<StructType>(Ty)) {
      const StructLayout *SL = TD->getStructLayout(STy);
      for (unsigned i = 0, e = STy->getNumElements(); i != e; ++i) {
        if (SL->getElementOffset(i) < SL->getSizeInBytes()) {
          Indices.push_back(ConstantInt::get(Int32Ty, i));
          visitGlobal(M, GV, Constant::getNullValue(STy->getElementType(i)), I, Indices);
          Indices.pop_back();
        }
      }
    } else {
      // Zeroinitializer of a primitive type
      GetElementPtrInst *GEP = GetElementPtrInst::CreateInBounds(&GV, Indices, "", &I);

      Value *BCI = castTo(GEP, VoidPtrTy, "", &I);
      std::vector<Value *> Args;
      Args.push_back(BCI);
      Args.push_back(getTypeMarkerConstant(CAZ));
      Args.push_back(getSizeConstant(CAZ->getType()));
      Args.push_back(getTagCounter());
      CallInst::Create(trackGlobal, Args, "", &I);
    }
  }
  else {
    // Primitive type value
    GetElementPtrInst *GEP = GetElementPtrInst::CreateInBounds(&GV, Indices, "", &I);

    Value *BCI = castTo(GEP, VoidPtrTy, "", &I);
    std::vector<Value *> Args;
    Args.push_back(BCI);
    Args.push_back(getTypeMarkerConstant(C));
    Args.push_back(getSizeConstant(C->getType()));
    Args.push_back(getTagCounter());
    CallInst::Create(trackGlobal, Args, "", &I);
  }
  return true;
}
  bool TypeChecks::visitVAArgInst(Module &M, VAArgInst &VI) {
    if(!VI.getParent()->getParent()->hasInternalLinkage())
      return false;
    Value *BCI = castTo(VI.getOperand(0), VoidPtrTy, "", &VI);
    std::vector<Value *>Args;
    Args.push_back(BCI);
    Args.push_back(getTypeMarkerConstant(&VI));
    Args.push_back(getTagCounter());
    CallInst::Create(checkVAArg, Args, "", &VI);
    return false;
  }

// Insert code to initialize meta data to bottom
// Insert code to set objects to 0
bool TypeChecks::visitAllocaInst(Module &M, AllocaInst &AI) {

  PointerType * PT = AI.getType();
  Type * ET = PT->getElementType();
  Value * AllocSize = ConstantInt::get(Int64Ty, TD->getTypeAllocSize(ET));
  CastInst *BCI = BitCastInst::CreatePointerCast(&AI, VoidPtrTy);
  BCI->insertAfter(&AI);

  Value *TotalSize;
  if(!AI.isArrayAllocation()) {
    TotalSize = AllocSize;
  } else {
    CastInst *ArraySize = CastInst::CreateSExtOrBitCast(AI.getArraySize(), Int64Ty, "", &AI);
    BinaryOperator *Size = BinaryOperator::Create(Instruction::Mul, AllocSize, ArraySize, "", &AI);
    TotalSize = Size;
  }

  // Setting metadata to be 0(BOTTOM/Uninitialized)

  std::vector<Value *> Args;
  Args.push_back(BCI);
  Args.push_back(TotalSize);
  Args.push_back(getTagCounter());
  CallInst *CI = CallInst::Create(trackUnInitInst, Args);
  CI->insertAfter(BCI);
  return true;
}

// Insert runtime checks for certain call instructions
bool TypeChecks::visitCallInst(Module &M, CallInst &CI) {
  return visitCallSite(M, &CI);
}

// Insert runtime checks for certain call instructions
bool TypeChecks::visitInvokeInst(Module &M, InvokeInst &II) {
  return visitCallSite(M, &II);
}

bool TypeChecks::visitCallSite(Module &M, CallSite CS) {
  //
  // Get the called value.  Strip off any casts which are lossless.
  //
  Value *Callee = CS.getCalledValue()->stripPointerCasts();
  Instruction *I = CS.getInstruction();

  // Special case handling of certain libc allocation functions here.
  if (Function *F = dyn_cast<Function>(Callee)) {
    if (F->isIntrinsic()) {
      switch(F->getIntrinsicID()) {
      case Intrinsic::memcpy: 
      case Intrinsic::memmove: 
        {
          Value *BCI_Src = castTo(CS.getArgument(1), VoidPtrTy, "", I);
          Value *BCI_Dest = castTo(CS.getArgument(0), VoidPtrTy, "", I);
          std::vector<Value *> Args;
          Args.push_back(BCI_Dest);
          Args.push_back(BCI_Src);
          CastInst *Size = CastInst::CreateIntegerCast(CS.getArgument(2), Int64Ty, false, "", I);
          Args.push_back(Size);
          Args.push_back(getTagCounter());
          CallInst::Create(copyTypeInfo, Args, "", I);
          return true;
        }

      case Intrinsic::memset:
        Value *BCI = castTo(CS.getArgument(0), VoidPtrTy, "", I);
        std::vector<Value *> Args;
        Args.push_back(BCI);
        CastInst *Size = CastInst::CreateIntegerCast(CS.getArgument(2), Int64Ty, false, "", I);
        Args.push_back(Size);
        Args.push_back(getTagCounter());
        CallInst::Create(trackInitInst, Args, "", I);
        return true;
      }
    } else if (F->getName().str() == std::string("_ZNKSs5c_strEv")) { //c_str
      std::vector<Value *>Args;
      Args.push_back(I);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgetcwd", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      Instruction *InsertPt = I;  
      if (InvokeInst *II = dyn_cast<InvokeInst>(InsertPt)) {
        InsertPt = II->getNormalDest()->begin();
        while (isa<PHINode>(InsertPt))
          ++InsertPt;
      } else
        ++InsertPt;
      CI->insertBefore(InsertPt);
    } else if (F->getName().str() == std::string("_ZNSsC1EPKcRKSaIcE")) { //c_str()
      Value *BCI = castTo(CS.getArgument(0), VoidPtrTy, "", I);
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgetcwd", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      Instruction *InsertPt = I;  
      if (InvokeInst *II = dyn_cast<InvokeInst>(InsertPt)) {
        InsertPt = II->getNormalDest()->begin();
        while (isa<PHINode>(InsertPt))
          ++InsertPt;
      } else
        ++InsertPt;
      CI->insertBefore(InsertPt);
    } else if (F->getName().str() == std::string("accept")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(CS.getArgument(1), VoidPtrTy);
      BCI->insertAfter(I);
      CastInst *BCI_Size = BitCastInst::CreatePointerCast(CS.getArgument(2), VoidPtrTy);
      BCI_Size->insertAfter(I);
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(BCI_Size);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackaccept", VoidTy, VoidPtrTy,VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("poll")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(CS.getArgument(0), VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value*>Args;
      Args.push_back(BCI);
      Args.push_back(CS.getArgument(1));
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackpoll", VoidTy, VoidPtrTy, Int64Ty, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("getaddrinfo")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(CS.getArgument(3), VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgetaddrinfo", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("mmap")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *> Args;
      Args.push_back(BCI);
      Args.push_back(CS.getArgument(1));
      Args.push_back(getTagCounter());
      CallInst *CI = CallInst::Create(trackInitInst, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("__strdup")) {
      CastInst *BCI_Dest = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI_Dest->insertAfter(I);
      CastInst *BCI_Src = BitCastInst::CreatePointerCast(CS.getArgument(0), VoidPtrTy);
      BCI_Src->insertAfter(BCI_Dest);
      std::vector<Value *> Args;
      Args.push_back(BCI_Dest);
      Args.push_back(BCI_Src);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackStrcpyInst", VoidTy, VoidPtrTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI_Src);
    } else if (F->getName().str() == std::string("gettimeofday") || 
               F->getName().str() == std::string("time") ||
               F->getName().str() == std::string("times")) {
      Value *BCI = castTo(CS.getArgument(0), VoidPtrTy, "", I);
      assert (isa<PointerType>(CS.getArgument(0)->getType()));
      PointerType * PT = cast<PointerType>(CS.getArgument(0)->getType());
      Type * ET = PT->getElementType();
      Value * AllocSize = ConstantInt::get(Int64Ty, TD->getTypeAllocSize(ET));
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(AllocSize);
      Args.push_back(getTagCounter());
      CallInst::Create(trackInitInst, Args, "", I);
    } else if (F->getName().str() == std::string("getpwuid")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgetpwuid", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("getpwnam")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgetpwuid", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if(F->getName().str() == std::string("getopt_long")) {
      Value *OptArg = M.getNamedGlobal("optarg");
      LoadInst *LI = new LoadInst(OptArg);
      LI->insertAfter(I);
      std::vector<Value *>Args;
      Args.push_back(LI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgetcwd", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(LI);
    } else if (F->getName().str() == std::string("getgruid") ||
               F->getName().str() == std::string("getgrnam") ||
               F->getName().str() == std::string("getpwnam") ||
               F->getName().str() == std::string("__errno_location")) {
      CastInst *BCI  = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      assert (isa<PointerType>(I->getType()));
      PointerType * PT = cast<PointerType>(I->getType());
      Type * ET = PT->getElementType();
      Value * AllocSize = ConstantInt::get(Int64Ty, TD->getTypeAllocSize(ET));
      BCI->insertAfter(I);
      std::vector<Value*>Args;
      Args.push_back(BCI);
      Args.push_back(AllocSize);
      Args.push_back(getTagCounter());
      CallInst *CI = CallInst::Create(trackInitInst, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("getservbyname")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value*>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgetservbyname", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("gethostbyname") ||
               F->getName().str() == std::string("gethostbyaddr")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value*>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgethostbyname", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("gethostname")) {
      CastInst *BCI  = BitCastInst::CreatePointerCast(CS.getArgument(0), VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value*>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgethostname", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("getenv") ||
               F->getName().str() == std::string("strerror") ||
               F->getName().str() == std::string("inet_ntoa")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgetcwd", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("getcwd")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgetcwd", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if(F->getName().str() == std::string("crypt")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgetcwd", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("getrusage") || 
               F->getName().str() == std::string("getrlimit") ||
               F->getName().str() == std::string("stat") ||
               F->getName().str() == std::string("vfsstat") ||
               F->getName().str() ==  std::string("fstat") ||
               F->getName().str() == std::string("lstat")) {
      Value *BCI = castTo(CS.getArgument(1), VoidPtrTy, "", I);
      assert (isa<PointerType>(CS.getArgument(1)->getType()));
      PointerType * PT = cast<PointerType>(CS.getArgument(1)->getType());
      Type * ET = PT->getElementType();
      Value * AllocSize = ConstantInt::get(Int64Ty, TD->getTypeAllocSize(ET));
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(AllocSize);
      Args.push_back(getTagCounter());
      CallInst::Create(trackInitInst, Args, "", I);
    } else if (F->getName().str() == std::string("sigaction")) {
      Value *BCI = castTo(CS.getArgument(2), VoidPtrTy, "", I);
      assert (isa<PointerType>(CS.getArgument(2)->getType()));
      PointerType * PT = cast<PointerType>(CS.getArgument(2)->getType());
      Type * ET = PT->getElementType();
      Value * AllocSize = ConstantInt::get(Int64Ty, TD->getTypeAllocSize(ET));
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(AllocSize);
      Args.push_back(getTagCounter());
      CallInst::Create(trackInitInst, Args, "", I);
    } else if (F->getName().str() == std::string("__ctype_b_loc")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackctype", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("__ctype_toupper_loc")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackctype_32", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("__ctype_tolower_loc")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackctype_32", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("strtol") ||
               F->getName().str() == std::string("strtod")) {
      Value *BCI = castTo(CS.getArgument(1), VoidPtrTy, "", I);
      PointerType *PTy = cast<PointerType>(CS.getArgument(1)->getType());
      Type * ElementType = PTy->getElementType();
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getSizeConstant(ElementType));
      Args.push_back(getTagCounter());
      CallInst::Create(trackInitInst, Args, "", I);
      return true;
    } else if (F->getName().str() == std::string("strcat") ||
               F->getName().str() == std::string("_ZNSspLEPKc")) {
      Value *BCI_Src = castTo(CS.getArgument(1), VoidPtrTy, "", I);
      Value *BCI_Dest = castTo(CS.getArgument(0), VoidPtrTy, "", I);
      std::vector<Value *> Args;
      Args.push_back(BCI_Dest);
      Args.push_back(BCI_Src);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackStrcatInst", VoidTy, VoidPtrTy, VoidPtrTy, Int32Ty, NULL);
      CallInst::Create(F, Args, "", I);
    } else if (F->getName().str() == std::string("strcpy")) {
      std::vector<Value *> Args;
      Args.push_back(CS.getArgument(0));
      Args.push_back(CS.getArgument(1));
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackStrcpyInst", VoidTy, VoidPtrTy, VoidPtrTy, Int32Ty, NULL);
      CallInst::Create(F, Args, "", I);
    } else if (F->getName().str() == std::string("strncpy")) {
      std::vector<Value *>Args;
      Args.push_back(CS.getArgument(0));
      Args.push_back(CS.getArgument(1));
      Args.push_back(CS.getArgument(2));
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackStrncpyInst", VoidTy, VoidPtrTy, VoidPtrTy, I->getOperand(3)->getType(), Int32Ty, NULL);
      CallInst::Create(F, Args, "", I);
    } else if (F->getName().str() == std::string("readlink")) {
      std::vector<Value *>Args;
      Args.push_back(CS.getArgument(1));
      Args.push_back(I);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackReadLink", VoidTy, VoidPtrTy, I->getType(), Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(I);
    } else if (F->getName().str() == std::string("pipe")) {
      Value *BCI = castTo(CS.getArgument(0), VoidPtrTy, "", I);
      std::vector<Value*> Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackpipe", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst::Create(F, Args, "", I);
      return true;
    } else if (F->getName().str() == std::string("getsockname")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(CS.getArgument(1), VoidPtrTy);
      BCI->insertAfter(I);
      CastInst *BCI_Size = BitCastInst::CreatePointerCast(CS.getArgument(2), VoidPtrTy);
      BCI_Size->insertAfter(I);
      std::vector<Value *> Args;
      Args.push_back(BCI);
      Args.push_back(BCI_Size);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgetsockname", VoidTy, VoidPtrTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CI = CallInst::Create(F, Args);
      CI->insertAfter(BCI);
      return true;
    } else if (F->getName().str() == std::string("readdir")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      PointerType *PTy = cast<PointerType>(I->getType());
      Type * ElementType = PTy->getElementType();
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getSizeConstant(ElementType));
      Args.push_back(getTagCounter());
      CallInst *CI = CallInst::Create(trackInitInst, Args);
      CI->insertAfter(BCI);
      return true;
    } else if (F->getName().str() == std::string("localtime") ||
               F->getName().str() == std::string("gmtime")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      PointerType *PTy = cast<PointerType>(I->getType());
      Type * ElementType = PTy->getElementType();
      std::vector<Value *>Args;
      Args.push_back(BCI);
      Args.push_back(getSizeConstant(ElementType));
      Args.push_back(getTagCounter());
      CallInst *CI = CallInst::Create(trackInitInst, Args);
      CI->insertAfter(BCI);
    } else if (F->getName().str() == std::string("ftime") ||
               F->getName().str() == std::string("gettimeofday")) {
      Value *BCI = castTo(CS.getArgument(0), VoidPtrTy, "", I);
      PointerType *PTy = cast<PointerType>(CS.getArgument(0)->getType());
      Type * ElementType = PTy->getElementType();
      std::vector<Value *> Args;
      Args.push_back(BCI);
      Args.push_back(getSizeConstant(ElementType));
      Args.push_back(getTagCounter());
      CallInst::Create(trackInitInst, Args, "", I);
      return true;
    } else if(F->getName().str() == std::string("read")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(CS.getArgument(1), VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *> Args;
      Args.push_back(BCI);
      CastInst *Size = CastInst::CreateIntegerCast(I, Int64Ty, false);
      Size->insertAfter(I);
      Args.push_back(Size);
      Args.push_back(getTagCounter());
      CallInst *CI = CallInst::Create(trackInitInst, Args);
      CI->insertAfter(BCI);
      return true;
    } else if(F->getName().str() == std::string("fread")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(CS.getArgument(0), VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *> Args;
      Args.push_back(BCI);
      CastInst *Elem = CastInst::CreateIntegerCast(I, Int64Ty, false);
      BinaryOperator *Size = BinaryOperator::Create(Instruction::Mul, Elem, CS.getArgument(1));
      Elem->insertAfter(I);
      Size->insertAfter(Elem);
      Args.push_back(Size);
      Args.push_back(getTagCounter());
      CallInst *CI = CallInst::Create(trackInitInst, Args);
      CI->insertAfter(BCI);
      return true;
    } else if(F->getName().str() == std::string("calloc")) {
      CastInst *BCI = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI->insertAfter(I);
      std::vector<Value *> Args;
      Args.push_back(BCI);
      CastInst *Size = CastInst::CreateIntegerCast(CS.getArgument(1), Int64Ty, false, "", I);
      Args.push_back(Size);
      Args.push_back(getTagCounter());
      CallInst *CI = CallInst::Create(trackInitInst, Args);
      CI->insertAfter(BCI);
      std::vector<Value *> Args1;
      Args1.push_back(BCI);
      Args1.push_back(Size);
      CastInst *Num = CastInst::CreateIntegerCast(CS.getArgument(0), Int64Ty, false, "", I);
      Args1.push_back(Num);
      Args1.push_back(getTagCounter());
      CallInst *CI_Arr = CallInst::Create(trackArray, Args1);
      CI_Arr->insertAfter(CI);
      return true;
    } else if(F->getName().str() ==  std::string("realloc")) {
      CastInst *BCI_Src = BitCastInst::CreatePointerCast(CS.getArgument(0), VoidPtrTy);
      CastInst *BCI_Dest = BitCastInst::CreatePointerCast(I, VoidPtrTy);
      BCI_Src->insertAfter(I);
      BCI_Dest->insertAfter(BCI_Src);
      std::vector<Value *> Args;
      Args.push_back(BCI_Dest);
      Args.push_back(BCI_Src);
      CastInst *Size = CastInst::CreateIntegerCast(CS.getArgument(1), Int64Ty, false, "", I);
      Args.push_back(Size);
      Args.push_back(getTagCounter());
      CallInst *CI = CallInst::Create(copyTypeInfo, Args);
      CI->insertAfter(BCI_Dest);
      return true;
    } else if(F->getName().str() == std::string("fgets")) {
      Value *BCI = castTo(CS.getArgument(0), VoidPtrTy, "", I);
      std::vector<Value *> Args;
      Args.push_back(BCI);
      CastInst *Size = CastInst::CreateIntegerCast(CS.getArgument(1), Int64Ty, false, "", I);
      Args.push_back(Size);
      Args.push_back(getTagCounter());
      CallInst::Create(trackInitInst, Args, "", I);
      return true;
    } else if(F->getName().str() == std::string("snprintf") ||
              F->getName().str() == std::string("vsnprintf")) {
      Value *BCI = castTo(CS.getArgument(0), VoidPtrTy, "", I);
      std::vector<Value*>Args;
      Args.push_back(BCI);
      Args.push_back(getTagCounter());
      Constant *F = M.getOrInsertFunction("trackgetcwd", VoidTy, VoidPtrTy, Int32Ty, NULL);
      CallInst *CINew = CallInst::Create(F, Args);
      CINew->insertAfter(I);
    } else if(F->getName().str() == std::string("sprintf")) {
      Value *BCI = castTo(CS.getArgument(0), VoidPtrTy, "", I);
      std::vector<Value*>Args;
      Args.push_back(BCI);
      CastInst *Size = CastInst::CreateIntegerCast(I, Int64Ty, false);
      Size->insertAfter(I);
      Instruction *NewValue = BinaryOperator::Create(BinaryOperator::Add,
                                                     Size,
                                                     One);
      NewValue->insertAfter(Size);
      Args.push_back(NewValue);
      Args.push_back(getTagCounter());
      CallInst *CINew = CallInst::Create(trackInitInst, Args);
      CINew->insertAfter(NewValue);
    } else if(F->getName().str() == std::string("scanf")) {
      unsigned i = 1;
      while(i < CS.arg_size()) {
        visitInputFunctionValue(M, CS.getArgument(i), I);
        i++;
      }
    } else if(F->getName().str() == std::string("sscanf")) {
      // FIXME: Need to look at the format string and check
      unsigned i = 2;
      while(i < CS.arg_size()) {
        visitInputFunctionValue(M, CS.getArgument(i), I);
        i++;
      }
    } else if(F->getName().str() == std::string("fscanf")) {
      unsigned i = 2;
      while(i < CS.arg_size()) {
        visitInputFunctionValue(M, CS.getArgument(i), I);
        i++;
      }
    }
  } else {
    // indirect call site
    IndCalls.insert(CS.getInstruction());
    return false;
  }
  return false;
}

// Add extra arguments to each indirect call site
bool TypeChecks::visitIndirectCallSite(Module &M, Instruction *I) {
  // add the number of arguments as the first argument
  Type* OrigType = I->getOperand(0)->getType();
  assert(OrigType->isPointerTy());
  FunctionType *FOldType = cast<FunctionType>((cast<PointerType>(OrigType))->getElementType());
  std::vector<Type*>TP;
  TP.push_back(Int64Ty);
  TP.push_back(TypeTagPtrTy);

  for(llvm::FunctionType::param_iterator ArgI = FOldType->param_begin(); ArgI != FOldType->param_end(); ++ArgI)
    TP.push_back(*ArgI);

  FunctionType *FTy = FunctionType::get(FOldType->getReturnType(), TP, FOldType->isVarArg());
  Value *Func = castTo(I->getOperand(0), FTy->getPointerTo(), "", I);

  inst_iterator InsPt = inst_begin(I->getParent()->getParent());
  CallSite CS = CallSite(I);
  unsigned int NumArgs = CS.arg_size();
  Value *NumArgsVal = ConstantInt::get(Int32Ty, NumArgs);
  AllocaInst *AI = new AllocaInst(TypeTagTy, NumArgsVal, "", &*InsPt);
  for(unsigned int i = 0; i < CS.arg_size(); i++) {
    Value *Idx[1];
    Idx[0] = ConstantInt::get(Int32Ty, i-1);
    GetElementPtrInst *GEP = GetElementPtrInst::CreateInBounds(AI, Idx, "", I);
    Constant *C = getTypeMarkerConstant(CS.getArgument(i));
    new StoreInst(C, GEP, I);
  }
  std::vector<Value *> Args;
  Args.push_back(ConstantInt::get(Int64Ty, NumArgs));
  Args.push_back(AI);
  for(unsigned int i = 0; i < CS.arg_size(); i++)
    Args.push_back(CS.getArgument(i));
  if(CallInst *CI = dyn_cast<CallInst>(I)) {
    CallInst *CI_New = CallInst::Create(Func, Args, "", CI);
    CI->replaceAllUsesWith(CI_New);
    CI->eraseFromParent();
  } else if(InvokeInst *II = dyn_cast<InvokeInst>(I)) {
    InvokeInst *INew = InvokeInst::Create(Func,
                                          II->getNormalDest(),
                                          II->getUnwindDest(),
                                          Args,
                                          "", I);
    II->replaceAllUsesWith(INew);
    II->eraseFromParent();
  }
  return true;
}

bool TypeChecks::visitInputFunctionValue(Module &M, Value *V, Instruction *CI) {
  // Cast the pointer operand to i8* for the runtime function.
  Value *BCI = castTo(V, VoidPtrTy, "", CI);
  PointerType *PTy = dyn_cast<PointerType>(V->getType());
  if(!PTy)
    return false;

  std::vector<Value *> Args;
  Args.push_back(BCI);
  Args.push_back(getTypeMarkerConstant(PTy->getElementType()));
  Args.push_back(getSizeConstant(PTy->getElementType()));
  Args.push_back(getTagCounter());

  // Create the call to the runtime check and place it before the store instruction.
  CallInst::Create(trackStoreInst, Args, "", CI);

  if(PTy == VoidPtrTy) {
    // TODO: This is currently a heuristic for strings. If we see a i8* in a call to 
    // input functions, treat as string, and get length using strlen.
    std::vector<Value*> Args;
    Args.push_back(BCI);
    Args.push_back(getTagCounter());
    CallInst *CINew = CallInst::Create(trackStringInput, Args);
    CINew->insertAfter(CI);
  }

  return true;
}

// Insert runtime checks before all load instructions.
bool TypeChecks::visitLoadInst(Module &M, LoadInst &LI) {
  inst_iterator InsPt = inst_begin(LI.getParent()->getParent());
  // Cast the pointer operand to i8* for the runtime function.
  Value *BCI = castTo(LI.getPointerOperand(), VoidPtrTy, "", &LI);

  Value *Size = ConstantInt::get(Int32Ty, getSize(LI.getType()));
  AllocaInst *AI = new AllocaInst(TypeTagTy, Size, "", &*InsPt);

  std::vector<Value *>Args1;
  Args1.push_back(BCI);
  Args1.push_back(getSizeConstant(LI.getType()));
  Args1.push_back(AI);
  Args1.push_back(getTagCounter());
  CallInst *getTypeCall = CallInst::Create(getTypeTag, Args1, "", &LI);
  if(TrackAllLoads) {
    std::vector<Value *> Args;
    Args.push_back(getTypeMarkerConstant(&LI));
    Args.push_back(getSizeConstant(LI.getType()));
    Args.push_back(AI);
    Args.push_back(BCI);
    Args.push_back(getTagCounter());
    CallInst::Create(checkTypeInst, Args, "", &LI);
  }
  visitUses(&LI, AI, BCI);

  if(AI->hasOneUse()) {
    // No uses needed checks
    getTypeCall->eraseFromParent();
  }

  // Create the call to the runtime check and place it before the load instruction.
  numLoadChecks++;
  return true;
}

// AI - metadata
// BCI - ptr
// I - instruction whose uses to instrument
bool TypeChecks::visitUses(Instruction *I, Instruction *AI, Value *BCI) {
  for(Value::use_iterator II = I->use_begin(); II != I->use_end(); ++II) {
    if(DisablePtrCmpChecks) {
      if(isa<CmpInst>(*II)) {
        if(I->getType()->isPointerTy())
          continue;
      }
    }
    std::vector<Value *> Args;
    Args.push_back(getTypeMarkerConstant(I));
    Args.push_back(getSizeConstant(I->getType()));
    Args.push_back(AI);
    Args.push_back(BCI);
    Args.push_back(getTagCounter());
    if(StoreInst *SI = dyn_cast<StoreInst>(*II)) {
      if(SI->getOperand(0) == I) {
        // Cast the pointer operand to i8* for the runtime function.
        Value *BCI_Dest = castTo(SI->getPointerOperand(), VoidPtrTy, "", SI);

        std::vector<Value *> Args;
        Args.push_back(BCI_Dest);
        Args.push_back(AI);
        Args.push_back(getSizeConstant(SI->getOperand(0)->getType()));
        Args.push_back(getTypeMarkerConstant(SI->getOperand(0)->getType()));
        Args.push_back(BCI);
        Args.push_back(getTagCounter());
        // Create the call to the runtime check and place it before the copying store instruction.
        CallInst::Create(setTypeInfo, Args, "", SI);
      } else {
        CallInst::Create(checkTypeInst, Args, "", cast<Instruction>(II.getUse().getUser()));
      }
    } else if(SelectInst *SelI = dyn_cast<SelectInst>(*II)) {
      if(SelI->getOperand(0) == I) {
        CallInst::Create(checkTypeInst, Args, "", cast<Instruction>(II.getUse().getUser()));
        // if it is used as the condition, just insert a check
      } else {
        SelectInst *Prev = NULL;
        SelectInst *PrevBasePtr = NULL;
        if(SelectInst_MD_Map.find(SelI) != SelectInst_MD_Map.end()) {
          Prev = SelectInst_MD_Map[SelI];
          PrevBasePtr = SelectInst_BasePtr_Map[SelI];
        }
        SelectInst *AI_New;
        SelectInst *BCI_New;
        if(SelI->getTrueValue() == I) {
          if(!Prev) {
            AI_New = SelectInst::Create(SelI->getCondition(), AI, Constant::getNullValue(AI->getType()), "", SelI);
            BCI_New = SelectInst::Create(SelI->getCondition(), BCI, Constant::getNullValue(BCI->getType()), "", SelI);
          } else {
            AI_New = SelectInst::Create(SelI->getCondition(), AI, Prev->getFalseValue(), "", SelI);
            BCI_New = SelectInst::Create(SelI->getCondition(), BCI, Prev->getFalseValue(), "", SelI);
            Prev->replaceAllUsesWith(AI_New);
            PrevBasePtr->replaceAllUsesWith(BCI_New);
          }
        }
        else {
          if(!Prev) {
            AI_New = SelectInst::Create(SelI->getCondition(), Constant::getNullValue(AI->getType()), AI, "", SelI);
            BCI_New = SelectInst::Create(SelI->getCondition(), Constant::getNullValue(BCI->getType()), BCI, "", SelI);
          } else {
            AI_New = SelectInst::Create(SelI->getCondition(),  Prev->getTrueValue(), AI, "", SelI);
            BCI_New = SelectInst::Create(SelI->getCondition(),  Prev->getTrueValue(), BCI, "", SelI);
            Prev->replaceAllUsesWith(AI_New);
            PrevBasePtr->replaceAllUsesWith(BCI_New);
          }
        }
        SelectInst_MD_Map[SelI] = AI_New;
        SelectInst_BasePtr_Map[SelI] = BCI_New;
        if(!Prev)
          visitUses(SelI, AI_New, BCI_New);
      }
    } else if(PHINode *PH = dyn_cast<PHINode>(*II)) {
      PHINode *Prev = NULL;
      PHINode *PrevBasePtr = NULL;
      if(PHINode_MD_Map.find(PH) != PHINode_MD_Map.end()) {
        Prev = PHINode_MD_Map[PH];
        PrevBasePtr = PHINode_BasePtr_Map[PH];
      }
      if(InsertedPHINodes.find(PH) != InsertedPHINodes.end())
        continue;
      /*if(isa<PHINode>(I)) {
        std::string name = PH->getName();
        if (strncmp(name.c_str(), "baseptr.", 8) == 0) continue;
        }*/
      PHINode *AI_New;
      PHINode *BCI_New;
      if(!Prev) {
        AI_New = PHINode::Create(AI->getType(),
                                 PH->getNumIncomingValues(),
                                 PH->getName().str() + ".md",
                                 PH);
        BCI_New = PHINode::Create(BCI->getType(),
                                  PH->getNumIncomingValues(),
                                  PH->getName().str() + ".baseptr",
                                  PH);
        for(unsigned c = 0; c < PH->getNumIncomingValues(); c++) {
          if(PH->getIncomingValue(c) == I) {
            AI_New->addIncoming(AI, PH->getIncomingBlock(c));
            BCI_New->addIncoming(BCI, PH->getIncomingBlock(c));
          }
          else {
            AI_New->addIncoming(Constant::getNullValue(AI->getType()), PH->getIncomingBlock(c));
            BCI_New->addIncoming(Constant::getNullValue(BCI->getType()), PH->getIncomingBlock(c));
          }
        }
        PHINode_MD_Map[PH] = AI_New;
        PHINode_BasePtr_Map[PH] = BCI_New;
        InsertedPHINodes.insert(AI_New);
        InsertedPHINodes.insert(BCI_New);
        visitUses(PH, AI_New, BCI_New);
      }
      else {
        for(unsigned c = 0; c < PH->getNumIncomingValues(); c++) {
          if(PH->getIncomingValue(c) == I) {
            Prev->setIncomingValue(c, AI);
            PrevBasePtr->setIncomingValue(c, BCI);
          }
        }
      }
    } else if(BitCastInst *BI = dyn_cast<BitCastInst>(*II)) {
      BitCast_MD_Map[BI] = AI;
      visitUses(BI, AI, BCI);
      //CallInst::Create(checkTypeInst, Args.begin(), Args.end(), "", cast<Instruction>(II.getUse().getUser()));
      /*} else if(PtrToIntInst *P2I = dyn_cast<PtrToIntInst>(II)) {
        visitUses(P2I, AI, BCI);
        } else if(IntToPtrInst *I2P = dyn_cast<IntToPtrInst>(II)) {
        visitUses(I2P, AI, BCI);*/
  }else {
    CallInst::Create(checkTypeInst, Args, "", cast<Instruction>(II.getUse().getUser()));
  }
  }
  return true;
}

// Insert runtime checks before all store instructions.
bool TypeChecks::visitStoreInst(Module &M, StoreInst &SI) {
  if(isa<LoadInst>(SI.getOperand(0)->stripPointerCasts())) {
    return false;
  }
  if(PHINode *PH = dyn_cast<PHINode>(SI.getOperand(0)->stripPointerCasts())) {
    if(PHINode_MD_Map.find(PH) != PHINode_MD_Map.end())
      return false;
  }
  if(SelectInst *SelI = dyn_cast<SelectInst>(SI.getOperand(0)->stripPointerCasts())) {
    if(SelectInst_MD_Map.find(SelI) != SelectInst_MD_Map.end())
      return false;
  }
  if(BitCastInst *BI = dyn_cast<BitCastInst>(SI.getOperand(0)->stripPointerCasts())) {
    if(BitCast_MD_Map.find(BI) != BitCast_MD_Map.end())
      return false;
  }
  // Cast the pointer operand to i8* for the runtime function.
  Value *BCI = castTo(SI.getPointerOperand(), VoidPtrTy, "", &SI);

  std::vector<Value *> Args;
  Args.push_back(BCI);
  Args.push_back(getTypeMarkerConstant(SI.getOperand(0))); // SI.getValueOperand()
  Args.push_back(getSizeConstant(SI.getOperand(0)->getType()));
  Args.push_back(getTagCounter());

  // Create the call to the runtime check and place it before the store instruction.
  CallInst::Create(trackStoreInst, Args, "", &SI);
  numStoreChecks++;

  return true;
}
