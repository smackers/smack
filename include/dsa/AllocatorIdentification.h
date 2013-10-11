//===-- AllocatorIdentification.h - Identify alloc wrappers --------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
// Identify malloc/free wrappers.
//===----------------------------------------------------------------------===//

#ifndef _ALLOCATORIDENTIFICATION_H
#define	_ALLOCATORIDENTIFICATION_H

#include <string>
#include "llvm/Pass.h"
#include "llvm/IR/Value.h"

namespace llvm {
  class Function;
  class Module;
  class Instruction;

  class AllocIdentify : public llvm::ModulePass {
  protected:
    std::set<std::string> allocators;
    std::set<std::string> deallocators;
    bool flowsFrom(Value *Dest,Value *Src);

  public:
    std::set<std::string>::iterator alloc_begin() {
      return allocators.begin();
    }
    std::set<std::string>::iterator alloc_end() {
      return allocators.end();
    }
    std::set<std::string>::iterator dealloc_begin() {
      return deallocators.begin();
    }
    std::set<std::string>::iterator dealloc_end() {
      return deallocators.end();
    }
    static char ID;
    AllocIdentify();
    virtual ~AllocIdentify();
    bool runOnModule(llvm::Module&);
    virtual void getAnalysisUsage(llvm::AnalysisUsage &Info) const;
    virtual const char * getPassName() const {
      return "Allocator Identification Analysis (find malloc/free wrappers)";
    }
  };

}

#endif	/* _ALLOCATORIDENTIFICATION_H */

