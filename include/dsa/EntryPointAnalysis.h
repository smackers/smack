//===-- EntryPointAnalysis.h - Entry point Finding Pass -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a general way of finding entry points in a system.  Simple programs
// will use the main version.  Libraries and OS kernels can have more
// specialized versions.
//
//===----------------------------------------------------------------------===//

#ifndef _ENTRYPOINTANALYSIS_H
#define	_ENTRYPOINTANALYSIS_H

namespace llvm {
class Function;
class Module;
}

#include <string>
#include "llvm/Pass.h"

class EntryPointAnalysis : public llvm::ModulePass {
  std::set<std::string> names;
  bool haveNames;
public:
  static char ID;
  EntryPointAnalysis();
  virtual ~EntryPointAnalysis();

  /// print - Print out the analysis results...
  ///
  void print(llvm::raw_ostream &O, const llvm::Module *M) const;

  bool runOnModule(llvm::Module&);

  virtual void getAnalysisUsage(llvm::AnalysisUsage &Info) const;

  bool isEntryPoint(const llvm::Function* F) const;

  void findEntryPoints(const llvm::Module& M,
                       std::vector<const llvm::Function*>& dest) const;

};



#endif	/* _ENTRYPOINTANALYSIS_H */

