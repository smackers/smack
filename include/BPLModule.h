//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef BPLMODULE_H_
#define BPLMODULE_H_

#include "BPLProcedure.h"
#include "Common.h"
#include <map>
#include <set>
#include <string>

using namespace llvm;

namespace smack {

class BPLModule {
private:
  std::set<std::string> globalVariables;
  std::map<std::string, BPLProcedure*> procedures;

public:
  BPLModule();
  virtual ~BPLModule();
  void addGlobalVariable(std::string name);
	void addProcedure(BPLProcedure* procedure);
	BPLProcedure* getProcedure(std::string name);
	std::map<std::string, BPLProcedure*>& getProcedures();
  void print(std::ostream &os) const;
};
std::ostream &operator<<(std::ostream &os, const BPLModule* module);
std::ostream &operator<<(std::ostream &os, const BPLModule& module);

raw_ostream &operator<<(raw_ostream &os, const BPLModule* module);
raw_ostream &operator<<(raw_ostream &os, const BPLModule& module);
}

#endif /*BPLMODULE_H_*/
