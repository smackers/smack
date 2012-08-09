//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKMODULE_H_
#define SMACKMODULE_H_

#include "Procedure.h"
#include "Common.h"
#include <map>
#include <set>
#include <string>

using namespace llvm;

namespace smack {

class SmackModule {
private:
  std::set<std::string> globalVariables;
  std::map<std::string, Procedure*> procedures;

public:
  SmackModule();
  virtual ~SmackModule();
  void addGlobalVariable(std::string name);
	void addProcedure(Procedure* procedure);
	Procedure* getProcedure(std::string name);
	std::map<std::string, Procedure*>& getProcedures();
  void print(std::ostream &os) const;
};
std::ostream &operator<<(std::ostream &os, const SmackModule* module);
std::ostream &operator<<(std::ostream &os, const SmackModule& module);

raw_ostream &operator<<(raw_ostream &os, const SmackModule* module);
raw_ostream &operator<<(raw_ostream &os, const SmackModule& module);
}

#endif /*SMACKMODULE_H_*/
