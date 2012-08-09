//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "SmackModule.h"

using namespace smack;

SmackModule::SmackModule() {}

SmackModule::~SmackModule() {}

void SmackModule::addGlobalVariable(std::string name) {
  assert(globalVariables.count(name) == 0);
  globalVariables.insert(name);
}

void SmackModule::addProcedure(Procedure* procedure) {
  assert(procedures.count(procedure->getName()) == 0);
  procedures[procedure->getName()] = procedure;
}

Procedure* SmackModule::getProcedure(std::string name) {
  if (procedures.count(name) == 0) {
    return NULL;
  } else {
    return procedures[name];
  }
}

std::map<std::string, Procedure*>& SmackModule::getProcedures() {
  return procedures;
}

void SmackModule::print(std::ostream &os) const {
  if (this == 0) {
    os << "<null BPLModule>";
  } else {
    os << "//**** MODULE ****\n";

    os << "\n";

    for(std::set<std::string>::const_iterator
        i = globalVariables.begin(), e = globalVariables.end(); i != e; ++i) {
      os << "var " << *i << ":ptr;\n";
    }

    os << "\n";

    for(std::map<std::string, Procedure*>::const_iterator
        i = procedures.begin(), e = procedures.end(); i != e; ++i) {
      os << i->second << "\n";
    }
  }
}


namespace smack {

std::ostream &operator<<(std::ostream &os, const SmackModule* module) {
  if (module == 0) {
    os << "<null> BPLModule!\n";
  } else {
    module->print(os);
  }
  return os;
}
 
std::ostream &operator<<(std::ostream &os, const SmackModule& module) {
  module.print(os);
  return os;
}

raw_ostream &operator<<(raw_ostream &os, const SmackModule* module) {
  if (module == 0) {
    os << "<null> BPLModule!\n";
  } else {
    std::ostringstream stream;
    module->print(stream);
    os << stream.str();
  }
  return os;
}
 
raw_ostream &operator<<(raw_ostream &os, const SmackModule& module) {
  std::ostringstream stream;
  module.print(stream);
  os << stream.str();
  return os;
}

}
