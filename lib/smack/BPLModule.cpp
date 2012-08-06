//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "BPLModule.h"

using namespace smack;

BPLModule::BPLModule() {}

BPLModule::~BPLModule() {}

void BPLModule::addGlobalVariable(std::string name) {
  assert(globalVariables.count(name) == 0);
  globalVariables.insert(name);
}

void BPLModule::addProcedure(BPLProcedure* procedure) {
  assert(procedures.count(procedure->getName()) == 0);
  procedures[procedure->getName()] = procedure;
}

BPLProcedure* BPLModule::getProcedure(std::string name) {
  if (procedures.count(name) == 0) {
    return NULL;
  } else {
    return procedures[name];
  }
}

std::map<std::string, BPLProcedure*>& BPLModule::getProcedures() {
  return procedures;
}

void BPLModule::print(std::ostream &os) const {
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

    for(std::map<std::string, BPLProcedure*>::const_iterator
        i = procedures.begin(), e = procedures.end(); i != e; ++i) {
      os << i->second << "\n";
    }
  }
}


namespace smack {

std::ostream &operator<<(std::ostream &os, const BPLModule* module) {
  if (module == 0) {
    os << "<null> BPLModule!\n";
  } else {
    module->print(os);
  }
  return os;
}
 
std::ostream &operator<<(std::ostream &os, const BPLModule& module) {
  module.print(os);
  return os;
}

raw_ostream &operator<<(raw_ostream &os, const BPLModule* module) {
  if (module == 0) {
    os << "<null> BPLModule!\n";
  } else {
    std::ostringstream stream;
    module->print(stream);
    os << stream.str();
  }
  return os;
}
 
raw_ostream &operator<<(raw_ostream &os, const BPLModule& module) {
  std::ostringstream stream;
  module.print(stream);
  os << stream.str();
  return os;
}

}
