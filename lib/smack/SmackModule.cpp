//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "SmackModule.h"

using namespace smack;
using namespace std;

SmackModule::SmackModule() {}

SmackModule::~SmackModule() {}

void SmackModule::addGlobalVariable(string name) {
  assert(globalVariables.count(name) == 0);
  globalVariables.insert(name);
}

void SmackModule::addProcedure(Procedure* procedure) {
  assert(procedures.count(procedure->getName()) == 0);
  procedures[procedure->getName()] = procedure;
}

Procedure* SmackModule::getProcedure(string name) {
  if (procedures.count(name) == 0) {
    return NULL;
  } else {
    return procedures[name];
  }
}

map<string, Procedure*>& SmackModule::getProcedures() {
  return procedures;
}

void SmackModule::print(ostream &os) const {
  if (this == 0) {
    os << "<null SmackModule>";
  } else {
    os << "// SMACK-MODULE-BEGIN" << endl;

    for(set<string>::const_iterator
        i = globalVariables.begin(), e = globalVariables.end(); i != e; ++i) {
      os << "const unique " << translateName(*i) << ": $ptr;" << endl;
      
      for(set<string>::const_iterator
        j = i, f = globalVariables.end(); j != f && ++j != f; ) {
          os << "axiom($obj(" << *i << ") != $obj(" << *j << "));" << endl;
      }
    }

    for(map<string, Procedure*>::const_iterator
        i = procedures.begin(), e = procedures.end(); i != e; ++i) {
      os << "const unique " << i->first << "#ptr: $ptr;" << endl;
    }

    for(map<string, Procedure*>::const_iterator
        i = procedures.begin(), e = procedures.end(); i != e; ++i) {
      os << endl << i->second;
    }

    os << "// SMACK-MODULE-END" << endl;
  }
}


namespace smack {

ostream &operator<<(ostream &os, const SmackModule* module) {
  if (module == 0) {
    os << "<null> SmackModule!" << endl;
  } else {
    module->print(os);
  }
  return os;
}
 
ostream &operator<<(ostream &os, const SmackModule& module) {
  module.print(os);
  return os;
}

raw_ostream &operator<<(raw_ostream &os, const SmackModule* module) {
  if (module == 0) {
    os << "<null> SmackModule!\n";
  } else {
    ostringstream stream;
    module->print(stream);
    os << stream.str();
  }
  return os;
}
 
raw_ostream &operator<<(raw_ostream &os, const SmackModule& module) {
  ostringstream stream;
  module.print(stream);
  os << stream.str();
  return os;
}

}
