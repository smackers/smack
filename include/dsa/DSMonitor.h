
#ifndef LLVM_ANALYSIS_DSMONITOR_H
#define LLVM_ANALYSIS_DSMONITOR_H

#include "dsa/DataStructure.h"
#include "dsa/DSSupport.h"

namespace llvm {

class DSMonitor {
  DSNodeHandle N;
  std::string caption;
  std::vector<Value*> VS;
  std::string message;
  std::string location;

  void unwatch();

public:
  DSMonitor() { }
  void watch(DSNodeHandle N, std::vector<Value*> VS, std::string M = "");
  void warn();
  void witness(DSNodeHandle N, std::vector<Value*> VS, std::string M = "");
  void check();
};

}

#endif
