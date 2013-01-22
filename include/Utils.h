//
// Copyright (c) 2008 Zvonimir Rakamaric (zvonimir@cs.utah.edu)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef UTILS_H_
#define UTILS_H_

#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/GraphWriter.h"
#include <algorithm>
#include <ostream>

namespace smack {

struct deleteObject {
  template <typename T>
  void operator()(T* obj) {
    delete obj;
  }
};

struct deleteSecondObject {
  template <typename T1, typename T2>
  void operator()(const std::pair<T1, T2>& pair) {
    delete pair.second;
  }
};

class printItem {
private:
  std::ostream &os;
  
public:
  printItem(std::ostream &stream) : os(stream) {}
  template <typename T>
  void operator()(T* item) {
    os << *item;
  }
};

class printSecondItem {
private:
  std::ostream &os;
  
public:
  printSecondItem(std::ostream &stream) : os(stream) {}
  template <typename T1, typename T2>
  void operator()(const std::pair<T1, T2>& pair) {
    os << pair.second << std::endl;
  }
};

template <class CT>
void printElements(const CT& collection, std::ostream& os) {
  std::for_each(collection.begin(), collection.end(), printItem(os));
}

template <class CT>
void printSecondElements(const CT& collection, std::ostream& os) {
  std::for_each(collection.begin(), collection.end(), printSecondItem(os));
}

std::string EscapeString(std::string str);

}

#endif /*UTILS_H_*/
