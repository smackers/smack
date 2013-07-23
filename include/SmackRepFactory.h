//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef SMACKREPFACTORY_H
#define SMACKREPFACTORY_H

#include "SmackRep2dMem.h"
#include "SmackRepFlatMem.h"
#include "llvm/DataLayout.h"

namespace smack {
class SmackRepFactory {
public:
  static SmackRep* createSmackRep(llvm::DataLayout* td);
};
}

#endif // SMACKREPFACTORY_H

