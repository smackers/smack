//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "SmackRepFactory.h"

namespace smack {

SmackRep* SmackRepFactory::createSmackRep(llvm::DataLayout* td, MemMod memoryModel) {
  if (memoryModel == twodim) {
    return new SmackRep2dMem(td);
  } else {
    return new SmackRepFlatMem(td);
  }
}

} // namespace smack

