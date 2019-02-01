//
// This file is distributed under the MIT License. See LICENSE for details.
//

#ifndef PRELUDE_H
#define PRELUDE_H

#include "smack/SmackRep.h"

#include <string>

namespace smack {

class Prelude {
  SmackRep &rep;

public:
  Prelude(SmackRep &rep) : rep(rep) {}

  std::string getPrelude();
};
}

#endif // PRELUDE_H
