/* 
 * File:   super_set.h
 * Author: andrew
 *
 * Created on March 10, 2010, 2:04 PM
 */

#ifndef _SUPER_SET_H
#define	_SUPER_SET_H

#include "dsa/svset.h"
#include <set>

// Contains stable references to a set
// The sets can be grown.

template<typename Ty>
class SuperSet {
  //std::set provides stable iterators, and that matters a lot
  typedef svset<Ty> InnerSetTy;
  typedef std::set<InnerSetTy> OuterSetTy;
  OuterSetTy container;
public:
  typedef const typename OuterSetTy::value_type* setPtr;

  setPtr getOrCreate(svset<Ty>& S) {
    if (S.empty()) return 0;
    return &(*container.insert(S).first);
  }

  setPtr getOrCreate(setPtr P, Ty t) {
    svset<Ty> s;
    if (P)
      s.insert(P->begin(), P->end());
    s.insert(t);
    return getOrCreate(s);
  }
};



#endif	/* _SUPER_SET_H */

