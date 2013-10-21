#ifndef _DSA_STL_UTIL_H_
#define _DSA_STL_UTIL_H_

#include "llvm/ADT/ilist.h"
#include <list>
#include <map>
#include <vector>

namespace llvm {

// Splicing one container into another as efficiently as we can
template <typename T>
inline void splice(std::list<T>& Dst, std::list<T>& Src) {
  Dst.splice(Dst.end(), Src);
}
template <typename T>
inline void splice(ilist<T>& Dst, ilist<T>& Src) {
  Dst.splice(Dst.end(), Src);
}

template <typename T>
static void splice(std::vector<T>& Dst, std::vector<T>& Src) {
  if (Dst.empty())
    Dst.swap(Src);
  else {
    Dst.insert(Dst.end(), Src.begin(), Src.end());
    Src.clear();
  }
}

template <typename T, typename U>
inline void splice(std::map<T, U>& Dst, std::map<T, U>& Src) {
  if (Dst.empty())
    Dst.swap(Src);
  else {
    Dst.insert(Src.begin(), Src.end());
    Src.clear();
  }
}

// Efficient sort
template <typename T>
inline void sort(std::vector<T>& L) {
  std::sort(L.begin(), L.end());
}

template <typename T>
inline void sort(std::list<T>& L) {
  L.sort();
}

} // end namespace llvm
#endif // _DSA_STL_UTIL_H_

