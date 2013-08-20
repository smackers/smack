//===- keyiterator.h - Iterator over just the keys in a map -----*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Implement a map key iterator
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_KEYITERATOR_H
#define	LLVM_KEYITERATOR_H

#include <functional>

//From SGI's STL

// select1st and select2nd are extensions: they are not part of the standard.

template <class _Pair>
class _Select1st : public std::unary_function<_Pair, typename _Pair::first_type> {
public:

  const typename _Pair::first_type & operator()(const _Pair& __x) const {
    return __x.first;
  }
};

template <class _Pair>
class _Select2nd : public std::unary_function<_Pair, typename _Pair::second_type> {
public:

  const typename _Pair::second_type & operator()(const _Pair& __x) const {
    return __x.second;
  }
};

template <class _Pair> class select1st : public _Select1st<_Pair> {
};

template <class _Pair> class select2nd : public _Select2nd<_Pair> {
};


// ref_mapped_iterator - This is a simple iterator adapter that causes a
// function to be dereferenced whenever operator* is invoked on the iterator.
// It is assumed that the function returns a valid reference, which differs
// from llvm::mapped_iterator from which this was derived (copied)

template <class RootIt, class UnaryFunc>
class ref_mapped_iterator {
  RootIt current;
  UnaryFunc Fn;
public:
  typedef typename std::iterator_traits<RootIt>::iterator_category
  iterator_category;
  typedef typename std::iterator_traits<RootIt>::difference_type
  difference_type;
  typedef typename UnaryFunc::result_type value_type;

  typedef typename UnaryFunc::result_type *pointer;
  typedef typename UnaryFunc::result_type& reference;

  typedef RootIt iterator_type;
  typedef ref_mapped_iterator<RootIt, UnaryFunc> _Self;

  inline const RootIt &getCurrent() const {
    return current;
  }

  inline const UnaryFunc &getFunc() const {
    return Fn;
  }

  inline explicit ref_mapped_iterator(const RootIt &I, UnaryFunc F)
  : current(I), Fn(F) { }

  inline ref_mapped_iterator(const ref_mapped_iterator &It)
  : current(It.current), Fn(It.Fn) { }

  inline reference operator*() const { // All this work to do this
    return Fn(*current); // little change
  }

  _Self & operator++() {
    ++current;
    return *this;
  }

  _Self & operator--() {
    --current;
    return *this;
  }

  _Self operator++(int) {
    _Self __tmp = *this;
    ++current;
    return __tmp;
  }

  _Self operator--(int) {
    _Self __tmp = *this;
    --current;
    return __tmp;
  }

  _Self operator+(difference_type n) const {
    return _Self(current + n, Fn);
  }

  _Self & operator+=(difference_type n) {
    current += n;
    return *this;
  }

  _Self operator-(difference_type n) const {
    return _Self(current - n, Fn);
  }

  _Self & operator-=(difference_type n) {
    current -= n;
    return *this;
  }

  reference operator[](difference_type n) const {
    return *(*this +n);
  }

  inline bool operator!=(const _Self &X) const {
    return !operator==(X);
  }

  inline bool operator==(const _Self &X) const {
    return current == X.current;
  }

  inline bool operator<(const _Self &X) const {
    return current < X.current;
  }

  inline difference_type operator-(const _Self &X) const {
    return current - X.current;
  }
};

template <class Iter>
class KeyIterator
: public ref_mapped_iterator<Iter, select1st<typename Iter::value_type> > {
  typedef select1st<typename Iter::value_type> FunTy;
public:

  KeyIterator(const Iter I)
  : ref_mapped_iterator<Iter, select1st<typename Iter::value_type> >(I, FunTy()) { }
};

template <class Iter>
class ValueIterator
: public ref_mapped_iterator<Iter, select2nd<typename Iter::value_type> > {
  typedef select2nd<typename Iter::value_type> FunTy;
public:

  ValueIterator(const Iter I)
  : ref_mapped_iterator<Iter, select2nd<typename Iter::value_type> >(I, FunTy()) { }
};


#if 0

template<class Iter>
class KeyIterator {
  Iter I;

public:
  typedef typename Iter::difference_type difference_type;
  typedef typename Iter::value_type::first_type value_type;
  typedef typename Iter::value_type::first_type* pointer;
  typedef typename Iter::value_type::first_type& reference;
  typedef typename Iter::iterator_category iterator_category;

  KeyIterator(Iter i) : I(i) { }

  Iter base() const {
    return I;
  }

  reference operator*() const {
    return I->first;
  }

  KeyIterator operator+(difference_type n) const {
    return KeyIterator(I + n);
  }

  KeyIterator & operator++() {
    ++I;
    return *this;
  }

  KeyIterator operator++(int) {
    Iter OI = I;
    ++I;
    return KeyIterator(OI);
  }

  KeyIterator & operator+=(difference_type n) {
    I += n;
    return *this;
  }

  KeyIterator operator-(difference_type n) const {
    return KeyIterator(I - n);
  }

  KeyIterator & operator--() {
    --I;
    return *this;
  }

  KeyIterator operator--(int) {
    Iter OI = I;
    --I;
    return KeyIterator(OI);
  }

  KeyIterator & operator-=(difference_type n) {
    I -= n;
    return *this;
  }

  pointer operator->() const {
    return &I->first;
  }

  bool operator==(const KeyIterator& RHS) const {
    return I == RHS.I;
  }

  bool operator!=(const KeyIterator& RHS) const {
    return I != RHS.I;
  }
};
#endif


#endif	/* LLVM_KEYITERATOR_H */

