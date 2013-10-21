#ifndef _SV_ORDERED_SET_HH_
#define _SV_ORDERED_SET_HH_ 1

#include <algorithm>
#include <functional>
#include <vector>

////////////////////////////////////////////////////////////////////////////////////////////////////

/// A set implemented atop a sorted vector.
/// Iterators are not stable accross insert or delete
template< typename Key,
        typename Compare = std::less<Key>,
        typename Alloc = std::allocator<Key> >
class svset {
  typedef std::vector<Key, Alloc> internal_type;

// Types
public:

  typedef Key     key_type;
  typedef Key     value_type;
  typedef Compare key_compare;
  typedef Compare value_compare;
  typedef Alloc   allocator_type;
  typedef typename Alloc::reference reference;
  typedef typename Alloc::const_reference const_reference;
  typedef typename Alloc::pointer pointer;
  typedef typename Alloc::const_pointer const_pointer;
  typedef typename internal_type::const_iterator const_iterator;
  typedef typename internal_type::iterator iterator;
  typedef typename internal_type::reverse_iterator reverse_iterator;
  typedef typename internal_type::const_reverse_iterator const_reverse_iterator;
  typedef typename internal_type::size_type size_type;
  typedef typename internal_type::difference_type difference_type;
        
private:
  
  internal_type container_;

  void sort_unique() {
    std::sort(container_.begin(), container_.end());
    iterator i = std::unique(container_.begin(), container_.end());
    container_.erase(i, container_.end());
  }

public:
  /// Empty constructor.
  svset()
  : container_() { }

  /// Constructor taking a range.
  template< typename Iterator >
  svset(const Iterator& begin, const Iterator& end)
  : container_(begin, end) {
    sort_unique();
  }
  
  /// Copy-constructor.
  svset(const svset& rhs)
  : container_(rhs.container_)
  {}

  /// Affectation of a sorted vector to another one.

  svset & operator=(const svset& rhs) {
    if (&rhs != this) {
      this->container_ = rhs.container_;
    }
    return *this;
  }

  /// Returns the beginning of the sorted vector.
  const_iterator begin() const {
    return container_.begin();
  }

  /// Returns the end of the sorted vector.
  const_iterator end() const {
    return container_.end();
  }

  /// Returns the beginning of the sorted vector.
  iterator begin() {
    return container_.begin();
  }

  /// Returns the end of the sorted vector.
  iterator end() {
    return container_.end();
  }

  /// Returns the beginning of the sorted vector.
  const_reverse_iterator rrbegin() const {
    return container_.rbegin();
  }

  /// Returns the end of the sorted vector.
  const_reverse_iterator rend() const {
    return container_.rend();
  }

  /// Returns the beginning of the sorted vector.
  reverse_iterator rbegin() {
    return container_.rbegin();
  }

  /// Returns the end of the sorted vector.
  reverse_iterator rend() {
    return container_.rend();
  }

  bool empty() const {
    return container_.empty();
  }

  size_type size() const {
    return container_.size();
  }

  size_type max_size() const {
    return container_.max_size();
  }

  /// Insert a value into the sorted vector.
  std::pair<iterator,bool>
  insert(const value_type& x) {
    bool insertion = false;
    iterator i = std::lower_bound(container_.begin(), container_.end(), x);
    if (i == container_.end() || x < *i) {
      i = container_.insert(i, x);
      insertion = true;
    }
    return std::make_pair(i, insertion);
  }

  /// Insert a value into the sorted vector.
  iterator insert(iterator position, const value_type& x) {
    return insert(x).first;
  }

  /// Insert a range.
  template < typename Iterator >
  void insert(Iterator _begin, Iterator _end) {
    while (_begin != _end)
      container_.push_back(*_begin++);
    sort_unique();
  }

  //specialized insert for another svset
  void insert(const_iterator ii, const_iterator ie ) {
    internal_type ctemp;
    ctemp.reserve(container_.size());
    std::set_union(ii, ie, container_.begin(), container_.end(),
                   std::back_inserter(ctemp));
    container_.swap(ctemp);
  }

  iterator erase ( iterator position ) {
    return container_.erase(position);
  }

  size_type erase(const key_type& x) {
    iterator i = find(x);
    if (i != end()) {
      erase(i);
      return 1;
    }
    return 0;
  }

  iterator erase ( iterator first, iterator last ) {
    return container_.erase(first, last);
  }

  /// Swap the content of two sorted_vector.
  void swap(svset& s) {
    container_.swap(s.container_);
  }

  void clear() {
    container_.clear();
  }

  /// Find the key k.

  const_iterator find(const key_type& k) const {
    const_iterator i = std::lower_bound(container_.begin(), container_.end(), k);
    if (i != container_.end() && *i == k) return i;
    return container_.end();
  }

  iterator find(const key_type& k) {
    iterator i = std::lower_bound(container_.begin(), container_.end(), k);
    if (i != container_.end() && *i == k) return i;
    return container_.end();
  }

  bool count(const key_type& k) const {
    return find(k) != end();
  }

  iterator lower_bound(const key_type& x) const {
    return std::lower_bound(container_.begin(), container_.end(), x);
  }

  iterator upper_bound(const key_type& x) const {
    return std::upper_bound(container_.begin(), container_.end(), x);
  }

  std::pair<iterator,iterator> equal_range(const key_type& x) const {
    return std::make_pair(lower_bound(x),upper_bound(x));
  }


  /// Tells if this sorted vector is equal to another one.
  bool operator==(const svset& rhs) const {
    return container_ == rhs.container_;
  }
  bool operator<(const svset& rhs) const {
    if (rhs.size() < size()) return false;
    if (size() < rhs.size()) return true;
    const_iterator ii = begin();
    const_iterator ee = end();
    const_iterator rhs_ii = rhs.begin();
    while (ii != ee) {
      if (*rhs_ii < *ii) return false;
      if (*ii < *rhs_ii) return true;
      ++ii;
      ++rhs_ii;
    }
    // Equal
    return false;
  }
  
};

////////////////////////////////////////////////////////////////////////////////////////////////////

#endif // _SV_ORDERED_SET_HH_
