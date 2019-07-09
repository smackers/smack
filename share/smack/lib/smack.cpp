#include <cstddef>
#include <new>

extern void *malloc(size_t size);
extern void free(void *p);

void *operator new(size_t size) throw(std::bad_alloc) { return malloc(size); }

void operator delete(void *p) throw() { free(p); }
