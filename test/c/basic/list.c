#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @flag --unroll=4
// @expect verified

typedef struct list {
  int key;
  struct list *next;
} mlist;

mlist *head;

mlist *search_list(mlist *l, int k) {
  l = head;
  while (l != NULL && l->key != k) {
    l = l->next;
  }
  return l;
}

void insert_list(mlist *l, int k) {
  l = (mlist *)malloc(sizeof(mlist));
  l->key = k;
  if (head == NULL) {
    l->next = NULL;
  } else {
    l->key = k;
    l->next = head;
  }
  head = l;
}

int main(void) {
  mlist *mylist, *temp;
  head = NULL;
  insert_list(mylist, 2);
  insert_list(mylist, 5);
  insert_list(mylist, 1);
  insert_list(mylist, 3);
  temp = search_list(head, 2);
  assert(temp->key == 2);
}
