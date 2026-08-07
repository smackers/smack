#include <assert.h>
#include <stdlib.h>

// @expect verified

typedef struct node {
  int value;
  struct node *next;
} node_t;

void set_value(int *p) { *p = 42; }

node_t *make_node(int value) {
  node_t *n = (node_t *)malloc(sizeof(node_t));
  n->value = value;
  n->next = 0;
  return n;
}

void link_node(node_t *head, node_t *next) { head->next = next; }

int read_next(node_t *head) { return head->next->value; }

int main(void) {
  int x = 0;
  set_value(&x);
  assert(x == 42);

  node_t *head = make_node(1);
  node_t *tail = make_node(7);
  link_node(head, tail);
  assert(read_next(head) == 7);

  return 0;
}
