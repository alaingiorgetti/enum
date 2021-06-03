#include <stdint.h>

#include <stdlib.h>

#include <assert.h>


struct cursor {
  int32_t * current;
  int32_t len;
  int new;
};

struct cursor create_cursor(int32_t n) {
  int32_t * a;
  int32_t i, o;
  struct cursor cursor;
  a = malloc((uint32_t)n * sizeof(int32_t));
  assert (a);
  o = n - 1;
  if (0 <= o) {
    for (i = 0; ; ++i) {
      a[i] = i;
      if (i == o) {
        break;
      }
    }
  }
  cursor.current = a;
  cursor.len = n;
  cursor.new = 1;
  return cursor;
}


void swap(int32_t * a, int32_t i, int32_t j) {
  int32_t v;
  v = (a[i]);
  (a[i] = (a[j]));
  (a[j] = v);
  return;
}

void reverse(int32_t * a, int32_t l, int32_t u) {
  int32_t x, y;
  x = l;
  y = u - 1;
  while (x < y) {
    swap(a, x, y);
    y = y - 1;
    x = x + 1;
  }
}

void next(struct cursor * c) {
  int32_t * a;
  int32_t n;
  int32_t r, j;
  a = (c->current);
  n = c->len;
  if (n <= 1) {
    c->new = 0;
  } else {
    r = n - 2;
    while (r >= 0 && (a[r]) > (a[(r + 1)])) {
      r = r - 1;
    }
    if (r < 0) {
      c->new = 0;
    } else {
      j = n - 1;
      while ((a[r]) > (a[j])) {
        j = j - 1;
      }
      swap(a, r, j);
      reverse(a, r + 1, n);
      c->new = 1;
    }
  }
}
