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
      a[i] = 0;
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


void next(struct cursor * c) {
  int32_t * a;
  int32_t n, i, o, o1;
  int32_t r;
  a = (c->current);
  n = c->len;
  if (n <= 1) {
    c->new = 0;
  } else {
    r = n - 1;
    while (r >= 1 && (a[r]) == (a[(r - 1)]) + 1) {
      r = r - 1;
    }
    if (r == 0) {
      c->new = 0;
    } else {
      (a[r] = ((a[r]) + 1));
      o = r + 1;
      o1 = n - 1;
      if (o <= o1) {
        for (i = o; ; ++i) {
          (a[i] = 0);
          if (i == o1) {
            break;
          }
        }
      }
      c->new = 1;
    }
  }
}
