#include <stdlib.h>

#include <stdint.h>

#include <stdio.h>

#include <assert.h>



int b_inc1(int32_t * a, int32_t n)
{
  int32_t o, o1, i;
  o = n - 1;
  o1 = 1;
  if (o >= o1) {
    for (i = o1; ; ++i) {
      if (!((a[(i - 1)]) <= (a[i]))) {
        return 0;
      }
      if (i == o) {
        break;
      }
      }
  }
  return 1;
}

int b_barray(int32_t * a, int32_t n, int32_t k)
{
  int32_t o, o1, i, q1_;
  int cond, cond1;
  if (k <= 0) {
    return 0;
  } else {
    o = n - 1;
    o1 = 0;
    if (o >= o1) {
      for (i = o1; ; ++i) {
        q1_ = (a[i]);
        if (0 <= q1_) {
          cond1 = q1_ < k;
        } else {
          cond1 = 0;
        }
        if (cond1) {
          cond = 0;
        } else {
          cond = 1;
        }
        if (cond) {
          return 0;
        }
        if (i == o) {
          break;
        }
        }
    }
    return 1;
  }
}

int b_sorted(int32_t * a, int32_t n, int32_t k)
{ if (b_barray(a, n, k)) {
    return b_inc1(a, n);
  } else {
    return 0;
  }
}

