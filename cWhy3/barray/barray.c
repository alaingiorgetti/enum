#include <stdlib.h>

#include <stdint.h>

#include <stdio.h>

#include <assert.h>



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

