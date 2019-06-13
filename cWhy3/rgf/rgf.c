#include <stdlib.h>

#include <stdint.h>

#include <stdio.h>

#include <assert.h>



int b_rgf(int32_t * a, int32_t n)
{
  int32_t o, o1, i, q1_;
  int cond, cond1;
  if (n == 0) {
    return 1;
  } else {
    if (!((a[0]) == 0)) {
      return 0;
    } else {
      o = n - 1;
      o1 = 1;
      if (o >= o1) {
        for (i = o1; ; ++i) {
          q1_ = (a[i]);
          if (0 <= q1_) {
            cond1 = q1_ <= (a[(i - 1)]) + 1;
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
    }
  }
  return 1;
}

