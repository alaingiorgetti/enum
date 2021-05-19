#include <stdint.h>

#include <stdlib.h>

#include <assert.h>



int b_barray(int32_t * a, int32_t n, int32_t k) {
  int32_t i, o, q1_;
  int cond, cond1;
  if (k <= 0) {
    return 0;
  } else {
    o = n - 1;
    if (0 <= o) {
      for (i = 0; ; ++i) {
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
