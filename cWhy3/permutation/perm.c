#include <stdint.h>

#include <stdlib.h>

#include <assert.h>



int b_range(int32_t * a, int32_t n) {
  int32_t j, o, q1_;
  int cond, cond1;
  o = n - 1;
  if (0 <= o) {
    for (j = 0; ; ++j) {
      q1_ = (a[j]);
      if (0 <= q1_) {
        cond1 = q1_ < n;
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
      if (j == o) {
        break;
      }
    }
  }
  return 1;
}

int b_diff(int32_t * a, int32_t i, int32_t n) {
  int32_t j, o;
  o = n - 1;
  if (0 <= o) {
    for (j = 0; ; ++j) {
      if ((a[j]) == (a[i]) && !(j == i)) {
        return 0;
      }
      if (j == o) {
        break;
      }
    }
  }
  return 1;
}

int b_injective(int32_t * a, int32_t n) {
  int32_t j, o;
  o = n - 1;
  if (0 <= o) {
    for (j = 0; ; ++j) {
      if (!b_diff(a, j, n)) {
        return 0;
      }
      if (j == o) {
        break;
      }
    }
  }
  return 1;
}

int b_permut(int32_t * a, int32_t n) {
  if (b_range(a, n)) {
    return b_injective(a, n);
  } else {
    return 0;
  }
}
