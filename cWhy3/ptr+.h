#ifndef PTR_INT_H__
#define TEST_INT_H__

struct cursor {
  int32_t * current;
  int32_t n;
  int new;
};

struct cursor create_cursor(int32_t n, int32_t k);

void next(struct cursor * c, int32_t k);

int b_barray(int32_t * a, int32_t n, int32_t k);

int b_sorted(int32_t * a, int32_t n, int32_t k);

#endif
