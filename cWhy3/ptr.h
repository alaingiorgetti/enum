#ifndef PTR_H__
#define PTR_H__

struct cursor {
  int32_t * current;
  int32_t n;
  int new;
};

struct cursor create_cursor(int32_t n);

void next(struct cursor * c);

int b_fact(int32_t * a, int32_t n);

int b_rgf(int32_t * a, int32_t n);

int b_permut(int32_t * a, int32_t n);

int b_injective(int32_t * a, int32_t n);

int b_diff(int32_t * a, int32_t i, int32_t n);

int b_range(int32_t * a, int32_t n);

#endif