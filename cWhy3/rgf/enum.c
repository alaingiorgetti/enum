#include <stdlib.h>

#include <stdint.h>

#include <stdio.h>

#include <assert.h>


#define LOW_MASK 0x00000000FFFFFFFFUL

struct __add32_with_carry_result
{ uint32_t __field_0;
  uint32_t __field_1;
};

struct __add32_with_carry_result add32_with_carry(uint32_t x, uint32_t y, uint32_t c)
{
  struct __add32_with_carry_result result;
  uint64_t r = (uint64_t)x + (uint64_t)y + (uint64_t) c;
  result.__field_0 = (uint32_t)(r & LOW_MASK);
  result.__field_1 = (uint32_t)(r >> 32);
  return result;
}

struct __sub32_with_borrow_result
{ uint32_t __field_0;
  uint32_t __field_1;
};

struct __sub32_with_borrow_result sub32_with_borrow(uint32_t x, uint32_t y, uint32_t b)
{
  struct __sub32_with_borrow_result result;
  uint64_t r = (uint64_t)x - (uint64_t)y - (uint64_t) b;
  result.__field_0 = (uint32_t)(r & LOW_MASK);
  result.__field_1 = (uint32_t)(r >> 63);
  return result;
}

struct __mul32_double_result
{ uint32_t __field_0;
  uint32_t __field_1;
};

struct __mul32_double_result mul32_double(uint32_t x, uint32_t y)
{
  struct __mul32_double_result result;
  uint64_t r = (uint64_t)x * (uint64_t)y;
  result.__field_0 = (uint32_t)(r & LOW_MASK);
  result.__field_1 = (uint32_t)(r >> 32);
  return result;
}

struct __add32_3_result
{ uint32_t __field_0;
  uint32_t __field_1;
};

struct __add32_3_result add32_3(uint32_t x, uint32_t y, uint32_t z)
{
  struct __add32_3_result result;
  uint64_t r = (uint64_t)x + (uint64_t)y + (uint64_t) z;
  result.__field_0 = (uint32_t)(r & LOW_MASK);
  result.__field_1 = (uint32_t)(r >> 32);
  return result;
}

struct __lsld32_result
{ uint32_t __field_0;
  uint32_t __field_1;
};

struct __lsld32_result lsld32(uint32_t x, uint32_t cnt)
{
  struct __lsld32_result result;
  uint64_t r = (uint64_t)x << cnt;
  result.__field_0 = (uint32_t)(r & LOW_MASK);
  result.__field_1 = (uint32_t)(r >> 32);
  return result;
}

#define IGNORE2(x,y) do { (void)(x); (void)(y); } while (0)
struct cursor
{ int32_t * current;
  int32_t len;
  int new;
};

struct cursor create_cursor(int32_t n)
{
  int32_t * a;
  int32_t o, o1, i;
  struct cursor cursor;
  a = malloc((uint32_t)n * sizeof(int32_t));
  assert (a);
  o = n - 1;
  o1 = 0;
  if (o >= o1) {
    for (i = o1; ; ++i) {
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


void next(struct cursor * c)
{
  int32_t * a;
  int32_t n, o, o1, i;
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
      o = n - 1;
      o1 = r + 1;
      if (o >= o1) {
        for (i = o1; ; ++i) {
          (a[i] = 0);
          if (i == o) {
            break;
          }
          }
      }
      c->new = 1;
    }
  }
}

