/* Functions for display, counting and conversion. */

#include <stdio.h>
#include <stdint.h>

// Display an array of length n.
void displayl(int32_t a[], int32_t n) {
 int i;
 printf("[ ");
 for (i = 0; i < n; i++)
  printf("%d ",a[i]);
 printf("]");
}

///////////////// count ////////////////////////

// Computes n!.
long fact(int32_t n) {
 int i;
 long x = 1;
 for (i = 2; i <= n; i++)
  x = x * i;
 return x;
}

// Computes x^n.
long power(int32_t x, int32_t n) {
 long y = 1;
 int m = 1;
 while (m <= n) {
  y *= (long) x;
  m++;
 }
 return y;
}