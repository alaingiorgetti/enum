/* Generation algorithm for RGFs (see also fxtbook/rgf/).
 * Here, by filtering endofunctions of [0..n-1]. */

#include "rgf.h"

/* Returns 1 when the array a is an RGF, and 0 otherwise. */
int b_rgf(int a[], int n) {
 int i;

 if (a[0] != 0) return 0;
 /*@ loop invariant 1 <= i <= n;
   @ loop invariant is_le_pred(a,i);
   @ loop assigns i;
   @ loop variant n-i; */
 for (i = 1; i < n; i++)
  if (a[i] > a[i-1]+1) return 0;
 return 1;
}

int first_rgf(int a[], int n) {
 int tmp;

 tmp = first_endobarray(a,n);
 /*@ loop invariant tmp != 0
   @  ==> is_endobarray(a,n);
   @ loop assigns a[0..n-1],tmp; */
 while (tmp != 0 && b_rgf(a,n) == 0) {
  tmp = next_endobarray(a,n);
 }
 if (tmp == 0) { return 0; }
 return 1;
}

int next_rgf(int a[], int n) {
 int tmp = 0;

 /*@ loop assigns a[0..n-1], tmp;
   @ loop invariant is_endobarray(a,n);
   @ loop invariant
   @  le_lex{Pre,Here}(a,n); */
 do {
  tmp = next_endobarray(a,n);
 } while (tmp != 0 && b_rgf(a,n) == 0);
 if (tmp == 0) { return 0; }
 return 1;
}
