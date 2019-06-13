/* Generation of arrays with values in [0..k-1] sorted in increasing order.
 * Here, by filtering functions from [0..n-1] to [0..k-1]. */

#include "sorted1.h"

/* Returns 1 when the array a is sorted, and 0 otherwise. */
int b_le(int a[], int n, int k) {
 int i;

 /*@ loop invariant 1 <= i <= n;
   @ loop invariant is_le(a,i);
   @ loop assigns i;
   @ loop variant n-i; */
 for (i = 1; i < n; i++)
  if (a[i-1] > a[i]) return 0;
 return 1;
}


int first_sorted1(int a[], int n, int k) {
 int tmp;

 tmp = first_barray(a,n,k);
 /*@ loop invariant tmp != 0 ==> is_barray(a,n,k);
   @ loop assigns a[0..n-1],tmp; */
 while (tmp != 0 && b_le(a,n,k) == 0) {
  tmp = next_barray(a,n,k);
 }
 if (tmp == 0) { return 0; }
 return 1;
}


int next_sorted1(int a[], int n, int k) {
 int tmp;

 /*@ loop invariant is_barray(a,n,k);
   @ loop assigns a[0..n-1],tmp;
   @ loop invariant le_lex{Pre,Here}(a,n); */
 do {
  tmp = next_barray(a,n,k);
 } while (tmp != 0 && b_le(a,n,k) == 0);
 if (tmp == 0) { return 0; }
 return 1;
}

