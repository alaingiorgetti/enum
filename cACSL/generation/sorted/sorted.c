/* Efficient generation algorithm for arrays with values in [0..k-1] sorted in
   increasing order. */

#include "sorted.h"

int first_sorted(int a[], int n, int k) {
 int i;
 /*@ loop invariant 0 <= i <= n;
   @ loop invariant is_zero(a,i);
   @ loop assigns i, a[0..n-1];
   @ loop variant n-i; */
 for (i = 0; i < n; i++) {
  a[i] = 0;
 }
 return 1;
}

int next_sorted(int a[], int n, int k) {
 int i,rev;

 // Find rightmost digit that can be incremented:
 /*@ loop invariant -1 <= rev <= n-1;
   @ loop invariant is_rightmost_rev(a,n,k,rev);
   @ loop assigns rev;
   @ loop variant rev; */
 for (rev = n-1; rev >= 0; rev--) {
  if (a[rev] < k-1) { break; }
 }
 // If there is no such index, then a = [k-1,...,k-1] is the last sorted array.
 if (rev == -1) { return 0; }
 a[rev]++;

 // Fill the suffix starting at a[rev+1] with a[rev]:
 /*@ loop invariant rev+1 <= i <= n;
   @ loop invariant is_barray(a,i,k);
   @ loop invariant is_eq_aj(a,rev+1,i,a[rev]);
   @ loop invariant is_le(a,rev+1,i);
   @ loop assigns i,a[rev+1..n-1];
   @ loop variant n-i; */
 for (i = rev+1; i < n; i++) { a[i] = a[rev]; }
 return 1;
}

