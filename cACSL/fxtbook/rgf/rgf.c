/* Generation algorithm for RGFs.
  Adaptation of the algorithm page 325 of the fxtbook. */

#include "rgf.h"

int first_rgf(int a[], int n) {
 int k;
 /*@ loop invariant 0 <= k <= n;
   @ loop invariant is_zero(a,k);
   @ loop assigns k, a[0..n-1];
   @ loop variant n-k; */
 for (k = 0; k < n; k++) { a[k] = 0; }
 return 1;
}

int next_rgf(int a[], int n) {
 int rev,k;
 /*@ loop invariant 0 <= rev <= n-1;
   @ loop invariant is_rightmost_rev(a,n,rev);
   @ loop assigns rev;
   @ loop variant rev; */
 for (rev = n-1; rev >= 1; rev--)
  if (a[rev] <= a[rev-1]) { break; }
 if (rev == 0) { return 0; } // Last RGF.
 a[rev]++;
 /*@ loop invariant rev+1 <= k <= n;
   @ loop invariant is_non_neg(a,k);
   @ loop invariant is_le_pred(a,k);
   @ loop assigns k, a[rev+1..n-1];
   @ loop variant n-k; */
 for (k = rev+1; k < n; k++) { a[k] = 0; }
 return 1;
}
