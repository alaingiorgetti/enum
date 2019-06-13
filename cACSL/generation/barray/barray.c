/* Generation of arrays containing values between 0 and k-1e, in the increasing
 * lexicographic order induced by the precedence order < on integers.
 * These arrays of lenth n encode functions from [0..n-1] to [0..k-1]. */

#include "barray.h"

int first_barray(int a[], int n, int k) {
 int i;
 /*@ loop invariant 0 <= i <= n;
   @ loop invariant is_barray(a,i,k);
   @ loop invariant cte_sub(a,i);
   @ loop assigns i, a[0..n-1];
   @ loop variant n-i; */
 for (i = 0; i < n; i++) {
  a[i] = 0;
 }
 return 1;
}

/* Returns 1 if the array is modified, or 0 if the array
   is unchanged. */
int next_barray(int a[], int n, int k) {
 int i,rev;

 // Find rightmost digit that can be incremented:
 /*@ loop invariant -1 <= rev <= n-1;
   @ loop invariant is_rightmost_rev(a,n,k,rev);
   @ loop assigns rev;
   @ loop variant rev; */
 for (rev = n-1; rev >= 0; rev--) {
  if (a[rev] < k-1) { break; }
 }
 // If there is no such index, then a = [k-1,...,k-1] is the last barray.
 if (rev == -1) { return 0; }
 a[rev]++;
 // Fill the suffix starting at a[rev+1] with zeros:
 /*@ loop invariant rev+1 <= i <= n;
   @ loop invariant is_barray(a,i,k);
   @ loop assigns i,a[rev+1..n-1];
   @ loop variant n-i; */
 for (i = rev+1; i < n; i++) { a[i] = 0; }
 return 1;
}
