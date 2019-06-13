/* Generation of all subsets of a set of n elements from delta sets, in
   the lexicographic increasing order (on the delta sets) induced by the
   precedence 0 < 1. Adaptation of the algorithm page 203 of the fxtbook. */

#include "subset.h"

int first_subset(int a[], int n) {
 int k;
 /*@ loop invariant 0 <= k <= n;
   @ loop invariant is_dset(a,k);
   @ loop assigns k, a[0..n-1];
   @ loop variant n-k; */
 for ( k = 0; k < n; k++) {
  a[k] = 0;
 }
 return 1;
}


int next_subset(int a[], int n) {
 int i,rev;

 /*@ loop invariant -1 <= rev <= n-1;
   @ loop invariant is_rightmost_rev(a,n,rev);
   @ loop assigns rev;
   @ loop variant rev; */
 for (rev = n-1; rev >= 0; rev--) { if (a[rev] == 0) { break; } }
 if (rev == -1) { return 0; }
 a[rev] = 1;
 /*@ loop invariant rev+1 <= i <= n;
   @ loop invariant is_dset(a,i);
   @ loop assigns i,a[rev+1..n-1];
   @ loop variant n-i; */
 for (i = rev+1; i < n; i++) { a[i] = 0; }
 /*@ assert lt_lex_at{Pre,Here}(a,rev); */
 return 1;
}
