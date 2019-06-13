/* Generation of combinations of p elements out of n in lexicographic order.
   Adaptation of the algorithm given page 178 of the fxtbook.
   The combination {e_0,..,e_{p-1}} with e_0 < ... < e_{p-1} is stored in the
   array c of size p such that c[i] = e_i. */

#include "comb.h"

int first_comb(int a[], int p, int n) {
 int k;
 /*@ loop invariant 0 <= k <= p;
   @ loop invariant is_id(a,k);
   @ loop assigns k, a[0..p-1];
   @ loop variant p-k; */
 for (k = 0; k < p; k++) {
  a[k] = k;
 }
 return 1;
}

int next_comb(int a[], int p, int n) {
 int k,rev;

 if (a[p-1] < n-1) { // easy case
  a[p-1]++;
  /*@ assert lt_lex_at{Pre,Here}(a,p-1); */
  return 1;
 } 

 /*@ loop invariant -1 <= rev <= p-2;
   @ loop invariant rev >= 0 ==> is_le(a,rev,p,n);
   @ loop invariant is_rightmost_rev(a,p,rev);
   @ loop assigns rev;
   @ loop variant rev; */
 for (rev = p-2; rev >= 0; rev--) 
  if (a[rev+1] - a[rev] > 1) break;
 if (rev < 0) return 0; // last comb reached
 a[rev]++;

 /*@ loop invariant rev+1 <= k <= p;
   @ loop invariant is_lt_next(a,rev,k-1);
   @ loop invariant is_le(a,rev,p,n);
   @ loop assigns k, a[rev+1..p-1];
   @ loop variant p-k; */
 for (k = rev+1; k < p; k++) 
  a[k] = a[k-1]+1;

 /*@ assert lt_lex_at{Pre,Here}(a,rev); */
 return 1;
}
