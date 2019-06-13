#include "suffix.h"

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_z(a,n);
  @ assigns a[0..n-1];
  @ ensures soundness: is_z(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_z(int a[], int n) {
 int rev;

 /*@ loop invariant -1 <= rev <= n-1;
   @ loop invariant is_rightmost_rev(a,n,rev);
   @ loop assigns rev;
   @ loop variant rev; */
 for (rev = n-1; rev >= 0; rev--) if (b_rev(a,n,rev)) break;
 if (rev == -1) return 0;
 suffix(a,n,rev);
 return 1;
}

