/* Generation of factorial arrays. */

#include "fact.h"

int first(int a[], int n) {
 int i;
 /*@ loop invariant 0 <= i <= n;
   @ loop invariant is_fact(a,i);
   @ loop assigns i, a[0..n-1];
   @ loop variant n-i; */
 for (i = 0; i < n; i++) {
  a[i] = 0;
 }
 return 1;
}

/* Returns 1 if the array is modified, or 0 if the array
   is unchanged. */
int next(int a[], int n) {
 int i,rev;

 // Find rightmost digit that can be incremented:
 /*@ loop invariant -1 <= rev <= n-1;
   @ loop invariant is_rightmost_rev(a,n,rev);
   @ loop assigns rev;
   @ loop variant rev; */
 for (rev = n-1; rev >= 0; rev--) {
  if (a[rev] != rev) { break; }
 }
 if (rev == -1) { return 0; }
 a[rev]++;
 // Fill the suffix starting at a[rev+1] with zeros:
 /*@ loop invariant rev+1 <= i <= n;
   @ loop invariant is_fact(a,i);
   @ loop assigns i,a[rev+1..n-1];
   @ loop variant n-i; */
 for (i = rev+1; i < n; i++) { a[i] = 0; }
 return 1;
}
