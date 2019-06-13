/* Generation algorithm for fixpoint free involutions. Here, by filtering
   involutions generated with the algorithm in the fxtbook. */

#include "ffi.h"

/** Returns 1 when the array a (assumed to encode an involution) is fixpoint
    free, and 0 otherwise. */
int b_ffi(int a[], int n) {
 int j;

 /*@ loop invariant 0 <= j <= n;
   @ loop invariant is_ff(a,j);
   @ loop assigns j; */
 for (j = 0; j < n; j++) {
  if (a[j] == j) {
   return 0;
  }
 }
 return 1;
}


int first_ffi(int a[], int n) {
 int tmp;

 tmp = first_invol(a,n);

 /*@ loop invariant tmp != 0 ==> is_invol(a,n);
   @ loop assigns a[0..n-1],tmp; */
 while (tmp != 0 && b_ffi(a,n) == 0) {
  tmp = next_invol(a,n);
 } 

 if (tmp == 0) { return 0; }
 return 1;
}

int next_ffi(int a[], int n) {
 int tmp;

 /*@ loop invariant is_invol(a,n);
   @ loop assigns a[0..n-1],tmp;
   @ loop invariant le_lex{Pre,Here}(a,n); */
 do {
  tmp = next_invol(a,n);
 } while (tmp != 0 && b_ffi(a,n) == 0);

 if (tmp == 0) { return 0; }
 return 1;
}

