/* Generation of all permutations on [0..n-1] by filtering endofunctions on
   [0..n-1] which are injections. */

#include "injEndo.h"

int b_diff(int a[], int n, int i) {
 int j;

 /*@ loop invariant 0 <= j <= n;
   @ loop invariant is_diff(a,j,i);
   @ loop assigns j; */
 for (j = 0; j < n; j++) {
  if (a[j] == a[i] && j != i) {
   return 0;
  }
 }
 return 1;
}


int b_linear(int a[], int n) {
 int i;

 /*@ loop invariant 0 <= i <= n;
   @ loop invariant is_linear_gen(a,n,i);
   @ loop assigns i; */
 for (i = 0; i < n; i++) {
  if (b_diff(a,n,i) != 1) {
   return 0;
  }
 }
 return 1;
}

/** Returns 1 when the array a is an injection, and 0 otherwise. */
int b_injEndo(int a[], int n) {
 return (b_linear(a,n));
}


int first_injEndo(int a[], int n) {
 int tmp;

 tmp = first_endobarray(a,n);
 if (tmp != 1) { return 0; }

 /*@ loop invariant tmp != 0 ==> is_endobarray(a,n);
   @ loop assigns a[0..n-1],tmp; */
 while (tmp != 0 && b_injEndo(a,n) == 0) {
  tmp = next_endobarray(a,n);
 } 

 if (tmp == 0) { return 0; }
 return 1;
}


int next_injEndo(int a[], int n) {
 int tmp;

 /*@ loop invariant is_endobarray(a,n);
   @ loop assigns a[0..n-1],tmp;
   @ loop invariant le_lex{Pre,Here}(a,n); */
 do {
  tmp = next_endobarray(a,n);
 } while (tmp != 0 && b_injEndo(a,n) == 0);

 if (tmp == 0) { return 0; }
 return 1;
}

