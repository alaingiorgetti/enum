/* Generation of all involutions of [0..n-1] by filtering permutations. */

#include "invol.h"

/** Returns 1 when the array a is an involution of n elements, and 0 otherwise. */
int b_invol(int a[], int n) {
 int i;

 /*@ loop invariant 0 <= i <= n;
   @ loop invariant is_inv(a,i);
   @ loop assigns i;
   @ loop variant n-i;*/
 for (i = 0; i < n; i++) {
  if (a[a[i]] != i) {
   return 0;
  }
 }
 return 1;
}


int first_invol(int a[], int n) {
 int tmp;

 tmp = first_injEndo(a,n);

 /*@ loop invariant tmp != 0 ==> is_injEndo(a,n);
   @ loop assigns a[0..n-1],tmp; */
 while (tmp != 0 && b_invol(a,n) == 0) {
  tmp = next_injEndo(a,n);
 }

 if (tmp == 0) { return 0; }
 return 1;
}

int next_invol(int a[], int n) {
 int tmp;

 /*@ loop invariant is_injEndo(a,n);
   @ loop assigns a[0..n-1],tmp;
   @ loop invariant le_lex{Pre,Here}(a,n); */
 do {
  tmp = next_injEndo(a,n);
 } while (tmp != 0 && b_invol(a,n) == 0);

 if (tmp == 0) { return 0; }
 return 1;
}

