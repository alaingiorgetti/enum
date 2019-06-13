/* Generation of combinations of p elements out of n in the lexicographic order,
   by filtering among functions from [0..p-1] to [0..n-1]. */

#include "comb.h"

/* Returns 1 when the array a is a combination
   of p elements out of n, and 0 otherwise. */
int b_comb(int a[], int p, int n) {
 int i;

 /*@ loop invariant 1 <= i <= p;
   @ loop invariant is_inc(a,i);
   @ loop assigns i;
   @ loop variant p-i; */
 for (i = 1; i < p; i++) {
  if (a[i] <= a[i-1]) {
   return 0;
  } 
 }
 return 1;
}


int first_comb(int a[], int p, int n) {
 int tmp;

 tmp = first_barray(a,p,n);
 /*@ loop invariant tmp != 0 ==> is_barray(a,p,n);
   @ loop assigns a[0..p-1],tmp; */
 while (tmp != 0 && b_comb(a,p,n) == 0) {
  tmp = next_barray(a,p,n);
 } 
 if (tmp == 0) { return 0; }
 return 1;
}


int next_comb(int a[], int p, int n) {
 int tmp;

 /*@ loop invariant is_barray(a,p,n);
   @ loop invariant le_lex{Pre,Here}(a,p);
   @ loop assigns a[0..p-1],tmp; */
 do {
  tmp = next_barray(a,p,n);
 } while (tmp != 0 && b_comb(a,p,n) == 0);
 if (tmp == 0) { return 0; }
 return 1;
}

