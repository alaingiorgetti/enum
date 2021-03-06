/* Generation of all derangements of [0..n-1]. Here, by filtering permutations
 * generated in lexicographic order. */

#include "derang.h"

/* Returns 1 when the array a (assumed to be a permutation) is a derangement
 * of n elements, and 0 otherwise. */
int b_derang(int a[], int n) {
 int i;

 /*@ loop invariant 0 <= i <= n;
   @ loop invariant is_ff(a,i);
   @ loop assigns i;
   @ loop variant n-i; */
 for (i = 0; i < n; i++) {
  if (a[i] == i) {
   return 0; 
  }
 }
 return 1;
}

int first_derang(int a[], int n) {
 int tmp;
 tmp = first_injEndo(a,n);

 /*@ loop invariant tmp != 0 ==> is_injEndo(a,n);
   @ loop assigns a[0..n-1],tmp; */
 while (tmp != 0 && b_derang(a,n) == 0) {
  tmp = next_injEndo(a,n);
 } 
 if (tmp == 0) { return 0; }
 return 1;
}

int next_derang(int a[], int n) {
 int tmp;
 
 /*@ loop invariant is_injEndo(a,n);
   @ loop assigns a[0..n-1],tmp;
   @ loop invariant le_lex{Pre,Here}(a,n); */
 do {
  tmp = next_injEndo(a,n);
 } while (tmp != 0 && b_derang(a,n) == 0);

 if (tmp == 0) { return 0; }
 return 1;
}

