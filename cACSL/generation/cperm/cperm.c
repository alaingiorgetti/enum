/* Generation of connected permutations of [0..n-1] (those not fixing [1..j]
   for 1 < j < n) by filtering permutations. */

#include "cperm.h"

int b_greater(int a[], int n, int n1, int n2) {
 return(a[n2] > n1);
}

int ex_greater(int a[], int n, int n1) {
 int p;

 /*@ loop invariant 0 <= p <= n1+1;
   @ loop invariant !ex_greater_gen(a,n,n1,p);
   @ loop assigns p;
   @ loop variant n1-p; */
 for (p = 0; p <= n1; p++)
  if (b_greater(a,n,n1,p) == 1) return 1;
 return 0;
}

/* Returns 1 when the array a is a connected permutation, and 0 otherwise. */
int b_connected(int a[], int n) {
 int i;

 /*@ loop invariant 0 <= i <= n;
   @ loop invariant is_connected_gen(a,n,i);
   @ loop assigns i;
   @ loop variant n-1-i;*/
 for (i = 0; i < n-1; i++) {
  if (ex_greater(a,n,i) == 0) {
   return 0;
  }
 }
 return 1;
}

int first_cperm(int a[], int n) {
 int tmp;
 tmp = first_perm(a,n);
 
 /*@ loop invariant tmp != 0 ==> is_perm(a,n);
   @ loop assigns a[0..n-1],tmp; */
 while (tmp != 0 && b_connected(a,n) == 0) {
  tmp = next_perm(a,n);
 } 
 
 if (tmp == 0) { return 0; }
 return 1;
}

int next_cperm(int a[], int n) {
 int tmp;

 /*@ loop invariant is_perm(a,n);
   @ loop assigns a[0..n-1],tmp;
   @ loop invariant le_lex{Pre,Here}(a,n); */
 do {
  tmp = next_perm(a,n);
 } while (tmp != 0 && b_connected(a,n) == 0);

 if (tmp == 0) { return 0; }
 return 1;
}

