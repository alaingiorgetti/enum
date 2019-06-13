/* Generation of all injections from [0..n-1] to [0..k-1], by filtering
   functions from [0..n-1] to [0..k-1]. */

#include "inj.h"


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

/* Returns 1 when the array a is an injection, and 0 otherwise. */
int b_inj(int a[], int n, int k) {
 return (b_linear(a,n));
}


int first_inj(int a[], int n, int k) {
 int tmp;

 tmp = first_barray(a,n,k);
 if (tmp != 1) { return 0; }

 /*@ loop invariant tmp != 0 ==> is_barray(a,n,k);
   @ loop assigns a[0..n-1],tmp; */
 while (tmp != 0 && b_inj(a,n,k) == 0) {
  tmp = next_barray(a,n,k);
 } 

 if (tmp == 0) { return 0; }
 return 1;
}


int next_inj(int a[], int n, int k) {
 int tmp;

 /*@ loop invariant is_barray(a,n,k);
   @ loop assigns a[0..n-1],tmp;
   @ loop invariant le_lex{Pre,Here}(a,n); */
 do {
  tmp = next_barray(a,n,k);
 } while (tmp != 0 && b_inj(a,n,k) == 0);

 if (tmp == 0) { return 0; }
 return 1;
}

