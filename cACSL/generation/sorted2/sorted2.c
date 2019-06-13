/* Generation of arrays with values in [0..k-1] sorted in increasing order.
   Here, by filtering functions from [0..n-1] to [0..k-1] with pattern all2. */

#include "sorted2.h"

int b_leq(int a[], int n, int v1, int v2) {
 return(a[v1] <= a[v2]);
}

int b_leq1(int a[], int n, int v1) {
 int i;

 /*@ loop invariant 0 <= v1 <= i <= n;
   @ loop invariant is_leq1_gen(a,n,v1,i);
   @ loop assigns i;
   @ loop variant n-i; */
 for (i = v1; i < n; i++)
  if (b_leq(a,n,v1,i) == 0) return 0;
 return 1;
}

int b_leq2(int a[], int n) {
 int i;

 /*@ loop invariant 0 <= i <= n;
   @ loop invariant is_leq2_gen(a,n,i);
   @ loop assigns i;
   @ loop variant n-i; */
 for (i = 0; i < n; i++)
  if (b_leq1(a,n,i) == 0) return 0;
 return 1;
}

/* Returns 1 when the array a is sorted, and 0 otherwise. */
int b_sorted2(int a[], int n, int k) {
 return (b_leq2(a,n));
}


int first_sorted2(int a[], int n, int k) {
 int tmp;

 tmp = first_barray(a,n,k);
 /*@ loop invariant tmp != 0 ==> is_barray(a,n,k);
   @ loop assigns a[0..n-1],tmp; */
 while (tmp != 0 && b_sorted2(a,n,k) == 0) {
  tmp = next_barray(a,n,k);
 }
 if (tmp == 0) { return 0; }
 return 1;
}

int next_sorted2(int a[], int n, int k) {
 int tmp;

 /*@ loop invariant is_barray(a,n,k);
   @ loop assigns a[0..n-1],tmp;
   @ loop invariant le_lex{Pre,Here}(a,n); */
 do {
  tmp = next_barray(a,n,k);
 } while (tmp != 0 && b_sorted2(a,n,k) == 0);
 if (tmp == 0) { return 0; }
 return 1;
}

