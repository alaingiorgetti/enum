#include "../barray/barray.h"

/*@ predicate is_inc{L}(int *a, integer n) =
  @  \forall integer i; 1 <= i < n ==> a[i] > a[i-1];
  @ predicate is_comb{L}(int *a, integer p, integer n) =
  @  is_barray(a,p,n) && is_inc(a,p);
  @*/

// Function declarations

/*@ requires p > 0 && n >= p && \valid(a+(0..p-1));
  @ requires is_barray(a,p,n);
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_comb(a,p,n); */
int b_comb(int a[], int p, int n);

/*@ @ requires p > 0 && n >= p && \valid(a+(0..p-1));
  @ assigns a[0..p-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_comb(a,p,n); */
int first_comb(int a[], int p, int n);

/*@ requires p > 0 && n >= p && \valid(a+(0..p-1));
  @ requires is_comb(a,p,n);
  @ assigns a[0..p-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_comb(a,p,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_comb(int a[], int p, int n);
