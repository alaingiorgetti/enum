#include "../barray/barray.h"

/*@ predicate is_zero{L}(int *a, integer n) =
  @  \forall integer i; 0 <= i < n ==> a[i] == 0;
  @ predicate is_eq_aj{L}(int *a, integer b, integer c, integer v) =
  @  \forall integer i; 0 < b <= i < c ==> a[i] == v;
  @ predicate is_le{L}(int *a, integer b, integer c) = 
  @  \forall integer i; b <= i < c ==> a[i-1] <= a[i]; 
  @ predicate is_sorted{L}(int *a, integer n, integer k) = 
  @  is_barray(a,n,k) && is_le(a,1,n); */

/*@ requires n > 0 && k > 0;
  @ requires \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures is_sorted(a,n,k); */
int first_sorted(int a[], int n, int k);

/*@ requires n > 0 && k > 0 && \valid(a+(0..n-1));
  @ requires is_sorted(a,n,k);
  @ assigns a[0..n-1];
  @ ensures is_sorted(a,n,k);
  @ ensures \result == 0 ==> is_eq{Pre,Post}(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_sorted(int a[], int n, int k);
