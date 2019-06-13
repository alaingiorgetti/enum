#include "../../global.h"

/*@ predicate is_id(int *a, integer k) =
  @  \forall integer i; 0 <= i < k ==> a[i] == i;
  @ predicate is_le(int *a, integer b, integer p, integer n) =
  @  \forall integer i; b <= i < p ==> 0 <= a[i] <= n-1-(p-1-i);
  @ predicate is_lt3(int *a, integer b, integer n) =
  @  \forall integer i; 0 <= i < b ==> 0 <= a[i] < n;
  @ predicate is_lt_next(int *a, integer b, integer c) =
  @  \forall integer i; b <= i < c ==> a[i] < a[i+1];
  @ predicate is_comb(int *a, integer p, integer n) =
  @  is_lt3(a,p,n) && is_lt_next(a,0,p-1); 
  @ predicate is_rev(int *a, integer p, integer j) = 
  @  j != p-1 && a[j+1] - a[j] > 1;
  @ predicate is_rightmost_rev(int *a, integer p, integer rev) =
  @  \forall integer j; rev < j < p ==> ! is_rev(a,p,j); */

/*@ requires n >= p > 0;
  @ requires \valid(a+(0..p-1));
  @ assigns a[0..p-1];
  @ ensures is_comb(a,p,n); */
int first_comb(int a[], int p, int n);

/*@ requires n >= p > 0;
  @ requires \valid(a+(0..p-1));
  @ requires is_comb(a,p,n);
  @ assigns a[0..p-1];
  @ ensures is_comb(a,p,n);
  @ ensures \result == 0 ==> is_eq{Pre,Post}(a,p);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,p); */
int next_comb(int a[], int p, int n);
