#include "../../global.h"

/*@ predicate is_non_neg(int *a, integer b) = \forall integer i; 0 <= i < b ==> a[i] >= 0;
  @ predicate is_le_pred(int *a, integer b) = \forall integer i; 1 <= i < b ==> a[i] <= a[i-1]+1;
  @ predicate is_rgf(int *a, integer n) = a[0] == 0 && is_non_neg(a,n) && is_le_pred(a,n);
  @ predicate is_rev(int *a, integer n, integer j) = a[j] <= a[j-1];
  @ predicate is_rightmost_rev(int *a, integer n, integer rev) =
  @  \forall integer j; rev < j < n ==> ! is_rev(a,n,j);
  @ predicate is_zero(int *a, integer b) = \forall integer i; 0 <= i < b ==> a[i] == 0; */

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures is_rgf(a,n); */
int first_rgf(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_rgf(a,n);
  @ assigns a[1..n-1];
  @ ensures is_rgf(a,n);
  @ ensures \result == 0 ==> is_eq{Pre,Post}(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_rgf(int a[], int n);
