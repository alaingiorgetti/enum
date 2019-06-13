#include "../../global.h"

/*@ predicate is_dset(int *a, integer n) =
  @  \forall integer i; 0 <= i < n ==> (a[i] == 0 || a[i] == 1);
  @ predicate is_rev(int *a, integer n, integer j) = a[j] == 0;
  @ predicate is_rightmost_rev(int *a, integer n, integer rev) =
  @  \forall integer j; rev < j < n ==> ! is_rev(a,n,j); */

// Function declarations

/*@ requires n >= 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures is_dset(a,n); */
int first_subset(int a[], int n);

/*@ requires n >= 0 && \valid(a+(0..n-1));
  @ requires is_dset(a,n);
  @ assigns a[0..n-1];
  @ ensures is_dset(a,n);
  @ ensures \result == 0 ==> is_eq{Pre,Post}(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_subset(int a[], int n);
