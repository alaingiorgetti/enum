#include "../../generation/barray/barray.h"

/*@ predicate is_id{L}(int *a, integer n) =
  @  \forall integer i; 0 <= i && i < n ==> a[i] == i;
  @ predicate is_linear{L}(int *a, integer n) =
  @  \forall integer i; 0 <= i && i < n ==> 
  @   (\forall integer j; 0 <= j && j < n ==> (a[i] == a[j] ==> i == j));
  @ predicate is_perm{L}(int *a, integer n) = is_linear(a,n) && is_barray(a,n,n);
  @ predicate is_rev(int *a, integer n, integer j) = j != n-1 && a[j] < a[j+1];
  @ predicate is_rightmost_rev(int *a, integer n, integer rev) =
  @  \forall integer j; rev < j < n ==> ! is_rev(a,n,j); */

/*@ requires n >= 0;
  @ requires \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures is_perm(a,n); */
int first_perm(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_perm(a,n);
  @ assigns a[0..n-1];
  @ ensures is_perm(a,n);
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 0 ==> is_eq{Pre,Post}(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_perm(int a[], int n);
