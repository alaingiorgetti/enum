#include "../../global.h"

/*@ predicate is_barray(int *a, integer b, integer c) =
  @  \forall integer i; 0 <= i < b ==> 0 <= a[i] < c; 
  @ predicate is_rev(int *a, integer n, integer k, integer j) = a[j] < k-1;
  @ predicate is_rightmost_rev(int *a, integer n, integer k, integer rev) =
  @  \forall integer j; rev < j < n ==> ! is_rev(a,n,k,j); */
     
/*@ predicate cte_sub (int *a, integer n) = 
    \forall integer i; 0 <= i < n ==> a[i] == 0; */

/*@ requires n > 0 && k > 0;
  @ requires \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 1;
  @ ensures is_barray(a,n,k); 
  @ ensures cte_sub(a,n);*/
int first_barray(int a[], int n, int k);

/*@ requires n > 0 && k > 0 && \valid(a+(0..n-1));
  @ requires is_barray(a,n,k);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures is_barray(a,n,k);
  @ ensures \result == 0 ==> is_eq{Pre,Post}(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_barray(int a[], int n, int k);