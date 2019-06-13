#include "../endobarray/endobarray.h"

/*@ predicate is_le_pred(int *a, integer n) =
  @  \forall integer i; 1 <= i < n ==> a[i] <= a[i-1]+1;
  @ predicate is_rgf(int *a, integer n) = is_endobarray(a,n) && a[0] == 0 && is_le_pred(a,n); */

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_endobarray(a,n);
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_rgf(a,n); */
int b_rgf(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_rgf(a,n); */
int first_rgf(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_rgf(a,n);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_rgf(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_rgf(int a[], int n);
