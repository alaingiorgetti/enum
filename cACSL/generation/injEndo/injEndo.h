#include "../endobarray/endobarray.h"

/*@ predicate is_diff(int *a, integer n, integer i) =
  @  \forall integer j; 0 <= j < n ==> (a[j] == a[i] ==> j == i);
  @ predicate is_linear_gen(int *a, integer n, integer b) =
  @  \forall integer i; 0 <= i < b ==> is_diff(a,n,i);
  @ predicate is_linear(int *a, integer n) =
  @  \forall integer i; 0 <= i < n ==> is_diff(a,n,i);
  @ predicate is_injEndo(int *a, integer n) = 
  @  is_linear(a,n) && is_endobarray(a,n); */

// Function declarations

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires 0 <= i < n;
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_diff(a,n,i); */
int b_diff(int a[], int n, int i);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_linear(a,n); */
int b_linear(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_endobarray(a,n);
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_injEndo(a,n); */
int b_injEndo(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_injEndo(a,n); */
int first_injEndo(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_injEndo(a,n);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_injEndo(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_injEndo(int a[], int n);
