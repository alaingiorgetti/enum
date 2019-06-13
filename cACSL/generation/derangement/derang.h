#include "../injEndo/injEndo.h"

/*@ predicate is_ff{L}(int *a, integer n) =
  @  \forall integer i; 0 <= i < n ==> a[i] != i;
  @ predicate is_derang{L}(int *a, integer n) = is_injEndo(a,n) && is_ff(a,n); */

// Function declarations

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_injEndo(a,n);
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_derang(a,n); */
int b_derang(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_derang(a,n); */
int first_derang(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_derang(a,n);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_derang(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_derang(int a[], int n);
