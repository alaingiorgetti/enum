#include "../injEndo/injEndo.h"

/*@ predicate is_inv{L}(int *a, integer n) =
  @  \forall integer i; 0 <= i < n ==> a[a[i]] == i;
  @ predicate is_invol{L}(int *a, integer n) =
  @  is_injEndo(a,n) && is_inv(a,n); */

// Function declarations

 /*@ requires n > 0 && \valid(a+(0..n-1));
   @ requires is_injEndo(a,n);
   @ assigns \nothing;
   @ ensures \result == 0 || \result == 1;
   @ ensures \result == 1 <==> is_invol(a,n); */
int b_invol(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_invol(a,n); */
int first_invol(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_invol(a,n);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_invol(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_invol(int a[], int n);

