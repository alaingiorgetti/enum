#include "../invol/invol.h"

/*@ predicate is_ff{L}(int *a, integer n) =
  @  \forall integer i; 0 <= i < n ==> a[i] != i;
  @ predicate is_ffi{L}(int *a, integer n) = 
  @  is_ff(a,n) && is_invol(a,n); */

// Function declarations

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_invol(a,n);
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_ffi(a,n); */
int b_ffi(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_ffi(a,n); */
int first_ffi(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_ffi(a,n);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_ffi(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_ffi(int a[], int n);
