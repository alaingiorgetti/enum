#include "../injection/inj.h"

/*@ predicate is_endoinj{L}(int *a, integer n) = is_inj(a,n,n); */

// Function declarations

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_endoinj(a,n); */
int first_endoinj(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_endoinj(a,n);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_endoinj(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_endoinj(int a[], int n);
