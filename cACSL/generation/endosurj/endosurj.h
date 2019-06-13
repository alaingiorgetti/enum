#include "../surjection/surj.h"

/*@ predicate is_endosurj{L}(int *a, integer n) = is_surj(a,n,n); */

// Function declarations

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_endosurj(a,n); */
int first_endosurj(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_endosurj(a,n);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_endosurj(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_endosurj(int a[], int n);
