#include "../barray/barray.h"

/*@ predicate is_endobarray(int *a, integer n) = is_barray(a,n,n); */

// Function declarations

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 1;
  @ ensures is_endobarray(a,n); */
int first_endobarray(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_endobarray(a,n);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures is_endobarray(a,n); 
  @ ensures \result == 0 ==> is_eq{Pre,Post}(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_endobarray(int a[], int n);
