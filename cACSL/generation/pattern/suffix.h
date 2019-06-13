#include "../../global.h"

/*@ axiomatic preds {
  @  predicate is_z(int *a, integer n) reads a[0..n-1];
  @  predicate is_rev(int *a, integer n, integer i) reads a[0..n-1];
  @ } */

/*@ predicate is_rightmost_rev(int *a, integer n, integer rev) =
  @  \forall integer j; rev < j < n ==> ! is_rev(a,n,j); */

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires 0 <= rev <= n-1;
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result <==> is_rev(a,n,rev); */
int b_rev(int a[], int n, int rev);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires 0 <= rev <= n-1;
  @ assigns a[rev..n-1];
  @ ensures a[rev] > \at(a[rev],Pre); */
void suffix(int a[], int n, int rev);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_z(a,n);
  @ assigns a[0..n-1];
  @ ensures soundness: is_z(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_z(int a[], int n);

