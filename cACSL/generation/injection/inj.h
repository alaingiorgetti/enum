#include "../barray/barray.h"

/*@ predicate is_diff{L}(int *a, integer n, integer i) =
  @  \forall integer j; 0 <= j < n ==> (a[j] == a[i] ==> j == i);
  @ predicate is_linear_gen{L}(int *a, integer n, integer b) =
  @  \forall integer i; 0 <= i < b ==> is_diff(a,n,i);
  @ predicate is_linear{L}(int *a, integer n) =
  @  \forall integer i; 0 <= i < n ==> is_diff(a,n,i);
  @ predicate is_inj{L}(int *a, integer n, integer k) = 
  @  is_barray(a,n,k) && is_linear(a,n); */

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

/*@ requires n > 0 && k >= n && \valid(a+(0..n-1));
  @ requires is_barray(a,n,k);
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_inj(a,n,k); */
int b_inj(int a[], int n, int k);

/*@ requires n > 0 && k >= n && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_inj(a,n,k); */
int first_inj(int a[], int n, int k);

/*@ requires n > 0 && k >= n && \valid(a+(0..n-1));
  @ requires is_inj(a,n,k);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_inj(a,n,k);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n);  */
int next_inj(int a[], int n, int k);

