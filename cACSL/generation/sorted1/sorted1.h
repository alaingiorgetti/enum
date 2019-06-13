#include "../barray/barray.h"

/*@ predicate is_le{L}(int *a, integer n) = 
  @  (\forall integer i; 1 <= i < n ==> a[i-1] <= a[i]);
  @ predicate is_sorted1{L}(int *a, integer n, integer k) = 
  @  is_barray(a,n,k) && is_le(a,n); */

// Function declarations

/*@ requires n > 0 && k > 0 && \valid(a+(0..n-1));
  @ requires is_barray(a,n,k);
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_sorted1(a,n,k); */
int b_le(int a[], int n, int k);

/*@ requires n > 0 && k > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_sorted1(a,n,k); */
int first_sorted1(int a[], int n, int k);

/*@ requires n > 0 && k > 0 && \valid(a+(0..n-1));
  @ requires is_sorted1(a,n,k);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_sorted1(a,n,k);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_sorted1(int a[], int n, int k);

