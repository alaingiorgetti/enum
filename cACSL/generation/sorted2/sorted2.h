#include "../barray/barray.h"

/*@ predicate is_leq{L}(int *a, integer n, integer v1, integer v2) = a[v1] <= a[v2];
  @ predicate is_leq1_gen(int *a, integer n, integer v1, integer v2) =
  @  \forall integer i2; v1 <= i2 < v2 ==> is_leq(a,n,v1,i2);
  @ predicate is_leq1(int *a, integer n, integer v1) = is_leq1_gen(a,n,v1,n);
  @ predicate is_leq2_gen(int *a, integer n, integer v1) =
  @  \forall integer i1; 0 <= i1 < v1 ==> is_leq1(a,n,i1);
  @ predicate is_leq2(int *a, integer n) = is_leq2_gen(a,n,n);
  @ predicate is_sorted2{L}(int *a, integer n, integer k) = is_barray(a,n,k) && is_leq2(a,n); */

// Function declarations

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_leq(a,n,v1,v2); */
int b_leq(int a[], int n, int v1, int v2);

/*@ requires n > 0 && n > v1 >= 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_leq1(a,n,v1); */
int b_leq1(int a[], int n, int v1);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_leq2(a,n); */
int b_leq2(int a[], int n);

/*@ requires n > 0 && k > 0 && \valid(a+(0..n-1));
  @ requires is_barray(a,n,k);
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_sorted2(a,n,k); */
int b_sorted2(int a[], int n, int k);

/*@ requires n > 0 && k > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_sorted2(a,n,k); */
int first_sorted2(int a[], int n, int k);

/*@ requires n > 0 && k > 0 && \valid(a+(0..n-1));
  @ requires is_sorted2(a,n,k);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_sorted2(a,n,k);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_sorted2(int a[], int n, int k);

