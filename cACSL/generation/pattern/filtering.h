#include "../../global.h"

/*@ axiomatic preds {
  @  predicate is_x(int *a, integer n)
  @   reads a[0..n-1];
  @  predicate is_y(int *a, integer n)
  @   reads a[0..n-1];
  @  predicate is_z(int *a, integer n) =
  @   is_x(a,n) && is_y(a,n);
  @ } */

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_y(a,n); */
int b_y(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_x(a,n); */
int first_x(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_x(a,n);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_x(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_x(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_z(a,n); */
int first_z(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_z(a,n);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_z(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_z(int a[], int n);
