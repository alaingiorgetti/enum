#include "../../global.h"

/*@ predicate is_fact(int *a, integer n) =
  @  \forall integer i; 0 <= i < n ==> 0 <= a[i] <= i;
  @ predicate is_rev(int *a, integer n, integer j) = a[j] != j;
  @ predicate is_rightmost_rev(int *a, integer n, integer rev) =
  @  \forall integer j; rev < j < n ==> ! is_rev(a,n,j); */

/*@ predicate min_lex(int *a, integer n) =
  @  \forall int *b; \valid(b+(0..n-1)) && is_fact(b,n) ==> le_lex2(a,b,n);

  @ predicate max_lex(int *a, integer n) =
  @  \forall int *b; \valid(b+(0..n-1)) && is_fact(b,n) ==> le_lex2(b,a,n); */

/*@ requires n > 0;
  @ requires \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 1;
  @ ensures is_fact(a,n); */
int first(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_fact(a,n);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures is_fact(a,n);
  @ ensures \result == 0 ==> is_eq{Pre,Post}(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next(int a[], int n);
