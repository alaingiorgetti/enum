#include "../../fxtbook/permutation/perm.h"

/*@ predicate is_gen(int *a, integer n, integer n1, integer n2) = a[n2] > n1;
  @ predicate ex_greater_gen(int *a, integer n, integer n1, integer n2) =
  @  \exists integer i; 0 <= i < n2 && is_gen(a,n,n1,i);
  @ predicate ex_greater(int *a, integer n, integer n1) = ex_greater_gen(a,n,n1,n1+1);
  @ predicate is_connected_gen(int *a, integer n, integer n1) =
  @  \forall integer i1; 0 <= i1 < n1 ==> ex_greater(a,n,i1);
  @ predicate is_connected(int *a, integer n) = is_connected_gen(a,n,n-1);
  @ predicate is_cperm(int *a, integer n) = is_connected(a,n) && is_perm(a,n); */

// Function declarations

/*@ requires n > n1 >= n2 >= 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_gen(a,n,n1,n2); */
int b_greater(int a[], int n, int n1, int n2);

/*@ requires n > n1 >= 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> ex_greater(a,n,n1);*/
int ex_greater(int a[], int n, int n1);

/*@ requires n > 0 && \valid(a+(0..n-1));
   @ requires is_perm(a,n);
   @ assigns \nothing;
   @ ensures \result == 0 || \result == 1;
   @ ensures \result == 1 <==> is_connected(a,n); */
int b_connected(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_cperm(a,n); */
int first_cperm(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
   @ requires is_cperm(a,n);
   @ assigns a[0..n-1];
   @ ensures \result == 0 || \result == 1;
   @ ensures \result == 1 ==> is_cperm(a,n);
   @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_cperm(int a[], int n);
