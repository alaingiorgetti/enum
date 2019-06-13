#include "../barray/barray.h"

/*@ predicate is_X3{L}(int *a, integer n, integer k, integer n1, integer n2) = a[n2] == n1;
  @ predicate is_eq_im_gen{L}(int *a, integer n, integer k, integer n1, integer n2) =
  @  \exists integer i2; 0 <= i2 < n2 && is_X3(a,n,k,n1,i2);
  @ predicate is_eq_im{L}(int *a, integer n, integer k, integer n1) = is_eq_im_gen(a,n,k,n1,n);
  @ predicate is_im_gen{L}(int *a, integer n, integer k, integer n1) =
  @  \forall integer i1; 0 <= i1 < n1 ==> is_eq_im(a,n,k,i1);
  @ predicate is_im{L}(int *a, integer n, integer k) = is_im_gen(a,n,k,k);
  @ predicate is_surj{L}(int *a, integer n, integer k) = is_barray(a,n,k) && is_im(a,n,k); */

// Function declarations

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_X3(a,n,k,n1,n2);*/
int b_x3(int a[], int n, int k, int n1, int n2);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_eq_im(a,n,k,n1);*/
int b_eq_im(int a[], int n, int k, int n1);

/*@ requires n >= k > 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_im(a,n,k);*/
int b_im(int a[], int n, int k);

/*@ requires n >= k > 0 && \valid(a+(0..n-1));
  @ requires is_barray(a,n,k);
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_surj(a,n,k); */
int b_surj(int a[], int n, int k);

/*@ requires n >= k > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_surj(a,n,k); */
int first_surj(int a[], int n, int k);

/*@ requires n >= k > 0 && \valid(a+(0..n-1));
  @ requires is_surj(a,n,k);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_surj(a,n,k);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_surj(int a[], int n, int k);

