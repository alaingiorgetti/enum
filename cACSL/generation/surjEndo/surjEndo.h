#include "../endobarray/endobarray.h"

/*@ predicate is_x3{L}(int *a, integer n, integer n1, integer n2) = a[n2] == n1;
  @ predicate is_eq_im_gen{L}(int *a, integer n, integer n1, integer n2) =
  @  \exists integer i2; 0 <= i2 < n2 && is_x3(a,n,n1,i2);
  @ predicate is_eq_im{L}(int *a, integer n, integer n1) = is_eq_im_gen(a,n,n1,n);
  @ predicate is_im_gen{L}(int *a, integer n, integer n1) =
  @  \forall integer i1; 0 <= i1 < n1 ==> is_eq_im(a,n,i1);
  @ predicate is_im{L}(int *a, integer n) = is_im_gen(a,n,n); 
  @ predicate is_surjEndo{L}(int *a, integer n) = is_endobarray(a,n) && is_im(a,n); */

// Function declarations

/*@ requires n >= 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_x3(a,n,n1,n2);*/
int b_x3(int a[], int n, int n1, int n2);

/*@ requires n >= 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_eq_im(a,n,n1);*/
int b_eq_im(int a[], int n, int n1);

/*@ requires n >= 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_im(a,n);*/
int b_im(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_endobarray(a,n);
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_surjEndo(a,n); */
int b_surjEndo(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_surjEndo(a,n); */
int first_surjEndo(int a[], int n);

/*@ requires n > 0 && \valid(a+(0..n-1));
  @ requires is_surjEndo(a,n);
  @ assigns a[0..n-1];
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> is_surjEndo(a,n);
  @ ensures \result == 1 ==> lt_lex{Pre,Post}(a,n); */
int next_surjEndo(int a[], int n);

