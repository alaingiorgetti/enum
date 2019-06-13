#include "../permutation/perm.h"

/*@ predicate is_inv(int *a, integer b) = 
  @  \forall integer i; 0 <= i < b ==> a[a[i]] == i;
  @ predicate is_invol(int *a, integer n) = is_perm(a,n) && is_inv(a,n); */
 
// Function declarations

/*@ requires n >= 0;
  @ requires \valid(inv+(0..n-1));
  @ assigns inv[0..n-1]; 
  @ ensures is_invol(inv,n); */ 
int first_invol(int inv[], int n);

/*@ requires n > 0 && \valid(inv+(0..n-1));
  @ requires is_invol(inv,n);
  @ assigns inv[0..n-1]; 
  @ ensures is_invol(inv,n); */ 
int next_invol(int inv[], int n);
