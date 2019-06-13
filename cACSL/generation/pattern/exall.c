#include "exall.h"

/* File: exall.c.
 *
 * This file defines a pattern for the ACSL contract and C code of a Boolean
 * function corresponding to a hybrid predicate defining a property of an array
 * of given length. It covers all the cases when the hybrid predicate is of the
 * form
 *  \exists integer i; 0 <= i < n ==> (\forall integer j; 0 <= j < n && ..),
 * for an array a of length n.
 *
 * The predicate is named is_x1(a,n). The corresponding Boolean function is
 * named b_x1. The inner quantified formula
 *  (\forall integer j; 0 <= j < n && ..)
 * is named is_x2(a,n,i). This hybrid predicate is implemented by a Boolean
 * function b_x2. The quantifier-free formula in the predicate is_x2(a,n1,n2)
 * is named is_x3(a,n1,n2,j). It is implemented by the Boolean function b_x3.
 *
 * Assume that the Boolean function b_x3 correctly implements the predicate
 * is_x3. Then the contracts of the other Boolean functions is automatically
 * proved with frama-C, WP and Alt-Ergo.
 *
 * For k = 1,2, the predicate is_xk is generalized by the predicate is_xk_gen
 * with one more parameter. This generalization is useful to specify the loop
 * invariant of the corresponding Boolean functions.
 *
 * Commands for the proof:
 *  frama-c -wp exall.c -wp-fct b_x1
 *  frama-c -wp exall.c -wp-fct b_x2 */


int b_x2(int a[], int n1, int n2) {
 int i;

 /*@ loop invariant 0 <= i <= n1;
   @ loop invariant is_x2_gen(a,n1,n2,i);
   @ loop assigns i;
   @ loop variant n1-i; */
 for (i = 0; i < n1; i++) {
  if (b_x3(a,n1,n2,i) == 0) {
   return 0;
  }
 }
 return 1;
}

int b_x1(int a[], int n1) {
 int i;

 /*@ loop invariant 0 <= i <= n1;
   @ loop invariant ! is_x1_gen(a,n1,i);
   @ loop assigns i;
   @ loop variant n1-i; */
 for (i = 0; i < n1; i++) {
  if (b_x2(a,n1,i) == 1) {
   return 1;
  }
 }
 return 0;
}
