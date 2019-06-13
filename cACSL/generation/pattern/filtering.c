#include "filtering.h"

int first_z(int a[], int n) {
 int tmp;

 tmp = first_x(a, n);
 /*@ loop invariant tmp != 0 ==> is_x(a,n);
   @ loop assigns a[0..n-1], tmp; */
 while (tmp != 0 && b_y(a, n) == 0) {
  tmp = next_x(a, n);
 }
 if (tmp == 0) {
  return 0;
 }
 return 1;
}

int next_z(int a[], int n) {
 int tmp;

 /*@ loop invariant is_x(a,n);
   @ loop assigns a[0..n-1],tmp;
   @ loop invariant le_lex{Pre,Here}(a,n); */
 do {
  tmp = next_x(a, n);
 } while (tmp != 0 && b_y(a, n) == 0);
 if (tmp == 0) {
  return 0;
 }
 return 1;
}
