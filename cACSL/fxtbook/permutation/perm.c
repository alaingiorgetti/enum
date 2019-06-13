/** fxtbook page 243. */

#include "perm.h"

int first_perm(int a[], int n) {
 int i;

 /*@ loop invariant 0 <= i <= n;
   @ loop invariant is_id(a,i);
   @ loop assigns i, a[0..n-1];
   @ loop variant n-i; */
 for (i = 0; i < n; i++) {
  a[i] = i;
 }
 return 1;
}

int next_perm(int a[], int n) {
 int rev,j,tmp,s,r;

 // 1. find the rightmost index rev s.t. a[rev] < a[rev+1]:
 /*@ loop invariant -1 <= rev <= n-2;
   @ loop invariant is_rightmost_rev(a,n,rev);
   @ loop assigns rev;
   @ loop variant rev; */
 for (rev = n-2; rev >= 0; rev--)
  if (a[rev] < a[rev+1]) break;
 if (rev < 0) { return 0; } // last sequence is falling seq.

 // 2. Find rightmost (i.e. smallest) element a[j] more (not less) than a[rev]:
 j = n-1;
 /*@ loop invariant rev+1 <= j <= n-1;
   @ loop assigns j; */
 while (j > rev+1 && a[rev] >= a[j]) { j--; }

 // 3. swap(p[i], p[j]):
 tmp = a[rev];
 a[rev] = a[j];
 a[j] = tmp;

 // 4. Reverse order to the right:
 s = rev+1;
 r = n-1;

 /*@ loop invariant rev+1 <= r <= n-1;
   @ loop invariant rev+1 <= s <= n-1;
   @ loop invariant is_perm(a,n);
   @ loop assigns tmp,r,s,a[rev+1..n-1];
   @ loop variant r-s; */
 while (r >= 0 && n-1 >= s && r > s) {
  tmp = a[r];
  a[r] = a[s];
  a[s] = tmp;
  r--;
  s++;
 }

 return 1;
}

