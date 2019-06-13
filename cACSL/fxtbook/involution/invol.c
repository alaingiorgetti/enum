/* Generation of all involutions of n elements, in increasing order.
 * The algorithm comes from Section 11.3 of the fxtbook (pages 284-285). */
 
#include "invol.h"
 
int first_invol(int inv[], int n) {
 int k;
 /*@ loop invariant 0 <= k <= n;
   @ loop invariant is_id(inv,k);
   @ loop assigns k, inv[0..n-1];
   @ loop variant n-k; */
 for (k = 0; k < n; k++) inv[k] = k; 
 return 1;
}

int next_invol(int inv[], int n) {
 int j,k,ip;

 /*@ loop invariant 0 <= j <= n-1;
   @ loop invariant is_invol(inv,n);
   @ loop assigns j,k,ip,inv[0..n-1];
   @ loop variant j; */
 for (j = n-1; j > 0; j--) {
  ip = inv[j];
  inv[j] = j;
  inv[ip] = ip;
  
  /*@ loop invariant -1 <= k <= ip-1;
    @ loop assigns k;
    @ loop variant k+1; */
  for (k = ip-1; k >= 0; k--) if (inv[k] == k) break;
  if (k != -1) {
   inv[j] = k;
   inv[k] = j;
   return 1;
  }
 }
 return 0;
}

/* Code modified :
for (k = ip-1; k >= 0; k--) if (inv[k] == k) break;
  if (k != -1) {
instead of
for (k = ip-1; k >= 0; k--) {
  if (inv[k] == k) {
*/
