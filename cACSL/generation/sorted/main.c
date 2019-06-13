/* Validation of the generator in sorted.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "../../fcts/fcts.h"
#include "sorted.h"

#define MAX 24

int main(int argc,char *argv[]) {
 int n,k;
 int a[MAX];
 long c;
 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 3) {
  printf("Invalid number of arguments.\n");
  printf("Usage: sorted [n k]\n");
  printf("Generation of all arrays of length n, with values in [0..k-1], sorted in increasing order.\n");
  return(-1);
 }

 n = atoi(argv[argc-2]);
 if (n < 1) {
  printf("Invalid first argument: The minimal size should be 1 or more.\n");
  return(-1);
 }
 if (n > MAX) {
  printf("Invalid first argument: The maximal size should be structurally %d or less.\n",MAX);
  return(-1);
 }

 k = atoi(argv[argc-1]);
 if (k > MAX) {
  printf("Invalid second argument: Should be structurally %d or less.\n",MAX);
  return(-1);
 }
 if (k < 0) {
  printf("Invalid second argument: Should be positive.\n");
  return(-1);
 }

 printf("arrays of length %d, with values in [0..%d], sorted in increasing order:\n",n,k-1);

 first_sorted(a,n,k);
 displayl(a,n);
 printf("\n");

 c = 1;
 lasttime = clock();

 while(next_sorted(a,n,k) != 0) {
  displayl(a,n);
  printf("\n");
  c++;
 }

 printf("Number of sorted arrays generated: %ld\n", c);
 // oeis sequence A046899
 if (binomial(n+k-1,n) == c) {
  printf("Equal to the expected number of the oeis sequence A046899.\n");
 } else {
  printf("Not equal to %ld.\n",binomial(n+k,n));
 }
 now = clock();
 diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
 printf("Time (ms): %ld\n", (long) diff);
 printf("\n");

 return 0;
}
