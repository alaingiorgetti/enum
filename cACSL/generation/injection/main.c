/* Validation of the generator in inj.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "../../fcts/fcts.h"
#include "../barray/barray.h"
#include "inj.h"

#define MAX 16

int main(int argc,char *argv[]) {
 int n,k;
 int a[MAX]; // array of injection
 long c;
 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 3) {
  printf("Invalid number of arguments.\n");
  printf("Usage: inj [n k]\n");
  printf("Generation of all injections from [0..n-1] to [0..k-1].\n");
  return(-1);
 }

 n = atoi(argv[argc-2]);
 if (n < 1) {
  printf("Invalid first argument: The minimal size should be 1 or more.\n");
  return(-1);
 }
 if (n > MAX) {
  printf("Invalid first argument: The minimal size should be structurally %d or less.\n",MAX);
  return(-1);
 }

 k = atoi(argv[argc-1]);
 if (k > MAX) {
  printf("Invalid second argument: Should be structurally %d or less.\n",MAX);
  return(-1);
 }
 if (k < n) {
  printf("Invalid second argument: Should be more than the first argument.\n");
  return(-1);
 }

 printf("Injections from [0..%d] to [0..%d] :\n",n-1,k-1);

 first_inj(a,n,k);
 displayl(a,n);
 printf("\n");

 c = 1; 
 lasttime = clock();

 while(next_inj(a,n,k) != 0) {
  displayl(a,n);
  printf("\n");
  c++;
 }

 printf("Number of injections generated : %ld\n", c);
 if (countInj(n,k) == c) {
  printf("Equal to the expected number.\n");
 } else {
  printf("Not equal to %ld.\n",countInj(n,k));
 }

 now = clock();
 diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
 printf("Time (ms): %ld\n", (long) diff);
 printf("\n");

 return 0;
}
