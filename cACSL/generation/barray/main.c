/* Validation of the generator in barray.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "barray.h"
#include "../../fcts/fcts.h"
#define MAX 20

int main(int argc,char *argv[]) {
 int n,k;
 long d;
 int f[MAX]; // array of the function f

 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 3) {
  printf("Invalid number of arguments.\n");
  printf("Usage: ./barray [n k]\n");
  printf("Generation of functions from [0..n-1] to [0..k].\n");
  return(-1);
 }

 n = atoi(argv[argc-2]);
 if (n < 1) {
  printf("Invalid first argument: The minimal number should be 1 or more.\n");
  return(-1);
 }
 if (n > MAX) {
  printf("Invalid first argument: The maximal number should be structurally %d or less.\n",MAX);
  return(-1);
 }

 k = atoi(argv[argc-1]);
 if (k < 1) {
  printf("Invalid second argument: Should be structurally at less 1.\n");
  return(-1);
 }
 printf("functions from [0..%d] to [0..%d] :\n",n-1,k-1);
 printf("\n");

 first_barray(f,n,k);
 displayl(f,n);
 printf("\n");

 d = 1;
 lasttime = clock();

 while(next_barray(f,n,k) == 1) {
  displayl(f,n);
  printf("\n");
  d++;
 }
 printf("Number of functions from [0..%d] to [0..%d] generated: %ld\n",n-1,k-1,d);
 if (power(k,n) == d) {
  printf("Equal to %d^%d.\n",k,n);
 } else {
  printf("Not equal to %d^%d.\n",k,n);
 }
 now = clock();
 diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
 printf("Time (ms): %ld\n", (long) diff);
 printf("\n");

 return 0;
}
