/*  Validation of the generator in ffi.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include"ffi.h"
#include"../invol/invol.h"
#include"../injEndo/injEndo.h"
#include"../endobarray/endobarray.h"
#include"../barray/barray.h"
#include"../../fcts/fcts.h"

#define MAX 16

int main(int argc,char *argv[]) {
 int n;
 int f[MAX]; // array of f
 long d = 0;
 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 2) {
  printf("Invalid number of arguments.\n");
  printf("Usage: ffi n\n");
  printf("Generation of all fixpoint free involutions on {0,...,n-1}.\n");
  return(-1);
 }

 // argc == 2.
 n = atoi(argv[argc-1]);
 if (n <= 0) {
  printf("Invalid argument: The minimal number is 1.\n");
  return(-1);
 }

 if (n > MAX) {
  printf("Invalid argument: The size should be structurally %d or less.\n",MAX);
  return(-1);
 }

 if (n%2 == 1) {
  printf("Invalid argument: The size should be even.\n");
  return(-1);
 }
 
 printf("fixpoint free involutions on {0,...,%d}:\n",n-1);

 first_ffi(f,n);
 displayl(f,n);
 printf("\n");
 d++;
 lasttime = clock();

 while (next_ffi(f,n) != 0) {
  displayl(f,n);
  printf("\n");
  d++;
 }

 printf("Number of fixpoint free involutions generated: %ld\n",d);

 if (d == count1147(n/2)) {
  printf("Equal to the oeis expected number.\n");
 } else {
  printf("Not equal to the oeis expected number.\n");
 }

 now = clock();
 diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
 printf("Time (ms): %ld\n", (long) diff);
 printf("\n");

 return 0;
}
