/* Validation of the generator in surjEndo.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "../../fcts/fcts.h"
#include "surjEndo.h"
#include "../barray/barray.h"
#include "../endobarray/endobarray.h"

#define MAX 16

int main(int argc,char *argv[]) {
 int n;
 int f[MAX];
 long c;

 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 2) {
  printf("Invalid number of arguments.\n");
  printf("Usage: surjEndo [n]\n");
  printf("Generation of permutations on [0..n-1].\n");
  return(-1);
 }

 n = atoi(argv[argc-1]);
 if (n < 1) {
  printf("Invalid argument: The minimal size should be 1 or more.\n");
  return(-1);
 }
 if (n > MAX) {
  printf("Invalid argument: The minimal size should be structurally %d or less.\n",MAX);
  return(-1);
 }

 printf("permutations on [0..%d]:\n",n-1);
 printf("\n");  

 first_surjEndo(f,n);
 displayl(f,n);
 printf("\n");

 c = 1;
 lasttime = clock();

 while(next_surjEndo(f,n) == 1) {
  displayl(f,n);
  printf("\n");
  c++;
 }
 printf("Number of permutations of [0..%d] generated: %ld\n", n-1, c);
 if (fact(n) == c) {
  printf("Equal to %d!.\n",n);
 } else {
  printf("Not equal to %d!.\n",n); 
 }
 now = clock();
 diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
 printf("Time (ms): %ld\n", (long) diff);
 printf("\n");

 return 0;
}

