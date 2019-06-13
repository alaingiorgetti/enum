/* Validation of the generator in cperm.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include"cperm.h"
#include"../../fxtbook/permutation/perm.h"
#include"../../fcts/fcts.h"
#define MAX 16

int main(int argc,char *argv[]) {
 int n;
 long d;
 int f[MAX];

 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 2) {
  printf("Invalid number of arguments.\n");
  printf("Usage: cperm n\n");
  printf("Generation of all connected permutations on {0,...,n-1}.\n");
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

 printf("Connected permutations on {0,...,%d}:\n",n-1);
 printf("\n");

 first_cperm(f,n);
 displayl(f,n);
 printf("\n");

 d = 1;
 lasttime = clock();
 
 while(next_cperm(f,n) == 1) {
  displayl(f,n);
  printf("\n");
  d++;
 }

 printf("Number of connected permutations generated: %ld\n",d);
 if (count3319(n) == d) {
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
