/* Validation of the generator in perm.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "../../fcts/fcts.h"
#include "perm.h"
#include "../endobarray/endobarray.h"
#include "../barray/barray.h"

#define MAX 16

int main(int argc,char *argv[]) {
 int n;
 int p[MAX]; // array of permutation
 long c;

 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 2) {
  printf("Invalid number of arguments.\n");
  printf("Usage: ./perm [n]\n");
  printf("Generation of all permutations on [0..n-1].\n");
  return(-1);
 }

 n = atoi(argv[argc-1]);
 if (n < 1) {
  printf("Invalid first argument: The minimal size should be 1 or more.\n");
  return(-1);
 }
 if (n > MAX) {
  printf("Invalid first argument: The minimal size should be structurally %d or less.\n",MAX);
  return(-1);
 }

 printf("Permutations of [0..%d-1]:\n",n);

 first_perm(p,n);
 displayl(p,n);
 printf("\n");

 c = 1;
 lasttime = clock();

 while(next_perm(p,n) != 0) {
  displayl(p,n);
  printf("\n");
  c++;
 }

 printf("Number of permutations of [0..%d-1] generated: %ld\n", n, c);
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
