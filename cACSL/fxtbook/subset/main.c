/* Validation of the generator in subset.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "subset.h"
#include "../../fcts/fcts.h"
#define MAX 30

int main(int argc,char *argv[]) {
 int d,n;
 long c;
 int ds[MAX]; // Array representing one delta set.
 int s[MAX]; // Array representing one subset.
 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 2) {
  printf("Invalid number of arguments.\n");
  printf("Usage: subset [n]\n");
  printf("Generation of all subsets of a set of n elements.\n");
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

 printf("Subsets of a set of %d elements:\n",n);
 printf("\n");

 first_subset(ds,n);
 displayl(ds,n);
 printf("\n");
 d = delta2subset(ds,s,n);
 displayl(s,d);
 printf("\n");

 c = 1;
 lasttime = clock();

 while(next_subset(ds,n) == 1) {
  displayl(ds,n);
  printf("\n");
  d = delta2subset(ds,s,n);
  displayl(s,d);
  printf("\n");
  c++;
 }
 printf("Number of subsets of a set of %d elements generated: %ld\n", n, c);
 if (power(2,n) == c) {
  printf("Equal to 2^%d.\n",n);
 } else {
  printf("Not equal to 2^%d.\n",n); 
 }
 now = clock();
 diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
 printf("Time (ms): %ld\n", (long) diff);
 printf("\n");

 return 0;
}
