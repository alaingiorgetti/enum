/* Generation of all permutations of a set of n elements in lexicographic order. */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include "perm.h"
#include "../../fcts/fcts.h"

#define MAX 16

/* Display and validation options */
#define PRINT 0

/* Global variables. */
int option[1] = {0}; // Array for options. The default value is no option.

/* Treatment of display and test options.
 * p is the permutation.
 * n is its size. */
int options(int p[], int n) {
 if (option[PRINT]) {
  displayl(p,n); printf("\n");
 }
 return(1);
}

int main(int argc,char *argv[]) {
 int n;
 int p[MAX];
 long c = 0;         // number of generated arrays
 int first_next_out; // output of first* and next* functions.
 int k;

 // Variables for time computation:
 clock_t lasttime, now, diff;
 
 if (argc < 2) {
  printf("Invalid number of arguments.\n");
  printf("Usage: perm [options] [n]\n");
  printf("Generation of all permutations of a set of n elements.\n");
  printf("Options are:\n");
  printf("  -print  \t prints each generated array.\n");
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

 printf("Permutations of a set of %d elements:\n",n);
 printf("\n");

 // If there are options
 for (k = 1; k < argc-1; k++) {
  if (strcmp(argv[k], "-print") == 0) {
   option[PRINT] = 1;
  }
 }

 lasttime = clock();

 first_next_out = first_perm(p,n);
 if (first_next_out == 1) {
  if (options(p,n) == 1) c++;
 }

 while((first_next_out = next_perm(p,n)) == 1) {
  if (options(p,n) == 1) c++;
 }

 printf("Number of permutations of a set of %d elements generated: %ld.", n, c);
 if (fact(n) == c) {
  printf(" Equal to %d!.",n);
 } else {
  printf(" Not equal to %d!.",n);
 }
 now = clock();
 diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
 printf(" Time (ms): %ld\n", (long) diff);
 printf("\n");

 return 0;
}
