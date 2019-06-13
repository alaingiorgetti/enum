/* Validation of the generator in comb.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "comb.h"
#include "../../fcts/fcts.h"
#define MAX 30

int main(int argc, char *argv[]) {
 int c[MAX];
 int p, n;
 long d;
 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 3) {
  printf("Invalid number of arguments.\n");
  printf("Usage: comb [p n]\n");
  printf("Generation of Combinations of p elements out of n.\n");
  return (-1);
 }

 // argc == 3.
 p = atoi(argv[argc-2]);
 if (p < 2) {
  printf("Invalid first argument: The minimal number should be 2 or more.\n");
  return (-1);
 }
 if (p > MAX) {
  printf(
    "Invalid first argument: The minimal number should be structurally %d or less.\n",
    MAX);
  return (-1);
 }

 n = atoi(argv[argc-1]);
 if (n > MAX) {
  printf("Invalid second argument: Should be structurally %d or less.\n",MAX);
  return (-1);
 }
 if (p > n) {
  printf("Invalid second argument: Should be more than the first argument.\n");
  return (-1);
 }

 printf("Combinations of %d elements out of %d :\n",p,n);
 printf("\n");

  first_comb(c,p,n);
  displayl(c,p);
  printf("\n");

  d = 1;

  lasttime = clock();

  while(next_comb(c,p,n) == 1) {
   displayl(c,p);
   printf("\n");
   d++;
  }
  printf("Number of combinations of %d elements out of %d generated: %ld\n", p, n, d);
  if (binomial(n,p) == d) {
   printf("Equal to the corresponding binomial number.\n");
  } else {
   printf("Not equal to the corresponding binomial number %ld.\n",binomial(n,p));
  }
  now = clock();
  diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
  printf("Time (ms): %ld\n", (long) diff);
  printf("\n");

 return 0;
}
