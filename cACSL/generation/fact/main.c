/* Validation of the generator in fact.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "fact.h"
#include "../../fcts/fcts.h"

#define MAX 20

int main(int argc,char *argv[]) {
 int n;
 long d;
 int f[MAX];

 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 2) {
  printf("Invalid number of arguments.\n");
  return(-1);
 }

 n = atoi(argv[argc-1]);
 if (n < 1) {
  printf("Invalid argument: The minimal number should be 1 or more.\n");
  return(-1);
 }
 if (n > MAX) {
  printf("Invalid argument: The maximal number should be structurally %d or less.\n",MAX);
  return(-1);
 }

 first(f,n);
 displayl(f,n);
 printf("\n");

 d = 1;
 lasttime = clock();

 while(next(f,n) == 1) {
  displayl(f,n);
  printf("\n");
  d++;
 }
 printf("Number of factorials generated: %ld\n",d);
 now = clock();
 diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
 printf("Time (ms): %ld\n", (long) diff);
 printf("\n");

 return 0;
}
