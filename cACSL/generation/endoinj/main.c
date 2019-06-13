/* Validation of the generator in endoinj.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "endoinj.h"
#include "../../fcts/fcts.h"
#include"../injection/inj.h" 
#include"../barray/barray.h"

#define MAX 16

int main(int argc,char *argv[]) {
 int n;
 long c;
 int f[MAX];

 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 2) {
  printf("Invalid number of arguments.\n");
  printf("Usage: endoinj [n]\n");
  printf("Generation of injections of size n.\n");
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

 printf("endoinjections of length %d :\n",n);
 printf("\n");  

 first_endoinj(f,n);
  displayl(f,n);
  printf("\n");
  c = 1;

  lasttime = clock();

  while(next_endoinj(f,n) == 1) {
   displayl(f,n);
   printf("\n");
   c++;
  }
  printf("Number of endoinjections of size %d generated: %ld\n", n, c);
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
