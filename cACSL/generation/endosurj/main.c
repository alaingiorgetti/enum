/* Validation of the generator in endosurj.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "endosurj.h"
#include "../../fcts/fcts.h"
#include "../surjection/surj.h"
#include "../barray/barray.h"

#define MAX 16

int main(int argc,char *argv[]) {
 int n;
 long c;
 int f[MAX];

 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 2) {
  printf("Invalid number of arguments.\n");
  printf("Usage: endosurj [n]\n");
  printf("Generation of endosurjections of size n.\n");
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

 printf("endosurjections of length %d :\n",n);
 printf("\n");  
 
 first_endosurj(f,n);   
  displayl(f,n);
  printf("\n");

  c = 1;

  lasttime = clock(); 

  while(next_endosurj(f,n) == 1) {
   displayl(f,n);
   printf("\n");
   c++;
  }
  printf("Number of endosurjections of size %d generated: %ld\n", n, c);
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
