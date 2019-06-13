/* Validation of the generator in rgf.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "rgf.h"
#include "../../fcts/fcts.h"
#define MAX 20

int main(int argc,char *argv[]) {
 int n;
 int rgf[MAX];
 long c;

 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 2) {
  printf("Invalid number of arguments.\n");
  printf("Usage: rgf [n]\n");
  printf("Generation of RGFs of size n.\n");
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

 printf("RGF of length %d :\n",n);
 printf("\n");  

 first_rgf(rgf,n);
 displayl(rgf,n);
 printf("\n"); 
 c = 1;

 lasttime = clock();

 while(next_rgf(rgf,n) == 1) {
  displayl(rgf,n);
  printf("\n");
  c++;
 }

 printf("Number of RGF of size %d generated: %ld\n", n, c);
 if (count108(n) == c) {
  printf("Equal to the corresponding Catalan number.\n");
 } else {
  printf("Not equal to the corresponding Catalan number %ld.\n",count108(n)); 
 }
 now = clock();
 diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
 printf("Time (ms): %ld\n", (long) diff);
 printf("\n");

 return 0;
}
