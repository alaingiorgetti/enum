/* Validation of the generator in derang.c by counting. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include"derang.h"
#include"../injEndo/injEndo.h" 
#include"../endobarray/endobarray.h"
#include"../barray/barray.h"
#include"../../fcts/fcts.h"

#define MAX 16

int main(int argc,char *argv[]) {
 int n;
 long c;
 int a[MAX]; // array storing one derangement

 // Variables for time computation:
 clock_t lasttime, now, diff;

 if (argc != 2) {
  printf("Invalid number of arguments.\n");
  printf("Usage: derang [n]\n");
  printf("Generation of derangements of size n.\n");
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

 printf("derangements of length %d :\n",n);

 first_derang(a,n);
 displayl(a,n);
 printf("\n");

 c = 1;
 lasttime = clock(); 

 while(next_derang(a,n) == 1) {
  displayl(a,n);
  printf("\n");
  c++;
 }
 printf("Number of derangements of size %d generated: %ld\n", n, c);  
 if (c == count166(n)) {
  printf("Equal to the %d-th number of the sequence https://oeis.org/A000166.\n",n);
 } else {
  printf("Not equal to the %d-th number of the sequence https://oeis.org/A000166).\n",n);
 }

 now = clock();
 diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
 printf("Time (ms): %ld\n", (long) diff);
 printf("\n");

 return 0;
}
