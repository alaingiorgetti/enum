/* Generation of all involutions of n elements. Generation in increasing order. */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>  
#include "../../fcts/fcts.h"
#include "invol.h"
#define MAX 20

int main(int argc,char *argv[]) {
 int n;
 int p[MAX]; 
 long c;
 
  // Variables for time computation:
 clock_t lasttime, now, diff;
 
 if (argc != 2) {
  printf("Invalid number of arguments.\n");
  printf("Usage: invol [n]\n");
  printf("Generation of involutions of size n.\n");
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

 printf("Involutions of %d elements:\n",n);

 first_invol(p,n);   
 displayl(p,n);
 printf("\n");
 c = 1;        
 lasttime = clock(); 
  
 while(next_invol(p,n) == 1) {
  displayl(p,n); 
  printf("\n");
  c++;
 }
  printf("Number of involutions on {0,...,%d}: %ld\n", n-1, c);
  if (c == count85(n)) {
   printf("Equal to https://oeis.org/A000085(%d).\n",n);
  } else {
   printf("Not equal to https://oeis.org/A000085() %ld.\n",c);
  }
  now = clock();
  diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
  printf("Time (ms): %ld\n", (long) diff);
  printf("\n");

 return 0;
}
