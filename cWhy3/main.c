/* cWhy3/main.c */
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <time.h>
#include "ptr.h"
#include "fcts/fcts.h"

int main(int argc,char *argv[]) {
  struct cursor c;
  int32_t n;
  long d=0;

  # ifdef TIMING
  // Variables for time computation:
  clock_t lasttime, now, diff;
  // Variable for writing in the file:  
  FILE* fichier = NULL;
  if (argc != 3) {
    printf("Invalid number of arguments.\n");
    return (-1);
  }
  # else
  if (argc != 2) {
    printf("Invalid number of arguments.\n");
    return(-1);
  }
  # endif
  n = atoi(argv[1]);
  if (n < 1) {
    printf("Invalid first argument: The minimal number should be 1 or more.\n");
    return(-1);
  }
  printf("Start for length %d\n", n);
    # ifdef TIMING 
  lasttime = clock();
  #endif
  c = create_cursor(n);
  while (c.new) {
    # ifndef TIMING 
    displayl(c.current,n);
    printf("\n");
    # endif
    next(&c);
    d++;
  }
  free(c.current);
  # ifdef TIMING
  now = clock();
  diff = (now - lasttime) / (CLOCKS_PER_SEC / 1000);
  # endif
  printf("Number of arrays generated: %ld\n",d);
  # ifdef TIMING
  // Open the file for writing
  fichier = fopen(argv[2],"a w");

  // Write the execution time
  if (fichier != NULL) {
    fprintf(fichier,"%d",n);
    fprintf(fichier,",");
    fprintf(fichier,"%.3f",(float) diff / 1000);
    fprintf(fichier,"\n");
    fclose(fichier);
  } else {
    printf("Unable to open file");
  }
  # endif
  return 0;
}