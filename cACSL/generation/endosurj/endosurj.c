/* Generation algorithm for endosurjections on [0..n-1].
 * Here, by filtering surjections from [0..n-1] to [0..k-1]. */

#include "endosurj.h"

int first_endosurj(int a[], int n) {
 return first_surj(a,n,n);
}

int next_endosurj(int a[], int n) {
 return next_surj(a,n,n);
}

