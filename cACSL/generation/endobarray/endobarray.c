/* Generation algorithm for endoarrays, encoding endofunctions on [0..n-1].
   Here, by specialization of bounded arrays, encoding functions from [0..n-1]
   to [0..k-1]. */

#include "endobarray.h"

int first_endobarray(int a[], int n) {
 return first_barray(a,n,n);
}

int next_endobarray(int a[], int n) {
 return next_barray(a,n,n);
}
