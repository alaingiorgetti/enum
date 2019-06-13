/* Generation algorithm for injections on [0..n-1].
 * Here, by specialization of injections from [0..n-1] to [0..k-1]. */

#include "endoinj.h"

int first_endoinj(int a[], int n) {
 return first_inj(a,n,n);
}

int next_endoinj(int a[], int n) {
 return next_inj(a,n,n);
}

