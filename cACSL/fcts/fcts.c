/* Functions for display, counting and conversion. */

#include <stdio.h>

/* copy(a,b,n) copies an array a of length n in an array b. */
void copy(int a[], int b[], int n) {
 int i;
 for (i = 0; i < n; i++)
  b[i] = a[i];
}

/* Returns 1 when arrays a and b are equal, 0 otherwise. */
int is_equal(int a[], int b[], int n) {
 int i;
 for (i = 0; i < n; i++)
  if (b[i] != a[i])
   return 0;
 return 1;
}

/* Display an array of length n. */
void displayl(int a[], int n) {
 int i;
 printf("[ ");
 for (i = 0; i < n; i++)
  printf("%d ",a[i]);
 printf("]");
}

/* Display a word of char of length 2n. */
void displayp(char p[], int n) {
 int i;
 for (i = 0; i < 2 * n; i++)
  printf("%c ",p[i]);
 printf("\n");
}

/** Counting **/

/* Computes n! */
long fact(int n) {
 int i;
 long x = 1;
 for (i = 2; i <= n; i++)
  x = x * i;
 return x;
}

/* Computes x^n */
long power(int x, int n) {
 long y = 1;
 int m = 1;
 while (m <= n) {
  y *= (long) x;
  m++;
 }
 return y;
}

/* count108(n) computes the n-th Catalan number, for n <= MAX.
   See http://oeis.org/A000108 for details. */
long count108(int n) {
 if (n < 0)
  return -1;
 else if (n == 0)
  return 1;
 else
  return 2 * (2 * n - 1) * count108(n - 1) / (n + 1);
}

/* count85(n) computes the n-th number of the
   sequence https://oeis.org/A000085. */
long count85(int n) {
 if (n < 0)
  return -1;
 else if (n <= 1)
  return 1;
 else if (n == 2)
  return 2;
 else
  return count85(n - 1) + (n - 1) * count85(n - 2);
}

/* count166(n) computes the number of derangements of n elements (number of
   permutations of n elements with no fixed points), n-th number of the
   sequence https://oeis.org/A000166. */
long count166(int n) {
 if (n < 0)
  return (long) -1;
 else if (n == 0)
  return 1;
 else
  return n * count166(n - 1) + power(-1,n);
}

/* Returns the number of rooted planar maps with n edges.
   Sequence https://oeis.org/A000168. */
long count168(int n) {
 if (n == 0)
  return 1;
 else
  return (count168(n - 1) * 6 * (long) (2 * n - 1) / (n + 2));
}

/* binomial(n,k) computes the number of ways to choose k elements from 
   a set of n elements, equals the binomial coefficient ‘n choose k'. */
long binomial(int n, int k) {
 int i;
 long f, b;
 if (k > n)
  return 0;
 if ((k == 0) || (k == n))
  return 1;
 if (2 * k > n)
  k = n - k;
 b = (long) n - k + 1;
 f = b;
 for (i = 2; i <= k; ++i) {
  f++;
  b *= f;
  b /= i;
 }
 return b;
}

/* Returns the number of injections from [0..n-1] to [0..k]. */
long countInj(int n, int k) {
 if (k < n)
  return 0;
 return binomial(k,n) * fact(n);
}

/* Returns the number of surjections from [0..n-1] to [0..p-1]. */
long countSurj(int n, int p) {
 if (n <= 0 || p <= 0 || p > n)
  return 0;
 if (n == 1 && p == 1)
  return 1;
 return (p * (countSurj(n - 1,p - 1) + countSurj(n - 1,p)));
}

/* Computes n!! */
long doubleFact(int n) {
 if (n == 1)
  return 1;
 else
  return (
    (n % 2 == 1) ?
      (long) n * doubleFact(n - 2) : (long) (n - 1) * doubleFact(n - 3));
}

/* Computes the sum of the (m-1)-nth elements of i[] * (2m-2p-1)!! */
long sum1(long i[], int m) {
 int p;
 long s = 0;
 for (p = 1; p < m; p++) {
  s += i[p] * doubleFact(2 * m - 2 * p - 1);
 }
 s = doubleFact(2 * m - 1) - s;
 return s;
}

/* For e >= 0, count698(e+1) is the number of rooted ordinary orientable maps
   with e edges.
   Sequence http://oeis.org/A000698. */
long count698(int m) {
 long i[10];
 int n;
 i[0] = 1;
 i[1] = 1;
 for (n = 2; n <= m; n++) {
  i[n] = sum1(i,n);
 }
 return i[m];
}

/* Computes the sum of the (n-1)-nth elements of c[] * (n-p)!. */
long sum2(long c[], int n) {
 int p;
 long s = 0;
 for (p = 1; p < n; p++) {
  s += c[p] * fact(n - p);
 }
 s = fact(n) - s;
 return s;
}

/* Counts the connected permutations.
   Sequence http://oeis.org/A003319 */
long count3319(int n) {
 long c[10];
 int m;
 c[0] = 0;
 c[1] = 1;
 for (m = 2; m <= n; m++) {
  c[m] = sum2(c,m);
 }
 return c[n];
}

/* Counts the connected involutions.
   Sequence http://oeis.org/A140456.
   1, 1, 1, 3, 7, 23, 71, 255, 911, 3535, 13903, 57663, 243871, 1072031;
   Returns 1,1,3,7,... */
long count140456(int n) {
 int k;
 long s = 0;
 if (n < 0)
  return 0;
 else if (n == 0)
  return 1;
 else {
  for (k = 0; k <= n / 2; k++)
   s += count698(k + 1) * binomial(n,n - 2 * k);
  return s;
 }
}

/* Returns the number of fixpoint free involutions of size n.
   Double factorial of odd numbers: count1147(n) = (2*n-1)!!
   Sequence https://oeis.org/A001147. */
long count1147(int n) {
 return (fact(2 * n) / (power(2,n) * fact(n)));
}

/** conversion **/

/* displaySubset() display the subsets of a set of n elements
 from the array ds of delta set. */
int delta2subset(int ds[], int s[], int n) {
 int i, c;
 c = 0;
 for (i = 0; i < n; i++) {
  if (ds[i] == 1) {
   s[c] = i;
   c++;
  }
 }
 return c;
}

/* From ha and hb to shuffle composed of '(', ')', '[' and ']' */
void decode(int ha[], int hb[], char p[], int n) {
 int i;
 if (ha[0] == 1)
  p[0] = '(';
 if (hb[0] == 1)
  p[0] = '[';
 for (i = 0; i < 2 * n - 1; i++) {
  if (ha[i + 1] - ha[i] == 1)
   p[i + 1] = '(';
  if (ha[i + 1] - ha[i] == -1)
   p[i + 1] = ')';
  if (hb[i + 1] - hb[i] == 1)
   p[i + 1] = '[';
  if (hb[i + 1] - hb[i] == -1)
   p[i + 1] = ']';
 }
}
