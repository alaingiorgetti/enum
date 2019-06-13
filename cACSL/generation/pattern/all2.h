/*@ axiomatic preds {
  @  predicate is_x3(int *a, integer n, integer v1, integer v2) reads a[0..n-1];
  @ }
  @ predicate is_x2_gen(int *a, integer n, integer v1, integer v2) =
  @  \forall integer i2; v1 <= i2 < v2 ==> is_x3(a,n,v1,i2);
  @ predicate is_x2(int *a, integer n, integer v1) = is_x2_gen(a,n,v1,n);
  @ predicate is_x1_gen(int *a, integer n, integer v1) =
  @  \forall integer i1; 0 <= i1 < v1 ==> is_x2(a,n,i1);
  @ predicate is_x1(int *a, integer n) = is_x1_gen(a,n,n); */

/*@ requires n >= 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_x3(a,n,v1,v2); */
int b_x3(int a[], int n, int v1, int v2);

/*@ requires n >= 0 && n > v1 >= 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_x2(a,n,v1); */
int b_x2(int a[], int n, int v1);

/*@ requires n >= 0 && \valid(a+(0..n-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_x1(a,n); */
int b_x1(int a[], int n);
