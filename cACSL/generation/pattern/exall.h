/*@ axiomatic preds {
  @  predicate is_x3{L}(int *a, integer n1, integer n2, integer n3) reads a[0..n1-1];
  @ }
  @
  @ predicate is_x2_gen{L}(int *a, integer n1, integer n2, integer n3) =
  @  \forall integer i2; 0 <= i2 < n3 ==> is_x3(a,n1,n2,i2);
  @ predicate is_x2{L}(int *a, integer n1, integer n2) = is_x2_gen(a,n1,n2,n1);
  @
  @ predicate is_x1_gen{L}(int *a, integer n1, integer n2) =
  @  \exists integer i1; 0 <= i1 < n2 && is_x2(a,n1,i1);
  @ predicate is_x1{L}(int *a, integer n) = is_x1_gen(a,n,n); */

/*@ requires 0 <= n1 && \valid(a+(0..n1-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_x3(a,n1,n2,n3); */
int b_x3(int a[], int n1, int n2, int n3);

/*@ requires 0 <= n1 && \valid(a+(0..n1-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_x2(a,n1,n2); */
int b_x2(int a[], int n1, int n2);

/*@ requires n1 >= 0 && \valid(a+(0..n1-1));
  @ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> is_x1(a,n1);  */
int b_x1(int a[], int n1);
