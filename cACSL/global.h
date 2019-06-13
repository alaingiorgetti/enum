/*@ predicate is_eq{L1,L2}(int *a, integer i) =
  @  \forall integer j; 0 <= j < i ==> \at(a[j],L1) == \at(a[j],L2);
 
  @ predicate lt_lex_at{L1,L2}(int *a, integer i) = 
  @  is_eq{L1,L2}(a,i) && \at(a[i],L1) < \at(a[i],L2);

  @ predicate lt_lex{L1,L2}(int *a, integer n) =
  @  \exists int i; 0 <= i < n && lt_lex_at{L1,L2}(a,i);

  @ predicate le_lex{L1,L2}(int *a, integer n) = lt_lex{L1,L2}(a,n)
  @  || is_eq{L1,L2}(a,n); */


/*@ predicate is_eq2(int *a, int *b, integer i) =
  @  \forall integer j; 0 <= j < i ==> a[j] == b[j];

  @ predicate lt_lex_at2(int *a, int *b, integer i) =
  @  is_eq2(a,b,i) && a[i] < b[i];

  @ predicate lt_lex2(int *a, int *b, integer n) =
  @  \exists int i; 0 <= i < n && lt_lex_at2(a,b,i);

  @ predicate le_lex2(int *a, int *b, integer n) = lt_lex2(a,b,n)
  @  || is_eq2(a,b,n); */


/*@ lemma trans_le_lt_lex{L1,L2,L3}: \forall int *a; \forall integer n;
     (le_lex{L1,L2}(a,n) && lt_lex{L2,L3}(a,n)) ==> lt_lex{L1,L3}(a,n); */
