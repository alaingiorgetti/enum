(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require HighOrd.
Require int.Int.
Require map.Map.
Require map.Occ.
Require map.MapPermut.
Require map.MapInjection.
Require list.List.

(* Why3 assumption *)
Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Axiom ref_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (ref a).
Existing Instance ref_WhyType.
Arguments mk_ref {a}.

(* Why3 assumption *)
Definition contents {a:Type} {a_WT:WhyType a} (v:ref a) : a :=
  match v with
  | mk_ref x => x
  end.

Axiom array : forall (a:Type), Type.
Parameter array_WhyType :
  forall (a:Type) {a_WT:WhyType a}, WhyType (array a).
Existing Instance array_WhyType.

Parameter elts:
  forall {a:Type} {a_WT:WhyType a}, array a -> Numbers.BinNums.Z -> a.

Parameter length:
  forall {a:Type} {a_WT:WhyType a}, array a -> Numbers.BinNums.Z.

Axiom array'invariant :
  forall {a:Type} {a_WT:WhyType a},
  forall (self:array a), (0%Z <= (length self))%Z.

(* Why3 assumption *)
Definition mixfix_lbrb {a:Type} {a_WT:WhyType a} (a1:array a)
    (i:Numbers.BinNums.Z) : a :=
  elts a1 i.

Parameter mixfix_lblsmnrb:
  forall {a:Type} {a_WT:WhyType a}, array a -> Numbers.BinNums.Z -> a ->
  array a.

Axiom mixfix_lblsmnrb_spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:array a) (i:Numbers.BinNums.Z) (v:a),
  ((length (mixfix_lblsmnrb a1 i v)) = (length a1)) /\
  ((elts (mixfix_lblsmnrb a1 i v)) = (map.Map.set (elts a1) i v)).

Parameter make:
  forall {a:Type} {a_WT:WhyType a}, Numbers.BinNums.Z -> a -> array a.

Axiom make_spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (n:Numbers.BinNums.Z) (v:a), (0%Z <= n)%Z ->
  (forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z /\ (i < n)%Z ->
   ((mixfix_lbrb (make n v) i) = v)) /\
  ((length (make n v)) = n).

(* Why3 assumption *)
Definition injective (a:array Numbers.BinNums.Z) : Prop :=
  map.MapInjection.injective (elts a) (length a).

(* Why3 assumption *)
Definition surjective (a:array Numbers.BinNums.Z) : Prop :=
  map.MapInjection.surjective (elts a) (length a).

(* Why3 assumption *)
Definition range (a:array Numbers.BinNums.Z) : Prop :=
  map.MapInjection.range (elts a) (length a).

(* Why3 assumption *)
Definition range_sub (a:array Numbers.BinNums.Z) (l:Numbers.BinNums.Z)
    (u:Numbers.BinNums.Z) (b:Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z), (l <= i)%Z /\ (i < u)%Z ->
  (0%Z <= (elts a i))%Z /\ ((elts a i) < b)%Z.

(* Why3 assumption *)
Definition inj_sub (a:array Numbers.BinNums.Z) (l:Numbers.BinNums.Z)
    (u:Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z), (l <= i)%Z /\ (i < u)%Z ->
  forall (j:Numbers.BinNums.Z), (l <= j)%Z /\ (j < u)%Z -> ~ (i = j) ->
  ~ ((elts a i) = (elts a j)).

Axiom injective_surjective :
  forall (a:array Numbers.BinNums.Z), injective a -> range a -> surjective a.

Axiom injection_occ :
  forall (a:array Numbers.BinNums.Z),
  injective a <->
  (forall (v:Numbers.BinNums.Z),
   ((map.Occ.occ v (elts a) 0%Z (length a)) <= 1%Z)%Z).

Axiom endoinjection_occ :
  forall (a:array Numbers.BinNums.Z),
  map.MapInjection.range (elts a) (length a) /\ injective a ->
  forall (v:Numbers.BinNums.Z), (0%Z <= v)%Z /\ (v < (length a))%Z ->
  ((map.Occ.occ v (elts a) 0%Z (length a)) = 1%Z).

(* Why3 assumption *)
Definition map_eq_sub {a:Type} {a_WT:WhyType a} (a1:Numbers.BinNums.Z -> a)
    (a2:Numbers.BinNums.Z -> a) (l:Numbers.BinNums.Z) (u:Numbers.BinNums.Z) :
    Prop :=
  forall (i:Numbers.BinNums.Z), (l <= i)%Z /\ (i < u)%Z -> ((a1 i) = (a2 i)).

(* Why3 assumption *)
Definition array_eq_sub {a:Type} {a_WT:WhyType a} (a1:array a) (a2:array a)
    (l:Numbers.BinNums.Z) (u:Numbers.BinNums.Z) : Prop :=
  ((length a1) = (length a2)) /\
  ((0%Z <= l)%Z /\ (l <= (length a1))%Z) /\
  ((0%Z <= u)%Z /\ (u <= (length a1))%Z) /\
  map_eq_sub (elts a1) (elts a2) l u.

(* Why3 assumption *)
Definition array_eq {a:Type} {a_WT:WhyType a} (a1:array a) (a2:array a) :
    Prop :=
  ((length a1) = (length a2)) /\
  map_eq_sub (elts a1) (elts a2) 0%Z (length a1).

(* Why3 assumption *)
Definition lt_lex_sub_at (a1:array Numbers.BinNums.Z)
    (a2:array Numbers.BinNums.Z) (l:Numbers.BinNums.Z) (u:Numbers.BinNums.Z)
    (i:Numbers.BinNums.Z) : Prop :=
  ((l <= i)%Z /\ (i < u)%Z) /\
  array_eq_sub a1 a2 l i /\ ((mixfix_lbrb a1 i) < (mixfix_lbrb a2 i))%Z.

(* Why3 assumption *)
Definition lt_lex_at (a1:array Numbers.BinNums.Z)
    (a2:array Numbers.BinNums.Z) (i:Numbers.BinNums.Z) : Prop :=
  ((length a1) = (length a2)) /\ lt_lex_sub_at a1 a2 0%Z (length a1) i.

(* Why3 assumption *)
Definition lt_lex_sub (a1:array Numbers.BinNums.Z)
    (a2:array Numbers.BinNums.Z) (l:Numbers.BinNums.Z)
    (u:Numbers.BinNums.Z) : Prop :=
  exists i:Numbers.BinNums.Z, lt_lex_sub_at a1 a2 l u i.

(* Why3 assumption *)
Definition lt_lex (a1:array Numbers.BinNums.Z) (a2:array Numbers.BinNums.Z) :
    Prop :=
  ((length a1) = (length a2)) /\ lt_lex_sub a1 a2 0%Z (length a1).

(* Why3 assumption *)
Definition le_lex_sub (a1:array Numbers.BinNums.Z)
    (a2:array Numbers.BinNums.Z) (l:Numbers.BinNums.Z)
    (u:Numbers.BinNums.Z) : Prop :=
  lt_lex_sub a1 a2 l u \/ array_eq_sub a1 a2 l u.

(* Why3 assumption *)
Definition le_lex (a1:array Numbers.BinNums.Z) (a2:array Numbers.BinNums.Z) :
    Prop :=
  ((length a1) = (length a2)) /\ le_lex_sub a1 a2 0%Z (length a1).

Axiom prefix_le_lex_sub :
  forall (a:array Numbers.BinNums.Z) (b:array Numbers.BinNums.Z)
    (l:Numbers.BinNums.Z) (u:Numbers.BinNums.Z),
  array_eq_sub a b 0%Z l /\ le_lex_sub a b l u -> le_lex_sub a b 0%Z u.

Axiom not_array_eq_sub :
  forall (a:array Numbers.BinNums.Z) (b:array Numbers.BinNums.Z)
    (l:Numbers.BinNums.Z) (u:Numbers.BinNums.Z),
  (0%Z <= l)%Z /\
  (l < u)%Z /\ (u <= (length a))%Z /\ ((length a) = (length b)) ->
  ~ array_eq_sub a b l u ->
  exists i:Numbers.BinNums.Z,
  ((l <= i)%Z /\ (i < u)%Z) /\
  array_eq_sub a b l i /\ ~ ((mixfix_lbrb a i) = (mixfix_lbrb b i)).

Axiom total_order :
  forall (a:array Numbers.BinNums.Z) (b:array Numbers.BinNums.Z)
    (l:Numbers.BinNums.Z) (u:Numbers.BinNums.Z),
  ((0%Z <= l)%Z /\
   (l < u)%Z /\ (u <= (length a))%Z /\ ((length a) = (length b))) /\
  ~ lt_lex_sub b a l u -> le_lex_sub a b l u.

(* Why3 assumption *)
Definition exchange {a:Type} {a_WT:WhyType a} (a1:Numbers.BinNums.Z -> a)
    (a2:Numbers.BinNums.Z -> a) (l:Numbers.BinNums.Z) (u:Numbers.BinNums.Z)
    (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z) : Prop :=
  ((l <= i)%Z /\ (i < u)%Z) /\
  ((l <= j)%Z /\ (j < u)%Z) /\
  ((a1 i) = (a2 j)) /\
  ((a1 j) = (a2 i)) /\
  (forall (k:Numbers.BinNums.Z), (l <= k)%Z /\ (k < u)%Z -> ~ (k = i) ->
   ~ (k = j) -> ((a1 k) = (a2 k))).

Axiom exchange_set :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:Numbers.BinNums.Z -> a) (l:Numbers.BinNums.Z)
    (u:Numbers.BinNums.Z) (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z),
  (l <= i)%Z /\ (i < u)%Z -> (l <= j)%Z /\ (j < u)%Z ->
  exchange a1 (map.Map.set (map.Map.set a1 i (a1 j)) j (a1 i)) l u i j.

(* Why3 assumption *)
Definition exchange1 {a:Type} {a_WT:WhyType a} (a1:array a) (a2:array a)
    (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z) : Prop :=
  ((length a1) = (length a2)) /\
  exchange (elts a1) (elts a2) 0%Z (length a1) i j.

(* Why3 assumption *)
Definition permut {a:Type} {a_WT:WhyType a} (a1:array a) (a2:array a)
    (l:Numbers.BinNums.Z) (u:Numbers.BinNums.Z) : Prop :=
  ((length a1) = (length a2)) /\
  ((0%Z <= l)%Z /\ (l <= (length a1))%Z) /\
  ((0%Z <= u)%Z /\ (u <= (length a1))%Z) /\
  map.MapPermut.permut (elts a1) (elts a2) l u.

(* Why3 assumption *)
Definition permut_sub {a:Type} {a_WT:WhyType a} (a1:array a) (a2:array a)
    (l:Numbers.BinNums.Z) (u:Numbers.BinNums.Z) : Prop :=
  map_eq_sub (elts a1) (elts a2) 0%Z l /\
  permut a1 a2 l u /\ map_eq_sub (elts a1) (elts a2) u (length a1).

(* Why3 assumption *)
Definition permut_all {a:Type} {a_WT:WhyType a} (a1:array a) (a2:array a) :
    Prop :=
  ((length a1) = (length a2)) /\
  map.MapPermut.permut (elts a1) (elts a2) 0%Z (length a1).

Axiom exchange_permut_sub :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:array a) (a2:array a) (i:Numbers.BinNums.Z)
    (j:Numbers.BinNums.Z) (l:Numbers.BinNums.Z) (u:Numbers.BinNums.Z),
  exchange1 a1 a2 i j -> (l <= i)%Z /\ (i < u)%Z ->
  (l <= j)%Z /\ (j < u)%Z -> (0%Z <= l)%Z -> (u <= (length a1))%Z ->
  permut_sub a1 a2 l u.

Axiom permut_sub_weakening :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:array a) (a2:array a) (l1:Numbers.BinNums.Z)
    (u1:Numbers.BinNums.Z) (l2:Numbers.BinNums.Z) (u2:Numbers.BinNums.Z),
  permut_sub a1 a2 l1 u1 -> (0%Z <= l2)%Z /\ (l2 <= l1)%Z ->
  (u1 <= u2)%Z /\ (u2 <= (length a1))%Z -> permut_sub a1 a2 l2 u2.

Axiom exchange_permut_all :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:array a) (a2:array a) (i:Numbers.BinNums.Z)
    (j:Numbers.BinNums.Z),
  exchange1 a1 a2 i j -> permut_all a1 a2.

(* Why3 assumption *)
Definition is_permut (a:array Numbers.BinNums.Z) : Prop :=
  range a /\ injective a.

Axiom endoinj_permut :
  forall (a:array Numbers.BinNums.Z) (b:array Numbers.BinNums.Z),
  ((0%Z <= (length a))%Z /\ ((length a) = (length b))) /\
  is_permut a /\ is_permut b -> permut a b 0%Z (length a).

(* Why3 assumption *)
Definition is_id_sub (a:array Numbers.BinNums.Z) (l:Numbers.BinNums.Z)
    (u:Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z), (l <= i)%Z /\ (i < u)%Z ->
  ((mixfix_lbrb a i) = i).

(* Why3 assumption *)
Definition im_sup1 (a:array Numbers.BinNums.Z) (r:Numbers.BinNums.Z)
    (k:Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z), (r < i)%Z /\ (i < k)%Z ->
  ((mixfix_lbrb a k) < (mixfix_lbrb a i))%Z.

(* Why3 assumption *)
Definition im_sup2 (a:array Numbers.BinNums.Z) (r:Numbers.BinNums.Z)
    (k:Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z), (k < i)%Z /\ (i < (length a))%Z ->
  ((mixfix_lbrb a i) < (mixfix_lbrb a r))%Z.

(* Why3 assumption *)
Definition is_inc_sub (a:array Numbers.BinNums.Z) (l:Numbers.BinNums.Z)
    (u:Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z),
  (l <= i)%Z /\ (i < j)%Z /\ (j < u)%Z ->
  ((mixfix_lbrb a i) < (mixfix_lbrb a j))%Z.

(* Why3 assumption *)
Definition is_inc (a:array Numbers.BinNums.Z) : Prop :=
  is_inc_sub a 0%Z (length a).

(* Why3 assumption *)
Definition is_dec_sub (a:array Numbers.BinNums.Z) (l:Numbers.BinNums.Z)
    (u:Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z),
  (l <= i)%Z /\ (i < j)%Z /\ (j < u)%Z ->
  ((mixfix_lbrb a j) < (mixfix_lbrb a i))%Z.

Axiom min_lex_sub :
  forall (a:array Numbers.BinNums.Z) (l:Numbers.BinNums.Z)
    (u:Numbers.BinNums.Z),
  ((0%Z <= l)%Z /\ (l < u)%Z /\ (u <= (length a))%Z) /\
  injective a /\ is_inc_sub a l u -> forall (b:array Numbers.BinNums.Z),
  permut a b l u /\ injective b -> le_lex_sub a b l u.

Axiom max_lex_sub :
  forall (a:array Numbers.BinNums.Z) (l:Numbers.BinNums.Z)
    (u:Numbers.BinNums.Z),
  ((0%Z <= l)%Z /\ (l < u)%Z /\ (u <= (length a))%Z) /\
  injective a /\ is_dec_sub a l u -> forall (b:array Numbers.BinNums.Z),
  permut a b l u /\ injective b -> le_lex_sub b a l u.

(* Why3 assumption *)
Definition min_lex (a:array Numbers.BinNums.Z) : Prop :=
  forall (b:array Numbers.BinNums.Z),
  ((length a) = (length b)) /\ is_permut b -> le_lex_sub a b 0%Z (length a).

(* Why3 assumption *)
Definition max_lex (a:array Numbers.BinNums.Z) : Prop :=
  forall (b:array Numbers.BinNums.Z),
  ((length a) = (length b)) /\ is_permut b -> le_lex_sub b a 0%Z (length a).

(* Why3 assumption *)
Definition inc (a1:array Numbers.BinNums.Z) (a2:array Numbers.BinNums.Z) :
    Prop :=
  ((length a1) = (length a2)) /\
  lt_lex_sub a1 a2 0%Z (length a1) /\
  (forall (a3:array Numbers.BinNums.Z),
   ((length a1) = (length a3)) /\
   is_permut a3 /\ lt_lex_sub a1 a3 0%Z (length a1) ->
   le_lex_sub a2 a3 0%Z (length a1)).

Axiom occ_append_instance :
  forall {a:Type} {a_WT:WhyType a},
  forall (v:a) (m:Numbers.BinNums.Z -> a) (mid:Numbers.BinNums.Z)
    (u:Numbers.BinNums.Z),
  (0%Z <= mid)%Z /\ (mid <= u)%Z ->
  ((map.Occ.occ v m 0%Z u) =
   ((map.Occ.occ v m 0%Z mid) + (map.Occ.occ v m mid u))%Z).

Axiom permut_split :
  forall (a:array Numbers.BinNums.Z) (b:array Numbers.BinNums.Z)
    (i:Numbers.BinNums.Z),
  (0%Z <= i)%Z /\ (i < (length a))%Z /\ ((length a) = (length b)) ->
  permut a b 0%Z (length a) -> permut a b 0%Z i -> permut a b i (length a).

(* Why3 assumption *)
Inductive cursor :=
  | mk_cursor : array Numbers.BinNums.Z -> Init.Datatypes.bool -> cursor.
Axiom cursor_WhyType : WhyType cursor.
Existing Instance cursor_WhyType.

(* Why3 assumption *)
Definition new (v:cursor) : Init.Datatypes.bool :=
  match v with
  | mk_cursor x x1 => x1
  end.

(* Why3 assumption *)
Definition current (v:cursor) : array Numbers.BinNums.Z :=
  match v with
  | mk_cursor x x1 => x
  end.

(* Why3 assumption *)
Definition sound (c:cursor) : Prop := is_permut (current c).

(* Why3 goal *)
Theorem split_inc_sub :
  forall (a:array Numbers.BinNums.Z) (l:Numbers.BinNums.Z)
    (m:Numbers.BinNums.Z) (u:Numbers.BinNums.Z),
  ((0%Z <= l)%Z /\ (l <= m)%Z /\ (m < u)%Z /\ (u <= (length a))%Z) /\
  is_inc_sub a l (m + 1%Z)%Z /\ is_inc_sub a m u -> is_inc_sub a l u.
(* Why3 intros a l m u ((h1,(h2,(h3,h4))),(h5,h6)). *)
Proof.
intros a l m u ((h1,(h2,(h3,h4))),(h5,h6)).
intros i j [I I0].
case (Z.compare_spec i m).
- intuition.
- {
  intro A.
  case (Z.compare_spec j m).
  - intuition.
  - intuition.
  - {
  intro B.
  assert (mixfix_lbrb a i < mixfix_lbrb a m)%Z. apply h5. omega.
  assert (mixfix_lbrb a m < mixfix_lbrb a j)%Z. apply h6. omega.
  omega.
  }
}
- intuition.
Qed.

