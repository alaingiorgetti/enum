(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.
Require map.Map.
Require map.Occ.
Require map.MapPermut.
Require map.MapInjection.

(* Why3 assumption *)
Definition unit := unit.

(* Why3 assumption *)
Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Axiom ref_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (ref a).
Existing Instance ref_WhyType.
Implicit Arguments mk_ref [[a]].

(* Why3 assumption *)
Definition contents {a:Type} {a_WT:WhyType a} (v:(ref a)): a :=
  match v with
  | (mk_ref x) => x
  end.

(* Why3 assumption *)
Inductive array (a:Type) :=
  | mk_array : Z -> (map.Map.map Z a) -> array a.
Axiom array_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (array a).
Existing Instance array_WhyType.
Implicit Arguments mk_array [[a]].

(* Why3 assumption *)
Definition elts {a:Type} {a_WT:WhyType a} (v:(array a)): (map.Map.map Z a) :=
  match v with
  | (mk_array x x1) => x1
  end.

(* Why3 assumption *)
Definition length {a:Type} {a_WT:WhyType a} (v:(array a)): Z :=
  match v with
  | (mk_array x x1) => x
  end.

(* Why3 assumption *)
Definition get {a:Type} {a_WT:WhyType a} (a1:(array a)) (i:Z): a :=
  (map.Map.get (elts a1) i).

(* Why3 assumption *)
Definition set {a:Type} {a_WT:WhyType a} (a1:(array a)) (i:Z) (v:a): (array
  a) := (mk_array (length a1) (map.Map.set (elts a1) i v)).

(* Why3 assumption *)
Definition injective (a:(array Z)): Prop := (map.MapInjection.injective
  (elts a) (length a)).

(* Why3 assumption *)
Definition surjective (a:(array Z)): Prop := (map.MapInjection.surjective
  (elts a) (length a)).

(* Why3 assumption *)
Definition range (a:(array Z)): Prop := (map.MapInjection.range (elts a)
  (length a)).

Axiom injective_surjective : forall (a:(array Z)), (injective a) -> ((range
  a) -> (surjective a)).

Axiom injection_occ : forall (a:(array Z)), (injective a) <-> forall (v:Z),
  ((map.Occ.occ v (elts a) 0%Z (length a)) <= 1%Z)%Z.

Axiom endoinjection_occ : forall (a:(array Z)), ((map.MapInjection.range
  (elts a) (length a)) /\ (injective a)) -> forall (v:Z), ((0%Z <= v)%Z /\
  (v < (length a))%Z) -> ((map.Occ.occ v (elts a) 0%Z (length a)) = 1%Z).

(* Why3 assumption *)
Definition map_eq_sub {a:Type} {a_WT:WhyType a} (a1:(map.Map.map Z a))
  (a2:(map.Map.map Z a)) (l:Z) (u:Z): Prop := forall (i:Z), ((l <= i)%Z /\
  (i < u)%Z) -> ((map.Map.get a1 i) = (map.Map.get a2 i)).

(* Why3 assumption *)
Definition array_eq_sub {a:Type} {a_WT:WhyType a} (a1:(array a)) (a2:(array
  a)) (l:Z) (u:Z): Prop := ((length a1) = (length a2)) /\ (((0%Z <= l)%Z /\
  (l <= (length a1))%Z) /\ (((0%Z <= u)%Z /\ (u <= (length a1))%Z) /\
  (map_eq_sub (elts a1) (elts a2) l u))).

(* Why3 assumption *)
Definition array_eq {a:Type} {a_WT:WhyType a} (a1:(array a)) (a2:(array
  a)): Prop := ((length a1) = (length a2)) /\ (map_eq_sub (elts a1) (elts a2)
  0%Z (length a1)).

(* Why3 assumption *)
Definition lt_lex_sub_at (a1:(array Z)) (a2:(array Z)) (l:Z) (u:Z)
  (i:Z): Prop := ((l <= i)%Z /\ (i < u)%Z) /\ ((array_eq_sub a1 a2 l i) /\
  ((get a1 i) < (get a2 i))%Z).

(* Why3 assumption *)
Definition lt_lex_at (a1:(array Z)) (a2:(array Z)) (i:Z): Prop :=
  ((length a1) = (length a2)) /\ (lt_lex_sub_at a1 a2 0%Z (length a1) i).

(* Why3 assumption *)
Definition lt_lex_sub (a1:(array Z)) (a2:(array Z)) (l:Z) (u:Z): Prop :=
  exists i:Z, (lt_lex_sub_at a1 a2 l u i).

(* Why3 assumption *)
Definition lt_lex (a1:(array Z)) (a2:(array Z)): Prop :=
  ((length a1) = (length a2)) /\ (lt_lex_sub a1 a2 0%Z (length a1)).

(* Why3 assumption *)
Definition le_lex_sub (a1:(array Z)) (a2:(array Z)) (l:Z) (u:Z): Prop :=
  (lt_lex_sub a1 a2 l u) \/ (array_eq_sub a1 a2 l u).

Axiom prefix_le_lex_sub : forall (a:(array Z)) (b:(array Z)) (l:Z) (u:Z),
  ((array_eq_sub a b 0%Z l) /\ (le_lex_sub a b l u)) -> (le_lex_sub a b 0%Z
  u).

Axiom not_array_eq_sub : forall (a:(array Z)) (b:(array Z)) (l:Z) (u:Z),
  (((0%Z <= (length a))%Z /\ (0%Z <= (length b))%Z) /\ (((0%Z <= l)%Z /\
  ((l < u)%Z /\ ((u <= (length a))%Z /\ ((length a) = (length b))))) /\
  ~ (array_eq_sub a b l u))) -> exists i:Z, ((l <= i)%Z /\ (i < u)%Z) /\
  ((array_eq_sub a b l i) /\ ~ ((get a i) = (get b i))).

Axiom total_order : forall (a:(array Z)) (b:(array Z)) (l:Z) (u:Z),
  (((0%Z <= l)%Z /\ ((l < u)%Z /\ ((u <= (length a))%Z /\
  ((length a) = (length b))))) /\ ~ (lt_lex_sub b a l u)) -> (le_lex_sub a b
  l u).

(* Why3 assumption *)
Definition exchange {a:Type} {a_WT:WhyType a} (a1:(map.Map.map Z a))
  (a2:(map.Map.map Z a)) (l:Z) (u:Z) (i:Z) (j:Z): Prop := ((l <= i)%Z /\
  (i < u)%Z) /\ (((l <= j)%Z /\ (j < u)%Z) /\ (((map.Map.get a1
  i) = (map.Map.get a2 j)) /\ (((map.Map.get a1 j) = (map.Map.get a2 i)) /\
  forall (k:Z), ((l <= k)%Z /\ (k < u)%Z) -> ((~ (k = i)) -> ((~ (k = j)) ->
  ((map.Map.get a1 k) = (map.Map.get a2 k))))))).

Axiom exchange_set : forall {a:Type} {a_WT:WhyType a},
  forall (a1:(map.Map.map Z a)) (l:Z) (u:Z) (i:Z) (j:Z), ((l <= i)%Z /\
  (i < u)%Z) -> (((l <= j)%Z /\ (j < u)%Z) -> (exchange a1
  (map.Map.set (map.Map.set a1 i (map.Map.get a1 j)) j (map.Map.get a1 i)) l
  u i j)).

(* Why3 assumption *)
Definition exchange1 {a:Type} {a_WT:WhyType a} (a1:(array a)) (a2:(array a))
  (i:Z) (j:Z): Prop := ((length a1) = (length a2)) /\ (exchange (elts a1)
  (elts a2) 0%Z (length a1) i j).

(* Why3 assumption *)
Definition permut {a:Type} {a_WT:WhyType a} (a1:(array a)) (a2:(array a))
  (l:Z) (u:Z): Prop := ((length a1) = (length a2)) /\ (((0%Z <= l)%Z /\
  (l <= (length a1))%Z) /\ (((0%Z <= u)%Z /\ (u <= (length a1))%Z) /\
  (map.MapPermut.permut (elts a1) (elts a2) l u))).

(* Why3 assumption *)
Definition permut_sub {a:Type} {a_WT:WhyType a} (a1:(array a)) (a2:(array a))
  (l:Z) (u:Z): Prop := (map_eq_sub (elts a1) (elts a2) 0%Z l) /\ ((permut a1
  a2 l u) /\ (map_eq_sub (elts a1) (elts a2) u (length a1))).

(* Why3 assumption *)
Definition permut_all {a:Type} {a_WT:WhyType a} (a1:(array a)) (a2:(array
  a)): Prop := ((length a1) = (length a2)) /\ (map.MapPermut.permut (elts a1)
  (elts a2) 0%Z (length a1)).

Axiom exchange_permut_sub : forall {a:Type} {a_WT:WhyType a},
  forall (a1:(array a)) (a2:(array a)) (i:Z) (j:Z) (l:Z) (u:Z), (exchange1 a1
  a2 i j) -> (((l <= i)%Z /\ (i < u)%Z) -> (((l <= j)%Z /\ (j < u)%Z) ->
  ((0%Z <= l)%Z -> ((u <= (length a1))%Z -> (permut_sub a1 a2 l u))))).

Axiom permut_sub_weakening : forall {a:Type} {a_WT:WhyType a},
  forall (a1:(array a)) (a2:(array a)) (l1:Z) (u1:Z) (l2:Z) (u2:Z),
  (permut_sub a1 a2 l1 u1) -> (((0%Z <= l2)%Z /\ (l2 <= l1)%Z) ->
  (((u1 <= u2)%Z /\ (u2 <= (length a1))%Z) -> (permut_sub a1 a2 l2 u2))).

Axiom exchange_permut_all : forall {a:Type} {a_WT:WhyType a},
  forall (a1:(array a)) (a2:(array a)) (i:Z) (j:Z), (exchange1 a1 a2 i j) ->
  (permut_all a1 a2).

(* Why3 assumption *)
Definition is_permut (a:(array Z)): Prop := (range a) /\ (injective a).

Axiom endoinj_permut : forall (a:(array Z)) (b:(array Z)),
  (((0%Z <= (length a))%Z /\ ((length a) = (length b))) /\ ((is_permut a) /\
  (is_permut b))) -> (permut a b 0%Z (length a)).

(* Why3 assumption *)
Definition is_id_sub (a:(array Z)) (l:Z) (u:Z): Prop := forall (i:Z),
  ((l <= i)%Z /\ (i < u)%Z) -> ((get a i) = i).

(* Why3 assumption *)
Definition im_sup1 (a:(array Z)) (r:Z) (k:Z): Prop := forall (i:Z),
  ((r < i)%Z /\ (i < k)%Z) -> ((get a k) < (get a i))%Z.

(* Why3 assumption *)
Definition im_sup2 (a:(array Z)) (r:Z) (k:Z): Prop := forall (i:Z),
  ((k < i)%Z /\ (i < (length a))%Z) -> ((get a i) < (get a r))%Z.

(* Why3 assumption *)
Definition is_inc_sub (a:(array Z)) (l:Z) (u:Z): Prop := forall (i:Z) (j:Z),
  ((l <= i)%Z /\ ((i < j)%Z /\ (j < u)%Z)) -> ((get a i) < (get a j))%Z.

(* Why3 assumption *)
Definition is_inc (a:(array Z)): Prop := (is_inc_sub a 0%Z (length a)).

(* Why3 assumption *)
Definition is_dec_sub (a:(array Z)) (l:Z) (u:Z): Prop := forall (i:Z) (j:Z),
  ((l <= i)%Z /\ ((i < j)%Z /\ (j < u)%Z)) -> ((get a j) < (get a i))%Z.

Axiom min_lex_sub : forall (a:(array Z)) (l:Z) (u:Z), (((0%Z <= l)%Z /\
  ((l < u)%Z /\ (u <= (length a))%Z)) /\ ((injective a) /\ (is_inc_sub a l
  u))) -> forall (b:(array Z)), ((permut a b l u) /\ (injective b)) ->
  (le_lex_sub a b l u).

Axiom max_lex_sub : forall (a:(array Z)) (l:Z) (u:Z), (((0%Z <= l)%Z /\
  ((l < u)%Z /\ (u <= (length a))%Z)) /\ ((injective a) /\ (is_dec_sub a l
  u))) -> forall (b:(array Z)), ((permut a b l u) /\ (injective b)) ->
  (le_lex_sub b a l u).

(* Why3 assumption *)
Definition min_lex (a:(array Z)): Prop := forall (b:(array Z)),
  (((length a) = (length b)) /\ (is_permut b)) -> (le_lex_sub a b 0%Z
  (length a)).

(* Why3 assumption *)
Definition max_lex (a:(array Z)): Prop := forall (b:(array Z)),
  (((length a) = (length b)) /\ (is_permut b)) -> (le_lex_sub b a 0%Z
  (length a)).

(* Why3 assumption *)
Definition inc (a1:(array Z)) (a2:(array Z)): Prop :=
  ((length a1) = (length a2)) /\ ((lt_lex_sub a1 a2 0%Z (length a1)) /\
  forall (a3:(array Z)), (((length a1) = (length a3)) /\ ((is_permut a3) /\
  (lt_lex_sub a1 a3 0%Z (length a1)))) -> (le_lex_sub a2 a3 0%Z
  (length a1))).

(* Why3 assumption *)
Inductive cursor :=
  | mk_cursor : (array Z) -> bool -> cursor.
Axiom cursor_WhyType : WhyType cursor.
Existing Instance cursor_WhyType.

(* Why3 assumption *)
Definition new (v:cursor): bool := match v with
  | (mk_cursor x x1) => x1
  end.

(* Why3 assumption *)
Definition current (v:cursor): (array Z) :=
  match v with
  | (mk_cursor x x1) => x
  end.

(* Why3 assumption *)
Definition sound (c:cursor): Prop := (is_permut (current c)).

(* Why3 goal *)
Theorem split_inc_sub : forall (a:(array Z)) (l:Z) (m:Z) (u:Z),
  (((0%Z <= l)%Z /\ ((l <= m)%Z /\ ((m < u)%Z /\ (u <= (length a))%Z))) /\
  ((is_inc_sub a l (m + 1%Z)%Z) /\ (is_inc_sub a m u))) -> (is_inc_sub a l
  u).
(* Why3 intros a l m u ((h1,(h2,(h3,h4))),(h5,h6)). *)
intros a l m u ((h1,(h2,(h3,h4))),(h5,h6)).

intros i j [I I0].

case (Zcompare_spec i m).
- intuition.
-{
 intro A.
 case (Zcompare_spec j m).
 -intuition.
 -intuition.
 -{
  intro B.
  assert ( get a i < get a m)%Z. apply h5. omega.
  assert ( get a m < get a j)%Z. apply h6. omega.
  omega.
 }
}
-intuition.
Qed.

