Require Import UniMath.Foundations.All.

(** Section 2.3. Equality *)

Definition J {A : UU} (P : forall (x y : A), paths x y -> UU) (h : forall (x : A), P x x (idpath x)) {x y : A} (eq : paths x y): P x y eq.
Proof.
induction eq.
apply h.
Defined.

Lemma J_refl {A : UU} (P : forall (x y : A), x = y -> UU) (r : forall (x : A), P x x (idpath x)) (x : A): J P r (idpath x) = r x.
Proof.
simpl.
reflexivity.
Qed.

Definition subst {A : UU} (P : A -> UU) {x y : A}: x = y -> P x -> P y
:= J (fun u v _ => P u -> P v) (fun _ p => p).


(** Section 3.1. Parameters *)
(** Section 3.4. A universe *)
Inductive U : UU :=
  | id : U
  | type : U
  | k : UU -> U
  | func : U -> U -> U
  | cart : U -> U -> U
  | binsum : U -> U -> U.

Fixpoint El (u : U) (C: UU): UU :=
match u with
| id => C
| type => UU
| (k A) => A
| (func a b) => (El a C) -> (El b C)
| (cart a b) => (El a C) × (El b C)
| (binsum a b) => (El a C) ⨿ (El b C)
end.

Definition funceq {A B C D} : A <-> B -> C <-> D -> (A -> C) <-> (B -> D).
Proof.
intros p q.
destruct p as [ab ba].
destruct q as [cd dc].
split.

- intros ac b.
apply cd.
apply ac.
apply ba.
exact b.

- intros bd a.
apply dc.
apply bd.
apply ab.
exact a.
Defined.

Definition cartprodeq {A B C D} : A <-> B -> C <-> D -> (A × C) <-> (B × D).
Proof.
intros p q.
destruct p as [ab ba].
destruct q as [cd dc].
split.

- intros pair.
destruct pair as [a c].
split.
-- apply ab.
exact a.
-- apply cd.
exact c.

- intros pair.
destruct pair as [b d].
split.
-- apply ba.
exact b.
-- apply dc.
exact d.

Defined.

Definition binsumeq {A B C D} : A <-> B -> C <-> D -> (A ⨿ C) <-> (B ⨿ D).
Proof.
intros p q.
destruct p as [ab ba].
destruct q as [cd dc].
split.

- intros [a | c].
+ left. apply ab. exact a.
+ right. apply cd. exact c.

- intros [b | d].
+ left. apply ba. exact b.
+ right. apply dc. exact d.

Defined.

Definition leq_refl (P : UU) : P <-> P.
Proof.
apply isrefl_logeq.
Defined.

Fixpoint cast (a : U) {B C : UU} (eq : B <-> C) : (El a B) <-> (El a C)
:=
match a with
| id => (eq : (El id B) <-> (El id C))
| type => (leq_refl Type)
| (k A) => (leq_refl A)
| (func l r) => funceq (cast l eq) (cast r eq)
| (cart l r) => cartprodeq (cast l eq) (cast r eq)
| (binsum l r) => binsumeq (cast l eq) (cast r eq)
end.

Lemma cast_id (a : U) (B : UU)
  : cast a (isrefl_logeq B) = isrefl_logeq (El a B).
Proof.
  induction a;
    try reflexivity.
  - refine (maponpaths (λ x, _ x _) IHa1 @ maponpaths (λ x, _ _ x) IHa2).
  - refine (maponpaths (λ x, _ x _) IHa1 @ maponpaths (λ x, _ _ x) IHa2).
  - refine (maponpaths (λ x, _ x _) IHa1 @ maponpaths (λ x, _ _ x) IHa2 @ _).
    apply pathsdirprod;
      apply funextfun;
      intro X;
      induction X;
      reflexivity.
Qed.

Definition resp (a : U) {B C : UU} (weq : B ≃ C)
  : El a B -> El a C
  := pr1 (cast a (weq_to_iff weq)).

Definition resp_id (a : U) {B} (x : El a B) : resp a (idweq B) x = x.
Proof.
  exact (maponpaths (λ f, _ f x) (cast_id _ _)).
Qed.


(** Section 3.2. Codes for structures *)

Definition Code : UU := ∑ a : U, ∏ (C : UU), El a C -> (∑ P : UU, isaprop P).

Definition Instance (c : Code) : UU
:= ∑ (C : UU) (x : El (pr1 c) C), pr1 ((pr2 c) C x).

Definition is_isomorphism (a : U) {B C} (eq : B ≃ C) (x : El a B) (y : El a C): UU
:= resp a eq x = y.

Definition isomorphic (c : Code) (x y : Instance c): UU
:= ∑ (eq : pr1 x ≃ pr1 y), is_isomorphism (pr1 c) eq (pr1 (pr2 x)) (pr1 (pr2 y)).

Definition Carrier (c : Code) (X : Instance c): UU := pr1 X.
Definition element (c : Code) (X : Instance c): El (pr1 c) (Carrier c X) := (pr1 (pr2 X)).

Lemma equality_pair_lemma (c : Code) (X Y : Instance c): (X = Y) <-> ∑ (eq : Carrier c X = Carrier c Y), subst (El (pr1 c)) eq (element c X) = element c Y.
Proof.
split.
- intros.
destruct X0.
exists (idpath (Carrier c X)).
unfold subst.
exact (maponpaths (λ x, x _) (J_refl _ _ _)).
-
Qed.

Theorem isomorphism_is_equality (c : Code) (X Y : Instance c) : (X = Y) <-> isomorphic c X Y .
Proof.
split.
- intros.
rewrite X0.
unfold isomorphic.
unfold is_isomorphism.
exists (eqweqmap (idpath (pr1 Y))).
(* Requires resp_id *)
- intros.
(* Requires equality_pair_lemma *)
Qed.

