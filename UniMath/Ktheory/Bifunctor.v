Require Import
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Sets
        UniMath.Ktheory.Precategories.

Local Open Scope cat.

Set Automatic Introduction.

(** bifunctor commutativity *)

Definition bifunctor_comm_functor_data {I A B:Precategory} :
  [I, [A, B] ] -> A -> functor_data I B
  := λ D a, functor_data_constr I B (λ i, D ◾ i ◾ a) (λ i j e, D ▭ e ◽ a).

Lemma isfunctor_bifunctor_comm_functor_data {I A B:Precategory} :
  ∀ (D:[I,[A,B]]) (a:A), is_functor (bifunctor_comm_functor_data D a).
Proof.
  split.
  { unfold functor_idax. intro i; simpl. unfold functor_mor_application.
    now rewrite functor_id. }
  { intros i j k f g; simpl. unfold functor_mor_application.
    now rewrite functor_comp. }
Qed.

Definition bifunctor_comm_functor {I A B:Precategory} :
  [I, [A, B] ] -> A -> [I,B].
Proof.
  intros D a.
  exists (bifunctor_comm_functor_data D a).
  exact (isfunctor_bifunctor_comm_functor_data D a).
Defined.

Definition bifunctor_comm_functor_data_2 (I A B:Precategory) : functor_data [I,[A,B]] [A,[I,B]].
Proof.
  refine (_,,_).
  { intros D.
    refine (_,,_).
    { refine (_,,_).
      { intros a. exact (bifunctor_comm_functor D a). }
      intros a a' f; simpl.
      refine (_,,_).
      { simpl; intro i. exact (D ◾ i ▭ f). }
      { abstract (intros i j r; simpl; eqn_logic) using L. } }
    { abstract ( split;
                 [ intros a; simpl; apply nat_trans_eq;
                   [ apply homset_property
                   | intros i; simpl; apply functor_id ]
                 | intros a b g r s; simpl; apply nat_trans_eq;
                   [ apply homset_property
                   | simpl; intros i; apply functor_comp ] ] ) using M. } }
  { intros D D' p. simpl.
    refine (_,,_).
    { intros a. simpl.
      refine (_,,_).
      { exact (λ i, p ◽ i ◽ a). }
      { abstract (exact (λ i j e, maponpaths (λ v, v ◽ a) (nat_trans_ax p _ _ e))) using N. } }
    { abstract (intros a b f; apply nat_trans_eq;
                [ apply homset_property
                | intros i; simpl; apply nat_trans_ax]) using O. } }
Defined.

Definition isfunctor_bifunctor_comm_functor_data_2 {I A B:Precategory} :
  is_functor (bifunctor_comm_functor_data_2 I A B).
Proof.
  split.
  { intros D. simpl. apply nat_trans_eq.
    { exact (homset_property [I,B]). }
    simpl; intros a. apply nat_trans_eq.
    { apply homset_property. }
    reflexivity. }
  { intros D D' D'' p q; simpl. apply nat_trans_eq. exact (homset_property [I,B]).
    intros a; simpl. apply nat_trans_eq.
    { apply homset_property. }
    intros i; simpl. eqn_logic. }
Qed.

Definition bifunctor_comm (A B C:Precategory) : [A,[B,C]] ==> [B,[A,C]].
Proof.
  exists (bifunctor_comm_functor_data_2 A B C).
  apply isfunctor_bifunctor_comm_functor_data_2.
Defined.

(** bifunctors related to representable functors  *)

Definition θ_1 {B C:Precategory} (X : [B^op, [C, SET]]) (F : [B, C]) : hSet
  := (∀ b, X ◾ b ⇒ F ◾ b) % set.

Definition θ_2 {B C:Precategory} (X : [B^op, [C, SET]]) (F : [B, C])
           (x : θ_1 X F) : hSet
  := (∀ (b b':B) (f:b→b'), F ▭ f ⟳ x b = x b' ⟲ X ▭ f) % set.

Definition θ {B C:Precategory} (X : [B^op, [C, SET]]) (F : [B, C]) : hSet
  := ( Σ x : θ_1 X F, θ_2 X F x ) % set.

Notation "X ⟹ F" := (θ X F) (at level 50) : cat.

Definition θ_subset {B C:Precategory} {X : [B^op, [C, SET]]} {F : [B, C]}
           (t u : X ⟹ F) :
  pr1 t = pr1 u -> t = u.
Proof.
  apply subtypeEquality.
  intros x. apply impred; intro b;apply impred; intro b'; apply impred; intro f.
  apply setproperty.
Defined.

Definition θ_map_1 {B C:Precategory} {X : [B^op, [C, SET]]^op} {F F':[B, C]} :
  X ⟹ F -> F → F' -> θ_1 X F'
  := λ xe p (b:B), p ◽ b ⟳ pr1 xe b.

Definition θ_map_2 {B C:Precategory} {X : [B^op, [C, SET]]^op} {F F':[B, C]}
  (xe : X ⟹ F) (p : F → F') : θ_2 X F' (θ_map_1 xe p).
Proof.
  induction xe as [x e]. unfold θ_map_1; unfold θ_1 in x; unfold θ_2 in e.
  intros b b' f; simpl.
  rewrite <- arrow_mor_mor_assoc.
  rewrite <- nattrans_naturality.
  rewrite arrow_mor_mor_assoc.
  rewrite e.
  rewrite nattrans_arrow_mor_assoc.
  reflexivity.
Qed.

Definition θ_map {B C:Precategory} {X : [B^op, [C, SET]]^op} {F F':[B, C]} :
  X ⟹ F -> F → F' -> X ⟹ F'
  := λ xe p, θ_map_1 xe p ,, θ_map_2 xe p.

Notation "xe ⟲⟲ p" := (θ_map xe p) (at level 50) : cat. (* ⟲ agda-input \l C-N C-N C-N 2 the first time, \l the second time *)

Definition φ_map_1 {B C:Precategory} {X X': [B^op, [C, SET]]^op} {F:[B, C]} :
  X' → X -> X ⟹ F -> θ_1 X' F
  := λ p x b, pr1 x b ⟲ p ◽ b.

Definition φ_map_2 {B C:Precategory} {X X': [B^op, [C, SET]]^op} {F:[B, C]}
  (p : X' → X) (x : X ⟹ F) : θ_2 X' F (φ_map_1 p x).
Proof.
  induction x as [x e]. unfold φ_map_1; unfold θ_1 in x; unfold θ_2 in e; unfold θ_2.
  intros b b' f; simpl.
  rewrite nattrans_arrow_mor_assoc.
  rewrite e.
  rewrite 2? nattrans_nattrans_arrow_assoc.
  exact (maponpaths (λ k, x b' ⟲ k) (nattrans_naturality p f)).
Qed.

Definition φ_map {B C:Precategory} {X X': [B^op, [C, SET]]^op} {F:[B, C]} :
  X' → X -> X ⟹ F -> X' ⟹ F
  := λ p x, φ_map_1 p x,, φ_map_2 p x.

Definition bifunctor_assoc {B C:Precategory} : [B^op, [C,SET]] ==> [[B,C],SET].
Proof.
  refine (makeFunctor _ _ _ _).
  { intros X.
    refine (makeFunctor _ _ _ _).
    { intro F. exact (X ⟹ F). }
    { intros F F' p xe. exact (xe ⟲⟲ p). }
    { abstract (
          intros F; apply funextsec; intro xe; apply θ_subset;
          simpl; apply funextsec; intro b; apply arrow_mor_id) using K. }
    { abstract (
          intros F F' F'' p q; simpl; apply funextsec; intro xe; apply θ_subset;
          simpl; apply funextsec; intro b; apply arrow_mor_mor_assoc) using K. } }
  { intros X Y p. simpl.
    refine (_,,_).
    { intros F. simpl. intro x. exact (φ_map p x). }
    { postponeProof. } }
  { intros X.




Admitted.

(* *)
