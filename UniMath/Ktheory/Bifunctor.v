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

Definition θ {B C:Precategory} (X : [B^op, [C, SET]]) (F : [B, C]) : hSet
  := (
      Σ x : (∀ b, X ◾ b ⇒ F ◾ b) % set,
            (∀ (b b':B) (f:b→b'), F ▭ f ⟳ x b = x b' ⟲ X ▭ f)
    ) % set.

Notation "X ⟹ F" := (θ X F) (at level 50) : cat.

Definition θ_subset {B C:Precategory} {X : [B^op, [C, SET]]} {F : [B, C]}
           (t u : X ⟹ F) :
  pr1 t = pr1 u -> t = u.
Proof.
  apply subtypeEquality.
  intros x. apply impred; intro b;apply impred; intro b'; apply impred; intro f.
  apply setproperty.
Defined.

Definition θ_map {B C:Precategory} {X : [B^op, [C, SET]]} {F F':[B, C]} :
  X ⟹ F -> F → F' -> X ⟹ F'.
Proof.
  intros xe p. set (x := pr1 xe). refine (_,,_).
  { exact (λ b:B, p ◽ b ⟳ x b). }
  intros b b' f; simpl.
  intermediate_path ((F' ▭ f ∘ p ◽ b) ⟳ x b).
  { apply pathsinv0, arrow_mor_mor_assoc. }
  intermediate_path ((p ◽ b' ∘ F ▭ f) ⟳ x b).
  { apply maponpaths. apply pathsinv0, nattrans_naturality. }
  intermediate_path (p ◽ b' ⟳ (F ▭ f ⟳ x b)).
  { apply arrow_mor_mor_assoc. }
  intermediate_path (p ◽ b' ⟳ (x b' ⟲ X ▭ f)).
  { apply (maponpaths (λ k, p ◽ b' ⟳ k)). apply (pr2 xe). }
  apply nattrans_arrow_mor_assoc.
Defined.

Notation "xe ⟲⟲ p" := (θ_map xe p) (at level 50) : cat. (* ⟲ agda-input \l C-N C-N C-N 2 the first time, \l the second time *)

Definition bifunctor_assoc {B C:Precategory} : [B^op, [C,SET]] -> [[B,C],SET].
Proof.
  intros X. refine (makeFunctor _ _ _ _).
  { intro F. exact (X ⟹ F). }
  { intros F F' p xe. exact (xe ⟲⟲ p). }
  { intros F. apply funextsec; intro xe. apply θ_subset.
    simpl. apply funextsec; intro b. apply arrow_mor_id. }
  { intros F F' F'' p q; simpl. apply funextsec; intro xe. apply θ_subset.
    simpl. apply funextsec; intro b. apply arrow_mor_mor_assoc. }
Defined.

(* *)
