(********************************************************************************

 Oblique Morphisms in an Adjunction

 Author: B. Szilvasy
 January–October 2026

 Given an adjunction [θ : L ⊣ R] between [L : P ⟶ N] and [R : N ⟶ P], the
 oblique morphisms [f : oblique_mor θ (p : P) (n : N)] are pairs of morphisms
 [f♭ : N⟦L p, n⟧] and [f♯ : P⟦p, R n⟧] such that [f♯] is the transpose of [f♭]
 (via [φ_adj θ]).

 Contents:
 1. Definition and proofs of oblique morphisms
 1.1. Definition of oblique morphisms
 1.2. Constructors and compositions
 1.3. Linearity and thunkability of oblique morphisms

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Local Open Scope cat.

Declare Scope oblique_mor.
Delimit Scope oblique_mor with oblique_mor.
Local Open Scope oblique_mor.

(** ** Definition and proofs of oblique morphisms *)

Section oblique_mor_defs.
  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let η : functor_identity P ⟹ L ∙ R := adjunit θ.
  Let ε : R ∙ L ⟹ functor_identity N := adjcounit θ.

  (** *** Definition of oblique morphisms *)
  Definition oblique_mor (p : P) (n : N) : UU
    := ∑ (f : N⟦L p, n⟧) (g : P⟦p, R n⟧), φ_adj θ f = g.

  Definition oblique_mor_negative {p : P} {n : N} (f : oblique_mor p n)
    : N⟦L p, n⟧ := pr1 f.
  Definition oblique_mor_positive {p : P} {n : N} (f : oblique_mor p n)
    : P⟦p, R n⟧ := pr12 f.

  Local Notation "f '♭'" := (oblique_mor_negative f) (at level 4, format "f ♭") : oblique_mor.
  Local Notation "f '♯'" := (oblique_mor_positive f) (at level 4, format "f ♯") : oblique_mor.

  Definition oblique_mor_negative_transpose {p : P} {n : N} (f : oblique_mor p n)
    : φ_adj θ f♭ = f♯ := pr22 f.
  Definition oblique_mor_positive_transpose {p : P} {n : N} (f : oblique_mor p n)
    : φ_adj_inv θ f♯ = f♭.
  Proof.
    intermediate_path (φ_adj_inv θ (φ_adj θ f♭)).
    - apply maponpaths, pathsinv0, oblique_mor_negative_transpose.
    - apply φ_adj_inv_after_φ_adj.
  Qed.

  (** Construct an oblique morphism from a proof either with [φ_adj] or [φ_adj_inv]. *)
  Definition make_oblique_mor_forward {p : P} {n : N}
    (f : N⟦L p, n⟧) (g : P⟦p, R n⟧) (H : φ_adj θ f = g)
    : oblique_mor p n := f,,g,,H.
  Definition make_oblique_mor_backward {p : P} {n : N}
    (f : N⟦L p, n⟧) (g : P⟦p, R n⟧) (H : φ_adj_inv θ g = f)
    : oblique_mor p n.
  Proof.
    apply (make_oblique_mor_forward f g).
    abstract (apply (maponpaths (φ_adj θ)) in H;
              refine (!H @ _);
              apply φ_adj_after_φ_adj_inv).
  Defined.

  Definition oblique_mor_from_negative {p : P} {n : N}
    (f : N⟦L p, n⟧) : oblique_mor p n
    := make_oblique_mor_forward f _ (idpath _).
  Definition oblique_mor_from_positive {p : P} {n : N}
    (g : P⟦p, R n⟧) : oblique_mor p n
    := make_oblique_mor_backward _ g (idpath _).

  (** Negative injectivity/equivalence. *)
  Lemma weq_oblique_mor_negative (p : P) (n : N)
    : oblique_mor p n ≃ N⟦L p, n⟧.
  Proof.
    use remakeweqboth.
    - apply weqpr1; intro f.
      apply iscontr_paths_from.
    - apply oblique_mor_negative.
    - apply oblique_mor_from_negative.
    - easy.
    - easy.
  Defined.

  Definition isweq_oblique_mor_negative (p : P) (n : N)
    : isweq (@oblique_mor_negative p n)
    := weqproperty (weq_oblique_mor_negative p n).
  Definition weq_oblique_mor_from_negative (p : P) (n : N)
    : N⟦L p, n⟧ ≃ oblique_mor p n
    := invweq (weq_oblique_mor_negative p n).
  Definition isweq_oblique_mor_from_negative (p : P) (n : N)
    : isweq (@oblique_mor_from_negative p n)
    := weqproperty (weq_oblique_mor_from_negative p n).

  Lemma isaset_oblique_mor (p : P) (n : N) : isaset (oblique_mor p n).
  Proof.
    apply (isofhlevelweqb 2 (weq_oblique_mor_negative p n)).
    apply homset_property.
  Qed.

  Definition oblique_mor_negative_path_weq {p : P} {n : N}
    (f g : oblique_mor p n) : f = g ≃ f♭ = g♭.
  Proof.
    apply weqonpathsincl, isinclweq, isweq_oblique_mor_negative.
  Defined.
  Definition oblique_mor_negative_path {p : P} {n : N}
    (f g : oblique_mor p n) (H : f♭ = g♭) : f = g.
  Proof.
    now apply (invmap (oblique_mor_negative_path_weq f g)).
  Defined.

  (** Positive injectivity/equivalence. *)
  Lemma weq_oblique_mor_positive (p : P) (n : N)
    : oblique_mor p n ≃ P⟦p, R n⟧.
  Proof.
    use remakeweqboth.
    - intermediate_weq (∑ (g : P⟦p, R n⟧) (f : N⟦L p, n⟧), φ_adj θ f = g).
      { use weq_iso.
        - intros [f [g H]]; exact (g,, f,, H).
        - intros [f [g H]]; exact (g,, f,, H).
        - easy.
        - easy. }
      apply weqpr1; intro f.
      apply isweq_φ_adj.
    - apply oblique_mor_positive.
    - apply oblique_mor_from_positive.
    - easy.
    - intros f.
      now apply oblique_mor_negative_path.
  Defined.

  Definition isweq_oblique_mor_positive (p : P) (n : N)
    : isweq (@oblique_mor_positive p n)
    := weqproperty (weq_oblique_mor_positive p n).
  Definition weq_oblique_mor_from_positive (p : P) (n : N)
    : P⟦p, R n⟧ ≃ oblique_mor p n
    := invweq (weq_oblique_mor_positive p n).
  Definition isweq_oblique_mor_from_positive (p : P) (n : N)
    : isweq (@oblique_mor_from_positive p n)
    := weqproperty (weq_oblique_mor_from_positive p n).

  Definition oblique_mor_positive_path_weq {p : P} {n : N}
    (f g : oblique_mor p n) : f = g ≃ f♯ = g♯.
  Proof.
    apply weqonpathsincl, isinclweq, isweq_oblique_mor_positive.
  Defined.
  Definition oblique_mor_positive_path {p : P} {n : N}
    (f g : oblique_mor p n) (H : f♯ = g♯) : f = g.
  Proof.
    now apply (invmap (oblique_mor_positive_path_weq f g)).
  Defined.

  (** *** Constructors and compositions *)
  Definition oblique_positive_identity (p : P) : oblique_mor p (L p).
  Proof.
    use make_oblique_mor_forward.
    - exact (identity (L p)).
    - exact (η p).
    - apply φ_adj_identity.
  Defined.

  Definition oblique_negative_identity (n : N) : oblique_mor (R n) n.
  Proof.
    use make_oblique_mor_backward.
    - exact (ε n).
    - exact (identity (R n)).
    - apply φ_adj_inv_identity.
  Defined.

  (** Compose a negative morphism on the right *)
  Definition oblique_compose_negative {p : P} {n m : N}
    (f : oblique_mor p n) (g : N⟦n, m⟧) : oblique_mor p m.
  Proof.
    use make_oblique_mor_forward.
    - exact (f♭ · g).
    - exact (f♯ · #R g).
    - etrans; [apply φ_adj_natural_postcomp|].
      apply cancel_postcomposition.
      apply oblique_mor_negative_transpose.
  Defined.

  Definition oblique_compose_negative_identity {p : P} {n : N}
    (f : oblique_mor p n)
    : oblique_compose_negative f (identity n) = f.
  Proof. apply oblique_mor_negative_path, id_right. Qed.

  Definition oblique_compose_negative_compose {p : P} {n m r : N}
    (f : oblique_mor p n) (g : n --> m) (h : m --> r)
    : oblique_compose_negative f (g · h)
      = oblique_compose_negative (oblique_compose_negative f g) h.
  Proof. apply oblique_mor_negative_path, assoc. Qed.

  (** Compose a positive morphism on the left *)
  Definition oblique_compose_positive {p q : P} {n : N}
    (f : P⟦p, q⟧) (g : oblique_mor q n) : oblique_mor p n.
  Proof.
    use make_oblique_mor_backward.
    - exact (#L f · g♭).
    - exact (f · g♯).
    - etrans; [apply φ_adj_inv_natural_precomp|].
      apply cancel_precomposition.
      apply oblique_mor_positive_transpose.
  Defined.

  Definition oblique_compose_positive_identity {p : P} {n : N}
    (f : oblique_mor p n)
    : oblique_compose_positive (identity p) f = f.
  Proof. apply oblique_mor_positive_path, id_left. Qed.

  Definition oblique_compose_positive_compose {p q r : P} {n : N}
    (f : p --> q) (g : q --> r) (h : oblique_mor r n)
    : oblique_compose_positive (f · g) h
      = oblique_compose_positive f (oblique_compose_positive g h).
  Proof. apply oblique_mor_positive_path, assoc'. Qed.

  (** Combination *)
  Definition oblique_compose_negative_positive_comm {p q : P} {n m : N}
    (f : p --> q) (g : oblique_mor q n) (h : n --> m)
    : oblique_compose_negative (oblique_compose_positive f g) h
      = oblique_compose_positive f (oblique_compose_negative g h).
  Proof. apply oblique_mor_negative_path, assoc'. Qed.

  (** *** Linearity and thunkability of oblique morphisms *)

  Definition is_oblique_mor_linear
    {n m : N} (f : oblique_mor (R n) m) : UU
    := #(R ∙ L) (ε n) · f♭ = ε ((R ∙ L) n) · f♭.
  Lemma isaprop_is_oblique_mor_linear
    {n m : N} (f : oblique_mor (R n) m)
    : isaprop (is_oblique_mor_linear f).
  Proof. apply homset_property. Qed.

  Definition ish_oblique_mor_linear (n m : N)
    : hsubtype (oblique_mor (R n) m)
    := λ f, make_hProp
              (is_oblique_mor_linear f)
              (isaprop_is_oblique_mor_linear f).
  Definition oblique_linear_mor (n m : N) := carrier (ish_oblique_mor_linear n m).
  Coercion oblique_linear_mor_mor {n m : N} (f : oblique_linear_mor n m)
    : oblique_mor (R n) m := pr1carrier _ f.
  Coercion oblique_linear_mor_property {n m : N} (f : oblique_linear_mor n m)
    : is_oblique_mor_linear f := pr2 f.

  Definition is_oblique_mor_thunkable
    {p q : P} (f : oblique_mor p (L q)) : UU
    := f♯ · #(L ∙ R) (η q) = f♯ · η ((L ∙ R) q).
  Lemma isaprop_is_oblique_mor_thunkable
    {p q : P} (f : oblique_mor p (L q))
    : isaprop (is_oblique_mor_thunkable f).
  Proof. apply homset_property. Qed.

  Definition ish_oblique_mor_thunkable (p q : P)
    : hsubtype (oblique_mor p (L q))
    := λ f, make_hProp
              (is_oblique_mor_thunkable f)
              (isaprop_is_oblique_mor_thunkable f).
  Definition oblique_thunkable_mor (p q : P) := carrier (ish_oblique_mor_thunkable p q).
  Coercion oblique_thunkable_mor_mor {p q : P} (f : oblique_thunkable_mor p q)
    : oblique_mor p (L q) := pr1carrier _ f.
  Coercion oblique_thunkable_mor_property {p q : P} (f : oblique_thunkable_mor p q)
    : is_oblique_mor_thunkable f := pr2 f.

  (** Embed a negative morphism *)
  Definition oblique_lift_negative {n m : N}
    (f : n --> m) : oblique_linear_mor n m.
  Proof.
    use tpair.
    - use make_oblique_mor_backward.
      + exact (ε n · f).
      + exact (#R f).
      + etrans; [apply maponpaths, pathsinv0, id_left|].
        etrans; [apply φ_adj_inv_natural_postcomp|].
        apply cancel_postcomposition.
        apply φ_adj_inv_identity.
    - cbn; red; cbn.
      rewrite !assoc.
      apply cancel_postcomposition, (nat_trans_ax ε).
  Defined.

  (** Embed a positive morphism *)
  Definition oblique_lift_positive {p q : P}
    (f : p --> q) : oblique_thunkable_mor p q.
  Proof.
    use tpair.
    - use make_oblique_mor_forward.
      + exact (#L f).
      + exact (f · η q).
      + etrans; [apply maponpaths, pathsinv0, id_right|].
        etrans; [apply φ_adj_natural_precomp|].
        apply cancel_precomposition.
        apply φ_adj_identity.
    - cbn; red; cbn.
      rewrite !assoc'.
      apply cancel_precomposition, pathsinv0, (nat_trans_ax η).
  Defined.

  Definition is_negative_pre_fixed_point (n : N) : UU
    := #(R ∙ L) (ε n) = ε ((R ∙ L) n).
  Lemma isaprop_is_negative_pre_fixed_point (n : N)
    : isaprop (is_negative_pre_fixed_point n).
  Proof. apply homset_property. Qed.

  Definition is_negative_fixed_point (n : N) : UU
    := is_z_isomorphism (ε n).
  Identity Coercion Id_is_negative_fixed_point : is_negative_fixed_point >-> is_z_isomorphism.
  Lemma isaprop_is_negative_fixed_point (n : N)
    : isaprop (is_negative_fixed_point n).
  Proof. apply isaprop_is_z_isomorphism. Qed.

  Definition is_positive_pre_fixed_point (p : P) : UU
    := #(L ∙ R) (η p) = η ((L ∙ R) p).
  Lemma isaprop_is_positive_pre_fixed_point (p : P)
    : isaprop (is_positive_pre_fixed_point p).
  Proof. apply homset_property. Qed.

  Definition is_positive_fixed_point (p : P) : UU
    := is_z_isomorphism (η p).
  Identity Coercion Id_is_positive_fixed_point : is_positive_fixed_point >-> is_z_isomorphism.
  Lemma isaprop_is_positive_fixed_point (p : P)
    : isaprop (is_positive_fixed_point p).
  Proof. apply isaprop_is_z_isomorphism. Qed.

End oblique_mor_defs.
Arguments is_oblique_mor_linear / _.
Arguments is_oblique_mor_thunkable / _.

Notation "f '♭'" := (oblique_mor_negative _ f) (at level 4, format "f ♭") : oblique_mor.
Notation "f '♯'" := (oblique_mor_positive _ f) (at level 4, format "f ♯") : oblique_mor.
Notation "f '◅·' g" := (oblique_compose_positive _ f g) (at level 40, left associativity) : oblique_mor.
Notation "f '·▻' g" := (oblique_compose_negative _ f g) (at level 40, left associativity) : oblique_mor.
Notation "g '▻∘' f" := (f ·▻ g) (at level 40, left associativity, only parsing) : oblique_mor.
Notation "g '∘◅' f" := (f ◅· g) (at level 40, left associativity, only parsing) : oblique_mor.
