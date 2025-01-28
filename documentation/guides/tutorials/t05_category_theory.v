Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.opp_precat.

Local Open Scope cat.

Coercion HLevel_to_type
  {n : nat}
  (X : HLevel n)
  : UU
  := pr1 X.

Definition hlevel_property
  {n : nat}
  (X : HLevel n)
  : isofhlevel n X
  := pr2 X.

Section PathCategory.

  Context (X : UU).
  Context (H : isofhlevel 3 X).

  Definition path_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - use make_precategory_ob_mor.
      + exact X.
      + intros a b.
        exact (a = b).
    - exact idpath.
    - intros a b c f g.
      exact (f @ g).
  Defined.

  Lemma path_is_precategory
    : is_precategory path_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros a b f.
      reflexivity.
    - intros a b f.
      apply pathscomp0rid.
    - intros a b c d f g h.
      apply path_assoc.
  Qed.

  Lemma path_has_homsets
    : has_homsets path_precategory_data.
  Proof.
    intros a b.
    exact (H a b).
  Qed.

End PathCategory.

Definition path_category
  (X : HLevel 3)
  : category
  :=
  make_category
    (make_precategory
      (path_precategory_data X)
      (path_is_precategory X))
    (path_has_homsets _ (hlevel_property X)).

Definition path_category_morphism_is_iso
  {X : HLevel 3}
  {a b : path_category X}
  (f : a --> b)
  : is_z_isomorphism f.
Proof.
  use make_is_z_isomorphism.
  - exact (!f).
  - split.
    + apply pathsinv0r.
    + apply pathsinv0l.
Defined.

Definition path_category_morphism_iso
  {X : HLevel 3}
  {a b : path_category X}
  (f : a --> b)
  : z_iso a b
  := make_z_iso'
    f
    (path_category_morphism_is_iso f).

Definition path_category_involution_functor_data
  (X : HLevel 3)
  : functor_data (path_category X) (path_category X)^op.
Proof.
  use make_functor_data.
  - intro x.
    exact x.
  - intros a b f.
    exact (!f).
Defined.

Lemma path_category_involution_is_functor
  (X : HLevel 3)
  : is_functor (path_category_involution_functor_data X).
Proof.
  split.
  - intro x.
    reflexivity.
  - intros x y z.
    exact pathscomp_inv.
Qed.

Definition path_category_involution
  (X : HLevel 3)
  : path_category X ⟶ (path_category X)^op
  := make_functor
    (path_category_involution_functor_data X)
    (path_category_involution_is_functor X).

Definition path_category_involution_essentially_surjective
  (X : HLevel 3)
  : split_essentially_surjective (path_category_involution X).
Proof.
  intro x.
  exists x.
  exact (identity_z_iso x).
Defined.

Definition path_category_fully_faithful
  (X : HLevel 3)
  : fully_faithful (path_category_involution X).
Proof.
  intros x y.
  use isweq_iso.
  - intro f.
    exact (!f).
  - exact pathsinv0inv0.
  - exact pathsinv0inv0.
Defined.

Definition path_category_involution_nat_iso
  (X : HLevel 3)
  : nat_z_iso
    (path_category_involution X ∙ functor_opp (path_category_involution X))
    (functor_identity (path_category X)).
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + intro x.
      exact (idpath x).
    + intros x y f.
      refine (pathscomp0rid _ @ _).
      exact (pathsinv0inv0 f).
  - intro x.
    apply (is_z_isomorphism_identity x).
Defined.

Definition path_category_involution_iso
  (X : HLevel 3)
  : z_iso (C := [path_category X, path_category X])
    (path_category_involution X ∙ functor_opp (path_category_involution X))
    (functor_identity (path_category X))
  := invmap
    (z_iso_is_nat_z_iso (D := path_category X) _ _)
    (path_category_involution_nat_iso X).

Lemma is_univalent_path_category
  (X : HLevel 3)
  : is_univalent (path_category X).
Proof.
  intros a b.
  use isweq_iso.
  - exact z_iso_mor.
  - intro x.
    induction x.
    reflexivity.
  - intro y.
    apply z_iso_eq.
    induction (z_iso_mor y).
    reflexivity.
Qed.

Lemma involution_is_involution
  (X : HLevel 3)
  : path_category_involution X ∙ functor_opp (path_category_involution X)
  = functor_identity (path_category X).
Proof.
  use (isotoid _ _ (path_category_involution_iso X)).
  apply is_univalent_functor_category.
  apply is_univalent_path_category.
Qed.

Lemma path_category_terminal_contr
  (X : HLevel 3)
  : Terminal (path_category X) → iscontr X.
Proof.
  intro T.
  exists (T : path_category X).
  intro x.
  exact (TerminalArrow T x).
Qed.
