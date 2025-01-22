Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

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

Lemma is_univalent_path_category
  (X : HLevel 3)
  : is_univalent (path_category X).
Proof.
  intros a b.
  use isweq_iso.
  - exact z_iso_mor.
  - intro x.
    now induction x.
  - intro y.
    apply z_iso_eq.
    now induction (z_iso_mor y).
Qed.
