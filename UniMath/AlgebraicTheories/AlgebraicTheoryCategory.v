(**************************************************************************************************

  Properties of the category of algebraic theories

  The displayed category structure is leveraged to show that the category is univalent and has all
  limits.

  Contents
  1. A characterization of iso's of algebraic theories [make_algebraic_theory_z_iso]
  2. Univalence [is_univalent_algebraic_theory_cat]
  3. Limits [limits_algebraic_theory_cat]

 **************************************************************************************************)
Require Export UniMath.AlgebraicTheories.AlgebraicTheoryCategoryCore.

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Limits.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.

Require Import UniMath.AlgebraicTheories.IndexedSetCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(** * 1. A characterization of iso's of algebraic theories *)

Section Iso.

  Context (a b : algebraic_theory).
  Context (F : ∏ (n : nat), z_iso (C := HSET) (a n) (b n)).
  Context (Hvar : ∏ n i, mor_var_ax (λ n, z_iso_mor (F n)) n i).
  Context (Hsubst : ∏ m n f g, mor_subst_ax (λ n, z_iso_mor (F n)) m n f g).

  Definition make_algebraic_theory_z_iso_mor
    : algebraic_theory_morphism a b
    := (_ ,, Hvar ,, Hsubst) ,, tt.

  Definition make_algebraic_theory_z_iso_inv_data
    : indexed_set_cat _ ⟦b, a⟧
    := λ n, inv_from_z_iso (F n).

  Lemma make_algebraic_theory_z_iso_inv_var_ax
    : ∏ n i, mor_var_ax make_algebraic_theory_z_iso_inv_data n i.
  Proof.
    intros n i.
    refine (!_ @ maponpaths (λ x, x _) (z_iso_inv_after_z_iso (F n))).
    apply (maponpaths (inv_from_z_iso (F n))).
    apply Hvar.
  Qed.

  Lemma make_algebraic_theory_z_iso_inv_subst_ax
    : ∏ m n f g, mor_subst_ax make_algebraic_theory_z_iso_inv_data m n f g.
  Proof.
    intros m n f g.
    refine (!_ @ maponpaths (λ x, x _) (z_iso_inv_after_z_iso (F n))).
    refine (maponpaths (λ x, inv_from_z_iso (F n) x) (Hsubst _ _ _ _) @ _).
    apply maponpaths.
    refine (maponpaths (λ x, (x f) • _) (z_iso_after_z_iso_inv (F m)) @ _).
    apply maponpaths.
    apply funextfun.
    intro.
    exact (maponpaths (λ x, x (g _)) (z_iso_after_z_iso_inv (F n))).
  Qed.

  Definition make_algebraic_theory_z_iso_inv
    : algebraic_theory_morphism b a
    := (_ ,, make_algebraic_theory_z_iso_inv_var_ax ,, make_algebraic_theory_z_iso_inv_subst_ax) ,, tt.

  Lemma make_algebraic_theory_z_iso_is_iso
    : is_inverse_in_precat (C := algebraic_theory_cat)
      make_algebraic_theory_z_iso_mor
      make_algebraic_theory_z_iso_inv.
  Proof.
    split;
      apply algebraic_theory_morphism_eq;
      intros n f;
      refine (eqtohomot _ f).
    - apply (z_iso_inv_after_z_iso (F n)).
    - apply (z_iso_after_z_iso_inv (F n)).
  Qed.

  Definition make_algebraic_theory_z_iso
    : z_iso (C := algebraic_theory_cat) a b
    := make_z_iso (C := algebraic_theory_cat)
      make_algebraic_theory_z_iso_mor
      make_algebraic_theory_z_iso_inv
      make_algebraic_theory_z_iso_is_iso.

End Iso.

(** * 2. Univalence *)

Lemma is_univalent_disp_algebraic_theory_data_disp_cat
  : is_univalent_disp algebraic_theory_data_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  intros T Tdata Tdata'.
  use isweq_iso.
  - intro f.
    apply pathsdirprod;
      repeat (apply funextsec; intro);
      apply (pr1 f).
  - intro.
    apply isasetdirprod;
      repeat (apply impred_isaset; intro);
      apply setproperty.
  - intro.
    apply z_iso_eq.
    apply subtypePath.
    {
      intro.
      do 4 (apply impred_isaprop; intro).
      apply setproperty.
    }
    do 2 (apply funextsec; intro).
    apply setproperty.
Qed.

Lemma is_univalent_algebraic_theory_data_cat
  : is_univalent algebraic_theory_data_cat.
Proof.
  apply is_univalent_total_category.
  - apply is_univalent_indexed_set_cat.
  - exact is_univalent_disp_algebraic_theory_data_disp_cat.
Qed.

Lemma is_univalent_disp_algebraic_theory_disp_cat
  : is_univalent_disp algebraic_theory_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  exact isaprop_is_algebraic_theory.
Qed.

Lemma is_univalent_algebraic_theory_cat
  : is_univalent algebraic_theory_cat.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_algebraic_theory_data_cat.
  - exact is_univalent_disp_algebraic_theory_disp_cat.
Qed.

(** * 3. Limits *)

Section AlgebraicTheoryLimits.

  Context (D := algebraic_theory_data_disp_cat).
  Context {J : graph}.
  Context (d : diagram J (total_category D)).
  Context (L := limits_indexed_set_cat _ J (mapdiagram (pr1_category _) d)).

  Definition tip_algebraic_theory_data_disp_cat
    : D (lim L).
  Proof.
    split.
    - intros n i.
      use tpair.
      + exact (λ u, var i).
      + exact (λ u v e, pr12 (dmor d e) _ i).
    - intros m n f g.
      use tpair.
      + exact (λ i, (pr1 f i) • (λ j, pr1 (g j) i)).
      + abstract (
          refine (λ u v e, pr22 (dmor d e) _ _ _ _ @ _);
          refine (maponpaths (λ x, x • _) _ @ maponpaths _ _);
          [ exact (pr2 f u v e)
          | apply funextfun;
            intro;
            exact (pr2 (g _) u v e) ]
        ).
  Defined.

  Lemma cone_algebraic_theory_data_disp_cat
    (j : vertex J)
    : tip_algebraic_theory_data_disp_cat -->[limOut L j] pr2 (dob d j).
  Proof.
    easy.
  Qed.

  Lemma uniqueness_algebraic_theory_data_disp_cat
    (d' : D (lim L))
    (cone_out : ∏ (j : vertex J), d' -->[limOut L j] (pr2 (dob d j)))
    : d' = tip_algebraic_theory_data_disp_cat.
  Proof.
    apply pathsdirprod.
    - do 2 (apply funextsec; intro).
      apply subtypePairEquality.
      {
        intro.
        repeat (apply impred_isaprop; intro).
        apply setproperty.
      }
      apply funextsec.
      intro.
      exact (pr1 (cone_out _) _ _).
    - do 4 (apply funextsec; intro).
      apply subtypePairEquality.
      {
        intro.
        repeat (apply impred_isaprop; intro).
        apply setproperty.
      }
      apply funextsec.
      intro.
      exact (pr2 (cone_out _) _ _ _ _).
  Qed.

  Lemma is_limit_algebraic_theory_data_disp_cat
    (d' : total_category D)
    (cone_out : ∏ (u : vertex J), d' --> (dob d u))
    (is_cone : ∏ (u v : vertex J) (e : edge u v), cone_out u · (dmor d e) = cone_out v)
    : pr2 d' -->[limArrow L _ (make_cone
        (d := (mapdiagram (pr1_category D) d)) _
        (λ u v e, (maponpaths pr1 (is_cone u v e))))
      ] tip_algebraic_theory_data_disp_cat.
  Proof.
    split.
    - intros n i.
      apply subtypePairEquality.
      {
        intro.
        repeat (apply impred_isaprop; intro).
        apply setproperty.
      }
      apply funextsec.
      intro u.
      exact (pr12 (cone_out u) n i).
    - intros m n f g.
      apply subtypePairEquality.
      {
        intro.
        repeat (apply impred_isaprop; intro).
        apply setproperty.
      }
      apply funextsec.
      intro i.
      exact (pr22 (cone_out i) m n f g).
  Qed.

End AlgebraicTheoryLimits.

Definition creates_limits_algebraic_theory_data_disp_cat
  {J : graph}
  (d : diagram J (total_category algebraic_theory_data_disp_cat))
  : creates_limit d (limits_indexed_set_cat _ J (mapdiagram (pr1_category _) d))
  := creates_limit_disp_struct _
    (tip_algebraic_theory_data_disp_cat _)
    (cone_algebraic_theory_data_disp_cat _)
    (is_limit_algebraic_theory_data_disp_cat _).

Definition creates_limits_unique_algebraic_theory_data_disp_cat
  {J : graph}
  (d : diagram J (total_category algebraic_theory_data_disp_cat))
  : creates_limit_unique d (limits_indexed_set_cat _ J (mapdiagram (pr1_category _) d))
  := creates_limit_unique_disp_struct
    (creates_limits_algebraic_theory_data_disp_cat _)
    (uniqueness_algebraic_theory_data_disp_cat _).

Definition limits_algebraic_theory_data_cat
  : Lims algebraic_theory_data_cat
  := λ _ _, total_limit _ (creates_limits_algebraic_theory_data_disp_cat _).

Definition creates_limits_algebraic_theory_disp_cat
  {J : graph}
  (d : diagram J (total_category algebraic_theory_disp_cat))
  : creates_limit d (limits_algebraic_theory_data_cat _ _).
Proof.
  apply creates_limit_disp_full_sub.
  - apply isaprop_is_algebraic_theory.
  - abstract (
      use (_ ,, _ ,, _);
        repeat intro;
        (use total2_paths_f;
        [ apply funextsec;
          intro
        | do 3 (apply impred_isaprop; intro);
          apply setproperty ]);
      [ apply subst_subst
      | apply var_subst
      | apply subst_var ]
    ).
Defined.

Definition limits_algebraic_theory_cat
  : Lims algebraic_theory_cat
  := λ _ _, total_limit
    (limits_algebraic_theory_data_cat _ _)
    (creates_limits_algebraic_theory_disp_cat _).
