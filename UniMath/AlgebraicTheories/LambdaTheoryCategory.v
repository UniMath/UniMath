(**************************************************************************************************

  The category of λ-theories

  Defines the category of λ-theories. The category is formalized via a stack of displayed
  categories. The displayed category structure is then leveraged to show that the category is
  univalent and has all limits.

  Contents
  1. The category of λ-theories [lambda_theory_cat]
  2. A characterization of iso's of λ-theories [make_lambda_theory_z_iso]
  3. Univalence [is_univalent_lambda_theory_cat]
  4. Limits [limits_lambda_theory_cat]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Limits.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms2.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.
Require Import UniMath.Combinatorics.Tuples.

Local Open Scope cat.

(** * 1. The category of λ-theories *)

Definition lambda_theory_data_disp_cat
  : disp_cat algebraic_theory_cat.
Proof.
  use disp_struct.
  - exact (λ (T : algebraic_theory),
      (∏ n, (T n : hSet) → (T (S n) : hSet)) ×
      (∏ n, (T (S n) : hSet) → (T n : hSet))).
  - exact (λ _ _ appabs appabs' (F : algebraic_theory_morphism _ _),
      (∏ n t, F _ ((pr1 appabs) n t) = (pr1 appabs') n (F _ t)) ×
      (∏ n t, F _ ((pr2 appabs) n t) = (pr2 appabs') n (F _ t))).
  - abstract (
      intros;
      apply isapropdirprod;
      do 2 (apply impred; intro);
      apply setproperty
    ).
  - abstract now intros.
  - abstract (
      intros ? ? ? ? ? ? ? ? Fdata F'data;
      split;
      do 2 intro;
      [ exact (maponpaths _ (pr1 Fdata _ _) @ (pr1 F'data _ _))
      | exact (maponpaths _ (pr2 Fdata _ _) @ (pr2 F'data _ _)) ]
    ).
Defined.

Definition lambda_theory_data_cat
  : category
  := total_category lambda_theory_data_disp_cat.

Section Test.
  Goal ob lambda_theory_data_cat = lambda_theory_data.
    exact (idpath _).
  Qed.
  Goal ∏ (L L' : lambda_theory_data),
    lambda_theory_data_cat⟦L, L'⟧ = lambda_theory_data_morphism L L'.
    exact (λ _ _, idpath _).
  Qed.
End Test.

Definition lambda_theory_disp_cat
  : disp_cat lambda_theory_data_cat
  := disp_full_sub lambda_theory_data_cat is_lambda_theory.

Definition lambda_theory_cat
  : category
  := total_category lambda_theory_disp_cat.

Section Test.
  Goal ob lambda_theory_cat = lambda_theory.
    exact (idpath _).
  Qed.
  Goal ∏ (L L' : lambda_theory), lambda_theory_cat⟦L, L'⟧ = lambda_theory_morphism L L'.
    exact (λ _ _, idpath _).
  Qed.
End Test.

(** * 2. A characterization of iso's of λ-theories *)

Section Iso.

  Context (a b : lambda_theory).
  Context (F : z_iso (C := algebraic_theory_cat) (a : algebraic_theory) (b : algebraic_theory)).
  Context (Happ : ∏ n f, (morphism_from_z_iso _ _ F : algebraic_theory_morphism _ _) (S n) (app f)
     = app ((morphism_from_z_iso _ _ F : algebraic_theory_morphism _ _) _ f)).
  Context (Habs : ∏ n f, (morphism_from_z_iso _ _ F : algebraic_theory_morphism _ _) n (abs f)
      = abs ((morphism_from_z_iso _ _ F : algebraic_theory_morphism _ _) _ f)).

  Definition iso_morphism
    : lambda_theory_morphism a b.
  Proof.
    use make_lambda_theory_morphism.
    use make_lambda_theory_data_morphism.
    - exact (morphism_from_z_iso _ _ F).
    - exact Happ.
    - exact Habs.
  Defined.

  Definition iso_inv_data
    : algebraic_theory_morphism b a
    := inv_from_z_iso F.

  Lemma iso_inv_preserves_app
    (n : nat)
    (f : (b n : hSet))
    : iso_inv_data (S n) (app f) = app (iso_inv_data n f).
  Proof.
    refine (!_ @ maponpaths
      (λ x, (x : algebraic_theory_morphism a a) (S n) _)
      (z_iso_inv_after_z_iso F)
    ).
    apply (maponpaths ((inv_from_z_iso F : algebraic_theory_morphism b a) (S n))).
    refine (Happ _ _ @ _).
    apply maponpaths.
    exact (maponpaths (λ x, (x : algebraic_theory_morphism b b) n f) (z_iso_after_z_iso_inv F)).
  Qed.

  Lemma iso_inv_preserves_abs
    (n : nat)
    (f : (b (S n) : hSet))
    : iso_inv_data n (abs f) = abs (iso_inv_data (S n) f).
  Proof.
    refine (!_ @ maponpaths
      (λ x, (x : algebraic_theory_morphism a a) _ _)
      (z_iso_inv_after_z_iso F)
    ).
    apply (maponpaths ((inv_from_z_iso F : algebraic_theory_morphism b a) n)).
    refine (Habs _ _ @ _).
    apply maponpaths.
    exact (maponpaths (λ x, (x : algebraic_theory_morphism b b) _ f) (z_iso_after_z_iso_inv F)).
  Qed.

  Definition iso_inv
    : lambda_theory_morphism b a
    := make_lambda_theory_morphism
      (make_lambda_theory_data_morphism
        iso_inv_data
        iso_inv_preserves_app
        iso_inv_preserves_abs
      ).

  Lemma iso_is_inverse
    : is_inverse_in_precat (C := lambda_theory_cat) iso_morphism iso_inv.
  Proof.
    split;
    (apply subtypePath;
    [ intro;
      apply isapropunit | ]);
    (apply subtypePath;
    [ intro;
      apply isapropdirprod;
      do 2 (apply impred_isaprop; intro);
      apply setproperty | ]).
    - apply (z_iso_inv_after_z_iso F).
    - apply (z_iso_after_z_iso_inv F).
  Qed.

  Definition make_lambda_theory_z_iso
    : z_iso (a : lambda_theory_cat) (b : lambda_theory_cat).
  Proof.
    use make_z_iso.
    - exact iso_morphism.
    - exact iso_inv.
    - exact iso_is_inverse.
  Defined.

End Iso.

(** * 3. Univalence *)

Lemma is_univalent_disp_lambda_theory_data_disp_cat
  : is_univalent_disp lambda_theory_data_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  refine (λ (T : algebraic_theory) _ _, _).
  use isweq_iso.
  - intro f.
    use pathsdirprod;
      do 2 (apply funextsec; intro);
      apply f.
  - intro e.
    refine (maponpaths (λ x, _ x _) _ @ maponpaths _ _ @ !(pathsdirprod_eta e));
    refine (pr1 ((_ : isaset _) _ _ _ _));
      do 2 (apply (impred 2); intro);
      apply setproperty.
  - intro.
    apply z_iso_eq.
    refine (pr1 ((_ : isaprop _) _ _)).
    apply isapropdirprod;
    do 2 (apply impred; intro);
    apply setproperty.
Qed.

Lemma is_univalent_lambda_theory_data_cat
  : is_univalent lambda_theory_data_cat.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_algebraic_theory_cat.
  - exact is_univalent_disp_lambda_theory_data_disp_cat.
Qed.

Lemma is_univalent_disp_lambda_theory_disp_cat
  : is_univalent_disp lambda_theory_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  exact isaprop_is_lambda_theory.
Qed.

Lemma is_univalent_lambda_theory_cat
  : is_univalent lambda_theory_cat.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_lambda_theory_data_cat.
  - exact is_univalent_disp_lambda_theory_disp_cat.
Qed.

(** * 4. Limits *)

Section Limits.

  Context (D := lambda_theory_data_disp_cat).
  Context {J : graph}.
  Context (d : diagram J (total_category D)).
  Context (L := limits_algebraic_theory_cat J (mapdiagram (pr1_category _) d)).

  Definition tip_lambda_theory_data_disp_cat
    : D (lim L).
  Proof.
    split.
    - intros n f.
      use tpair.
      + intro u.
        exact (pr12 (dob d u) _ (pr1 f u)).
      + abstract exact (λ u v e, pr12 (dmor d e) _ _ @ maponpaths _ (pr2 f _ _ _)).
    - intros n f.
      use tpair.
      + intro u.
        exact (pr22 (dob d u) _ (pr1 f u)).
      + abstract exact (λ u v e, pr22 (dmor d e) _ _ @ maponpaths _ (pr2 f _ _ _)).
  Defined.

  Lemma cone_lambda_theory_data_disp_cat
    (j : vertex J)
    : tip_lambda_theory_data_disp_cat -->[limOut L j] pr2 (dob d j).
  Proof.
    easy.
  Qed.

  Lemma is_limit_lambda_theory_data_disp_cat
    (d' : total_category D)
    (cone_out : ∏ u, d' --> (dob d u))
    (is_cone : ∏ u v e, cone_out u · (dmor d e) = cone_out v)
    (algebraic_theory_arrow := limArrow L _
      (make_cone (d := (mapdiagram (pr1_category D) d)) _
      (λ u v e, (maponpaths pr1 (is_cone u v e)))))
    : pr2 d' -->[algebraic_theory_arrow] tip_lambda_theory_data_disp_cat.
  Proof.
    split;
      intros n f;
      (apply subtypePath;
        [ intro;
          repeat (apply impred_isaprop; intro);
          apply setproperty | ]);
      apply funextsec;
      intro i.
    - exact (pr12 (cone_out i) n f).
    - exact (pr22 (cone_out i) n f).
  Qed.

End Limits.

Definition creates_limits_lambda_theory_data_disp_cat
  {J : graph}
  (d : diagram J (total_category lambda_theory_data_disp_cat))
  : creates_limit d (limits_algebraic_theory_cat _ _)
  := creates_limit_disp_struct _
    (tip_lambda_theory_data_disp_cat _)
    (cone_lambda_theory_data_disp_cat _)
    (is_limit_lambda_theory_data_disp_cat _).

Definition limits_lambda_theory_data_cat
  : Lims lambda_theory_data_cat
  := λ _ _, total_limit _ (creates_limits_lambda_theory_data_disp_cat _).

Definition creates_limits_lambda_theory_disp_cat
  {J : graph}
  (d : diagram J (total_category lambda_theory_disp_cat))
  : creates_limit d (limits_lambda_theory_data_cat _ _).
Proof.
  use creates_limit_disp_full_sub.
  - intro.
    repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply setproperty.
  - abstract (
      use make_is_lambda_theory';
      intros m n f g;
      (use subtypePath;
        [ intro;
          repeat (apply impred_isaprop; intro);
          apply setproperty
        | ];
        apply funextsec;
        intro u);
      [ refine (lambda_theory_app_compatible_with_comp _ _ @ _);
        unfold extended_composition;
        apply (maponpaths (comp (_ (pr1 f u))));
        apply extend_tuple_eq;
        [ intro i;
          now rewrite extend_tuple_inl
        | now rewrite extend_tuple_inr ]
      | refine (!_ @ lambda_theory_abs_compatible_with_comp _ _);
        unfold extended_composition;
        apply (maponpaths (λ x, abs (comp (pr1 f u) x)));
        apply extend_tuple_eq;
        [ intro i;
          now rewrite extend_tuple_inl
        | now rewrite extend_tuple_inr ]
      ]
      ).
Defined.

Definition limits_lambda_theory_cat
  : Lims lambda_theory_cat
  := λ _ _, total_limit _ (creates_limits_lambda_theory_disp_cat _).
