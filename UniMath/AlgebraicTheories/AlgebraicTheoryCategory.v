(* Defines the univalent category of algebraic theories and shows that it has all limits *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Limits.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms2.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(* Base category of functors from the finite set skeleton to HSET *)
Definition base_functor_category
  : category
  := [finite_set_skeleton_category, HSET].

Lemma is_univalent_base_functor_category
  : is_univalent base_functor_category.
Proof.
  apply is_univalent_functor_category.
  apply is_univalent_HSET.
Qed.

Definition limits_base_functor_category
  : Lims base_functor_category.
Proof.
  apply LimsFunctorCategory, LimsHSET.
Defined.

(* The category of functors T, together with a point in T 1 *)
Definition pointed_functor_disp_cat
  : disp_cat base_functor_category.
Proof.
  use disp_struct.
  - intro T.
    exact ((T : base_functor) 1 : hSet).
  - intros T T' Tdata T'data F.
    exact ((F : base_nat_trans _ _) _ Tdata = T'data).
  - abstract (intros; apply setproperty).
  - now intros.
  - abstract (
      intros T T' T'' e e' e'' F F' HF HF';
      now rewrite (!HF'), (!HF)
    ).
Defined.

Lemma is_univalent_disp_pointed_functor_disp_cat
  : is_univalent_disp pointed_functor_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  do 3 intro.
  use isweq_iso.
  - exact pr1.
  - intro.
    apply setproperty.
  - intro.
    apply z_iso_eq.
    apply setproperty.
Qed.

Section Limits.
  Context (D := pointed_functor_disp_cat).
  Context {J : graph}.
  Context (d : diagram J (total_category D)).
  Context (L := limits_base_functor_category J (mapdiagram (pr1_category _) d)).

  Definition tip_pointed_functor_disp_cat
    : D (lim L).
  Proof.
    use tpair.
    - exact (λ i, pr2 (dob d i)).
    - exact (λ _ _ e, pr2 (dmor d e)).
  Defined.

  Lemma cone_pointed_functor_disp_cat
    (j : vertex J)
    : tip_pointed_functor_disp_cat -->[limOut L j] pr2 (dob d j).
  Proof.
    easy.
  Qed.

  Lemma uniqueness_pointed_functor_disp_cat
    (d' : D (lim L))
    (cone_out : ∏ j, d' -->[limOut L j] (pr2 (dob d j)))
    : d' = tip_pointed_functor_disp_cat.
  Proof.
    apply subtypePairEquality.
    {
      intro.
      repeat (apply impred_isaprop; intro).
      apply setproperty.
    }
    apply funextsec.
    exact cone_out.
  Qed.

  Lemma is_limit_pointed_functor_disp_cat
    (d' : total_category D)
    (cone_out : ∏ u, d' --> (dob d u))
    (is_cone : ∏ u v e, cone_out u · (dmor d e) = cone_out v)
    : pr2 d' -->[limArrow L _ (make_cone
        (d := (mapdiagram (pr1_category D) d)) _
        (λ u v e, (maponpaths pr1 (is_cone u v e))))
      ] tip_pointed_functor_disp_cat.
  Proof.
    apply subtypePairEquality.
    {
      intro.
      repeat (apply impred_isaprop; intro).
      apply setproperty.
    }
    apply funextsec.
    intro i.
    exact (pr2 (cone_out i)).
  Qed.

End Limits.

Definition creates_limits_pointed_functor_disp_cat
  {J : graph}
  (d : diagram J _)
  : creates_limit pointed_functor_disp_cat d (limits_base_functor_category _ _)
  := creates_limit_disp_struct _
    (tip_pointed_functor_disp_cat _)
    (cone_pointed_functor_disp_cat _)
    (is_limit_pointed_functor_disp_cat _).

Definition pointed_functor_cat
  : category
  := total_category pointed_functor_disp_cat.

Lemma is_univalent_pointed_functor_cat
  : is_univalent pointed_functor_cat.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_base_functor_category.
  - exact is_univalent_disp_pointed_functor_disp_cat.
Qed.

Definition limits_pointed_functor_cat
  : Lims pointed_functor_cat
  := λ _ _, total_limit _
    (limits_base_functor_category _ _)
    (creates_limits_pointed_functor_disp_cat _).

(* The category of algebraic theory data *)
Definition algebraic_theory_data_disp_cat
  : disp_cat pointed_functor_cat.
Proof.
  use disp_struct.
  - exact (λ (T : pointed_functor), ∏ m n, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet)).
  - exact (λ T T' Tdata T'data (F : pointed_functor_morphism T T'),
      ∏ m n f g, (F _ (Tdata m n f g)) = T'data m n (F _ f) (λ i, F _ (g i))).
  - abstract (
      intros;
      repeat (apply impred_isaprop; intro);
      apply setproperty
    ).
  - abstract easy.
  - abstract (
      intros T T' T'' Tdata T'data T''data F F' Fdata F'data m n f g;
      refine (maponpaths _ (Fdata _ _ _ _) @ _);
      apply F'data
    ).
Defined.

Lemma is_univalent_disp_algebraic_theory_data_disp_cat
  : is_univalent_disp algebraic_theory_data_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  intros T comp comp'.
  use isweq_iso.
  - intro f.
    do 4 (apply funextsec; intro).
    apply (pr1 f _).
  - intro.
    refine (pr1 ((_ : isaset algebraic_theory_data_disp_cat[{T}]) _ _ _ _)).
    do 4 (apply impred_isaset; intro).
    apply setproperty.
  - intro.
    apply z_iso_eq.
    do 4 (apply impred_isaprop; intro).
    apply setproperty.
Qed.

Section Limits.
  Context (D := algebraic_theory_data_disp_cat).
  Context {J : graph}.
  Context (d : diagram J (total_category D)).
  Context (L := limits_pointed_functor_cat J (mapdiagram (pr1_category _) d)).

  Definition tip_algebraic_theory_data_disp_cat
    : D (lim L).
  Proof.
    intros m n f g.
    use tpair.
    - exact (λ i, (pr1 f) i • (λ j, pr1 (g j) i)).
    - abstract (
        refine (λ u v e, pr2 (dmor d e) _ _ _ _ @ _);
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
    (cone_out : ∏ j, d' -->[limOut L j] (pr2 (dob d j)))
    : d' = tip_algebraic_theory_data_disp_cat.
  Proof.
    do 4 (apply funextsec; intro).
    apply subtypePairEquality.
    {
      intro.
      repeat (apply impred_isaprop; intro).
      apply setproperty.
    }
    apply funextsec.
    intro.
    exact (cone_out _ _ _ _ _).
  Qed.

  Lemma is_limit_algebraic_theory_data_disp_cat
    (d' : total_category D)
    (cone_out : ∏ u, d' --> (dob d u))
    (is_cone : ∏ u v e, cone_out u · (dmor d e) = cone_out v)
    : pr2 d' -->[limArrow L _ (make_cone
        (d := (mapdiagram (pr1_category D) d)) _
        (λ u v e, (maponpaths pr1 (is_cone u v e))))
      ] tip_algebraic_theory_data_disp_cat.
  Proof.
    intros m n f g.
    apply subtypePairEquality.
    {
      intro.
      repeat (apply impred_isaprop; intro).
      exact (setproperty _ _ _).
    }
    apply funextsec.
    intro i.
    exact (pr2 (cone_out i) m n f g).
  Qed.

End Limits.

Definition creates_limits_algebraic_theory_data_disp_cat
  {J : graph}
  (d : diagram J _)
  : creates_limit algebraic_theory_data_disp_cat d (limits_pointed_functor_cat _ _)
  := creates_limit_disp_struct _
    (tip_algebraic_theory_data_disp_cat _)
    (cone_algebraic_theory_data_disp_cat _)
    (is_limit_algebraic_theory_data_disp_cat _).

Definition creates_limits_unique_algebraic_theory_data_disp_cat
  {J : graph}
  (d : diagram J _)
  : creates_limit_unique algebraic_theory_data_disp_cat d (limits_pointed_functor_cat _ _)
  := creates_limit_unique_disp_struct _
    (creates_limits_algebraic_theory_data_disp_cat _)
    (uniqueness_algebraic_theory_data_disp_cat _).

Definition algebraic_theory_data_cat
  : category
  := total_category algebraic_theory_data_disp_cat.

Lemma is_univalent_algebraic_theory_data_cat
  : is_univalent algebraic_theory_data_cat.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_pointed_functor_cat.
  - exact is_univalent_disp_algebraic_theory_data_disp_cat.
Qed.

Definition limits_algebraic_theory_data_cat
  : Lims algebraic_theory_data_cat
  := λ _ _, total_limit _ _ (creates_limits_algebraic_theory_data_disp_cat _).

(* The category of algebraic theories *)
Definition algebraic_theory_disp_cat
  : disp_cat algebraic_theory_data_cat
  := disp_full_sub algebraic_theory_data_cat is_algebraic_theory.

Lemma is_univalent_disp_algebraic_theory_disp_cat
  : is_univalent_disp algebraic_theory_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  exact isaprop_is_algebraic_theory.
Qed.

Definition creates_limits_algebraic_theory_disp_cat
  {J : graph}
  (d : diagram J _)
  : creates_limit algebraic_theory_disp_cat d (limits_algebraic_theory_data_cat _ _).
Proof.
  apply creates_limit_disp_full_sub.
  - apply isaprop_is_algebraic_theory.
  - abstract (
      use make_is_algebraic_theory;
        repeat intro;
        (use total2_paths_f;
        [ apply funextsec;
          intro
        | do 3 (apply impred_isaprop; intro);
          apply setproperty ]);
      [ apply algebraic_theory_comp_is_assoc
      | apply (algebraic_theory_comp_is_unital _ _ (pr1 _ _))
      | apply algebraic_theory_comp_identity_projections
      | apply algebraic_theory_comp_is_natural_l ]
    ).
Defined.

Definition algebraic_theory_cat
  : category
  := total_category algebraic_theory_disp_cat.

Lemma is_univalent_algebraic_theory_cat
  : is_univalent algebraic_theory_cat.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_algebraic_theory_data_cat.
  - exact is_univalent_disp_algebraic_theory_disp_cat.
Qed.

Definition limits_algebraic_theory_cat
  : Lims algebraic_theory_cat
  := λ _ _, total_limit _
    (limits_algebraic_theory_data_cat _ _)
    (creates_limits_algebraic_theory_disp_cat _).

Definition algebraic_theory_univalent_category
  : univalent_category
  := make_univalent_category _ is_univalent_algebraic_theory_cat.

Definition make_algebraic_theory_z_iso
  (a b : algebraic_theory)
  (F : ∏ n, z_iso (C := HSET) (a n : hSet) (b n : hSet))
  (Hpr : ∏ n i, morphism_from_z_iso _ _ (F n) (pr i) = pr i)
  (Hcomp : ∏ m n f (g : stn m → (a n : hSet)),
    morphism_from_z_iso _ _ (F n) (f • g)
    = morphism_from_z_iso _ _ (F m) f • (λ i, (morphism_from_z_iso _ _ (F n) (g i))))
  : z_iso (a : algebraic_theory_cat) (b : algebraic_theory_cat).
Proof.
  use make_z_iso.
  - use make_algebraic_theory_morphism'.
    + intro n.
      exact (morphism_from_z_iso _ _ (F n)).
    + abstract (
        split;
        [ exact Hcomp
        | exact Hpr ]
      ).
  - use make_algebraic_theory_morphism'.
    + intro n.
      exact (inv_from_z_iso (F n)).
    + abstract (
        split;
        [ intros m n f g;
          refine (!_ @ maponpaths (λ x, x _) (z_iso_inv_after_z_iso (F n)));
          refine (maponpaths (λ x, inv_from_z_iso (F n) x) (Hcomp _ _ _ _) @ _);
          apply maponpaths;
          refine (maponpaths (λ x, (x f) • _) (z_iso_after_z_iso_inv (F m)) @ _);
          apply maponpaths;
          apply funextfun;
          intro;
          exact (maponpaths (λ x, x (g _)) (z_iso_after_z_iso_inv (F n)))
        | intros n i;
          refine (!_ @ maponpaths (λ x, x _) (z_iso_inv_after_z_iso (F n)));
          apply (maponpaths (inv_from_z_iso (F n)));
          apply Hpr ]
      ).
  - abstract (
      split;
      ( apply subtypePath;
        [ intro;
          apply isapropunit | ]);
      ( apply subtypePath;
        [ intro;
          repeat (apply impred_isaprop; intro);
          apply setproperty | ]);
      ( apply subtypePath;
        [ intro;
          apply setproperty | ] );
      ( apply subtypePath;
        [ intro;
          repeat (apply impred_isaprop; intro);
          apply homset_property | ] );
      apply funextsec;
      intro n;
      [ apply (z_iso_inv_after_z_iso (F n)) |
        apply (z_iso_after_z_iso_inv (F n)) ]
    ).
Defined.
