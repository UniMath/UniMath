(**************************************************************************************************

  The category of algebraic theories

  Defines the category of algebraic theories. The category is formalized via a stack of displayed
  categories and this displayed category structure is then leveraged to show that the category is
  univalent and has all limits.

  Contents
  1. The category of algebraic theories [algebraic_theory_cat]
  2. A characterization of iso's of algebraic theories [make_algebraic_theory_z_iso]
  3. Univalence [is_univalent_algebraic_theory_cat]
  4. Limits [limits_algebraic_theory_cat]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
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
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.

Local Open Scope cat.

(** * 1. The category of algebraic theories *)

Definition algebraic_theory_data_disp_cat
  : disp_cat [finite_set_skeleton_category, HSET].
Proof.
  use disp_struct.
  - refine (λ (T : _ ⟶ _), _ × _).
    + exact (T 1 : hSet).
    + exact (∏ m n, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet)).
  - refine (λ T T' Tdata T'data (F : _ ⟹ _), _ × _).
    + exact (F _ (pr1 Tdata) = (pr1 T'data)).
    + exact (∏ m n f g, (F _ (pr2 Tdata m n f g)) = pr2 T'data m n (F _ f) (λ i, F _ (g i))).
  - abstract (
      intros;
      apply isapropdirprod;
      [ apply setproperty
      | repeat (apply impred_isaprop; intro);
        apply setproperty ]
    ).
  - abstract easy.
  - abstract (
      intros T T' T'' Tdata T'data T''data F F' Fdata F'data;
      split;
      [ exact (maponpaths _ (pr1 Fdata) @ pr1 F'data)
      | intros m n f g;
        refine (maponpaths _ (pr2 Fdata _ _ _ _) @ pr2 F'data _ _ _ _) ]
    ).
Defined.

Definition algebraic_theory_data_cat
  : category
  := total_category algebraic_theory_data_disp_cat.

Local Definition data_f_ob
  (T : algebraic_theory_data_cat)
  : finite_set_skeleton_category → hSet
  := pr11 T.

Local Definition data_f_mor
  {T : algebraic_theory_data_cat}
  {m n : nat}
  : finite_set_skeleton_category⟦m, n⟧ → HSET⟦data_f_ob T m, data_f_ob T n⟧
  := functor_on_morphisms (pr11 T).

Local Definition data_id (T : algebraic_theory_data_cat)
  : data_f_ob T 1
  := pr12 T.

Local Definition data_comp
  {T : algebraic_theory_data_cat}
  {m n : nat}
  (f : data_f_ob T m)
  (g : stn m → data_f_ob T n)
  : data_f_ob T n
  := pr22 T m n f g.

Local Definition data_mor
  {T T' : algebraic_theory_data_cat}
  (F : T --> T')
  {n : nat}
  : data_f_ob T n → data_f_ob T' n
  := pr11 F n.

Local Definition data_mor_id
  {T T' : algebraic_theory_data_cat}
  (F : T --> T')
  : data_mor F (data_id T) = data_id T'
  := pr12 F.

Local Definition data_mor_comp
  {T T' : algebraic_theory_data_cat}
  (F : T --> T')
  {m n : nat}
  (f : data_f_ob T m)
  (g : stn m → data_f_ob T n)
  : data_mor F (data_comp f g) = data_comp (data_mor F f) (λ i, data_mor F (g i))
  := pr22 F m n f g.

Definition comp_is_assoc (T : algebraic_theory_data_cat) : UU := ∏
  (l m n : nat)
  (f_l : data_f_ob T l)
  (f_m : stn l → data_f_ob T m)
  (f_n : stn m → data_f_ob T n),
    data_comp (data_comp f_l f_m) f_n = data_comp f_l (λ t_l, data_comp (f_m t_l) f_n).

Definition comp_is_unital (T : algebraic_theory_data_cat) : UU := ∏
  (n : nat)
  (f : data_f_ob T n),
    data_comp (data_id T) (λ _, f) = f.

Definition comp_identity_projections (T : algebraic_theory_data_cat) : UU := ∏
  (n : nat)
  (f : data_f_ob T n),
    data_comp f (λ i, data_f_mor (λ _, i) (data_id T)) = f.

Definition comp_is_natural_l (T : algebraic_theory_data_cat) : UU := ∏
  (m m' n : finite_set_skeleton_category)
  (a : finite_set_skeleton_category⟦m, m'⟧)
  (f : data_f_ob T m)
  (g : stn m' → data_f_ob T n),
  data_comp (data_f_mor a f) g = data_comp f (λ i, g (a i)).

Definition is_algebraic_theory (T : algebraic_theory_data_cat) : UU :=
  comp_is_assoc T ×
  comp_is_unital T ×
  comp_identity_projections T ×
  comp_is_natural_l T.

Lemma isaprop_is_algebraic_theory (T : algebraic_theory_data_cat) : isaprop (is_algebraic_theory T).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply setproperty.
Qed.

Definition algebraic_theory_disp_cat
  : disp_cat algebraic_theory_data_cat
  := disp_full_sub algebraic_theory_data_cat is_algebraic_theory.

Definition algebraic_theory_cat
  : category
  := total_category algebraic_theory_disp_cat.

Local Definition theory_data
  (T : algebraic_theory_cat)
  : algebraic_theory_data_cat
  := pr1 T.

Local Definition theory_assoc
  (T : algebraic_theory_cat)
  {l m n : nat}
  (f_l : data_f_ob (theory_data T) l)
  (f_m : stn l → data_f_ob (theory_data T) m)
  (f_n : stn m → data_f_ob (theory_data T) n)
  : data_comp (data_comp f_l f_m) f_n = data_comp f_l (λ t_l, data_comp (f_m t_l) f_n)
  := pr12 T l m n f_l f_m f_n.

Local Definition theory_id_comp
  {T : algebraic_theory_cat}
  {n : nat}
  (f : data_f_ob (theory_data T) n)
  : data_comp (data_id (theory_data T)) (λ _, f) = f
  := pr122 T n f.

Local Definition theory_comp_pr
  (T : algebraic_theory_cat)
  {n : nat}
  (f : data_f_ob (theory_data T) n)
  : data_comp f (λ i, data_f_mor (λ _, i) (data_id (theory_data T))) = f
  := pr1 (pr222 T) n f.

Local Definition theory_nat
  (T : algebraic_theory_cat)
  (m m' n : finite_set_skeleton_category)
  {a : finite_set_skeleton_category⟦m, m'⟧}
  (f : data_f_ob (theory_data T) m)
  (g : stn m' → data_f_ob (theory_data T) n)
  : data_comp (data_f_mor a f) g = data_comp f (λ i, g (a i))
  := pr2 (pr222 T) m m' n a f g.

(** * 2. A characterization of iso's of algebraic theories *)
(*
Section Iso.

  Context (a b : algebraic_theory).
  Context (F : ∏ (n : nat), z_iso (C := HSET) (a n : hSet) (b n : hSet)).
  Context (Hpr : ∏ (n : nat) (i : stn n), morphism_from_z_iso _ _ (F n) (pr i) = pr i).
  Context (Hcomp : ∏ (m n : nat) (f : (a m : hSet)) (g : stn m → (a n : hSet)),
      morphism_from_z_iso _ _ (F n) (f • g)
      = morphism_from_z_iso _ _ (F m) f • (λ i, (morphism_from_z_iso _ _ (F n) (g i)))).

  Definition make_algebraic_theory_z_iso_mor_data
    : algebraic_theory_morphism'_data a b
    := λ n, morphism_from_z_iso _ _ (F n).

  Lemma make_algebraic_theory_z_iso_is_mor
    : is_algebraic_theory_morphism' make_algebraic_theory_z_iso_mor_data.
  Proof.
    use make_is_algebraic_theory_morphism'.
    - exact Hcomp.
    - exact Hpr.
  Qed.

  Definition make_algebraic_theory_z_iso_mor
    : algebraic_theory_morphism a b
    := make_algebraic_theory_morphism' _ make_algebraic_theory_z_iso_is_mor.

  Definition make_algebraic_theory_z_iso_inv_data
    : algebraic_theory_morphism'_data b a
    := λ n, inv_from_z_iso (F n).

  Lemma make_algebraic_theory_z_iso_is_inv
    : is_algebraic_theory_morphism' make_algebraic_theory_z_iso_inv_data.
  Proof.
    use make_is_algebraic_theory_morphism'.
    - intros m n f g.
      refine (!_ @ maponpaths (λ x, x _) (z_iso_inv_after_z_iso (F n))).
      refine (maponpaths (λ x, inv_from_z_iso (F n) x) (Hcomp _ _ _ _) @ _).
      apply maponpaths.
      refine (maponpaths (λ x, (x f) • _) (z_iso_after_z_iso_inv (F m)) @ _).
      apply maponpaths.
      apply funextfun.
      intro.
      exact (maponpaths (λ x, x (g _)) (z_iso_after_z_iso_inv (F n))).
    - intros n i.
      refine (!_ @ maponpaths (λ x, x _) (z_iso_inv_after_z_iso (F n))).
      apply (maponpaths (inv_from_z_iso (F n))).
      apply Hpr.
  Qed.

  Definition make_algebraic_theory_z_iso_inv
    : algebraic_theory_morphism b a
    := make_algebraic_theory_morphism' _ make_algebraic_theory_z_iso_is_inv.

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

End Iso. *)

(** * 3. Univalence [is_univalent_algebraic_theory_cat] *)

Lemma is_univalent_disp_algebraic_theory_data_disp_cat
  : is_univalent_disp algebraic_theory_data_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  intros T Tdata Tdata'.
  use isweq_iso.
  - intro f.
    apply pathsdirprod.
    + exact (pr11 f).
    + do 4 (apply funextsec; intro).
      apply (pr21 f).
  - intro.
    apply isasetdirprod.
    + apply setproperty.
    + do 4 (apply impred_isaset; intro).
      apply setproperty.
  - intro.
    apply z_iso_eq.
    apply subtypePath.
    {
      intro.
      do 4 (apply impred_isaprop; intro).
      apply setproperty.
    }
    apply setproperty.
Qed.

Lemma is_univalent_algebraic_theory_data_cat
  : is_univalent algebraic_theory_data_cat.
Proof.
  apply is_univalent_total_category.
  - apply is_univalent_functor_category.
    apply is_univalent_HSET.
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

(** * 4. Limits [limits_algebraic_theory_cat] *)

Section AlgebraicTheoryLimits.

  Context (D := algebraic_theory_data_disp_cat).
  Context {J : graph}.
  Context (d : diagram J (total_category D)).
  Context (L := LimsFunctorCategory _ _ LimsHSET J (mapdiagram (pr1_category _) d)).

  Definition tip_algebraic_theory_data_disp_cat
    : D (lim L).
  Proof.
    split.
    - use tpair.
      + exact (λ i, data_id (dob d i)).
      + exact (λ _ _ e, data_mor_id (dmor d e)).
    - intros m n f g.
      use tpair.
      + exact (λ i, data_comp (pr1 f i) (λ j, pr1 (g j) i)).
      + abstract (
          refine (λ u v e, data_mor_comp (dmor d e) _ _ @ _);
          refine (maponpaths (λ x, data_comp x _) _ @ maponpaths _ _);
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
    - apply subtypePairEquality.
      {
        intro.
        repeat (apply impred_isaprop; intro).
        apply setproperty.
      }
      apply funextsec.
      intro.
      exact (pr1 (cone_out _)).
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
    - apply subtypePairEquality.
      {
        intro.
        repeat (apply impred_isaprop; intro).
        apply setproperty.
      }
      apply funextsec.
      intro i.
      exact (pr12 (cone_out i)).
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
  : creates_limit d (LimsFunctorCategory _ _ LimsHSET J (mapdiagram (pr1_category _) d))
  := creates_limit_disp_struct _
    (tip_algebraic_theory_data_disp_cat _)
    (cone_algebraic_theory_data_disp_cat _)
    (is_limit_algebraic_theory_data_disp_cat _).

Definition creates_limits_unique_algebraic_theory_data_disp_cat
  {J : graph}
  (d : diagram J (total_category algebraic_theory_data_disp_cat))
  : creates_limit_unique d (LimsFunctorCategory _ _ LimsHSET J (mapdiagram (pr1_category _) d))
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
      use (_ ,, _ ,, _ ,, _);
        repeat intro;
        (use total2_paths_f;
        [ apply funextsec;
          intro
        | do 3 (apply impred_isaprop; intro);
          apply setproperty ]);
      [ apply theory_assoc
      | apply (theory_id_comp (pr1 _ _))
      | apply theory_comp_pr
      | apply theory_nat ]
    ).
Defined.

Definition limits_algebraic_theory_cat
  : Lims algebraic_theory_cat
  := λ _ _, total_limit
    (limits_algebraic_theory_data_cat _ _)
    (creates_limits_algebraic_theory_disp_cat _).
