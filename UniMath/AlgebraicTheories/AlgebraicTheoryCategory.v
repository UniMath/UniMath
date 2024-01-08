(**************************************************************************************************

  The category of algebraic theories

  Defines the category of algebraic theories. The category is formalized via a stack of displayed
  categories and this displayed category structure is then leveraged to show that the category is
  univalent and has all limits.

  Contents
  1. The category of algebraic theories [algebraic_theory_cat]
  1.1. The category of algebraic theory data [algebraic_theory_data_cat]
  1.1.1. Temporary accessors
  1.1.2. Properties of the morphisms
  1.2. The category of algebraic theories
  1.2.1. Temporary accessors
  1.2.2. Two lemmas about algebraic theories [isaprop_is_algebraic_theory]
    [algebraic_theory_morphism_eq]
  2. A characterization of iso's of algebraic theories [make_algebraic_theory_z_iso]
  3. Univalence [is_univalent_algebraic_theory_cat]
  4. Limits [limits_algebraic_theory_cat]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
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

Require Import UniMath.AlgebraicTheories.IndexedSetCategory.

Local Open Scope cat.

(** * 1. The category of algebraic theories *)

(** ** 1.1. The category of algebraic theory data *)
Definition algebraic_theory_data_disp_cat
  : disp_cat (indexed_set_cat nat).
Proof.
  use disp_struct.
  - refine (λ T, _ × _).
    + exact (∏ n, stn n → T n).
    + exact (∏ m n, T m → (stn m → T n) → T n).
  - refine (λ T T' Tdata T'data F, _ × _).
    + exact (∏ n i, F _ (pr1 Tdata n i) = (pr1 T'data n i)).
    + exact (∏ m n f g, (F _ (pr2 Tdata m n f g)) = pr2 T'data m n (F _ f) (λ i, F _ (g i))).
  - abstract (
      intros;
      apply isapropdirprod;
      repeat (apply impred_isaprop; intro);
      apply setproperty
    ).
  - abstract easy.
  - abstract (
      intros T T' T'' Tdata T'data T''data F F' Fdata F'data;
      split;
      [ intros n i;
        exact (maponpaths _ (pr1 Fdata _ _) @ pr1 F'data _ _)
      | intros m n f g;
        refine (maponpaths _ (pr2 Fdata _ _ _ _) @ pr2 F'data _ _ _ _) ]
    ).
Defined.

Definition algebraic_theory_data_cat
  : category
  := total_category algebraic_theory_data_disp_cat.

(** *** 1.1.1. Temporary accessors *)

Local Definition data_set
  (T : algebraic_theory_data_cat)
  : nat → hSet
  := pr1 T.

Local Definition data_pr
  (T : algebraic_theory_data_cat)
  {n : nat}
  (i : stn n)
  : data_set T n
  := pr12 T n i.

Local Definition data_comp
  {T : algebraic_theory_data_cat}
  {m n : nat}
  (f : data_set T m)
  (g : stn m → data_set T n)
  : data_set T n
  := pr22 T m n f g.

Local Definition data_mor
  {T T' : algebraic_theory_data_cat}
  (F : T --> T')
  {n : nat}
  : data_set T n → data_set T' n
  := pr1 F n.

Local Definition data_mor_pr
  {T T' : algebraic_theory_data_cat}
  (F : T --> T')
  {n : nat}
  (i : stn n)
  : data_mor F (data_pr T i) = data_pr T' i
  := pr12 F n i.

Local Definition data_mor_comp
  {T T' : algebraic_theory_data_cat}
  (F : T --> T')
  {m n : nat}
  (f : data_set T m)
  (g : stn m → data_set T n)
  : data_mor F (data_comp f g) = data_comp (data_mor F f) (λ i, data_mor F (g i))
  := pr22 F m n f g.

(** *** 1.1.2. Properties of the morphisms *)

Definition mor_pr_ax
  {T T' : algebraic_theory_data_cat}
  (F : indexed_set_cat _ ⟦data_set T, data_set T'⟧)
  : UU
  := ∏ n i, F n (data_pr T i) = data_pr T' i.

Definition mor_comp_ax
  {T T' : algebraic_theory_data_cat}
  (F : indexed_set_cat _ ⟦data_set T, data_set T'⟧)
  : UU
  := ∏ m n f g, F n (data_comp f g) = data_comp (F m f) (λ i, F n (g i)).

(** ** 1.2. The category of algebraic theories  *)

Definition assoc_ax (T : algebraic_theory_data_cat) : UU := ∏
  (l m n : nat)
  (f_l : data_set T l)
  (f_m : stn l → data_set T m)
  (f_n : stn m → data_set T n),
    data_comp (data_comp f_l f_m) f_n = data_comp f_l (λ t_l, data_comp (f_m t_l) f_n).

Definition pr_comp_ax (T : algebraic_theory_data_cat) : UU := ∏
  (n : nat)
  (i : stn n)
  (f : stn n → data_set T n),
    data_comp (data_pr T i) f = f i.

Definition comp_pr_ax (T : algebraic_theory_data_cat) : UU := ∏
  (n : nat)
  (f : data_set T n),
    data_comp f (data_pr T) = f.

Definition is_algebraic_theory (T : algebraic_theory_data_cat) : UU :=
  assoc_ax T ×
  pr_comp_ax T ×
  comp_pr_ax T.

Definition algebraic_theory_disp_cat
  : disp_cat algebraic_theory_data_cat
  := disp_full_sub algebraic_theory_data_cat is_algebraic_theory.

Definition algebraic_theory_cat
  : category
  := total_category algebraic_theory_disp_cat.

(** *** 1.2.1. Temporary accessors *)

Local Definition theory_data
  (T : algebraic_theory_cat)
  : algebraic_theory_data_cat
  := pr1 T.

Local Definition theory_mor_data
  {T T' : algebraic_theory_cat}
  (F : algebraic_theory_cat⟦T, T'⟧)
  : algebraic_theory_data_cat⟦theory_data T, theory_data T'⟧
  := pr1 F.

Local Definition assoc
  (T : algebraic_theory_cat)
  {l m n : nat}
  (f_l : data_set (theory_data T) l)
  (f_m : stn l → data_set (theory_data T) m)
  (f_n : stn m → data_set (theory_data T) n)
  : data_comp (data_comp f_l f_m) f_n = data_comp f_l (λ t_l, data_comp (f_m t_l) f_n)
  := pr12 T l m n f_l f_m f_n.

Local Definition pr_comp
  (T : algebraic_theory_cat)
  {n : nat}
  (i : stn n)
  (f : stn n → data_set (theory_data T) n)
  : data_comp (data_pr (theory_data T) i) f = f i
  := pr122 T n i f.

Local Definition comp_pr
  (T : algebraic_theory_cat)
  {n : nat}
  (f : data_set (theory_data T) n)
  : data_comp f (data_pr (theory_data T)) = f
  := pr222 T n f.

(** *** 1.2.2. Two lemmas about algebraic theories *)

Lemma isaprop_is_algebraic_theory (T : algebraic_theory_data_cat) : isaprop (is_algebraic_theory T).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply setproperty.
Qed.

Lemma algebraic_theory_morphism_eq
  {T T' : algebraic_theory_cat}
  (F F' : algebraic_theory_cat⟦T, T'⟧)
  (H : ∏ n (x : data_set (theory_data T) n), data_mor (theory_mor_data F) x = data_mor (theory_mor_data F') x)
  : F = F'.
Proof.
  apply subtypePath.
  {
    intro.
    apply isapropunit.
  }
  apply subtypePath.
  {
    intro.
    apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply setproperty.
  }
  do 2 (apply funextsec; intro).
  apply H.
Qed.

(** * 2. A characterization of iso's of algebraic theories *)

Section Iso.

  Context (a b : algebraic_theory_cat).
  Context (F : ∏ (n : nat), z_iso (C := HSET) (data_set (theory_data a) n) (data_set (theory_data b) n)).
  Context (Hpr : ∏ (n : nat) (i : stn n), z_iso_mor (F n) (data_pr _ i) = data_pr _ i).
  Context (Hcomp : ∏ (m n : nat) (f : (data_set (theory_data a) m)) (g : stn m → (data_set (theory_data a) n)),
      z_iso_mor (F n) (data_comp f g)
      = data_comp (z_iso_mor (F m) f) (λ i, (z_iso_mor (F n) (g i)))).

  Definition make_algebraic_theory_z_iso_mor
    : algebraic_theory_cat⟦a, b⟧
    := (_ ,, Hpr ,, Hcomp) ,, tt.

  Definition make_algebraic_theory_z_iso_inv_data
    : indexed_set_cat _ ⟦data_set (theory_data b), data_set (theory_data a)⟧
    := λ n, inv_from_z_iso (F n).

  Lemma make_algebraic_theory_z_iso_inv_pr_ax
    : mor_pr_ax make_algebraic_theory_z_iso_inv_data.
  Proof.
    intros n i.
    refine (!_ @ maponpaths (λ x, x _) (z_iso_inv_after_z_iso (F n))).
    apply (maponpaths (inv_from_z_iso (F n))).
    apply Hpr.
  Qed.

  Lemma make_algebraic_theory_z_iso_inv_comp_ax
    : mor_comp_ax make_algebraic_theory_z_iso_inv_data.
  Proof.
    intros m n f g.
    refine (!_ @ maponpaths (λ x, x _) (z_iso_inv_after_z_iso (F n))).
    refine (maponpaths (λ x, inv_from_z_iso (F n) x) (Hcomp _ _ _ _) @ _).
    apply maponpaths.
    refine (maponpaths (λ x, data_comp (x f) _) (z_iso_after_z_iso_inv (F m)) @ _).
    apply maponpaths.
    apply funextfun.
    intro.
    exact (maponpaths (λ x, x (g _)) (z_iso_after_z_iso_inv (F n))).
  Qed.

  Definition make_algebraic_theory_z_iso_inv
    : algebraic_theory_cat⟦b, a⟧
    := (_ ,, make_algebraic_theory_z_iso_inv_pr_ax ,, make_algebraic_theory_z_iso_inv_comp_ax) ,, tt.

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

(** * 3. Univalence [is_univalent_algebraic_theory_cat] *)

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

(** * 4. Limits [limits_algebraic_theory_cat] *)

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
      + exact (λ u, data_pr (dob d u) i).
      + exact (λ _ _ e, data_mor_pr (dmor d e) i).
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
      [ apply assoc
      | apply pr_comp
      | apply comp_pr ]
    ).
Defined.

Definition limits_algebraic_theory_cat
  : Lims algebraic_theory_cat
  := λ _ _, total_limit
    (limits_algebraic_theory_data_cat _ _)
    (creates_limits_algebraic_theory_disp_cat _).
