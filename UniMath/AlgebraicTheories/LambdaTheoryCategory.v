(**************************************************************************************************

  The category of λ-theories

  Defines the category of λ-theories. The category is formalized via a stack of displayed
  categories. The displayed category structure is then leveraged to show that the category is
  univalent and has all limits.

  Contents
  1. The category of λ-theories [lambda_theory_cat]
  1.1. The category of λ-theory data [lambda_theory_data_cat]
  1.1.1. Temporary accessors
  1.1.2. Properties of the morphisms
  1.2. The category of λtheories
  1.2.1. Temporary accessors
  1.2.2. Two lemmas about λ-theories [isaprop_is_lambda_theory]
    [lambda_theory_morphism_eq]
  2. A characterization of iso's of λ-theories [make_lambda_theory_z_iso]
  3. Univalence [is_univalent_lambda_theory_cat]
  4. Limits [limits_lambda_theory_cat]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
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
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.Combinatorics.Tuples.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Section LambdaTheoryCategory.

(** * 1. The category of λ-theories *)
(** ** 1.1. The category of λ-theory data *)

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

(** *** 1.1.1. Temporary accessors *)

  Let data_theory
    (L : lambda_theory_data_cat)
    : algebraic_theory
    := pr1 L.

  Let data_app
    {L : lambda_theory_data_cat}
    {n : nat}
    (f : data_theory L n)
    : data_theory L (S n)
    := pr12 L n f.

  Let data_abs
    {L : lambda_theory_data_cat}
    {n : nat}
    (f : data_theory L (S n))
    : data_theory L n
    := pr22 L n f.

  Let data_mor
    {L L' : lambda_theory_data_cat}
    (F : lambda_theory_data_cat⟦L, L'⟧)
    : algebraic_theory_morphism (data_theory L) (data_theory L')
    := pr1 F.

  Let data_mor_app
    {L L' : lambda_theory_data_cat}
    (F : lambda_theory_data_cat⟦L, L'⟧)
    {n : nat}
    (f : data_theory L n)
    : data_mor F (S n) (data_app f) = data_app (data_mor F n f)
    := pr12 F n f.

  Let data_mor_abs
    {L L' : lambda_theory_data_cat}
    (F : lambda_theory_data_cat⟦L, L'⟧)
    {n : nat}
    (f : data_theory L (S n))
    : data_mor F n (data_abs f) = data_abs (data_mor F (S n) f)
    := pr22 F n f.

(** *** 1.1.2. Properties of the morphisms *)

  Definition mor_app_ax
    {L L' : lambda_theory_data_cat}
    (F : algebraic_theory_morphism (data_theory L) (data_theory L'))
    : UU
    := ∏ n f, F (S n) (data_app f) = data_app (F n f).

  Definition mor_abs_ax
    {L L' : lambda_theory_data_cat}
    (F : algebraic_theory_morphism (data_theory L) (data_theory L'))
    : UU
    := ∏ n f, F n (data_abs f) = data_abs (F (S n) f).

  Definition is_lambda_theory_morphism
    {L L' : lambda_theory_data_cat}
    (F : algebraic_theory_morphism (data_theory L) (data_theory L'))
    : UU
    := mor_app_ax F × mor_abs_ax F.

(** ** 1.2. The category of λtheories *)

  Definition extended_composition
    {T : algebraic_theory_data}
    {m n : nat}
    (f : T (S m))
    (g : stn m → T n)
    : T (S n)
    := f • (extend_tuple (λ i, (g i) • (λ i, pr (dni lastelement i))) (pr lastelement)).

  Definition app_comp_ax (L : lambda_theory_data_cat)
    : UU
    := ∏ m n f (g : stn m → data_theory L n), data_app (f • g) = extended_composition (data_app f) g.

  Definition abs_comp_ax (L : lambda_theory_data_cat)
    : UU
    := ∏ m n f (g : stn m → data_theory L n), data_abs (extended_composition f g) = (data_abs f) • g.

  Definition is_lambda_theory (L : lambda_theory_data_cat) : UU
    := app_comp_ax L × abs_comp_ax L.

  Definition lambda_theory_disp_cat
    : disp_cat lambda_theory_data_cat
    := disp_full_sub lambda_theory_data_cat is_lambda_theory.

  Definition lambda_theory_cat
    : category
    := total_category lambda_theory_disp_cat.

(** *** 1.2.1. Temporary accessors *)

  Let theory_data
    (L : lambda_theory_cat)
    : lambda_theory_data_cat
    := pr1 L.

  Let theory_mor_data
    {T T' : lambda_theory_cat}
    (F : lambda_theory_cat⟦T, T'⟧)
    : lambda_theory_data_cat⟦theory_data T, theory_data T'⟧
    := pr1 F.

  Let app_comp
    (L : lambda_theory_cat)
    {m n : nat}
    (f : data_theory (theory_data L) m)
    (g : stn m → data_theory (theory_data L) n)
    : data_app (f • g) = extended_composition (data_app f) g
    := pr12 L m n f g.

  Let abs_comp
    (L : lambda_theory_cat)
    {m n : nat}
    (f : data_theory (theory_data L) (S m))
    (g : stn m → data_theory (theory_data L) n)
    : data_abs (extended_composition f g) = (data_abs f) • g
    := pr22 L m n f g.

(** *** 1.2.2. Two lemmas about λ-theories *)

  Lemma isaprop_is_lambda_theory
    (L : lambda_theory_data_cat)
    : isaprop (is_lambda_theory L).
  Proof.
    repeat apply isapropdirprod;
    do 4 (apply impred; intro);
    apply setproperty.
  Qed.

  Lemma lambda_theory_morphism_eq
    {L L' : lambda_theory_cat}
    (F F' : lambda_theory_cat⟦L, L'⟧)
    (H : data_mor (theory_mor_data F) = data_mor (theory_mor_data F'))
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
        do 2 (apply impred_isaprop; intro);
        apply setproperty.
    }
    apply H.
  Qed.

(** * 2. A characterization of iso's of λ-theories *)

  Section Iso.

    Context (a b : lambda_theory_cat).
    Context (F : z_iso (C := algebraic_theory_cat) (data_theory (theory_data a)) (data_theory (theory_data b))).
    Context (Happ : mor_app_ax (z_iso_mor F)).
    Context (Habs : mor_abs_ax (z_iso_mor F)).

    Definition iso_mor
      : lambda_theory_cat⟦a, b⟧
      := (morphism_from_z_iso _ _ F ,, Happ ,, Habs) ,, tt.

    Definition iso_inv_data
      : algebraic_theory_morphism (data_theory (theory_data b)) (data_theory (theory_data a))
      := inv_from_z_iso F.

    Lemma iso_inv_app_ax
      : mor_app_ax iso_inv_data.
    Proof.
      intros n f.
      refine (!_ @ maponpaths
        (λ x, (x : algebraic_theory_morphism _ _) (S n) _)
        (z_iso_inv_after_z_iso F)
      ).
      apply (maponpaths ((inv_from_z_iso F : algebraic_theory_morphism _ _) (S n))).
      refine (Happ _ _ @ _).
      apply maponpaths.
      exact (maponpaths (λ x, (x : algebraic_theory_morphism _ _) n f) (z_iso_after_z_iso_inv F)).
    Qed.

    Lemma iso_inv_abs_ax
      : mor_abs_ax iso_inv_data.
    Proof.
      intros n f.
      refine (!_ @ maponpaths
        (λ x, (x : algebraic_theory_morphism _ _) _ _)
        (z_iso_inv_after_z_iso F)
      ).
      apply (maponpaths ((inv_from_z_iso F : algebraic_theory_morphism _ _) n)).
      refine (Habs _ _ @ _).
      apply maponpaths.
      exact (maponpaths (λ x, (x : algebraic_theory_morphism _ _) _ f) (z_iso_after_z_iso_inv F)).
    Qed.

    Definition iso_inv
      : lambda_theory_cat⟦b, a⟧
      := (iso_inv_data ,,
          iso_inv_app_ax ,,
          iso_inv_abs_ax
        ) ,, tt.

    Lemma iso_is_inverse
      : is_inverse_in_precat (C := lambda_theory_cat) iso_mor iso_inv.
    Proof.
      split;
        apply lambda_theory_morphism_eq.
      - apply (z_iso_inv_after_z_iso F).
      - apply (z_iso_after_z_iso_inv F).
    Qed.

    Definition make_lambda_theory_z_iso
      : z_iso (a : lambda_theory_cat) (b : lambda_theory_cat).
    Proof.
      use make_z_iso.
      - exact iso_mor.
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
        split;
        intros m n f g;
        (use subtypePath;
          [ intro;
            do 3 (apply impred_isaprop; intro);
            apply setproperty
          | ];
          apply funextsec;
          intro u);
        [ refine (app_comp _ _ _ @ _);
          apply (maponpaths (comp (_ (pr1 f u))));
          apply extend_tuple_eq;
          [ intro i;
            now rewrite extend_tuple_inl
          | now rewrite extend_tuple_inr ]
        | refine (!_ @ abs_comp _ _ _);
          apply (maponpaths (λ x, data_abs (comp (pr1 f u) x)));
          apply extend_tuple_eq;
          [ intro i;
            now rewrite extend_tuple_inl
          | now rewrite extend_tuple_inr ] ]
      ).
  Defined.

  Definition limits_lambda_theory_cat
    : Lims lambda_theory_cat
    := λ _ _, total_limit _ (creates_limits_lambda_theory_disp_cat _).

End LambdaTheoryCategory.
