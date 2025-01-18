(**************************************************************************************************

  The category of λ-theories

  Defines the category of λ-theories. The category is formalized via a stack of displayed
  categories.

  Contents
  1. The category of λ-theories [lambda_theory_cat]
  1.1. The category of λ-theory data [lambda_theory_data_cat]
  1.1.1. Temporary accessors
  1.2. The category of λ-theories
  1.2.1. A lemma about λ-theories [isaprop_is_lambda_theory]

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
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.Combinatorics.Tuples.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Section LambdaTheoryCategory.

(** * 1. The category of λ-theories *)
(** ** 1.1. The category of λ-theory data *)

  Definition app_ax
    (T : algebraic_theory)
    (n : nat)
    (f : T n)
    : UU
    := T (S n).

  Definition abs_ax
    (T : algebraic_theory)
    (n : nat)
    (f : T (S n))
    : UU
    := T n.

  Let mor_app_ax'
    {T T' : algebraic_theory}
    (F : algebraic_theory_morphism T T')
    (app : ∏ n f, app_ax T n f)
    (app' : ∏ n f, app_ax T' n f)
    (n : nat)
    (f : T n)
    : UU
    := F (S n) (app n f) = app' n (F n f).

  Let mor_abs_ax'
    {T T' : algebraic_theory}
    (F : algebraic_theory_morphism T T')
    (abs : ∏ n f, abs_ax T n f)
    (abs' : ∏ n f, abs_ax T' n f)
    (n : nat)
    (f : T (S n))
    : UU
    := F n (abs n f) = abs' n (F (S n) f).

  Definition lambda_theory_data_disp_cat
    : disp_cat algebraic_theory_cat.
  Proof.
    use disp_struct.
    - refine (λ T, _ × _).
        + exact (∏ n f, app_ax T n f).
        + exact (∏ n f, abs_ax T n f).
    - refine (λ _ _ appabs appabs' F, _ × _).
        + exact (∏ n t, mor_app_ax' F (pr1 appabs) (pr1 appabs') n t).
        + exact (∏ n t, mor_abs_ax' F (pr2 appabs) (pr2 appabs') n t).
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

  Local Definition mor_app_ax
    {L L' : lambda_theory_data_cat}
    (F : algebraic_theory_morphism (data_theory L) (data_theory L'))
    (n : nat)
    (f : data_theory L n)
    : UU
    := mor_app_ax' F (@data_app L) (@data_app L') n f.

  Local Definition mor_abs_ax
    {L L' : lambda_theory_data_cat}
    (F : algebraic_theory_morphism (data_theory L) (data_theory L'))
    (n : nat)
    (f : data_theory L (S n))
    : UU
    := mor_abs_ax' F (@data_abs L) (@data_abs L') n f.

  Let data_mor_app
    {L L' : lambda_theory_data_cat}
    (F : lambda_theory_data_cat⟦L, L'⟧)
    {n : nat}
    (f : data_theory L n)
    : mor_app_ax (data_mor F) n f
    := pr12 F n f.

  Let data_mor_abs
    {L L' : lambda_theory_data_cat}
    (F : lambda_theory_data_cat⟦L, L'⟧)
    {n : nat}
    (f : data_theory L (S n))
    : mor_abs_ax (data_mor F) n f
    := pr22 F n f.

(** ** 1.2. The category of λtheories *)

  Local Definition extended_composition
    {T : algebraic_theory_data}
    {m n : nat}
    (f : T (S m))
    (g : stn m → T n)
    : T (S n)
    := f • (extend_tuple (λ i, (g i) • (λ i, var (stnweq (inl i)))) (var (stnweq (inr tt)))).

  Local Definition app_subst_ax
    (L : lambda_theory_data_cat)
    (m n : nat)
    (f : data_theory L m)
    (g : stn m → data_theory L n)
    : UU
    := data_app (f • g) = extended_composition (data_app f) g.

  Local Definition abs_subst_ax
    (L : lambda_theory_data_cat)
    (m n : nat)
    (f : data_theory L (S m))
    (g : stn m → data_theory L n)
    : UU
    := data_abs (extended_composition f g) = (data_abs f) • g.

  Local Definition is_lambda_theory (L : lambda_theory_data_cat) : UU :=
    (∏ m n f g, app_subst_ax L m n f g) ×
    (∏ m n f g, abs_subst_ax L m n f g).

  Definition lambda_theory_disp_cat
    : disp_cat lambda_theory_data_cat
    := disp_full_sub lambda_theory_data_cat is_lambda_theory.

  Definition lambda_theory_cat
    : category
    := total_category lambda_theory_disp_cat.

  Definition theory_data
    (L : lambda_theory_cat)
    : lambda_theory_data_cat
    := pr1 L.

  Definition β_ax
    (L : lambda_theory_cat)
    (n : nat)
    (l : (data_theory (theory_data L)) (S n))
    : UU
    := data_app (data_abs l) = l.

  Definition η_ax
    (L : lambda_theory_cat)
    (n : nat)
    (l : (data_theory (theory_data L)) n)
    : UU
    := data_abs (data_app l) = l.

  Definition β_lambda_theory_cat
    : category
    := full_subcat lambda_theory_cat (λ L, ∏ n l, β_ax L n l).

(** *** 1.2.1. A lemma about λ-theories *)

  Lemma isaprop_is_lambda_theory
    (L : lambda_theory_data_cat)
    : isaprop (is_lambda_theory L).
  Proof.
    repeat apply isapropdirprod;
    do 4 (apply impred; intro);
    apply setproperty.
  Qed.

End LambdaTheoryCategory.

Arguments app_ax /.
Arguments abs_ax /.
Arguments mor_app_ax /.
Arguments mor_abs_ax /.
Arguments app_subst_ax /.
Arguments abs_subst_ax /.
Arguments β_ax /.
Arguments η_ax /.
