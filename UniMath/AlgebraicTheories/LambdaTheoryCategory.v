(* Defines the univalent category of lambda theories *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.Tuples.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.

Local Open Scope cat.
Local Open Scope vec.
Local Open Scope algebraic_theories.

(* The datatype lambda_theory_data *)
Definition lambda_theory_data : UU
  := ∑ (T : algebraic_theory), ((∏ n, (T n : hSet) → (T (S n) : hSet)) × (∏ n, (T (S n) : hSet) → (T n : hSet))).

Coercion lambda_theory_data_to_algebraic_theory (L : lambda_theory_data) : algebraic_theory := pr1 L.

Definition app {L : lambda_theory_data} {n : nat} : (L n : hSet) → (L (S n) : hSet) := pr12 L n.

Definition abs {L : lambda_theory_data} {n : nat} : (L (S n) : hSet) → (L n : hSet) := pr22 L n.

Definition lambda_theory_data_morphism
  (L L' : lambda_theory_data)
  : UU
  := ∑ (F : algebraic_theory_morphism L L'),
      (∏ n t, F _ (app t) = app (F n t)) ×
      (∏ n t, F _ (abs t) = abs (F (S n) t)).

Coercion lambda_theory_data_morphism_to_algebraic_theory_morphism
  {L L' : lambda_theory_data}
  (F : lambda_theory_data_morphism L L')
  : algebraic_theory_morphism L L'
  := pr1 F.

Definition lambda_theory_data_morphism_preserves_app
  {L L' : lambda_theory_data}
  (F : lambda_theory_data_morphism L L')
  (n : nat) (t : (L n : hSet))
  : F _ (app t) = app (F _ t)
  := pr12 F n t.

Definition lambda_theory_data_morphism_preserves_abs
  {L L' : lambda_theory_data}
  (F : lambda_theory_data_morphism L L')
  (n : nat) (t : (L (S n) : hSet))
  : F _ (abs t) = abs (F _ t)
  := pr22 F n t.

Definition force_hlevel (n : nat) (T : UU) (H : isofhlevel n T) : isofhlevel n T := H.

(* The category of the data of lambda theories *)
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
  - intros.
    apply isapropdirprod;
    do 2 (apply impred; intro);
    apply setproperty.
  - now intros.
  - intros ? ? ? ? ? ? ? ? Fdata F'data.
    use tpair;
      do 2 intro.
    + exact (maponpaths _ (pr1 Fdata _ _) @ (pr1 F'data _ _)).
    + exact (maponpaths _ (pr2 Fdata _ _) @ (pr2 F'data _ _)).
Defined.

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
  - intro.
    refine (maponpaths (λ x, _ x _) _ @ maponpaths _ _ @ !(pathsdirprod_eta x));
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

Definition lambda_theory_data_cat
  : category
  := total_category lambda_theory_data_disp_cat.

Lemma is_univalent_lambda_theory_data_cat
  : is_univalent lambda_theory_data_cat.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_algebraic_theory_cat.
  - exact is_univalent_disp_lambda_theory_data_disp_cat.
Qed.

Section Test.
  Goal ob lambda_theory_data_cat = lambda_theory_data.
    exact (idpath _).
  Qed.
  Goal ∏ (L L' : lambda_theory_data), lambda_theory_data_cat⟦L, L'⟧ = lambda_theory_data_morphism L L'.
    exact (λ _ _, idpath _).
  Qed.
End Test.

(* The datatype lambda_theory *)
Definition extend_finite_morphism_with_identity
  {m n : finite_set_skeleton_category}
  (f : finite_set_skeleton_category⟦m, n⟧)
  : finite_set_skeleton_category⟦S m, S n⟧
  := extend_tuple (T := stn (S n)) (λ i, dni_lastelement (f i)) lastelement.

Definition extended_composition
  {T : algebraic_theory_data}
  {m n : nat}
  (f : T (S m) : hSet)
  (g : stn m → (T n : hSet))
  : (T (S n) : hSet)
  := f • (extend_tuple (λ i, #T (dni_lastelement (n := n)) (g i)) (pr lastelement)).

Definition is_lambda_theory (L : lambda_theory_data) : UU :=
    (∏ m n (a : finite_set_skeleton_category⟦m, n⟧) l, app (#L a l) = #L (extend_finite_morphism_with_identity a) (app l)) ×
    (∏ m n (a : finite_set_skeleton_category⟦m, n⟧) l, abs (#L (extend_finite_morphism_with_identity a) l) = #L a (abs l)) ×
    (∏ m n f (g : stn m → (L n : hSet)), app (f • g) = extended_composition (app f) g) ×
    (∏ m n f (g : stn m → (L n : hSet)), abs (extended_composition f g) = (abs f) • g).

Definition lambda_theory : UU := ∑ L, is_lambda_theory L.

Coercion lambda_theory_to_lambda_theory_data (L : lambda_theory) : lambda_theory_data := pr1 L.

Definition lambda_theory_app_is_natural
  {L : lambda_theory}
  {m n : nat}
  (a : finite_set_skeleton_category⟦m, n⟧)
  (l : (L m : hSet))
  : app (#L a l) = #L (extend_finite_morphism_with_identity a) (app l)
  := pr12 L m n a l.

Definition lambda_theory_abs_is_natural
  {L : lambda_theory}
  {m n : nat}
  (a : finite_set_skeleton_category⟦m, n⟧)
  (l : (L (S m) : hSet))
  : abs (#L (extend_finite_morphism_with_identity a) l) = #L a (abs l)
  := pr122 L m n a l.

Definition lambda_theory_app_compatible_with_comp
  {L : lambda_theory}
  {m n : nat}
  (f : (L m : hSet))
  (g : stn m → (L n : hSet))
  : app (f • g) = extended_composition (app f) g
  := pr1 (pr222 L) m n f g.

Definition lambda_theory_abs_compatible_with_comp
  {L : lambda_theory}
  {m n : nat}
  (f : (L (S m) : hSet))
  (g : stn m → (L n : hSet))
  : abs (extended_composition f g) = (abs f) • g
  := pr2 (pr222 L) m n f g.

Lemma isaprop_is_lambda_theory
  (L : lambda_theory_data)
  : isaprop (is_lambda_theory L).
Proof.
  repeat apply isapropdirprod;
  do 4 (apply impred; intro);
  apply setproperty.
Qed.

Definition lambda_theory_morphism
  (L L' : lambda_theory)
  : UU
  := lambda_theory_data_morphism L L' × unit.

(* The category of lambda theories without beta or eta *)
Definition lambda_theory_disp_cat
  : disp_cat lambda_theory_data_cat
  := disp_full_sub lambda_theory_data_cat is_lambda_theory.

Lemma is_univalent_disp_lambda_theory_disp_cat
  : is_univalent_disp lambda_theory_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  exact isaprop_is_lambda_theory.
Qed.

Definition lambda_theory_cat
  : category
  := total_category lambda_theory_disp_cat.

Lemma is_univalent_lambda_theory_cat
  : is_univalent lambda_theory_cat.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_lambda_theory_data_cat.
  - exact is_univalent_disp_lambda_theory_disp_cat.
Qed.

Section Test.
  Goal ob lambda_theory_cat = lambda_theory.
    exact (idpath _).
  Qed.
  Goal ∏ (L L' : lambda_theory), lambda_theory_cat⟦L, L'⟧ = lambda_theory_morphism L L'.
    exact (λ _ _, idpath _).
  Qed.
End Test.
