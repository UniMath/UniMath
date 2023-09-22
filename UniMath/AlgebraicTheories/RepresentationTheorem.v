Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
(* Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma. *)
(* Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian. *)
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.Presheaves.
Require Import UniMath.AlgebraicTheories.PresheafCategory.

Local Open Scope algebraic_theories.
Local Open Scope cat.
Local Open Scope mor_disp.

Section RepresentationTheorem.

  Context (L : lambda_theory).

  Definition theory_presheaf_data : presheaf_data L.
  Proof.
    use make_presheaf_data.
    - exact L.
    - intros ? ? f g.
      exact (f • g).
  Defined.

  Lemma theory_is_presheaf : is_presheaf theory_presheaf_data.
  Proof.
    use make_is_presheaf.
    - apply algebraic_theory_comp_is_assoc.
    - apply algebraic_theory_comp_identity_projections.
    - apply algebraic_theory_comp_is_natural_l.
  Qed.

  Definition theory_presheaf : presheaf L
    := make_presheaf _ theory_is_presheaf.

  Local Definition power (X : presheaf_cat L) (n : nat)
    : Product (stn n) (presheaf_cat L) (λ _, X)
    := Products_from_Lims _ _ (λ _, limits_presheaf_cat _ _ _) _.

  Local Definition presheaf_BinProducts
    : BinProducts (presheaf_cat L)
    := BinProducts_from_Lims _ (λ _, limits_presheaf_cat _ _ _).

  Definition presheaf_algebraic_theory : algebraic_theory.
  Proof.
    use endomorphism_theory.
    - exact (presheaf_cat L).
    - intros n P.
      apply Products_from_Lims.
      intro Q.
      apply limits_presheaf_cat.
    - exact theory_presheaf.
  Defined.

  Context (p : nat).

  Local Definition stnweq {n : nat}
    : stn n ⨿ stn p ≃ stn (n + p)
    := weqfromcoprodofstn n p.

  Definition plus_p_presheaf_data'
    (P : presheaf L)
    : presheaf_data' L.
  Proof.
    - use make_presheaf_data'.
      + exact (λ n, P (n + p)).
      + cbn.
        intros m n s t.
        refine (action (T := L) (P := P) s _).
        intro i.
        induction (invmap (weqfromcoprodofstn m p) i) as [i' | i'].
        * refine (t i' • (λ j, pr (stnweq (inl j)))).
        * exact (pr (stnweq (inr i'))).
  Defined.

  Lemma plus_p_is_presheaf'
    (P : presheaf L)
    : is_presheaf' (plus_p_presheaf_data' P).
  Proof.
    - use make_is_presheaf';
        repeat intro.
      + unfold action'.
        refine (presheaf_is_assoc _ _ _ _ _ _ _ @ _).
        cbn.
        apply maponpaths.
        apply funextfun.
        intro x.
        induction (weqfromcoprodofstn_invmap l p x) as [x' | x'].
        * cbn.
          rewrite algebraic_theory_comp_is_assoc.
          rewrite algebraic_theory_comp_is_assoc.
          apply maponpaths.
          apply funextfun.
          intro x''.
          rewrite algebraic_theory_comp_projects_component.
          now rewrite (homotinvweqweq stnweq (inl x'') : weqfromcoprodofstn_invmap _ _ (stn_left _ _ _) = _).
        * cbn.
          rewrite algebraic_theory_comp_projects_component.
          now rewrite (homotinvweqweq stnweq (inr x') : weqfromcoprodofstn_invmap _ _ (stn_right _ _ _) = _).
      + unfold action'.
        refine (_ @ presheaf_identity_projections _ _ _).
        cbn.
        use maponpaths.
        apply funextsec.
        intro x.
        refine (_ @ maponpaths _ (homotweqinvweq stnweq x)).
        cbn.
        induction (weqfromcoprodofstn_invmap n p x).
        * apply algebraic_theory_comp_projects_component.
        * apply idpath.
  Qed.

  Definition plus_p_presheaf
    (P : presheaf L)
  : presheaf L
  := make_presheaf' _ (plus_p_is_presheaf' P).

  Definition plus_p_presheaf_morphism
    {P P' : presheaf L}
    (F : presheaf_morphism P P')
    : presheaf_morphism (plus_p_presheaf P) (plus_p_presheaf P').
  Proof.
    use tpair.
    - use make_nat_trans.
      + intro n.
        exact (pr1 F (n + p)).
      + abstract (
          intros n n' a;
          apply funextfun;
          intro f;
          apply (pr12 F)
        ).
    - abstract (
        use (_ ,, tt);
        intros n n' a f;
        apply (pr12 F)
      ).
  Defined.

  Definition plus_p_presheaf_functor_data
    : functor_data (presheaf_cat L) (presheaf_cat L).
  Proof.
    use make_functor_data.
    - exact plus_p_presheaf.
    - do 2 intro.
      exact plus_p_presheaf_morphism.
  Defined.

  Lemma plus_p_presheaf_is_functor
    : is_functor plus_p_presheaf_functor_data.
  Proof.
    use tpair.
    - refine (λ (P : presheaf L), _ : ((_ : presheaf_morphism (plus_p_presheaf P) (plus_p_presheaf P)) = _)).
      apply presheaf_morphism_eq.
      intro n.
      simpl.
      unfold id_disp.
      simpl.
      unfold transportb, mor_disp.
      simpl.
      now do 2 rewrite transportf_const.
    - refine (λ (P P' P'' : presheaf L) (F : presheaf_morphism P P') (F' : presheaf_morphism P' P''), _ : ((_ : presheaf_morphism (plus_p_presheaf P) (plus_p_presheaf P'')) = _)).
      apply presheaf_morphism_eq.
      intro.
      unfold compose.
      cbn.
      (* Sloooow *)
      unfold mor_disp, presheaf_morphism_to_nat_trans.
      simpl.
      do 2 rewrite pr1_transportf.
      simpl.
      do 2 rewrite transportf_const.
      now do 2 rewrite transportb_const.
  Qed.

  Definition plus_p_presheaf_functor
    : presheaf_cat L ⟶ presheaf_cat L
    := make_functor _ plus_p_presheaf_is_functor.

  Definition theory_presheaf_exponentiable
    : is_exponentiable presheaf_BinProducts (power theory_presheaf p).
  Proof.
    unfold is_exponentiable, is_left_adjoint.
    use (_ ,, (_ ,, _) ,, _ ,, _).
    - exact plus_p_presheaf_functor.
    - simpl.
      admit.
    - simpl.
      admit.
    - simpl.
      admit.
    - simpl.
  Defined.

  Definition presheaf_lambda_theory : lambda_theory.
  Proof.
    use endomorphism_lambda_theory.
    - exact (presheaf_cat L).
    - intros n P.
      apply Products_from_Lims.
      intro Q.
      apply limits_presheaf_cat.
    - exact theory_presheaf.
    - apply BinProducts_from_Lims.
      intro Q.
      apply limits_presheaf_cat.
    - unfold is_exponentiable.
  Defined.

End RepresentationTheorm.
