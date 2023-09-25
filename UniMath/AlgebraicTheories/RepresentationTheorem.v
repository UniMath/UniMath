Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
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
    use make_presheaf_morphism'.
    - intro n.
      exact (pr1 F (n + p)).
    - abstract (
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

  Lemma presheaf_mor_comp
    {P P' P'' : presheaf_cat L}
    (F : presheaf_cat L⟦P, P'⟧)
    (F' : presheaf_cat L⟦P', P''⟧)
    (n : nat)
    : pr11 (F · F') n = (pr11 F n) · (pr11 F' n).
  Proof.
    refine (maponpaths (λ z, pr1 z _) (pr1_transportf (B := λ _, _ ⟹ _) _ _) @ _).
    refine (maponpaths (λ z, pr1 (z _) _) (transportf_const _ _) @ _).
    exact (maponpaths (λ z, pr1 (z _) _) (transportf_const _ _)).
  Qed.

  Lemma plus_p_presheaf_is_functor
    : is_functor plus_p_presheaf_functor_data.
  Proof.
    split.
    - refine (λ (P : presheaf L), _ : ((_ : presheaf_morphism (plus_p_presheaf P) (plus_p_presheaf P)) = _)).
      use presheaf_morphism_eq.
      intro n.
      refine (maponpaths (λ z, pr1 (z _) _) (transportf_const _ (pr1 P ⟹ pr1 P)) @ !_).
      exact (maponpaths (λ z, pr1 (z _) _) (transportf_const _ _)).
    - refine (λ (P P' P'' : presheaf L) (F : presheaf_morphism P P') (F' : presheaf_morphism P' P''), _ : ((_ : presheaf_morphism (plus_p_presheaf P) (plus_p_presheaf P'')) = _)).
      apply presheaf_morphism_eq.
      intro.
      refine (presheaf_mor_comp _ _ _ @ !_).
      exact (presheaf_mor_comp (P := plus_p_presheaf P) (P' := plus_p_presheaf P') (P'' := plus_p_presheaf P'') _ _ _).
  Qed.

  Definition plus_p_presheaf_functor
    : presheaf_cat L ⟶ presheaf_cat L
    := make_functor _ plus_p_presheaf_is_functor.

  Definition binproduct_presheaf_element_weq
    (P P' : presheaf L)
    (n : nat)
    : (P n : hSet) × (P' n : hSet) ≃ (((constprod_functor1 presheaf_BinProducts P P') : presheaf L) n : hSet).
  Proof.
    use weq_iso.
    - intro y.
      use tpair.
      + intro u.
        induction u.
        * exact (pr1 y).
        * exact (pr2 y).
      + abstract (intros u v e; induction e).
    - intro x.
      exact ((pr1 x true) ,, (pr1 x false)).
    - abstract exact idpath.
    - abstract (
        intro x;
        use subtypePairEquality;
        [ intro;
          repeat (apply impred_isaprop; intro);
          apply setproperty
        | apply funextsec;
          intro u;
          now induction u ]
      ).
  Defined.

  Lemma constprod_functor_mor_eq
    {P P' Q : presheaf_cat L}
    (F : presheaf_cat L⟦P, P'⟧)
    (n : nat)
    (x : (pr11 (constprod_functor1 presheaf_BinProducts Q P) n : hSet))
    (x' := (invmap (binproduct_presheaf_element_weq _ _ _) x))
    : pr11 (# (constprod_functor1 presheaf_BinProducts Q) F) n x
    = (binproduct_presheaf_element_weq _ _ _) (pr1 x' ,, pr11 F _ (pr2 x')).
  Proof.
    (* I get lost somewhere in this proof *)

    (* Attempt 1: *)
    (* use subtypePairEquality.
    {
      intro.
      repeat (apply impred_isaprop; intro).
      apply setproperty.
    }
    apply funextsec. (* Intractible *)
    intro u.
    induction u. *)

    (* Simplification is only "tractable" if we make this opaque *)
    (* Opaque BinProducts_from_Lims.
    simpl.
    unfold BinProduct_of_functors_mor.
    unfold BinProductOfArrows.
    unfold BinProductArrow.
    unfold isBinProduct_BinProduct.
    unfold presheaf_BinProducts. *)
  Qed.

  Definition power_presheaf_element_weq
    (P : presheaf L)
    (m n : nat)
    : (stn m → P n : hSet) ≃ ((((power P m) : presheaf_cat L) : presheaf L) n : hSet).
  Proof.
    use weq_iso.
    - intro y.
      use tpair.
      + exact y.
      + abstract (intros u v e; induction e).
    - intros x.
      exact (pr1 x).
    - abstract exact idpath.
    - abstract (
        intro x;
        use subtypePairEquality;
        [ intro;
          repeat (apply impred_isaprop; intro);
          apply setproperty
        | apply idpath ]
      ).
  Defined.

  Definition plus_p_presheaf_adjunction_unit_map
    {P : presheaf L}
    (n : nat)
    (x : P n : hSet)
    : (plus_p_presheaf_functor (constprod_functor1
      presheaf_BinProducts
      (power theory_presheaf p)
      P
    ) : presheaf L) n : hSet.
  Proof.
    refine (binproduct_presheaf_element_weq (power theory_presheaf p : presheaf_cat L) P _ _).
    split.
    + refine (power_presheaf_element_weq _ _ _ _).
      intro i.
      exact (pr (stnweq (inr i))).
    + apply (action x).
      intro i.
      exact (pr (stnweq (inl i))).
  Defined.

  Lemma plus_p_presheaf_adjunction_unit_is_morphism
    {P : presheaf L}
    (m n : nat)
    (a : P m : hSet)
    (f : stn m → L n : hSet)
    : plus_p_presheaf_adjunction_unit_map n (action a f) =
      action (plus_p_presheaf_adjunction_unit_map m a) f.
  Proof.
    use subtypePairEquality.
    {
      intro.
      repeat (apply impred_isaprop; intro).
      apply setproperty.
    }
    use funextsec.
    intro x.
    induction x.
    * use subtypePairEquality.
      {
        intro.
        repeat (apply impred_isaprop; intro).
        apply setproperty.
      }
      use funextfun.
      intro.
      refine (!(algebraic_theory_comp_projects_component _ _ _ _ _ @ _)).
      exact (maponpaths (coprod_rect _ _ _) (homotinvweqweq stnweq (inr x))).
    * refine (presheaf_is_assoc _ _ _ _ _ _ _ @ !_).
      refine (presheaf_is_assoc _ _ _ _ _ _ _ @ _).
      apply maponpaths.
      apply funextfun.
      intro i.
      refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
      exact (maponpaths (coprod_rect _ _ _) (homotinvweqweq stnweq (inl i))).
  Qed.

  Definition plus_p_presheaf_adjunction_presheaf_unit_morphism
    (P : presheaf L)
    : presheaf_morphism P (plus_p_presheaf_functor (constprod_functor1 presheaf_BinProducts (power theory_presheaf p) P) : presheaf L).
  Proof.
      use make_presheaf_morphism'.
      + exact plus_p_presheaf_adjunction_unit_map.
      + exact plus_p_presheaf_adjunction_unit_is_morphism.
  Defined.

  Definition TODO { A : UU } : A.
  Admitted.

  Lemma presheaf_cat_morphism_eq
    (T : algebraic_theory)
    {P P' : presheaf_cat T}
    (G G' : P --> P')
    (H : ∏ n, pr11 G n = pr11 G' n)
    : G = G'.
  Proof.
    apply subtypePairEquality.
    - intro.
      use isapropdirprod.
      + do 4 (apply impred_isaprop; intro).
        apply setproperty.
      + exact isapropunit.
    - apply nat_trans_eq.
      + apply homset_property.
      + exact H.
  Qed.

  Lemma plus_p_presheaf_is_functor_auxf
    (P P' : presheaf_cat L)
    (x x' : algebraic_theory_cat ⟦ (L : algebraic_theory) , (L : algebraic_theory)⟧)
    (H : x = x')
    (F : pr1 P -->[x] pr1 P')
    : transportf (mor_disp (pr1 P) (pr1 P')) H F = F.
  Proof.
    exact (eqtohomot (transportf_const _ _) _).
  Qed.

  Definition plus_p_presheaf_adjunction_unit
    : functor_identity (presheaf_cat L) ⟹ constprod_functor1 presheaf_BinProducts (power theory_presheaf p) ∙ plus_p_presheaf_functor.
  Proof.
    use make_nat_trans.
    - exact plus_p_presheaf_adjunction_presheaf_unit_morphism.
    - intros P P' F.
      apply presheaf_cat_morphism_eq.
      (* pose (P'' := plus_p_presheaf_functor (constprod_functor1 presheaf_BinProducts (power theory_presheaf p) P') : presheaf L); *)
      intro n.
      refine (presheaf_mor_comp _ _ _ @ !_).
      refine (presheaf_mor_comp _ _ _ @ !_).
      (* apply BinProductArrow_eq. *)
      apply funextsec.
      intro x.
      Opaque presheaf_cat.
      etrans.
      unfold compose.
      simpl.
      apply idpath.
      cbn.
      unfold plus_p_presheaf_adjunction_unit_map.
      unfold compose.
      unfold functor_on_morphisms.
      Opaque constprod_functor1.
      simpl.
      Transparent constprod_functor1.
      (* unfold plus_p_presheaf_adjunction_unit_map. *)
      unfold functor_on_morphisms.
      unfold constprod_functor1.
      unfold BinProduct_of_functors.
      unfold BinProduct_of_functors_data.
      unfold BinProduct_of_functors_mor.
      unfold BinProductOfArrows.
      unfold BinProductArrow.
      unfold isBinProduct_BinProduct.
      unfold presheaf_BinProducts.
      Opaque BinProducts_from_Lims.
      simpl.
      Transparent BinProducts_from_Lims.
      unfold BinProducts_from_Lims.
      unfold make_BinProduct.
      Opaque make_isBinProduct.
      simpl.
      Transparent make_isBinProduct.
      unfold make_isBinProduct.
      unfold unique_exists.
      unfold make_iscontr.
      simpl.

  Defined.
  (* Defined. *)

  (* Definition plus_p_presheaf_adjunction_counit
    : plus_p_presheaf_functor ∙ constprod_functor1 presheaf_BinProducts (power theory_presheaf p) ⟹ functor_identity (presheaf_cat L).
  Proof.
    use make_nat_trans.
    - refine (λ (P : presheaf L), _ : presheaf_morphism (constprod_functor1 presheaf_BinProducts (power theory_presheaf p) (plus_p_presheaf_functor P) : presheaf L) (P : presheaf L)).
      use make_presheaf_morphism'.
      + intros n x.
        induction (invmap (binproduct_presheaf_element_weq _ _ _) x) as [t x'].
        pose (invmap (power_presheaf_element_weq _ _ _) t) as t'.
        refine (action (P := P) x' _).
        intro i.
        induction (invmap stnweq i) as [i' | i'].
        * exact (pr i').
        * exact (t' i').
      + admit.
    - admit.
  Admitted. *)

  Definition theory_presheaf_exponentiable
    : is_exponentiable presheaf_BinProducts (power theory_presheaf p).
  Proof.
    unfold is_exponentiable, is_left_adjoint.
    use (_ ,, _ ,, _).
    - exact plus_p_presheaf_functor.
    - split.
      +
      +
    - split.
      +
      +
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
