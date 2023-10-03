Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.Tuples.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms2.
Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.
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

  Local Definition presheaf_Terminal
    : Terminal (presheaf_cat L).
  Proof.
    use tpair.
    - use make_presheaf'.
      + use make_presheaf_data'.
        * exact (λ _, unitset).
        * exact (λ _ _ _ _, tt).
      + use make_is_presheaf';
          repeat intro.
        * apply idpath.
        * symmetry.
          apply iscontrunit.
    - intro a.
      use make_iscontr.
      + use (make_presheaf_morphism' (P' := make_presheaf' _ _)).
        * intros.
          exact tt.
        * trivial.
      + intro.
        use (presheaf_morphism_eq (P := a : presheaf L) (P' := make_presheaf' _ _)).
        intro.
        apply funextfun.
        intro.
        apply iscontrunit.
  Defined.

  Local Definition presheaf_BinProducts
    : BinProducts (presheaf_cat L)
    := bin_products_presheaf_cat _.

  Section Exponentiable.

    Section PlusPPresheaf.

      Definition plus_p_presheaf_data'
        (P : presheaf L)
        : presheaf_data' L.
      Proof.
        - use make_presheaf_data'.
          + exact (λ n, P (1 + n)).
          + intros m n s t.
            refine (action (T := L) (P := P) s _).
            intro i.
            induction (invmap stnweq i) as [i' | i'].
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
            apply (maponpaths (action (a : (P _ : hSet)))).
            apply funextfun.
            intro i.
            induction (invmap stnweq i) as [i' | i'].
            * do 2 refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ !_).
              apply maponpaths.
              apply funextfun.
              intro.
              refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
              exact (maponpaths _ (homotinvweqweq stnweq _)).
            * refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
              exact (maponpaths _ (homotinvweqweq stnweq _)).
          + refine (_ @ presheaf_identity_projections _ _ _).
            apply (maponpaths (action (a : (P _ : hSet)))).
            apply funextfun.
            intro i.
            refine (_ @ maponpaths _ (homotweqinvweq stnweq i)).
            induction (invmap stnweq i) as [i' | i'].
            * apply algebraic_theory_comp_projects_component.
            * apply idpath.
      Qed.

      Definition plus_p_presheaf
        (P : presheaf L)
      : presheaf L
      := make_presheaf' _ (plus_p_is_presheaf' P).

    End PlusPPresheaf.

    Definition presheaf_exponent_morphism_data
      (P : presheaf L)
      (n : nat)
      (t : ((constprod_functor1 presheaf_BinProducts theory_presheaf (plus_p_presheaf P) : presheaf L) n : hSet))
      : (P n : hSet).
    Proof.
      refine (action (P := P) (pr2 t) _).
      intro i.
      induction (invmap stnweq i) as [i' | i'].
      * exact (pr i').
      * exact (pr1 t).
    Defined.

    Lemma presheaf_exponent_is_morphism
      (P : presheaf L)
      (m n : nat)
      (a : ((constprod_functor1 presheaf_BinProducts theory_presheaf (plus_p_presheaf P) : presheaf L) m : hSet))
      (f : stn m → pr1 L n : hSet)
      : presheaf_exponent_morphism_data P n (action a f) = action (presheaf_exponent_morphism_data P m a) f.
    Proof.
      do 2 refine (presheaf_is_assoc _ _ _ _ _ _ _ @ !_).
      apply (maponpaths (action (pr2 a : (P _ : hSet)))).
      apply funextfun.
      intro i.
      induction (invmap stnweq i) as [i' | i'].
      - refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ !_).
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (!algebraic_theory_comp_identity_projections _ _ _ @ !_).
        apply maponpaths.
        apply funextfun.
        intro j.
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
      - refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
    Qed.

    Definition presheaf_exponent_morphism
      (P : presheaf L)
      : presheaf_morphism (constprod_functor1 presheaf_BinProducts theory_presheaf (plus_p_presheaf P) : presheaf L) P
      := make_presheaf_morphism' _ (presheaf_exponent_is_morphism P).

    Definition presheaf_exponent_induced_morphism_data
      {P P' : presheaf L}
      (F : presheaf_morphism (constprod_functor1 presheaf_BinProducts theory_presheaf P' : presheaf _) P)
      (n : nat)
      (t : (P' n : hSet))
      : plus_p_presheaf P n : hSet.
    Proof.
      refine (F (1 + n) _).
      split.
      - exact (pr (stnweq (inr tt))).
      - apply (action t).
        intro i.
        exact (pr (stnweq (inl i))).
    Defined.

    Lemma presheaf_exponent_induced_is_morphism
      {P P' : presheaf L}
      (F : presheaf_morphism (constprod_functor1 presheaf_BinProducts theory_presheaf P' : presheaf _) P)
      (m n : finite_set_skeleton_category)
      (a : P' m : hSet)
      (f : (⟦ m ⟧)%stn → L n : hSet)
      : presheaf_exponent_induced_morphism_data F n (action a f) = action (presheaf_exponent_induced_morphism_data F m a) f.
    Proof.
      refine (!_ @ presheaf_morphism_commutes_with_action F _ _).
      apply (maponpaths (F (1 + n))).
      apply pathsdirprod.
      - refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
      - do 2 refine (presheaf_is_assoc _ _ _ _ _ _ _ @ !_).
        apply maponpaths.
        apply funextfun.
        intro i.
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
    Qed.

    Definition presheaf_exponent_induced_morphism
      {P P' : presheaf L}
      (F : presheaf_morphism (constprod_functor1 presheaf_BinProducts theory_presheaf P' : presheaf _) P)
      : presheaf_morphism P' (plus_p_presheaf P)
      := make_presheaf_morphism' _ (presheaf_exponent_induced_is_morphism F).

    Lemma presheaf_exponent_induced_morphism_commutes
      {P P' : presheaf L}
      (F : presheaf_morphism (constprod_functor1 presheaf_BinProducts theory_presheaf P' : presheaf _) P)
      : F = # (constprod_functor1 presheaf_BinProducts theory_presheaf) (presheaf_exponent_induced_morphism F : presheaf_cat L⟦P', plus_p_presheaf P⟧) · presheaf_exponent_morphism P.
    Proof.
      pose (BPO := ((presheaf_BinProducts theory_presheaf P') : presheaf_cat L) : presheaf L).
      apply (presheaf_morphism_eq F _).
      intro n.
      refine (!(presheaf_mor_comp (P := BPO) _ _ _ @ _)).
      apply funextfun.
      intro t.
      refine (maponpaths (λ x, action (P := P) (x t) _) (presheaf_mor_comp (P := BPO) (P'' := plus_p_presheaf P) _ _ _) @ _).
      refine (!presheaf_morphism_commutes_with_action F _ _ @ _).
      apply maponpaths.
      apply pathsdirprod.
      - refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq stnweq _) @ _).
        exact (maponpaths (λ x, pr11 x n t) (id_right (BinProductPr1 _ (presheaf_BinProducts _ _)))).
      - refine (presheaf_is_assoc _ _ _ _ _ _ _ @ _).
        refine (_ @ presheaf_identity_projections _ _ _).
        apply maponpaths.
        apply funextfun.
        intro i.
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
    Qed.

    Lemma presheaf_exponent_induced_morphism_unique
      {P P' : presheaf L}
      (F : presheaf_morphism (constprod_functor1 presheaf_BinProducts theory_presheaf P' : presheaf _) P)
      (F' : ∑ (f' : presheaf_morphism P' (plus_p_presheaf P)), F = # (constprod_functor1 presheaf_BinProducts theory_presheaf) (f' : presheaf_cat L ⟦P', plus_p_presheaf P⟧) · presheaf_exponent_morphism P)
      : F' = presheaf_exponent_induced_morphism F,, presheaf_exponent_induced_morphism_commutes F.
    Proof.
      pose (BP := (presheaf_BinProducts theory_presheaf P')).
      pose (BPO := (BP : presheaf_cat L) : presheaf L).
      apply subtypePairEquality.
      {
        intro.
        apply (homset_property (presheaf_cat L)).
      }
      apply (presheaf_morphism_eq (pr1 F') _).
      intro n.
      apply funextfun.
      intro t.
      refine (_ @ maponpaths (λ x, pr11 x _ _) (!pr2 F')).
      refine (!(maponpaths (λ x, x _) (presheaf_mor_comp (P := BPO) _ _ _) @ _)).
      refine (maponpaths (λ x, action (x _ : P _ : hSet) _) (presheaf_mor_comp _ (pr1 F' : presheaf_cat L ⟦P', plus_p_presheaf P⟧) _) @ _).
      refine (maponpaths (λ x, (pr12 P) _ _ (x : P _ : hSet) _) (presheaf_morphism_commutes_with_action (pr1 F') _ _) @ _).
      refine (presheaf_is_assoc _ _ _ _ _ _ _ @ _).
      refine (_ @ presheaf_identity_projections _ _ _).
      apply maponpaths.
      apply funextfun.
      intro i.
      refine (_ @ maponpaths pr (homotweqinvweq stnweq i)).
      induction (invmap stnweq i) as [i' | i'].
      - refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ _).
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
      - refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq stnweq _) @ _).
        refine (maponpaths (λ x, pr1 (pr1 x) _ _) (id_right (BinProductPr1 _ BP)) @ _).
        apply (maponpaths (λ x, (pr (stnweq (inr x))))).
        exact (!pr2 iscontrunit i').
    Qed.

    Definition theory_presheaf_exponentiable
      : is_exponentiable presheaf_BinProducts theory_presheaf.
    Proof.
      unfold is_exponentiable.
      use left_adjoint_from_partial.
      - exact plus_p_presheaf.
      - exact presheaf_exponent_morphism.
      - intros P P' F.
        use make_iscontr.
        + use tpair.
          * exact (presheaf_exponent_induced_morphism F).
          * exact (presheaf_exponent_induced_morphism_commutes F).
        + exact (presheaf_exponent_induced_morphism_unique F).
    Defined.

  End Exponentiable.

  Lemma presheaf_lambda_theory_aux
    {m n : nat}
    (f : stn m → (L _ : hSet))
    : extend_tuple (λ i : stn m, # L dni_lastelement (f i)) (pr lastelement)
    = (λ i, let c := invmap (stnweq) i in
        coprod_rect (λ _, (L (1 + n) : hSet))
          (λ i', f i' • (λ j, pr (stnweq (inl j))))
          (λ i', pr (stnweq (inr i'))) c).
  Proof.
    apply extend_tuple_eq.
    intro i.
    - refine (algebraic_theory_functor_uses_projections _ _ _ _ _ @ !_).
      refine (maponpaths (λ x, let c := x in _) (_ : _ = inl i) @ _).
      + apply invmap_eq.
        exact (!eqtohomot (replace_dni_last _) i).
      + apply (maponpaths (λ x, _ • x)).
        apply funextfun.
        intro.
        apply maponpaths.
        exact (eqtohomot (replace_dni_last _) _).
    - exact (!maponpaths (λ x, let c := x in _) (homotinvweqweq stnweq (inr tt))).
  Qed.

  Definition presheaf_lambda_theory : lambda_theory.
  Proof.
    pose (exponential_object := pr1 theory_presheaf_exponentiable theory_presheaf : presheaf L).
    use endomorphism_lambda_theory.
    - exact (presheaf_cat L).
    - exact presheaf_Terminal.
    - exact presheaf_BinProducts.
    - exact theory_presheaf.
    - exact theory_presheaf_exponentiable.
    - use (make_presheaf_morphism' (P := exponential_object) (P' := theory_presheaf)).
      + intro.
        apply abs.
      + abstract (
          intros m n a f;
          refine (_ @ lambda_theory_abs_compatible_with_comp _ _);
          apply (maponpaths (λ x, abs (a • x)));
          symmetry;
          apply presheaf_lambda_theory_aux
        ).
    - use (make_presheaf_morphism' (P := theory_presheaf) (P' := exponential_object)).
      + intros n.
        apply app.
      + abstract (
          intros m n a f;
          refine (lambda_theory_app_compatible_with_comp _ _ @ _);
          apply (maponpaths (λ x, app a • x));
          apply presheaf_lambda_theory_aux
        ).
  Defined.

  Section Iso.

  Local Definition pow := λ n, EndomorphismTheory.power presheaf_Terminal presheaf_BinProducts theory_presheaf n.

  Definition L_to_presheaf_lambda_theory_algebraic_theory_morphism'_data
    : algebraic_theory_morphism'_data L presheaf_lambda_theory.
  Proof.
    intros n s.
    unfold presheaf_lambda_theory.
    use (make_presheaf_morphism' (P := ((EndomorphismTheory.power _ _ _ n) : presheaf_cat L) : presheaf L) (P' := theory_presheaf)).
    - intros n' t.
      refine (s • _).
      intro i.
      exact (((ProductPr _ _ (pow n) i) : presheaf_morphism ((pow n : presheaf_cat L) : presheaf L) theory_presheaf) _ t).
    - abstract (
        intros;
        refine (_ @ !algebraic_theory_comp_is_assoc _ _ _ _ _ _ _);
        apply maponpaths;
        apply funextfun;
        intro;
        now rewrite presheaf_morphism_commutes_with_action
      ).
  Defined.

  Lemma L_to_presheaf_lambda_theory_is_algebraic_theory_morphism'
    : is_algebraic_theory_morphism' L_to_presheaf_lambda_theory_algebraic_theory_morphism'_data.
  Proof.
    use make_is_algebraic_theory_morphism'.
    - intros m n f g.
      apply (presheaf_morphism_eq (P := (pow n : presheaf_cat L) : presheaf L) (P' := theory_presheaf)).
      intro l.
      refine (_ @ !presheaf_mor_comp (P'' := theory_presheaf) _ _ _).
      apply funextfun.
      intro t.
      refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ !_).
      apply (maponpaths (comp f)).
      apply funextfun.
      intro i.
      exact (maponpaths (λ x, x t) (!presheaf_mor_comp _ _ _) @
        maponpaths (λ x, pr11 x l t) (ProductPrCommutes _ _ _ (pow m) _ _ i)).
    - intros n i.
        apply (presheaf_morphism_eq (P := (pow n : presheaf_cat L) : presheaf L) (P' := theory_presheaf)).
      intro m.
      refine (_ @ !presheaf_mor_comp (P'' := theory_presheaf) _ _ _).
      apply funextfun.
      intro t.
      apply algebraic_theory_comp_projects_component.
  Qed.

  Definition L_to_presheaf_lambda_theory_algebraic_theory_morphism
    : algebraic_theory_morphism L presheaf_lambda_theory
    := make_algebraic_theory_morphism' _ L_to_presheaf_lambda_theory_is_algebraic_theory_morphism'.

  Lemma L_to_presheaf_lambda_theory_preserves_abs
    (n : nat)
    (s : (L n : hSet))
    : L_to_presheaf_lambda_theory_algebraic_theory_morphism (S n) (app s) = app (L_to_presheaf_lambda_theory_algebraic_theory_morphism n s).
  Proof.
    apply (presheaf_morphism_eq _ (_ : presheaf_morphism ((pow (S n) : presheaf_cat L) : presheaf L) theory_presheaf)).
    intro m.
    refine (!_).
    refine (presheaf_mor_comp (P := pow (S n)) (P'' := theory_presheaf) _ _ _ @ _).
    apply funextfun.
    intro t.
    refine (maponpaths (λ x, _ (pr11 x _ _ ,, _)) (id_right (BinProductPr1 _ (presheaf_BinProducts theory_presheaf _))) @ _).
    refine (maponpaths (λ x, _ (pr1 t ,, x t)) (presheaf_mor_comp (P'' := plus_p_presheaf theory_presheaf) _ _ _) @ _).
    refine (maponpaths (λ x, (presheaf_exponent_morphism_data theory_presheaf m (pr1 t ,, ((pr11 (BinProductPr2 _ (presheaf_BinProducts theory_presheaf (pow n))) m) · x) t))) (presheaf_mor_comp (P'' := plus_p_presheaf theory_presheaf) _ _ _) @ _).
    refine (maponpaths (λ x, x • _) (lambda_theory_app_compatible_with_comp _ _) @ _).
    refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ _).
    apply (maponpaths (comp (app s))).
    apply funextfun.
    intro u.
    unfold extend_tuple.
    unfold ProductPr.
    simpl.
    induction (invmap (Y := _ (S n)) stnweq u).
    - refine (maponpaths (λ x, x • _) (algebraic_theory_functor_uses_projections _ _ _ _ _) @ !_).
      refine (maponpaths (λ x, x t) (presheaf_mor_comp (P'' := theory_presheaf) _ _ _) @ !_).
      refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ _).
      refine (_ @ algebraic_theory_comp_identity_projections _ _ _).
      apply maponpaths.
      apply funextfun.
      intro.
      refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
      refine (maponpaths _ (_ : _ = inl x)).
      apply invmap_eq.
      exact (!eqtohomot (replace_dni_last _) _).
    - refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
      refine (maponpaths _ (homotinvweqweq _ (inr tt))).
  Qed.

  Lemma L_to_presheaf_lambda_theory_lambda_theory_morphism_preserves_app
    (n : nat)
    (s : (L (S n) : hSet))
    : L_to_presheaf_lambda_theory_algebraic_theory_morphism n (abs s) = abs (L_to_presheaf_lambda_theory_algebraic_theory_morphism (S n) s).
  Proof.
    apply (presheaf_morphism_eq _ (_ : presheaf_morphism ((pow n : presheaf_cat L) : presheaf L) theory_presheaf)).
    intro m.
    refine (!_).
    refine (presheaf_mor_comp (P'' := theory_presheaf) _ _ _ @ _).
    apply funextfun.
    intro.
    refine (_ @ lambda_theory_abs_compatible_with_comp _ _).
    apply (maponpaths abs).
    refine (maponpaths (λ x, x _) (presheaf_mor_comp (P'' := plus_p_presheaf theory_presheaf) _ _ _) @ _).
    apply TODO. (*
    refine (maponpaths (λ x, x (pr lastelement ,, _)) (presheaf_mor_comp (P := presheaf_BinProducts theory_presheaf (plus_p_presheaf (presheaf_BinProducts theory_presheaf (pow n) : presheaf_cat L))) (P'' := theory_presheaf) _ _ _) @ _).
    apply (maponpaths (comp s)).
    refine (!_).
    apply extend_tuple_eq.
    - intro i.
      refine (algebraic_theory_functor_uses_projections _ _ _ _ _ @ !_).
      simpl.
      unfold presheaf_exponent_morphism_data.
      unfold presheaf_exponent_induced_morphism_data.
      simpl.
      unfold id_disp.
      simpl.
      unfold mor_disp.
      simpl.
      rewrite transportb_const.
      simpl.
      rewrite algebraic_theory_comp_projects_component.
      refine (maponpaths (λ x, (coprod_rect (λ _, presheaf_morphism _ theory_presheaf) _ _ x) _ _) (_ : _ = inl i) @ _).
      {
        apply invmap_eq.
        exact (!eqtohomot (replace_dni_last _) _).
      }
      refine (maponpaths (λ x, x _) (presheaf_mor_comp (P'' := theory_presheaf) _ _ _) @ _).
      unfold compose.
      simpl.
      unfold ProductPr.
      refine (presheaf_morphism_commutes_with_action ((pr21 (pow n)) i : presheaf_morphism ((pow n : presheaf_cat L) : presheaf L) theory_presheaf) _ _ @ _).
      refine (maponpaths (λ x, action x _) (presheaf_morphism_commutes_with_action ((pr21 (pow n)) i : presheaf_morphism ((pow n : presheaf_cat L) : presheaf L) theory_presheaf) _ _) @ _).
      refine (maponpaths (λ x, action (action x _) _) (presheaf_morphism_commutes_with_action ((pr21 (pow n)) i : presheaf_morphism ((pow n : presheaf_cat L) : presheaf L) theory_presheaf) _ _) @ _).
      refine (presheaf_is_assoc _ _ _ _ _ _ _ @ _).
      refine (presheaf_is_assoc _ _ _ _ _ _ _ @ _).
      apply (maponpaths (comp (pr11 (pr21 (pow n) i) m x))).
      apply funextfun.
      intro.
      refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
      refine (maponpaths (λ x, (coprod_rect _ _ _ x) • _) (homotinvweqweq _ (inl _)) @ _).
      refine (maponpaths (λ x, x • _) (algebraic_theory_comp_projects_component _ _ _ _ _) @ _).
      refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
      refine (maponpaths _ (homotinvweqweq _ (inl _)) @ _).
      exact (maponpaths (λ x, pr (x _)) (replace_dni_last _)).
    - unfold ProductPr.
      refine (!_).
      refine (maponpaths (λ x, pr11 (coprod_rect (λ _, presheaf_morphism _ theory_presheaf) _ _ x) _ _) (homotinvweqweq _ (inr tt)) @ _).
      refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ _).
      refine (maponpaths (λ x, x • _) (_ : _ = pr lastelement) @ _).
      {
        simpl.
        unfold presheaf_exponent_induced_morphism_data.
        cbn.
        unfold transportb, mor_disp.
        cbn.
        now rewrite transportf_const.
      }
      refine (_ @ algebraic_theory_comp_identity_projections _ _ _).
      apply maponpaths.
      apply funextfun.
      intro.
      refine (_ @ maponpaths pr (homotweqinvweq stnweq x0)).
      induction (invmap stnweq x0).
      + refine (maponpaths (λ x, x • _) (algebraic_theory_comp_projects_component _ _ _ _ _) @ _).
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq _ (inl _))).
      + refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq _ (inr tt))). *)
  Time Qed.

  Definition L_to_presheaf_lambda_theory_lambda_theory_morphism
    : lambda_theory_morphism L presheaf_lambda_theory.
  Proof.
    use make_lambda_theory_morphism.
    use make_lambda_theory_data_morphism.
    - exact L_to_presheaf_lambda_theory_algebraic_theory_morphism.
    - exact L_to_presheaf_lambda_theory_preserves_abs.
    - exact L_to_presheaf_lambda_theory_lambda_theory_morphism_preserves_app.
  Defined.

  Definition presheaf_lambda_theory_iso
    : z_iso (C := lambda_theory_cat) L presheaf_lambda_theory.
  Proof.
    use make_z_iso.
    - Time exact L_to_presheaf_lambda_theory_lambda_theory_morphism.
    - use (make_lambda_theory_morphism (L := presheaf_lambda_theory) (L' := L)).
      use make_lambda_theory_data_morphism.
      + use make_algebraic_theory_morphism'.
        * refine (λ _ (l : presheaf_morphism ((power theory_presheaf _ : presheaf_cat L) : presheaf L) theory_presheaf), _).
          exact (l _ pr).
        * admit.
      + admit.
  Defined.

End RepresentationTheorm.
