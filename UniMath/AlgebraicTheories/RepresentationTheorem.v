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
Require Import UniMath.AlgebraicTheories.Examples.Plus1Presheaf.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.
Require Import UniMath.AlgebraicTheories.Presheaves.
Require Import UniMath.AlgebraicTheories.PresheafCategory.

Local Open Scope algebraic_theories.
Local Open Scope cat.
Local Open Scope mor_disp.

Definition TODO {A : UU} : A.
Admitted.

Section RepresentationTheorem.

  Context (L : lambda_theory).

  Section Exponentiable.

    Definition presheaf_exponent_morphism_data
      (P : presheaf L)
      (n : nat)
      (t : ((constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L) (plus_1_presheaf P) : presheaf L) n : hSet))
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
      (a : ((constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L) (plus_1_presheaf P) : presheaf L) m : hSet))
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
      : presheaf_morphism (constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L) (plus_1_presheaf P) : presheaf L) P
      := make_presheaf_morphism' _ (presheaf_exponent_is_morphism P).

    Definition presheaf_exponent_induced_morphism_data
      {P P' : presheaf L}
      (F : presheaf_morphism (constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L) P' : presheaf _) P)
      (n : nat)
      (t : (P' n : hSet))
      : plus_1_presheaf P n : hSet.
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
      (F : presheaf_morphism (constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L) P' : presheaf _) P)
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
      (F : presheaf_morphism (constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L) P' : presheaf _) P)
      : presheaf_morphism P' (plus_1_presheaf P)
      := make_presheaf_morphism' _ (presheaf_exponent_induced_is_morphism F).

    Lemma presheaf_exponent_induced_morphism_commutes
      {P P' : presheaf L}
      (F : presheaf_morphism (constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L) P' : presheaf _) P)
      : F = # (constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L)) (presheaf_exponent_induced_morphism F : presheaf_cat L⟦P', plus_1_presheaf P⟧) · presheaf_exponent_morphism P.
    Proof.
      pose (BPO := (((bin_products_presheaf_cat _) (theory_presheaf L) P') : presheaf_cat L) : presheaf L).
      apply (presheaf_morphism_eq F _).
      intro n.
      refine (!(presheaf_mor_comp (P := BPO) _ _ _ @ _)).
      apply funextfun.
      intro t.
      refine (maponpaths (λ x, action (P := P) (x t) _) (presheaf_mor_comp (P := BPO) (P'' := plus_1_presheaf P) _ _ _) @ _).
      refine (!presheaf_morphism_commutes_with_action F _ _ @ _).
      apply maponpaths.
      apply pathsdirprod.
      - refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq stnweq _) @ _).
        exact (maponpaths (λ x, pr11 x n t) (id_right (BinProductPr1 _ ((bin_products_presheaf_cat _) _ _)))).
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
      (F : presheaf_morphism (constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L) P' : presheaf _) P)
      (F' : ∑ (f' : presheaf_morphism P' (plus_1_presheaf P)), F = # (constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L)) (f' : presheaf_cat L ⟦P', plus_1_presheaf P⟧) · presheaf_exponent_morphism P)
      : F' = presheaf_exponent_induced_morphism F,, presheaf_exponent_induced_morphism_commutes F.
    Proof.
      pose (BP := ((bin_products_presheaf_cat _) (theory_presheaf L) P')).
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
      refine (maponpaths (λ x, action (x _ : P _ : hSet) _) (presheaf_mor_comp _ (pr1 F' : presheaf_cat L ⟦P', plus_1_presheaf P⟧) _) @ _).
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
      : is_exponentiable (bin_products_presheaf_cat _) (theory_presheaf L).
    Proof.
      unfold is_exponentiable.
      use left_adjoint_from_partial.
      - exact plus_1_presheaf.
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
    pose (exponential_object := pr1 theory_presheaf_exponentiable (theory_presheaf L) : presheaf L).
    use endomorphism_lambda_theory.
    - exact (presheaf_cat L).
    - exact (terminal_presheaf_cat _).
    - exact (bin_products_presheaf_cat _).
    - exact (theory_presheaf L).
    - exact theory_presheaf_exponentiable.
    - use (make_presheaf_morphism' (P := exponential_object) (P' := (theory_presheaf L))).
      + intro.
        apply abs.
      + abstract (
          intros m n a f;
          refine (_ @ lambda_theory_abs_compatible_with_comp _ _);
          apply (maponpaths (λ x, abs (a • x)));
          symmetry;
          apply presheaf_lambda_theory_aux
        ).
    - use (make_presheaf_morphism' (P := (theory_presheaf L)) (P' := exponential_object)).
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

  Local Definition pow := λ n, EndomorphismTheory.power (terminal_presheaf_cat _) (bin_products_presheaf_cat _) (theory_presheaf L) n.

  Local Definition pow' := λ n, products_presheaf_cat L (stn n) (λ _, (theory_presheaf L)).

  Local Definition pow_iso
    (n : nat)
    : z_iso (pow n) (pow' n)
    := z_iso_between_Product (pow n) (pow' n).

  Lemma identity_on_element
    (P : presheaf L)
    (n : nat)
    (x : (P n : hSet))
    : pr11 (identity (P : presheaf_cat L)) n x = x.
  Proof.
    exact (maponpaths (λ x, pr1 (x _) _ _) (transportb_const _ (P ⟹ P))).
  Qed.

  Definition presheaf_to_L
    : algebraic_theory_morphism'_data presheaf_lambda_theory L.
  Proof.
    intros n f.
    refine ((f : presheaf_morphism (_ : presheaf L) (theory_presheaf L)) n _).
    refine ((inv_from_z_iso (pow_iso n) : presheaf_morphism (ProductObject _ _ (pow' n) : presheaf L) (ProductObject _ _ (pow n) : presheaf L)) n _).
    exact pr.
  Defined.

  Definition L_to_presheaf
    : algebraic_theory_morphism'_data L presheaf_lambda_theory.
  Proof.
    intros n s.
    unfold presheaf_lambda_theory.
    use (make_presheaf_morphism' (P := ((EndomorphismTheory.power _ _ _ n) : presheaf_cat L) : presheaf L) (P' := (theory_presheaf L))).
    - intros n' t.
      refine (s • _).
      intro i.
      exact (((morphism_from_z_iso _ _ (pow_iso n)) : presheaf_morphism (ProductObject _ _ (pow n) : presheaf L) (ProductObject _ _ (pow' n) : presheaf L)) n' t i).
    - abstract (
        intros;
        refine (_ @ !algebraic_theory_comp_is_assoc _ _ _ _ _ _ _);
        apply maponpaths;
        apply funextfun;
        intro;
        now rewrite presheaf_morphism_commutes_with_action
      ).
  Defined.

  Lemma L_to_presheaf_to_L
    (n : nat)
    (l : (L n : hSet))
    : presheaf_to_L n (L_to_presheaf n l) = l.
  Proof.
    refine (_ @ algebraic_theory_comp_identity_projections _ _ _).
    apply (maponpaths (comp l)).
    apply funextfun.
    intro i.
    refine (maponpaths (λ x, x _ _) (!presheaf_mor_comp _ (morphism_from_z_iso _ _ (pow_iso n)) _) @ _).
    refine (maponpaths (λ x, pr11 x _ _ _) (z_iso_after_z_iso_inv (pow_iso n)) @ _).
    refine (maponpaths (λ x, x _) (identity_on_element (ProductObject _ _ (pow' n)) _ _)).
  Qed.

  Lemma presheaf_to_L_to_presheaf
    (n : nat)
    (l : (presheaf_lambda_theory n : hSet))
    : L_to_presheaf n (presheaf_to_L n l) = l.
  Proof.
    apply (presheaf_morphism_eq _ (l : presheaf_morphism (ProductObject _ _ (pow n) : presheaf L) ((theory_presheaf L)))).
    intro.
    apply funextfun.
    intro.
    refine (!presheaf_morphism_commutes_with_action (l : presheaf_morphism (ProductObject _ _ (pow n) : presheaf L) (theory_presheaf L)) _ _ @ _).
    apply maponpaths.
    refine (!presheaf_morphism_commutes_with_action ((inv_from_z_iso (pow_iso n)) : presheaf_morphism (ProductObject _ _ (pow' n) : presheaf L) (ProductObject _ _ (pow n) : presheaf L)) _ _ @ _).
    refine (_ @ identity_on_element _ _ _).
    refine (!_ @ maponpaths (λ x, pr11 x _ _) (z_iso_inv_after_z_iso (pow_iso n))).
    refine (maponpaths (λ x, x _) (presheaf_mor_comp _ _ _) @ _).
    apply (maponpaths (pr11 (inv_from_z_iso (pow_iso n)) _)).
    apply funextsec.
    intro.
    exact (!algebraic_theory_comp_projects_component _ _ _ _ _).
  Qed.

  (* Lemma presheaf_lambda_theory_to_L_is_algebraic_theory_morphism'
    : is_algebraic_theory_morphism' presheaf_lambda_theory_to_L_algebraic_theory_morphism'_data.
  Proof.
    split.
    - intros m n f g.
      refine (maponpaths (λ x, x _) (presheaf_mor_comp (P := pow n) (P'' := (theory_presheaf L)) _ _ _) @ !_).
      refine (!presheaf_morphism_commutes_with_action (f : presheaf_morphism (ProductObject _ _ (pow m) : presheaf L) (theory_presheaf L)) _ _ @ _).
      apply (maponpaths (λ x, _ n x)).
      refine (!presheaf_morphism_commutes_with_action ((inv_from_z_iso (pow_iso m)) : presheaf_morphism (ProductObject _ _ (pow' m) : presheaf L) (ProductObject _ _ (pow m) : presheaf L)) _ _ @ _).
      refine (maponpaths _ (funextsec _ _ _ (λ _, algebraic_theory_comp_projects_component _ _ _ _ _)) @ !_).
      refine (maponpaths (λ x, pr11 x n _) (!id_right (ProductArrow _ _ (pow m) _)) @ _).
      refine (maponpaths (λ x, pr11 ((ProductArrow _ _ (pow m) _) · x) n _) (!z_iso_inv_after_z_iso (pow_iso m)) @ _).
      refine (maponpaths (λ x, pr11 x n _) (assoc _ (pow_iso m) _) @ _).
      refine (maponpaths (λ x, x _) (presheaf_mor_comp (P := pow n) (P'' := pow m) _ _ _) @ _).
      apply (maponpaths (pr11 (inv_from_z_iso (pow_iso m)) n)).
      refine (maponpaths (λ x, x _) (presheaf_mor_comp (P := pow n) (P'' := pow' m) _ _ _) @ _).
      apply funextsec.
      intro i.
      refine (maponpaths (λ x, x _) (!presheaf_mor_comp (P'' := (theory_presheaf L)) _ _ _) @ _).
      exact (maponpaths (λ x, pr11 x _ _) (ProductPrCommutes _ _ _ (pow m) _ _ _)).
    - intros n i.
      refine (maponpaths (λ x, _ (_ x) _ _) (pr1 (endomorphism_is_theory' _ _ _) _ _ _ _) @ _).
      refine (maponpaths (λ x, x pr) (!presheaf_mor_comp (P := pow' n) (P'' := (theory_presheaf L)) _ _ _) @ _).
      exact (maponpaths (λ x, pr11 x _ _) (ProductPrCommutes _ _ _ (pow n) _ _ _)).
  Qed. *)

  (* Definition presheaf_lambda_theory_to_L_lambda_theory_morphism
    : lambda_theory_morphism presheaf_lambda_theory L.
  Proof.
    use make_lambda_theory_morphism.
    use make_lambda_theory_data_morphism.
    - use (make_algebraic_theory_morphism' _ presheaf_lambda_theory_to_L_is_algebraic_theory_morphism').
    - apply TODO.
    - apply TODO.
  Defined. *)

  Lemma L_to_presheaf_preserves_pr
    (n : nat)
    (i : stn n)
    : L_to_presheaf n (pr i) = pr i.
  Proof.
    apply (presheaf_morphism_eq (P := (pow n : presheaf_cat L) : presheaf L) (P' := (theory_presheaf L))).
    intro m.
    refine (_ @ !presheaf_mor_comp (P'' := (theory_presheaf L)) _ _ _).
    apply funextfun.
    intro t.
    apply algebraic_theory_comp_projects_component.
  Qed.

  Lemma L_to_presheaf_preserves_comp
    (m n : nat)
    (f : (L m : hSet))
    (g : stn m → (L n : hSet))
    : L_to_presheaf n (f • g) = (L_to_presheaf m f) • (λ i, L_to_presheaf n (g i)).
  Proof.
    apply (presheaf_morphism_eq (P := (pow n : presheaf_cat L) : presheaf L) (P' := (theory_presheaf L))).
    intro l.
    refine (_ @ !presheaf_mor_comp (P'' := (theory_presheaf L)) _ _ _).
    apply funextfun.
    intro t.
    refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ !_).
    apply (maponpaths (comp f)).
    apply funextfun.
    intro i.
    exact (maponpaths (λ x, x t) (!presheaf_mor_comp _ _ _) @
        maponpaths (λ x, pr11 x l t) (ProductPrCommutes _ _ _ (pow m) _ _ i)).
  Qed.

  Lemma L_to_presheaf_preserves_app
    (n : nat)
    (s : (L n : hSet))
    : L_to_presheaf (S n) (app s) = app (L_to_presheaf n s).
  Proof.
    apply (presheaf_morphism_eq _ (_ : presheaf_morphism ((pow (S n) : presheaf_cat L) : presheaf L) (theory_presheaf L))).
    intro m.
    refine (!_).
    refine (presheaf_mor_comp (P := pow (S n)) (P'' := (theory_presheaf L)) _ _ _ @ _).
    apply funextfun.
    intro t.
    refine (maponpaths (λ x, _ (pr11 x _ _ ,, _)) (id_right (BinProductPr1 _ ((bin_products_presheaf_cat _) (theory_presheaf L) _))) @ _).
    refine (maponpaths (λ x, _ (pr1 t ,, x t)) (presheaf_mor_comp (P'' := plus_1_presheaf (theory_presheaf L)) _ _ _) @ _).
    refine (maponpaths (λ x, (presheaf_exponent_morphism_data (theory_presheaf L) m (pr1 t ,, ((pr11 (BinProductPr2 _ ((bin_products_presheaf_cat _) (theory_presheaf L) (pow n))) m) · x) t))) (presheaf_mor_comp (P'' := plus_1_presheaf (theory_presheaf L)) _ _ _) @ _).
    refine (maponpaths (λ x, x • _) (lambda_theory_app_compatible_with_comp _ _) @ _).
    refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ _).
    apply (maponpaths (comp (app s))).
    apply funextfun.
    intro u.
    unfold extend_tuple.
    simpl.
    unfold ProductPr.
    simpl.
    induction (invmap (Y := _ (S n)) stnweq u).
    - refine (maponpaths (λ x, x • _) (algebraic_theory_functor_uses_projections _ _ _ _ _) @ !_).
      refine (maponpaths (λ x, x t) (presheaf_mor_comp (P'' := (theory_presheaf L)) _ _ _) @ !_).
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

  (* Lemma presheaf_to_L_preserves_app
    (n : nat)
    (s : (presheaf_lambda_theory n : hSet))
    : presheaf_to_L (S n) (app s) = app (presheaf_to_L n s).
  Proof.
    unfold presheaf_to_L.
    unfold app.
    Opaque pow_iso.
    simpl.
    unfold EndomorphismTheory.hom_weq.
    simpl.
  Qed. *)

  (* Lemma L_to_presheaf_lambda_theory_lambda_theory_morphism_preserves_app
    (n : nat)
    (s : (L (S n) : hSet))
    : L_to_presheaf_lambda_theory_algebraic_theory_morphism n (abs s) = abs (L_to_presheaf_lambda_theory_algebraic_theory_morphism (S n) s).
  Proof.
    apply (presheaf_morphism_eq _ (_ : presheaf_morphism ((pow n : presheaf_cat L) : presheaf L) (theory_presheaf L))).
    intro m.
    refine (!_).
    refine (presheaf_mor_comp (P'' := (theory_presheaf L)) _ _ _ @ _).
    apply funextfun.
    intro.
    refine (_ @ lambda_theory_abs_compatible_with_comp _ _).
    apply (maponpaths abs).
    refine (maponpaths (λ x, x _) (presheaf_mor_comp (P'' := plus_1_presheaf (theory_presheaf L)) _ _ _) @ _).
    apply TODO. (*
    refine (maponpaths (λ x, x (pr lastelement ,, _)) (presheaf_mor_comp (P := (bin_products_presheaf_cat _) (theory_presheaf L) (plus_1_presheaf ((bin_products_presheaf_cat _) (theory_presheaf L) (pow n) : presheaf_cat L))) (P'' := (theory_presheaf L)) _ _ _) @ _).
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
      refine (maponpaths (λ x, (coprod_rect (λ _, presheaf_morphism _ (theory_presheaf L)) _ _ x) _ _) (_ : _ = inl i) @ _).
      {
        apply invmap_eq.
        exact (!eqtohomot (replace_dni_last _) _).
      }
      refine (maponpaths (λ x, x _) (presheaf_mor_comp (P'' := (theory_presheaf L)) _ _ _) @ _).
      unfold compose.
      simpl.
      unfold ProductPr.
      refine (presheaf_morphism_commutes_with_action ((pr21 (pow n)) i : presheaf_morphism ((pow n : presheaf_cat L) : presheaf L) (theory_presheaf L)) _ _ @ _).
      refine (maponpaths (λ x, action x _) (presheaf_morphism_commutes_with_action ((pr21 (pow n)) i : presheaf_morphism ((pow n : presheaf_cat L) : presheaf L) (theory_presheaf L)) _ _) @ _).
      refine (maponpaths (λ x, action (action x _) _) (presheaf_morphism_commutes_with_action ((pr21 (pow n)) i : presheaf_morphism ((pow n : presheaf_cat L) : presheaf L) (theory_presheaf L)) _ _) @ _).
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
      refine (maponpaths (λ x, pr11 (coprod_rect (λ _, presheaf_morphism _ (theory_presheaf L)) _ _ x) _ _) (homotinvweqweq _ (inr tt)) @ _).
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
  Qed. *)

  (* Definition L_to_presheaf_lambda_theory_lambda_theory_morphism
    : lambda_theory_morphism L presheaf_lambda_theory.
  Proof.
    use make_lambda_theory_morphism.
    use make_lambda_theory_data_morphism.
    - exact L_to_presheaf_lambda_theory_algebraic_theory_morphism.
    - exact L_to_presheaf_lambda_theory_preserves_abs.
    - exact L_to_presheaf_lambda_theory_lambda_theory_morphism_preserves_app.
  Defined. *)

  Definition presheaf_lambda_theory_iso
    : z_iso (C := lambda_theory_cat) L presheaf_lambda_theory.
  Proof.
    use make_lambda_theory_z_iso.
    - use make_algebraic_theory_z_iso.
      + intro.
        use make_z_iso.
        * exact (λ l, L_to_presheaf n l).
        * exact (λ l, presheaf_to_L n l).
        * abstract (
            split;
            apply funextfun;
            intro l;
            [ exact (L_to_presheaf_to_L n l)
            | exact (presheaf_to_L_to_presheaf n l) ]
          ).
      + exact L_to_presheaf_preserves_pr.
      + exact L_to_presheaf_preserves_comp.
    - exact L_to_presheaf_preserves_app.
    - apply TODO.
  Defined.

End RepresentationTheorm.
