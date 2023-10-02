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

Definition one_element_product
  (C : category)
  (c : C)
  : Product (stn 1) C (λ _, c).
Proof.
  use make_Product.
  - exact c.
  - intro i.
    apply identity.
  - use make_isProduct.
    + apply homset_property.
    + intros c' cone'.
      use make_iscontr.
      * use tpair.
        -- exact (cone' firstelement).
        -- abstract (
          intro i;
          refine (id_right _ @ maponpaths _ _);
          use subtypePath;
          [ intro;
            apply isasetbool
          | symmetry;
            apply natlth1tois0;
            apply stnlt ]
        ).
      * abstract (
          intro t;
          use subtypePath;
          [ intro;
            apply impred_isaprop;
            intro;
            apply homset_property
          | exact (!id_right _ @ pr2 t _) ]
        ).
Defined.

Definition left_adjoint_to_is_universal_arrow_from
  {C C' : category}
  {F : C ⟶ C'}
  (H : is_left_adjoint F)
  (c: C')
  : is_universal_arrow_from F c (pr1 H c) ((pr212 H) c).
Proof.
  induction H as [H1 [[H2 H3] [H4 H5]]].
  unfold triangle_1_statement in H4.
  unfold triangle_2_statement in H5.
  cbn in *.
  - intros c' g.
    use make_iscontr.
    + use tpair.
      * refine ((H2 c') · (# H1 g)).
      * abstract (
          simpl;
          rewrite (functor_comp);
          rewrite assoc';
          pose (p := nat_trans_ax H3);
          simpl in p;
          rewrite p;
          rewrite assoc;
          rewrite H4;
          exact (!id_left _)
        ).
    + abstract (
        intro t;
        use subtypePairEquality;
        [ intro; apply homset_property | ];
        rewrite (pr2 t);
        rewrite functor_comp;
        rewrite assoc;
        pose (p := nat_trans_ax H2);
        simpl in p;
        rewrite <- p;
        rewrite assoc';
        rewrite H5;
        exact (!id_right _)
      ).
Defined.

Definition constprod_functor1_z_iso
  {C: category}
  {c c': C}
  (BP: BinProducts C)
  (f: z_iso c c')
  : z_iso (C := [C, C]) (constprod_functor1 BP c) (constprod_functor1 BP c').
Proof.
  use make_z_iso.
  - use make_nat_trans.
    + intro d.
      exact (# (constprod_functor2 BP d) f).
    + abstract (
        intros d d' g;
        do 2 refine (postcompWithBinProductArrow _ _ _ _ _ _ _ @ !_);
        apply BinProductArrow_eq;
        [ do 2 refine (BinProductPr1Commutes _ _ _ _ _ _ _ @ !_);
          do 2 refine (assoc' _ _ _ @ !_);
          apply maponpaths;
          exact (id_left _ @ !id_right _)
        | do 2 refine (BinProductPr2Commutes _ _ _ _ _ _ _ @ !_);
          do 2 refine (assoc' _ _ _ @ !_);
          apply maponpaths;
          exact (id_right _ @ !id_left _) ]
      ).
  - use make_nat_trans.
    + intro d.
      exact (# (constprod_functor2 BP d) (inv_from_z_iso f)).
    + abstract (
        intros d d' g;
        do 2 refine (postcompWithBinProductArrow _ _ _ _ _ _ _ @ !_);
        apply BinProductArrow_eq;
        [ do 2 refine (BinProductPr1Commutes _ _ _ _ _ _ _ @ !_);
          do 2 refine (assoc' _ _ _ @ !_);
          apply maponpaths;
          exact (id_left _ @ !id_right _)
        | do 2 refine (BinProductPr2Commutes _ _ _ _ _ _ _ @ !_);
          do 2 refine (assoc' _ _ _ @ !_);
          apply maponpaths;
          exact (id_right _ @ !id_left _) ]
      ).
  - abstract (
      split;
      (apply nat_trans_eq; [ apply homset_property | ]);
      intro;
      refine (postcompWithBinProductArrow _ _ _ _ _ _ _ @ _);
      do 2 refine (maponpaths _ (id_right _) @ _);
      refine (maponpaths _ (!id_left _) @ _);
      refine (maponpaths (λ x, _ x _) _ @ !BinProductArrowEta _ _ _ _ _ _);
      refine (assoc' _ _ _ @ _);
      [ refine (maponpaths _ (z_iso_inv_after_z_iso _) @ _)
      | refine (maponpaths _ (z_iso_after_z_iso_inv _) @ _) ];
      refine (id_right _ @ _);
      exact (!id_left _)
  ).
Defined.

Definition is_exponentiable_z_iso
  {C : category}
  {c c' : C}
  {BP : BinProducts C}
  (H : is_exponentiable BP c)
  (f : z_iso c c')
  : is_exponentiable BP c'
  := is_left_adjoint_z_iso _ _ (constprod_functor1_z_iso BP f) H.

Lemma stn_eq
  {n : nat}
  (i i' : stn n)
  (H : pr1 i = pr1 i')
  : i = i'.
Proof.
  use subtypePath.
  - intro.
    apply isasetbool.
  - exact H.
Qed.

Definition eqstnweq
  {n n' : nat}
  (H : n = n')
  : stn n ≃ stn n'.
Proof.
  use weq_iso.
  - intro i.
    refine (make_stn _ i _).
    abstract exact (transportf (λ x, i < x) H (stnlt i)).
  - intro i.
    refine (make_stn _ i _).
    abstract exact (transportf (λ x, i < x) (!H) (stnlt i)).
  - abstract (intro i; now apply stn_eq).
  - abstract (intro i; now apply stn_eq).
Defined.

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
    := products_presheaf_cat _ _ _.

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

    Context (p : nat).

    Local Definition stnweq {n : nat}
      : stn n ⨿ stn p ≃ stn (p + n)
      := ((eqstnweq (natpluscomm _ _)) ∘ (weqfromcoprodofstn n p))%weq.

    Definition plus_p_presheaf_data'
      (P : presheaf L)
      : presheaf_data' L.
    Proof.
      - use make_presheaf_data'.
        + exact (λ n, P (p + n)).
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

    Definition presheaf_exponent_morphism_data
      (P : presheaf L)
      (n : nat)
      (t : ((constprod_functor1 presheaf_BinProducts (power theory_presheaf p) (plus_p_presheaf P) : presheaf L) n : hSet))
      : (P n : hSet).
    Proof.
      refine (action (P := P) (pr2 t) _).
      intro i.
      induction (invmap stnweq i) as [i' | i'].
      * exact (pr i').
      * exact (pr1 t i').
    Defined.

    Lemma presheaf_exponent_is_morphism
      (P : presheaf L)
      (m n : nat)
      (a : ((constprod_functor1 presheaf_BinProducts (power theory_presheaf p) (plus_p_presheaf P) : presheaf L) m : hSet))
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
      : presheaf_morphism (constprod_functor1 presheaf_BinProducts (power theory_presheaf p) (plus_p_presheaf P) : presheaf L) P
      := make_presheaf_morphism' _ (presheaf_exponent_is_morphism P).

    Definition presheaf_exponent_induced_morphism_data
      {P P' : presheaf L}
      (F : presheaf_morphism (constprod_functor1 presheaf_BinProducts (power theory_presheaf p) P' : presheaf _) P)
      (n : nat)
      (t : (P' n : hSet))
      : plus_p_presheaf P n : hSet.
    Proof.
      refine (F (p + n) _).
      split.
      - intro i.
        exact (pr (stnweq (inr i))).
      - apply (action t).
        intro i.
        exact (pr (stnweq (inl i))).
    Defined.

    Lemma presheaf_exponent_induced_is_morphism
      {P P' : presheaf L}
      (F : presheaf_morphism (constprod_functor1 presheaf_BinProducts (power theory_presheaf p) P' : presheaf _) P)
      (m n : finite_set_skeleton_category)
      (a : P' m : hSet)
      (f : (⟦ m ⟧)%stn → L n : hSet)
      : presheaf_exponent_induced_morphism_data F n (action a f) = action (presheaf_exponent_induced_morphism_data F m a) f.
    Proof.
      refine (!_ @ presheaf_morphism_commutes_with_action F _ _).
      apply (maponpaths (F (p + n))).
      apply pathsdirprod.
      - apply (funextfun (Y := L _ : hSet)).
        intro i.
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
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
      (F : presheaf_morphism (constprod_functor1 presheaf_BinProducts (power theory_presheaf p) P' : presheaf _) P)
      : presheaf_morphism P' (plus_p_presheaf P)
      := make_presheaf_morphism' _ (presheaf_exponent_induced_is_morphism F).

    Lemma presheaf_exponent_induced_morphism_commutes
      {P P' : presheaf L}
      (F : presheaf_morphism (constprod_functor1 presheaf_BinProducts (power theory_presheaf p) P' : presheaf _) P)
      : F = # (constprod_functor1 presheaf_BinProducts (power theory_presheaf p)) (presheaf_exponent_induced_morphism F : presheaf_cat L⟦P', plus_p_presheaf P⟧) · presheaf_exponent_morphism P.
    Proof.
      pose (BPO := ((presheaf_BinProducts (power theory_presheaf p) P') : presheaf_cat L) : presheaf L).
      apply (presheaf_morphism_eq F _).
      intro n.
      refine (!(presheaf_mor_comp (P := BPO) _ _ _ @ _)).
      apply funextfun.
      intro t.
      refine (maponpaths (λ x, action (P := P) (x t) _) (presheaf_mor_comp (P := BPO) (P'' := plus_p_presheaf P) _ _ _) @ _).
      refine (!presheaf_morphism_commutes_with_action F _ _ @ _).
      apply maponpaths.
      apply pathsdirprod.
      - apply funextsec.
        intro i.
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq stnweq _) @ _).
        exact (maponpaths (λ x, pr11 x n t i) (id_right (BinProductPr1 _ (presheaf_BinProducts _ _)))).
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
      (F : presheaf_morphism (constprod_functor1 presheaf_BinProducts (power theory_presheaf p) P' : presheaf _) P)
      (F' : ∑ (f' : presheaf_morphism P' (plus_p_presheaf P)), F = # (constprod_functor1 presheaf_BinProducts (power theory_presheaf p)) (f' : presheaf_cat L ⟦P', plus_p_presheaf P⟧) · presheaf_exponent_morphism P)
      : F' = presheaf_exponent_induced_morphism F,, presheaf_exponent_induced_morphism_commutes F.
    Proof.
      pose (BP := (presheaf_BinProducts (power theory_presheaf p) P')).
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
        exact (maponpaths (λ x, pr11 x _ _ _) (id_right (BinProductPr1 _ BP))).
    Qed.

    Definition theory_presheaf_exponentiable
      : is_exponentiable presheaf_BinProducts (power theory_presheaf p).
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
    = (λ i, let c := invmap (stnweq 1) i in
        coprod_rect (λ _, (L (1 + n) : hSet))
          (λ i', f i' • (λ j, pr (stnweq 1 (inl j))))
          (λ i', pr (stnweq 1 (inr i'))) c).
  Proof.
    apply extend_tuple_eq.
    intro i.
    - refine (algebraic_theory_functor_uses_projections _ _ _ _ _ @ !_).
      refine (maponpaths (λ x, let c := x in _) (_ : _ = inl i) @ _).
      + apply invmap_eq.
        now apply stn_eq.
      + apply (maponpaths (λ x, _ • x)).
        apply funextfun.
        intro.
        apply maponpaths.
        now apply stn_eq.
    - refine (!(maponpaths (λ x, let c := x in _) (_ : _ = inr lastelement) @ _)).
      + apply invmap_eq.
        apply stn_eq.
        exact (!natplusr0 _).
      + apply (maponpaths pr).
        apply stn_eq.
        apply natplusr0.
  Qed.

  Definition theory_presheaf_exponentiable'
    : is_exponentiable presheaf_BinProducts theory_presheaf
    := is_exponentiable_z_iso (theory_presheaf_exponentiable 1)
      (z_iso_between_Product (power theory_presheaf 1) (one_element_product _ _)).

  Definition presheaf_lambda_theory : lambda_theory.
  Proof.
    pose (exponential_object := pr1 theory_presheaf_exponentiable' theory_presheaf : presheaf L).
    use endomorphism_lambda_theory.
    - exact (presheaf_cat L).
    - exact presheaf_Terminal.
    - exact presheaf_BinProducts.
    - exact theory_presheaf.
    - exact theory_presheaf_exponentiable'.
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

  Definition presheaf_lambda_theory_iso
    : z_iso (C := lambda_theory_cat) L presheaf_lambda_theory.
  Proof.
    pose (pow := λ n, EndomorphismTheory.power presheaf_Terminal presheaf_BinProducts theory_presheaf n).
    use make_z_iso.
    - use ((_ ,, _) ,, tt).
      + use (make_algebraic_theory_morphism' (T := pr1 L : algebraic_theory) (T' := pr1 presheaf_lambda_theory : algebraic_theory)).
        * intros n s.
          unfold presheaf_lambda_theory.
          simpl.
          use (make_presheaf_morphism' (P := ((EndomorphismTheory.power _ _ _ n) : presheaf_cat L) : presheaf L) (P' := theory_presheaf)).
          -- intros n' t.
            refine (s • _).
            intro i.
            exact (((ProductPr _ _ (pow n) i) : presheaf_morphism ((pow n : presheaf_cat L) : presheaf L) theory_presheaf) _ t).
          -- abstract (
              intros;
              refine (_ @ !algebraic_theory_comp_is_assoc _ _ _ _ _ _ _);
              apply maponpaths;
              apply funextfun;
              intro;
              now rewrite presheaf_morphism_commutes_with_action
            ).
        * use make_is_algebraic_theory_morphism'.
          -- abstract (
              intros m n f g;
              apply (presheaf_morphism_eq (P := (pow n : presheaf_cat L) : presheaf L) (P' := theory_presheaf));
              intro l;
              refine (_ @ !presheaf_mor_comp (P'' := theory_presheaf) _ _ _);
              apply funextfun;
              intro t;
              refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ !_);
              apply (maponpaths (comp f));
              apply funextfun;
              intro i;
              refine (maponpaths (λ x, x t) (!presheaf_mor_comp _ _ _) @
                maponpaths (λ x, pr11 x l t) (ProductPrCommutes _ _ _ (pow m) _ _ i))
            ).
          -- abstract (
              intros n i;
                apply (presheaf_morphism_eq (P := (pow n : presheaf_cat L) : presheaf L) (P' := theory_presheaf));
              intro m;
              refine (_ @ !presheaf_mor_comp (P'' := theory_presheaf) _ _ _);
              apply funextfun;
              intro t;
              apply algebraic_theory_comp_projects_component
            ).
      + split.
        * intros n s.
          apply (presheaf_morphism_eq _ (_ : presheaf_morphism ((pow (S n) : presheaf_cat L) : presheaf L) theory_presheaf)).
          intro m.
          refine (!_).
          refine (presheaf_mor_comp (P := pow (S n)) (P'' := theory_presheaf) _ _ _ @ _).
          refine (maponpaths _ (presheaf_mor_comp (P := presheaf_BinProducts _ _) _ _ m) @ _).
          simpl.
          apply funextfun.
          intro t.
          etrans.
          simpl.
          apply maponpaths_2.
          apply maponpaths_2.
          apply funextfun.
          intro.
          use pathsdirprod.
          Focus 3.
          match goal with
          | [|- _ _ (_ ?a) _ _ = _] => pose a
          end.
          exact (maponpaths (λ x, x _) (presheaf_mor_comp (P := presheaf_BinProducts (one_element_product (presheaf_cat L) theory_presheaf)
      (plus_p_presheaf 1 theory_presheaf)) _ _ m)).
          apply (maponpaths (λ x, (x ,, _))).
          apply maponpaths.
          simpl.
          simpl in p.
          simpl in t0.
          exact (presheaf_mor_comp (P := presheaf_BinProducts _ _) _ _ m).
          apply maponpaths_2.
          apply maponpaths.
          apply maponpaths.
          simpl.
          unfold presheaf_exponent_morphism_data.
          unfold compose.
          simpl.
          unfold comp.
          simpl.
          simpl.
          Set Printing Coercions.
          refine (presheaf_mor_comp (P := pow n) (P'' := plus_p_presheaf 1 theory_presheaf) _ _ _ @ _).
          cbn.
          unfold BinProductPr2.
          simpl.

    - use (make_lambda_theory_morphism (L := presheaf_lambda_theory) (L' := L)).
      use make_lambda_theory_data_morphism.
      + use make_algebraic_theory_morphism'.
        * refine (λ _ (l : presheaf_morphism ((power theory_presheaf _ : presheaf_cat L) : presheaf L) theory_presheaf), _).
          exact (l _ pr).
        * admit.
      + admit.
  Defined.

End RepresentationTheorm.
