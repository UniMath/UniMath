(**

 The set model of extensional type theory

 We show that sets form a model of extensional type theory, and that this model supports
 various type formers. Our approach is based on the fibration of set families: we have
 a fibration over the category of sets such that the objects over a set `X` are families
 `X → hSet`. Note that this fibration is equivalent to the codomain fibration over the
 category of sets, and thus the family fibrations provides an alternative way to construct
 the set model. We also show that the set model supports various type formers, which we
 use to conclude that sets form an elementary topos with an NNO. We also give concrete
 descriptions of various operations for terms in the comprehension category for the
 set model of type theory.

 Content
 1. The full comprehension category for the set model
 2. The set model is democratic
 3. The set model supports dependent sums
 4. The DFL full comprehension category for the set model
 5. Dependent products in the set model
 6. The subobject classifier and the natural numbers in the set model
 7. Sets form an elementary topos with an NNO
 8. Terms in the set model
 9. Useful calculational lemmas
 10. Calculational lemmas regarding ∏-types
 11. Propositions in the set model

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Reflections.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.SetFams.
Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.PowerObject.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.HPropMono.
Require Import UniMath.Bicategories.ComprehensionCat.PiTypeNotations.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.Democracy.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.EqualizerTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.ProductTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.UnitTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.SigmaTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatWithProp.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.PiTypesBiequiv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. The full comprehension category for the set model *)
Definition set_cat_with_terminal_disp_cat
  : cat_with_terminal_disp_cat.
Proof.
  use make_cat_with_terminal_disp_cat.
  - exact HSET_univalent_category.
  - exact TerminalHSET.
  - exact univalent_fam_disp_cat.
Defined.

Definition set_cat_with_terminal_cleaving
  : cat_with_terminal_cleaving.
Proof.
  use make_cat_with_terminal_cleaving.
  - exact set_cat_with_terminal_disp_cat.
  - exact cleaving_fam_disp_cat.
Defined.

Definition set_comprehension_functor
  : comprehension_functor set_cat_with_terminal_cleaving.
Proof.
  use make_comprehension_functor.
  - exact fam_disp_cat_comprehension.
  - exact is_cartesian_fam_disp_cat_comprehension.
Defined.

Definition set_comp_cat
  : comp_cat.
Proof.
  use make_comp_cat.
  - exact set_cat_with_terminal_cleaving.
  - exact set_comprehension_functor.
Defined.

Definition set_full_comp_cat
  : full_comp_cat.
Proof.
  use make_full_comp_cat.
  - exact set_comp_cat.
  - exact disp_functor_ff_fam_disp_cat_comprehension.
Defined.

(** * 2. The set model is democratic *)
Definition is_democratic_set_full_comp_cat
  : is_democratic set_full_comp_cat.
Proof.
  refine (λ (X : hSet), (λ _, X) ,, _).
  use make_z_iso.
  - exact (λ x, tt ,, x).
  - exact (λ x, pr2 x).
  - abstract
      (split ;
       use funextsec ;
       intro x ;
       [ apply idpath | ] ;
       cbn ;
       induction x as [ z x ] ;
       induction z ;
       apply idpath).
Defined.

(** * 3. The set model supports dependent sums *)
Section SetDependentSum.
  Context {X : set_full_comp_cat}
          (Y : ty X).

  Definition set_dependent_sum_data
             (Z : ty (X & Y))
    : reflection_data
        (D := fam_disp_cat[{_}])
        Z
        (fiber_functor_from_cleaving
           (disp_cat_of_types set_full_comp_cat)
           (cleaving_of_types set_full_comp_cat)
           (π Y)).
  Proof.
    use make_reflection_data.
    - exact (λ x, ∑ (y : Y x), Z (x ,, y))%set.
    - exact (λ xy z, pr2 xy ,, z).
  Defined.

  Definition is_reflection_set_dependent_sum_data
             (Z : ty (X & Y))
    : is_reflection (set_dependent_sum_data Z).
  Proof.
    intros [ W ff ].
    use make_iscontr.
    - simple refine (_ ,, _).
      + exact (λ x yz, ff (x ,, pr1 yz) (pr2 yz)).
      + abstract
          (use funextsec ; intro xy ;
           use funextsec ; intro z ;
           cbn -[fiber_category fiber_functor_from_cleaving] ;
           rewrite fam_disp_cat_fiber_comp ;
           rewrite (fam_disp_cat_fiber_functor_from_cleaving (π Y) _ _) ;
           cbn ;
           apply idpath).
    - abstract
        (intros gg ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use funextsec ; intro x ;
         use funextsec ; intro yz ;
         cbn ;
         refine (_ @ !(eqtohomot (eqtohomot (pr2 gg) (x ,, pr1 yz)) (pr2 yz))) ;
         cbn -[fiber_category fiber_functor_from_cleaving] ;
         rewrite fam_disp_cat_fiber_comp ;
         rewrite (fam_disp_cat_fiber_functor_from_cleaving (π Y) _ _) ;
         cbn ;
         apply idpath).
  Defined.

  Definition set_dependent_sum
    : dependent_sum (cleaving_of_types set_full_comp_cat) (π Y).
  Proof.
    use reflections_to_is_right_adjoint.
    intro Z.
    use make_reflection.
    - exact (set_dependent_sum_data Z).
    - exact (is_reflection_set_dependent_sum_data Z).
  Defined.

  Proposition set_dependent_sum_counit
              (Z : ty X)
              {x : (X : hSet)}
              {y : Y x}
              (z : Z x)
    : counit_from_right_adjoint set_dependent_sum Z x (y ,, z) = z.
  Proof.
    apply idpath.
  Qed.

  Proposition set_dependent_sum_mor
              {Z₁ Z₂ : ty (X & Y)}
              (ff : Z₁ <: Z₂)
              (x : (X : hSet))
              (y : Y x)
              (z : Z₁ (x ,, y))
    : #(left_adjoint set_dependent_sum) ff x (y ,, z) = (y ,, ff (x ,, y) z).
  Proof.
    cbn -[fiber_category].
    rewrite fam_disp_cat_fiber_comp.
    cbn.
    apply idpath.
  Qed.
End SetDependentSum.

Proposition set_left_beck_chevalley_nat_trans_eq
            {X₁ X₂ : set_full_comp_cat}
            (Y : ty X₂)
            (s : X₁ --> X₂)
            (Z : (disp_cat_of_types set_full_comp_cat)[{X₂ & Y}])
  : left_beck_chevalley_nat_trans
      (set_dependent_sum Y) (set_dependent_sum (Y [[ s ]]))
      (comm_nat_z_iso
         (cleaving_of_types set_full_comp_cat)
         (π Y)
         s
         (π (Y [[s]]))
         (comprehension_functor_mor
            (comp_cat_comprehension set_full_comp_cat)
            (cleaving_of_types set_full_comp_cat X₂ X₁ s Y))
         (comprehension_functor_mor_comm
            (comp_cat_comprehension set_full_comp_cat)
            (cleaving_of_types set_full_comp_cat X₂ X₁ s Y)))
      Z
    =
    λ x yz, yz.
Proof.
  rewrite left_beck_chevalley_nat_trans_ob.
  rewrite <- functor_comp.
  use funextsec ; intro x.
  use funextsec ; intros [ y z ].
  rewrite !fam_disp_cat_fiber_comp.
  rewrite set_dependent_sum_counit.
  rewrite set_dependent_sum_mor.
  rewrite fam_disp_cat_fiber_comp.
  cbn -[fiber_functor_from_cleaving comm_nat_z_iso].
  etrans.
  {
    apply maponpaths.
    pose ((λ xy, s (pr1 xy) ,, pr2 xy) : SET ⟦ total2_hSet (λ z, Y(s z)) , total2_hSet Y ⟧)
      as f.
    exact (fam_disp_cat_fiber_functor_from_cleaving f _ _).
  }
  cbn -[fiber_functor_from_cleaving comm_nat_z_iso].
  etrans.
  {
    exact (fam_disp_cat_comm_nat_z_iso
            _ s _
            (comprehension_functor_mor
            (comp_cat_comprehension set_full_comp_cat)
            (cleaving_of_types set_full_comp_cat X₂ X₁ s Y))
            (comprehension_functor_mor_comm
               set_comprehension_functor
               (λ (x : (X₁ : hSet)) (y : Y(s x)), y))
            (λ x, (∑ y, Z (x ,, y))%set)
            (x := (x ,,y))
            (y ,, z)).
  }
  cbn.
  apply (transportf_set (λ x, ∑ (y : Y x), Z (x ,, y))).
  apply setproperty.
Qed.

Definition dependent_sum_set_full_comp_cat
  : comp_cat_dependent_sum set_full_comp_cat.
Proof.
  use make_comp_cat_dependent_sum_from_chosen.
  use make_comp_cat_dependent_sum_chosen.
  - exact (λ X Y, set_dependent_sum Y).
  - intros X₁ X₂ Y s Z.
    use is_z_isomorphism_path.
    + exact (λ x yz, yz).
    + exact (!(set_left_beck_chevalley_nat_trans_eq Y s Z)).
    + apply (is_z_isomorphism_identity (C := fam_disp_cat [{ _ }])).
Defined.

Definition strong_dependent_sum_set_full_comp_cat
  : strong_dependent_sums set_full_comp_cat.
Proof.
  refine (dependent_sum_set_full_comp_cat ,, _).
  intros X Y Z.
  use make_is_z_isomorphism.
  - exact (λ xyz, (pr1 xyz ,, pr12 xyz) ,, pr22 xyz).
  - abstract (split ; apply idpath).
Defined.

(** * 4. The DFL full comprehension category for the set model *)
Definition set_dfl_full_comp_cat
  : dfl_full_comp_cat.
Proof.
  use make_dfl_full_comp_cat.
  - exact set_full_comp_cat.
  - exact is_democratic_set_full_comp_cat.
  - exact fam_disp_cat_fiberwise_terminal.
  - intros X.
    use make_is_z_isomorphism.
    + exact (λ x, x ,, tt).
    + abstract
        (split ;
         use funextsec ;
         intro x ;
         [ | apply idpath ] ;
         induction x as [ x z ] ;
         induction z ;
         apply idpath).
  - exact fam_disp_cat_fiberwise_binproduct.
  - exact fam_disp_cat_fiberwise_equalizers.
  - exact strong_dependent_sum_set_full_comp_cat.
Defined.

(** * 5. Dependent products in the set model *)
Section SetDependentProd.
  Context {X : set_full_comp_cat}
          (Y : ty X).

  Definition set_dependent_prod_data
             (Z : ty (X & Y))
    : coreflection_data
        (D := fam_disp_cat[{_}])
        Z
        (fiber_functor_from_cleaving
           (disp_cat_of_types set_full_comp_cat)
           (cleaving_of_types set_full_comp_cat)
           (π Y)).
  Proof.
    use make_coreflection_data.
    - exact (λ x, ∏ (y : Y x), Z (x ,, y))%set.
    - exact (λ xy f, f (pr2 xy)).
  Defined.

  Definition is_coreflection_set_dependent_sum_data
             (Z : ty (X & Y))
    : is_coreflection (set_dependent_prod_data Z).
  Proof.
    intros [ W ff ].
    use make_iscontr.
    - simple refine (_ ,, _).
      + exact (λ x w y, ff (x ,, y) w).
      + abstract
          (use funextsec ; intro xy ;
           use funextsec ; intro f ;
           cbn -[fiber_category fiber_functor_from_cleaving] ;
           rewrite fam_disp_cat_fiber_comp ;
           rewrite (fam_disp_cat_fiber_functor_from_cleaving (π Y) _ _) ;
           apply idpath).
    - abstract
        (intros gg ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use funextsec ; intro x ;
         use funextsec ; intro w ;
         use funextsec ; intro y ;
         cbn ;
         refine (_ @ !(eqtohomot (eqtohomot (pr2 gg) (x ,, y)) w)) ;
         cbn -[fiber_category fiber_functor_from_cleaving] ;
         rewrite fam_disp_cat_fiber_comp ;
         rewrite (fam_disp_cat_fiber_functor_from_cleaving (π Y) _ _) ;
         cbn ;
         apply idpath).
  Defined.

  Definition set_dependent_product
    : dependent_product (cleaving_of_types set_full_comp_cat) (π Y).
  Proof.
    use coreflections_to_is_left_adjoint.
    intro Z.
    use make_coreflection.
    - exact (set_dependent_prod_data Z).
    - exact (is_coreflection_set_dependent_sum_data Z).
  Defined.

  Proposition set_dependent_product_unit
              (Z : ty X)
              {x : (X : hSet)}
              (z : Z x)
              (y : Y x)
    : unit_from_left_adjoint set_dependent_product Z x z y = z.
  Proof.
    cbn.
    apply idpath.
  Qed.

  Proposition set_dependent_product_mor
              {Z₁ Z₂ : ty (X & Y)}
              (ff : Z₁ <: Z₂)
              {x : (X : hSet)}
              (g : ∏ (y : Y x), Z₁ (x ,, y))
              (y : Y x)
    : #(right_adjoint set_dependent_product) ff x g y = ff (x ,, y) (g y).
  Proof.
    cbn -[fiber_category].
    rewrite fam_disp_cat_fiber_comp.
    cbn.
    apply idpath.
  Qed.
End SetDependentProd.

Proposition set_right_beck_chevalley_nat_trans_eq
            {X₁ X₂ : set_full_comp_cat}
            (Y : ty X₂)
            (s : X₁ --> X₂)
            (Z : (disp_cat_of_types set_full_comp_cat)[{X₂ & Y}])
  : right_beck_chevalley_nat_trans
      (set_dependent_product Y) (set_dependent_product (Y [[ s ]]))
      (comm_nat_z_iso_inv
         (cleaving_of_types set_full_comp_cat)
         (π Y)
         s
         (π (Y [[s]]))
         (comprehension_functor_mor
            (comp_cat_comprehension set_full_comp_cat)
            (cleaving_of_types set_full_comp_cat X₂ X₁ s Y))
         (comprehension_functor_mor_comm
            (comp_cat_comprehension set_full_comp_cat)
            (cleaving_of_types set_full_comp_cat X₂ X₁ s Y)))
      Z
    =
    λ x yz, yz.
Proof.
  rewrite right_beck_chevalley_nat_trans_ob.
  rewrite assoc'.
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply (functor_comp (right_adjoint (set_dependent_product _))).
  }
  use funextsec ; intro x.
  use funextsec ; intro f.
  use funextsec ; intro y.
  rewrite fam_disp_cat_fiber_comp.
  rewrite set_dependent_product_mor.
  rewrite fam_disp_cat_fiber_comp.
  rewrite set_dependent_product_unit.
  etrans.
  {
    exact (fam_disp_cat_fiber_functor_from_cleaving _ _ _).
  }
  cbn -[comm_nat_z_iso_inv].
  etrans.
  {
    refine (maponpaths (λ h, h y) _).
    exact (fam_disp_cat_comm_nat_z_iso_inv
             _ _ _ _
             (comprehension_functor_mor_comm
                set_comprehension_functor
                (λ (x : (X₁ : hSet)) (y : Y(s x)), y))
             (λ x, (∏ y : Y x, Z (x ,, y))%set)
             (x := (x ,, y))
             f).
  }
  cbn.
  refine (maponpaths (λ h, h y) _).
  apply (transportf_set (λ x, ∏ (y : Y x), Z (x ,, y))).
  apply setproperty.
Qed.

Definition dependent_prod_set_comp_cat
  : comp_cat_dependent_prod set_full_comp_cat.
Proof.
  use make_comp_cat_dependent_prod_from_chosen.
  use make_comp_cat_dependent_prod_chosen.
  - exact (λ X Y, set_dependent_product Y).
  - intros X₁ X₂ Y s Z.
    use is_z_isomorphism_path.
    + exact (λ x yz, yz).
    + exact (!(set_right_beck_chevalley_nat_trans_eq Y s Z)).
    + apply (is_z_isomorphism_identity (C := fam_disp_cat [{ _ }])).
Defined.

(** * 6. The subobject classifier and the natural numbers in the set model *)
Definition subobject_classifier_set_comp_cat
  : fiberwise_cat_property
      subobject_classifier_local_property
      set_dfl_full_comp_cat.
Proof.
  use make_fiberwise_cat_property.
  - exact fam_disp_cat_fiber_subobject_classifier.
  - intros X₁ X₂ s.
    exact (preserves_subobject_classifier_fiber_functor_fam_disp_cat s).
Defined.

Definition pnno_set_comp_cat
  : fiberwise_cat_property
      parameterized_NNO_local_property
      set_dfl_full_comp_cat.
Proof.
  use make_fiberwise_cat_property.
  - intro X.
    refine (_ ,, _ ,, _ ,, _).
    exact (is_parameterized_NNO_prod_independent
             (C := univalent_fiber_category
                     univalent_fam_disp_cat
                     X)
             _
             (fam_disp_cat_fiber_parameterized_NNO X)).
  - intros X₁ X₂ f.
    use preserves_parameterized_NNO_prod_independent.
    exact (set_fiberwise_nno_stable f).
Defined.

(** * 7. Sets form an elementary topos with an NNO *)
Definition set_univ_cat_with_finlim
  : univ_cat_with_finlim
  := dfl_full_comp_cat_to_finlim set_dfl_full_comp_cat.

Definition is_locally_cartesian_closed_set_univ_cat_with_finlim
  : is_locally_cartesian_closed
      (pullbacks_univ_cat_with_finlim set_univ_cat_with_finlim)
  := dfl_comp_cat_to_finlim_disp_psfunctor_pi_types_ob
       set_dfl_full_comp_cat
       dependent_prod_set_comp_cat.

Definition set_univ_cat_subobject_classifier
  : subobject_classifier TerminalHSET
  := local_property_in_dfl_comp_cat
       subobject_classifier_local_property
       set_dfl_full_comp_cat
       subobject_classifier_set_comp_cat.

Definition set_univ_cat_pnno
  : parameterized_NNO
      TerminalHSET
      (binproducts_univ_cat_with_finlim
         set_univ_cat_with_finlim)
  := local_property_in_dfl_comp_cat
       parameterized_NNO_local_property
       set_dfl_full_comp_cat
       pnno_set_comp_cat.

Definition set_topos
  : Topos.
Proof.
  use make_Topos.
  - exact set_univ_cat_with_finlim.
  - use make_Topos_Structure.
    + exact (pullbacks_univ_cat_with_finlim set_univ_cat_with_finlim).
    + exact (terminal_univ_cat_with_finlim set_univ_cat_with_finlim).
    + exact set_univ_cat_subobject_classifier.
    + use PowerObject_from_exponentials.
      use is_locally_cartesian_closed_exponentials.
      exact is_locally_cartesian_closed_set_univ_cat_with_finlim.
Defined.

(** * 8. Terms in the set model *)
Definition set_comp_cat_tm_to_sec
           {Γ : set_dfl_full_comp_cat}
           {A : ty Γ}
           (t : tm Γ A)
           (γ : (Γ : hSet))
  : A γ
  := transportf A (eqtohomot (comp_cat_tm_eq t) γ) (pr2 (comp_cat_tm_to_mor t γ)).

Definition set_comp_cat_sec_to_tm
           {Γ : set_dfl_full_comp_cat}
           {A : ty Γ}
           (t : ∏ (γ : (Γ : hSet)), A γ)
  : tm Γ A.
Proof.
  use make_comp_cat_tm.
  - exact (λ γ, γ ,, t γ).
  - apply idpath.
Defined.

Arguments set_comp_cat_tm_to_sec /.
Arguments set_comp_cat_sec_to_tm /.

Proposition set_comp_cat_tm_to_sec_to_tm
            {Γ : set_dfl_full_comp_cat}
            {A : ty Γ}
            (t : tm Γ A)
  : set_comp_cat_sec_to_tm (set_comp_cat_tm_to_sec t) = t.
Proof.
  use eq_comp_cat_tm.
  use funextsec.
  intro γ.
  refine (!_).
  use total2_paths_f.
  {
    exact (eqtohomot (comp_cat_tm_eq t) γ).
  }
  apply idpath.
Qed.

Proposition set_comp_cat_sec_to_tm_to_sec
            {Γ : set_dfl_full_comp_cat}
            {A : ty Γ}
            (t : ∏ (γ : (Γ : hSet)), A γ)
  : set_comp_cat_tm_to_sec (set_comp_cat_sec_to_tm t) = t.
Proof.
  use funextsec.
  intro x.
  apply (transportf_set A).
  apply setproperty.
Qed.

Definition set_comp_cat_tm_weq
           {Γ : set_dfl_full_comp_cat}
           (A : ty Γ)
  : tm Γ A ≃ ∏ (γ : (Γ : hSet)), A γ.
Proof.
  use weq_iso.
  - exact set_comp_cat_tm_to_sec.
  - exact set_comp_cat_sec_to_tm.
  - exact set_comp_cat_tm_to_sec_to_tm.
  - exact set_comp_cat_sec_to_tm_to_sec.
Defined.

Proposition set_comp_cat_tm_subst
            {Γ Δ : set_dfl_full_comp_cat}
            {A : ty Γ}
            (t : tm Γ A)
            (s : Δ --> Γ)
  : t [[ s ]]tm
    =
    set_comp_cat_sec_to_tm (λ γ, set_comp_cat_tm_to_sec t (s γ)).
Proof.
  use eq_comp_cat_tm ; cbn.
  refine (!_).
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback A s))).
  - use funextsec ; intro γ ; cbn.
    refine (!_).
    use total2_paths_f.
    + exact (eqtohomot (comp_cat_tm_eq t) (s γ)).
    + cbn.
      apply idpath.
  - cbn.
    apply idpath.
Qed.

Proposition set_comp_cat_tm_coerce
            {Γ : set_dfl_full_comp_cat}
            {A B : ty Γ}
            (f : A <: B)
            (t : tm Γ A)
  : t ↑ f
    =
    set_comp_cat_sec_to_tm (λ γ, f γ (set_comp_cat_tm_to_sec t γ)).
Proof.
  use eq_comp_cat_tm ; cbn.
  use funextsec.
  intro γ.
  use total2_paths_f ; cbn.
  - exact (eqtohomot (comp_cat_tm_eq t) γ).
  - rewrite transport_map.
    apply idpath.
Qed.

(** * 9. Useful calculational lemmas *)
Proposition set_comp_cat_id_subst_ty
            {Γ : set_dfl_full_comp_cat}
            (A : ty Γ)
            {γ : (Γ : hSet)}
            (a : A γ)
  : id_subst_ty A γ a = a.
Proof.
  etrans.
  {
    exact (fam_disp_cat_transportb _ _ _ _).
  }
  apply (transportf_set A).
  apply setproperty.
Qed.

Proposition set_comp_cat_id_subst_ty_inv
            {Γ : set_dfl_full_comp_cat}
            (A : ty Γ)
            {γ : (Γ : hSet)}
            (a : A γ)
  : id_subst_ty_inv A γ a = a.
Proof.
  etrans.
  {
    exact (fam_disp_cat_transportf _ _ _ _).
  }
  cbn.
  etrans.
  {
    apply maponpaths.
    exact (fam_disp_cat_transportf _ _ _ _).
  }
  rewrite transport_f_f.
  apply (transportf_set A).
  apply setproperty.
Qed.

Proposition set_comp_cat_comp_subst_ty
            {Γ₁ Γ₂ Γ₃ : set_dfl_full_comp_cat}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (A : ty Γ₃)
            {γ : (Γ₁ : hSet)}
            (a : A (s₂ (s₁ γ)))
  : comp_subst_ty s₁ s₂ A γ a = a.
Proof.
  cbn.
  etrans.
  {
    exact (fam_disp_cat_transportb _ _ _ _).
  }
  apply (transportf_set A).
  apply setproperty.
Qed.

Proposition set_comp_cat_comp_subst_ty_inv
            {Γ₁ Γ₂ Γ₃ : set_dfl_full_comp_cat}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (A : ty Γ₃)
            {γ : (Γ₁ : hSet)}
            (a : A (s₂ (s₁ γ)))
  : comp_subst_ty_inv s₁ s₂ A γ a = a.
Proof.
  cbn.
  etrans.
  {
    exact (fam_disp_cat_transportf _ _ _ _).
  }
  apply (transportf_set A).
  apply setproperty.
Qed.

Proposition set_comp_cat_comp_subst_ty_inv'
            {Γ₁ Γ₂ Γ₃ : set_dfl_full_comp_cat}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (A : ty Γ₃)
  : comp_subst_ty_inv s₁ s₂ A = λ γ a, a.
Proof.
  use funextsec ; intro γ.
  use funextsec ; intro a.
  apply set_comp_cat_comp_subst_ty_inv.
Qed.

Proposition set_comp_cat_eq_subst_ty
            {Γ₁ Γ₂ : set_dfl_full_comp_cat}
            {s₁ s₂ : Γ₁ --> Γ₂}
            (A : ty Γ₂)
            (p : s₁ = s₂)
            {γ : (Γ₁ : hSet)}
            (a : A (s₁ γ))
  : eq_subst_ty A p γ a = transportf A (eqtohomot p γ) a.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition set_comp_cat_eq_subst_ty_inv
            {Γ₁ Γ₂ : set_dfl_full_comp_cat}
            {s₁ s₂ : Γ₁ --> Γ₂}
            (A : ty Γ₂)
            (p : s₁ = s₂)
            {γ : (Γ₁ : hSet)}
            (a : A (s₂ γ))
  : eq_subst_ty_inv A p γ a = transportb A (eqtohomot p γ) a.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition set_comp_cat_coerce_subst_ty
            {Γ₁ Γ₂ : set_dfl_full_comp_cat}
            (s : Γ₁ --> Γ₂)
            {A B : ty Γ₂}
            (f : A <: B)
            {γ : (Γ₁ : hSet)}
            (a : A (s γ))
  : coerce_subst_ty s f γ a = f (s γ) a.
Proof.
  cbn -[fam_disp_cat].
  etrans.
  {
    exact (fam_disp_cat_transportf _ _ _ _).
  }
  apply (transportf_set B).
  apply setproperty.
Qed.

Proposition set_comp_cat_sub_to_extension
            {Γ Δ : set_dfl_full_comp_cat}
            {A : ty Γ}
            (s : Δ --> Γ)
            (t : tm Δ (A [[ s ]]))
            (δ : (Δ : hSet))
  : sub_to_extension s t δ = s δ ,, set_comp_cat_tm_to_sec t δ.
Proof.
  cbn.
  use total2_paths_f ; cbn.
  - apply maponpaths.
    exact (eqtohomot (comp_cat_tm_eq t) δ).
  - rewrite (functtransportf s A).
    apply idpath.
Qed.

Proposition set_comp_cat_tm_var
            (Γ : set_dfl_full_comp_cat)
            (A : ty Γ)
  : comp_cat_tm_var Γ A = set_comp_cat_sec_to_tm (Γ := Γ & A) (λ γa, pr2 γa).
Proof.
  use eq_comp_cat_tm.
  refine (!_).
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback A (pr1 : Γ & A --> Γ)))).
  - cbn.
    apply idpath.
  - cbn.
    apply idpath.
Qed.

(**
   While a lot of the following lemmas hold by reflexivity, it can be more convenient to
   rewrite using the lemmas below instead of doing a full computation.
 *)
Proposition set_comp_cat_comp_mor_over_sub
            {Γ : set_dfl_full_comp_cat}
            {A₁ A₂ : ty Γ}
            {B₁ : ty (Γ & A₁)}
            {B₂ : ty (Γ & A₂)}
            (f : A₁ -->[ identity _ ] A₂)
            (g : B₁ <: B₂ [[ comp_cat_comp_mor f ]])
  : comp_cat_comp_mor_over_sub f g = λ x, (pr11 x ,, f _ (pr21 x)) ,, g _ (pr2 x).
Proof.
  apply idpath.
Qed.

Proposition set_comp_cat_comp_mor_over_sub'
            {Γ : set_dfl_full_comp_cat}
            {A₁ A₂ : ty Γ}
            {B₁ : ty (Γ & A₁)}
            {B₂ : ty (Γ & A₂)}
            (f : A₁ -->[ identity _ ] A₂)
            {g₁ g₂ : B₁ <: B₂ [[ comp_cat_comp_mor f ]]}
            (p : g₁ = g₂)
  : comp_cat_comp_mor_over_sub f g₁ = λ x, (pr11 x ,, f _ (pr21 x)) ,, g₂ _ (pr2 x).
Proof.
  induction p.
  apply idpath.
Qed.

Proposition set_comp_cat_subst
            {Γ Δ : set_dfl_full_comp_cat}
            {A : ty Δ}
            (s : Γ --> Δ)
            {γ : (Γ : hSet)}
            (x : A (s γ))
  : comp_cat_subst A s γ x = x.
Proof.
  apply idpath.
Qed.

Proposition set_comp_cat_extend_over
            {Γ₁ Γ₂ : set_dfl_full_comp_cat}
            (A : ty Γ₂)
            (s : Γ₁ --> Γ₂)
  : comp_cat_extend_over A s = λ x, s (pr1 x) ,, pr2 x.
Proof.
  apply idpath.
Qed.

Proposition set_comp_cat_comp_mor_over
            {Γ₁ Γ₂ : set_dfl_full_comp_cat}
            {A : ty Γ₁}
            {B : ty Γ₂}
            (s : Γ₁ --> Γ₂)
            (f : A <: B [[ s ]])
  : comp_cat_comp_mor_over s f = λ x, s (pr1 x) ,, f _ (pr2 x).
Proof.
  apply idpath.
Qed.

Proposition set_comp_cat_comp_mor_over'
            {Γ₁ Γ₂ : set_dfl_full_comp_cat}
            {A : ty Γ₁}
            {B : ty Γ₂}
            (s : Γ₁ --> Γ₂)
            {f₁ f₂ : A <: B [[ s ]]}
            (p : f₁ = f₂)
  : comp_cat_comp_mor_over s f₁ = λ x, s (pr1 x) ,, f₂ _ (pr2 x).
Proof.
  induction p.
  apply idpath.
Qed.

(** * 10. Calculational lemmas regarding ∏-types *)
Proposition set_comp_cat_pi_subst_coerce
            {Γ Δ : set_dfl_full_comp_cat}
            (s : Γ --> Δ)
            (A : ty Δ)
            (B : ty (Δ & A))
            {γ : (Γ : hSet)}
            (φ : ∏ (x : A (s γ)), B (s γ ,, x))
  : comp_cat_pi_subst_coerce
      (C := set_dfl_full_comp_cat)
      dependent_prod_set_comp_cat
      A B
      s
      γ
      φ
    =
    φ.
Proof.
  exact (eqtohomot (eqtohomot (set_right_beck_chevalley_nat_trans_eq A s B) γ) φ).
Qed.

Proposition set_comp_cat_pi_subst_coerce_inv
            {Γ Δ : set_dfl_full_comp_cat}
            (s : Γ --> Δ)
            (A : ty Δ)
            (B : ty (Δ & A))
            {γ : (Γ : hSet)}
            (φ : ∏ (x : A (s γ)), B (s γ ,, x))
  : comp_cat_pi_subst_coerce_inv
      (C := set_dfl_full_comp_cat)
      dependent_prod_set_comp_cat
      A B
      s
      γ
      φ
    =
    φ.
Proof.
  pose (maponpaths
          (λ z, z γ φ)
          (z_iso_inv_after_z_iso
             (comp_cat_pi_subst
                (C := set_dfl_full_comp_cat)
                dependent_prod_set_comp_cat
                A B
                s)))
    as p.
  refine (_ @ p).
  rewrite fam_disp_cat_fiber_comp.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    exact (set_comp_cat_pi_subst_coerce s A B φ).
  }
  apply idpath.
Qed.

Proposition set_dep_prod_functor_mor
            {Γ : set_dfl_full_comp_cat}
            (A : ty Γ)
            {B₁ B₂ : ty (Γ & A)}
            (g : B₁ <: B₂)
            {γ : (Γ : hSet)}
            (φ : ∏ (x : A γ), B₁ (γ ,, x))
            (x : A γ)
  : #(dep_prod_functor
        (C := set_dfl_full_comp_cat)
        dependent_prod_set_comp_cat
        A)
      g
      γ
      φ
      x
    =
    g (γ ,, x) (φ x).
Proof.
  cbn -[fiber_category].
  rewrite !fam_disp_cat_fiber_comp.
  cbn.
  apply idpath.
Qed.

Proposition transportf_set_dep_prod
            {Γ : set_dfl_full_comp_cat}
            {A : ty Γ}
            {B : ty (Γ & A)}
            {γ₁ γ₂ : (Γ : hSet)}
            (p : γ₁ = γ₂)
            (φ : ∏ (x : A γ₁), B (γ₁ ,, x))
            (x : A γ₂)
  : transportf
      (dep_prod_cc dependent_prod_set_comp_cat A B)
      p
      φ
      x
    =
    transportf
      B
      (total2_paths_b
         (B := A)
         (s := γ₁ ,, transportb A p x) (s' := γ₂ ,, x)
         p
         (idpath _))
      (φ (transportb A p x)).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition transportf_set_dep_prod_idpath
            {Γ : set_dfl_full_comp_cat}
            {A : ty Γ}
            {B : ty (Γ & A)}
            {γ : (Γ : hSet)}
            (p : γ = γ)
            (φ : ∏ (x : A γ), B (γ ,, x))
            (x : A γ)
  : transportf
      (dep_prod_cc dependent_prod_set_comp_cat A B)
      p
      φ
      x
    =
    φ x.
Proof.
  assert (p = idpath _) as ->.
  {
    apply setproperty.
  }
  cbn.
  apply idpath.
Qed.

Proposition set_comp_cat_pi_coerce_mor
            {Γ : set_dfl_full_comp_cat}
            {A₁ A₂ : ty Γ}
            (f : A₂ <: A₁)
            {B₁ : ty (Γ & A₁)}
            {B₂ : ty (Γ & A₂)}
            (g : B₁ [[ comp_cat_comp_mor (C := set_dfl_full_comp_cat) f ]] <: B₂)
            {γ : (Γ : hSet)}
            (φ : ∏ (x : A₁ γ), B₁ (γ ,, x))
            (x : A₂ γ)
  : comp_cat_pi_coerce_mor
      (C := set_dfl_full_comp_cat)
      dependent_prod_set_comp_cat
      f
      g
      (γ ,, x)
      φ
    =
    g (γ ,, x) (φ (f γ x)).
Proof.
  unfold comp_cat_pi_coerce_mor.
  rewrite !fam_disp_cat_fiber_comp.
  apply maponpaths.
  etrans.
  {
    apply (set_comp_cat_coerce_subst_ty (comp_cat_comp_mor (C := set_dfl_full_comp_cat) f)).
  }
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      apply set_comp_cat_eq_subst_ty.
    }
    exact (set_comp_cat_comp_subst_ty_inv
             (comp_cat_comp_mor (C := set_dfl_full_comp_cat) f)
             (π _)
             _ _).
  }
  cbn -[dep_prod_cc].
  apply transportf_set_dep_prod_idpath.
Qed.

Proposition set_comp_cat_pi_coerce
            {Γ : set_dfl_full_comp_cat}
            {A₁ A₂ : ty Γ}
            (f : A₂ <: A₁)
            {B₁ : ty (Γ & A₁)}
            {B₂ : ty (Γ & A₂)}
            (g : B₁ [[ comp_cat_comp_mor (C := set_dfl_full_comp_cat) f ]] <: B₂)
            {γ : (Γ : hSet)}
            (φ : ∏ (x : A₁ γ), B₁ (γ ,, x))
            (x : A₂ γ)
  : comp_cat_pi_coerce
      (C := set_dfl_full_comp_cat)
      dependent_prod_set_comp_cat
      f
      g
      γ
      φ
      x
    =
    g (γ ,, x) (φ (f γ x)).
Proof.
  unfold comp_cat_pi_coerce.
  rewrite !fam_disp_cat_fiber_comp.
  rewrite set_dep_prod_functor_mor.
  rewrite set_comp_cat_pi_coerce_mor.
  cbn.
  apply idpath.
Qed.

(** * 11. Propositions in the set model *)
Proposition set_comp_cat_hprop_ty
            {Γ : set_dfl_full_comp_cat}
            (A : ty Γ)
            (HA : ∏ (x : (Γ : hSet)), isaprop (A x))
  : is_hprop_ty A.
Proof.
  use mono_ty_to_hprop_ty.
  use (invmap (MonosAreInjective_HSET (π A))).
  use isweqonpathsincl.
  intros y.
  use invproofirrelevance.
  intros [ [ x₁ a₁ ] p₁ ] [ [ x₂ a₂ ] p₂ ].
  cbn in x₁, x₂, a₁, a₂, p₁, p₂.
  use subtypePath.
  {
    intro.
    apply setproperty.
  }
  cbn.
  induction p₁, p₂.
  apply maponpaths.
  apply HA.
Qed.

Proposition set_comp_cat_hprop_ty_inv
            {Γ : set_dfl_full_comp_cat}
            (A : ty Γ)
            (HA : is_hprop_ty A)
            (x : (Γ : hSet))
  : isaprop (A x).
Proof.
  apply hprop_ty_to_mono_ty in HA.
  apply MonosAreInjective_HSET in HA.
  apply isinclweqonpaths in HA.
  use invproofirrelevance.
  intros a₁ a₂.
  pose (proofirrelevance _ (HA x) ((x ,, a₁) ,, idpath _) ((x ,, a₂) ,, idpath _)) as H.
  pose (fiber_paths (maponpaths pr1 H)) as p.
  cbn in p.
  refine (!_ @ p).
  apply (transportf_set A).
  apply setproperty.
Qed.

Proposition set_comp_cat_hprop_ty_weq
            {Γ : set_dfl_full_comp_cat}
            (A : ty Γ)
  : is_hprop_ty A ≃ (∏ (x : (Γ : hSet)), isaprop (A x)).
Proof.
  use weqimplimpl.
  - exact (set_comp_cat_hprop_ty_inv A).
  - exact (set_comp_cat_hprop_ty A).
  - apply isaprop_is_hprop_ty.
  - abstract
      (use impred ; intro ;
       apply isapropisaprop).
Defined.
