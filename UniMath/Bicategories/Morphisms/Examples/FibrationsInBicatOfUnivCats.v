(**
 Fibrations in the bicat of univalent categories

 Contents:
 1. Internal Street Fibrations
 2. Internal Street Opfibrations
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetOpFibration.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.

Local Open Scope cat.

(**
 1. Internal Street Fibrations
 *)
Section InternalSFibToStreetFib.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F : C₁ --> C₂}
          (HF : internal_sfib F).

  Section InternalSFibToStreetFibFactor.
    Context {G₁ G₂ : (unit_category : bicat_of_univ_cats) --> C₁}
            {α : G₁ ==> G₂}
            (Hα : is_cartesian_2cell_sfib F α)
            {z : pr1 C₁}
            {g : z --> pr1 G₂ tt}
            {h : pr1 F z --> pr1 F (pr1 G₁ tt)}
            (q : # (pr1 F) g = h · # (pr1 F) (pr1 α tt)).

    Let Φ : unit_category ⟶ pr1 C₁
      := functor_from_unit z.

    Local Definition internal_sfib_is_cartesian_sfib_factor_nat_trans_1
      : Φ ⟹ pr1 G₂.
    Proof.
      use make_nat_trans.
      - intro x ; induction x.
        exact g.
      - abstract
          (intros x y f ; cbn ;
           induction x ; induction y ;
           cbn ;
           assert (p : f = identity _) ; [ apply isapropunit | ] ;
           rewrite p ;
           refine (id_left _ @ !(id_right _) @ _) ;
           apply maponpaths ;
           refine (!_) ;
           apply functor_id).
    Defined.

    Let ζ := internal_sfib_is_cartesian_sfib_factor_nat_trans_1.

    Local Definition internal_sfib_is_cartesian_sfib_factor_nat_trans_2
      : Φ ∙ F ⟹ G₁ ∙ F.
    Proof.
      use make_nat_trans.
      - intros x ; induction x.
        exact h.
      - abstract
          (intros x y f ; cbn ;
           induction x ; induction y ;
           cbn ;
           assert (p : f = identity _) ; [ apply isapropunit | ] ;
           rewrite p ;
           rewrite (functor_id G₁) ;
           rewrite !(functor_id F) ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Let ξ := internal_sfib_is_cartesian_sfib_factor_nat_trans_2.

    Local Lemma internal_sfib_is_cartesian_sfib_factor_eq
      : post_whisker ζ F
        =
        nat_trans_comp _ _ _ ξ (post_whisker α F).
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; induction x.
      exact q.
    Qed.

    Let p := internal_sfib_is_cartesian_sfib_factor_eq.

    Definition internal_sfib_is_cartesian_sfib_factor
      : z --> pr1 G₁ tt
      := pr1 (is_cartesian_2cell_sfib_factor _ Hα ζ ξ p) tt.

    Definition internal_sfib_is_cartesian_sfib_factor_over
      : # (pr1 F) internal_sfib_is_cartesian_sfib_factor = h.
    Proof.
      exact (nat_trans_eq_pointwise
              (is_cartesian_2cell_sfib_factor_over _ Hα p)
              tt).
    Qed.

    Definition internal_sfib_is_cartesian_sfib_factor_comm
      : internal_sfib_is_cartesian_sfib_factor · pr1 α tt = g.
    Proof.
      exact (nat_trans_eq_pointwise
               (is_cartesian_2cell_sfib_factor_comm _ Hα p)
               tt).
    Qed.

    Local Definition internal_sfib_is_cartesian_sfib_factor_unique_help
               (k : z --> pr1 G₁ tt)
      : Φ ⟹ pr1 G₁.
    Proof.
      use make_nat_trans.
      - intro x ; induction x.
        exact k.
      - abstract
          (intros x y f ;
           induction x ; induction y ; cbn ;
           assert (r : f = identity _) ; [ apply isapropunit | ] ;
           rewrite r ;
           rewrite !(functor_id G₁) ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Definition internal_sfib_is_cartesian_sfib_factor_unique
      : isaprop (∑ φ, # (pr1 F) φ = h × φ · pr1 α tt = g).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      refine (nat_trans_eq_pointwise
                (is_cartesian_2cell_sfib_factor_unique
                   _ Hα
                   Φ ζ ξ p
                   (internal_sfib_is_cartesian_sfib_factor_unique_help (pr1 φ₁))
                   (internal_sfib_is_cartesian_sfib_factor_unique_help (pr1 φ₂))
                   _ _ _ _)
                tt) ;
        (use nat_trans_eq ; [ apply homset_property | ]) ;
        intro x ; induction x ; cbn.
      - exact (pr12 φ₁).
      - exact (pr12 φ₂).
      - exact (pr22 φ₁).
      - exact (pr22 φ₂).
    Qed.
  End InternalSFibToStreetFibFactor.

  Definition internal_sfib_is_cartesian_sfib
             {G₁ G₂ : (unit_category : bicat_of_univ_cats) --> C₁}
             {α : G₁ ==> G₂}
             (Hα : is_cartesian_2cell_sfib F α)
    : is_cartesian_sfib F (pr1 α tt).
  Proof.
    intros z g h q.
    use iscontraprop1.
    - exact (internal_sfib_is_cartesian_sfib_factor_unique Hα q).
    - simple refine (_ ,, _ ,, _).
      + exact (internal_sfib_is_cartesian_sfib_factor Hα q).
      + exact (internal_sfib_is_cartesian_sfib_factor_over Hα q).
      + exact (internal_sfib_is_cartesian_sfib_factor_comm Hα q).
  Defined.

  Section Cleaving.
    Context {e : pr1 C₁}
            {b : pr1 C₂}
            (f : b --> pr1 F e).

    Definition internal_sfib_is_street_fib_nat_trans
      : functor_from_unit b ⟹ functor_from_unit e ∙ F.
    Proof.
      use make_nat_trans.
      - exact (λ _, f).
      - abstract
          (intros z₁ z₂ g ; cbn ;
           rewrite id_left, functor_id, id_right ;
           apply idpath).
    Defined.

    Let ℓ := pr1 HF _ _ _ internal_sfib_is_street_fib_nat_trans.

    Definition internal_sfib_is_street_fib_lift_ob
      : pr1 C₁
      := pr1 (pr1 ℓ) tt.

    Definition internal_sfib_is_street_fib_lift_mor
      : internal_sfib_is_street_fib_lift_ob --> e
      := pr1 (pr12 ℓ) tt.

    Definition internal_sfib_is_street_fib_lift_iso
      : iso (pr1 F internal_sfib_is_street_fib_lift_ob) b
      := nat_iso_pointwise_iso (invertible_2cell_to_nat_iso _ _ (pr122 ℓ)) tt.

    Definition internal_sfib_is_street_fib_lift_over
      : # (pr1 F) internal_sfib_is_street_fib_lift_mor
        =
        internal_sfib_is_street_fib_lift_iso · f
      := nat_trans_eq_pointwise (pr2 (pr222 ℓ)) tt.

    Definition internal_sfib_is_street_fib_lift_cartesian
      : is_cartesian_sfib F internal_sfib_is_street_fib_lift_mor
      := internal_sfib_is_cartesian_sfib (pr1 (pr222 ℓ)).
  End Cleaving.

  Definition internal_sfib_is_street_fib
    : street_fib F.
  Proof.
    intros e b f.
    simple refine (_ ,, (_ ,, _) ,, _ ,, _) ; cbn.
    - exact (internal_sfib_is_street_fib_lift_ob f).
    - exact (internal_sfib_is_street_fib_lift_mor f).
    - exact (internal_sfib_is_street_fib_lift_iso f).
    - exact (internal_sfib_is_street_fib_lift_over f).
    - exact (internal_sfib_is_street_fib_lift_cartesian f).
  Defined.
End InternalSFibToStreetFib.

Section StreetFibToInternalSFib.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F : C₁ --> C₂}
          (HF : street_fib F).

  Section IsCartesian.
    Context {C₀ : bicat_of_univ_cats}
            {G₁ G₂ : C₀ --> C₁}
            (α : G₁ ==> G₂)
            (Hα : ∏ (x : pr1 C₀), is_cartesian_sfib F (pr1 α x)).

    Section Factorization.
      Context {H : C₀ --> C₁}
              {β : H ==> G₂}
              {δp : H · F ==> G₁ · F}
              (q : β ▹ F = δp • (α ▹ F)).

      Definition pointwise_cartesian_is_cartesian_factor_data
        : nat_trans_data (pr1 H) (pr1 G₁)
        := λ x,
           cartesian_factorization_sfib
             _
             (Hα x)
             (pr1 β x)
             (pr1 δp x)
             (nat_trans_eq_pointwise q x).

      Definition pointwise_cartesian_is_cartesian_factor_laws
        : is_nat_trans _ _ pointwise_cartesian_is_cartesian_factor_data.
      Proof.
        intros x y f ; unfold pointwise_cartesian_is_cartesian_factor_data ; cbn.
        pose (cartesian_factorization_sfib_commute
                F
                (Hα x) (pr1 β x) (pr1 δp x)
                (nat_trans_eq_pointwise q x))
          as p.
        pose (cartesian_factorization_sfib_commute
                F
                (Hα y) (pr1 β y) (pr1 δp y)
                (nat_trans_eq_pointwise q y))
          as p'.
        use (cartesian_factorization_sfib_unique
               _
               (Hα y)
               (pr1 β x · # (pr1 G₂) f)
               (pr1 δp x · # (pr1 F) (# (pr1 G₁) f))).
        - rewrite functor_comp.
          pose (r := nat_trans_eq_pointwise q x) ; cbn in r.
          etrans.
          {
            apply maponpaths_2.
            exact r.
          }
          clear r.
          rewrite !assoc'.
          apply maponpaths.
          refine (!(functor_comp _ _ _) @ _ @ functor_comp _ _ _).
          apply maponpaths.
          exact (!(nat_trans_ax α _ _ f)).
        - rewrite functor_comp.
          rewrite cartesian_factorization_sfib_over.
          exact (nat_trans_ax δp _ _ f).
        - rewrite !functor_comp.
          rewrite cartesian_factorization_sfib_over.
          apply idpath.
        - rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            exact p'.
          }
          exact (nat_trans_ax β _ _ f).
        - rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            exact (nat_trans_ax α _ _ f).
          }
          rewrite assoc.
          apply maponpaths_2.
          exact p.
      Qed.

      Definition pointwise_cartesian_is_cartesian_factor
        : H ==> G₁.
      Proof.
        use make_nat_trans.
        - exact pointwise_cartesian_is_cartesian_factor_data.
        - exact pointwise_cartesian_is_cartesian_factor_laws.
      Defined.

      Definition pointwise_cartesian_is_cartesian_over
        : pointwise_cartesian_is_cartesian_factor ▹ F = δp.
      Proof.
        use nat_trans_eq.
        {
          apply homset_property.
        }
        intro x ; cbn.
        apply cartesian_factorization_sfib_over.
      Qed.

      Definition pointwise_cartesian_is_cartesian_comm
        : pointwise_cartesian_is_cartesian_factor • α = β.
      Proof.
        use nat_trans_eq.
        {
          apply homset_property.
        }
        intro x ; cbn.
        apply cartesian_factorization_sfib_commute.
      Qed.

      Definition pointwise_cartesian_is_cartesian_unique
        : isaprop (∑ (δ : H ==> G₁), δ ▹ F = δp × δ • α = β).
      Proof.
        use invproofirrelevance.
        intros δ₁ δ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply cellset_property.
        }
        use nat_trans_eq.
        {
          apply homset_property.
        }
        intro x.
        use (cartesian_factorization_sfib_unique
               _ (Hα x)
               (pr1 β x)
               (pr1 δp x)).
        - exact (nat_trans_eq_pointwise q x).
        - exact (nat_trans_eq_pointwise (pr12 δ₁) x).
        - exact (nat_trans_eq_pointwise (pr12 δ₂) x).
        - exact (nat_trans_eq_pointwise (pr22 δ₁) x).
        - exact (nat_trans_eq_pointwise (pr22 δ₂) x).
      Qed.
    End Factorization.

    Definition pointwise_cartesian_is_cartesian
      : is_cartesian_2cell_sfib F α.
    Proof.
      intros H β δp q.
      use iscontraprop1.
      - exact (pointwise_cartesian_is_cartesian_unique q).
      - simple refine (_ ,, _ ,, _).
        + exact (pointwise_cartesian_is_cartesian_factor q).
        + exact (pointwise_cartesian_is_cartesian_over q).
        + exact (pointwise_cartesian_is_cartesian_comm q).
    Defined.
  End IsCartesian.

  Section Cleaving.
    Context {C₀ : bicat_of_univ_cats}
            {G₁ : C₀ --> C₂}
            {G₂ : C₀ --> C₁}
            (α : G₁ ==> G₂ · F).

    Definition street_fib_is_internal_sfib_cleaving_lift_data
      : functor_data (pr1 C₀) (pr1 C₁).
    Proof.
      use make_functor_data.
      - exact (λ x, pr1 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x))).
      - intros x y f ; cbn.
        use (cartesian_factorization_sfib
               _
               (pr222 (HF (pr1 G₂ y) (pr1 G₁ y) (pr1 α y)))).
        + exact (pr112 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x)) · # (pr1 G₂) f).
        + exact (pr212 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x))
                 · # (pr1 G₁) f
                 · inv_from_iso (pr212 (HF (pr1 G₂ y) (pr1 G₁ y) (pr1 α y)))).
        + abstract
            (rewrite functor_comp ;
             rewrite (pr122 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x))) ;
             rewrite !assoc' ;
             apply maponpaths ;
             refine (!(nat_trans_ax α _ _ f) @ _) ;
             apply maponpaths ;
             refine (!_) ;
             use iso_inv_on_right ;
             rewrite (pr122 (HF (pr1 G₂ y) (pr1 G₁ y) (pr1 α y))) ;
             apply idpath).
    Defined.

    Definition street_fib_is_internal_sfib_cleaving_lift_is_functor
      : is_functor street_fib_is_internal_sfib_cleaving_lift_data.
    Proof.
      split.
      - intro x ; cbn.
        use (cartesian_factorization_sfib_unique
               _
               (pr222 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x)))).
        + exact (pr112 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x))).
        + apply identity.
        + rewrite id_left.
          apply idpath.
        + rewrite cartesian_factorization_sfib_over.
          refine (!_).
          use iso_inv_on_left.
          rewrite id_left.
          rewrite (functor_id G₁).
          rewrite id_right.
          apply idpath.
        + apply functor_id.
        + rewrite cartesian_factorization_sfib_commute.
          rewrite (functor_id G₂).
          apply id_right.
        + apply id_left.
      - intros x y z f g ; cbn.
        use (cartesian_factorization_sfib_unique
               _
               (pr222 (HF (pr1 G₂ z) (pr1 G₁ z) (pr1 α z)))).
        + exact (pr112 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x)) · # (pr1 G₂) (f · g)).
        + exact (pr212 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x))
                 · # (pr1 G₁) (f · g)
                 · inv_from_iso (pr212 (HF (pr1 G₂ z) (pr1 G₁ z) (pr1 α z)))).
        + rewrite functor_comp.
          etrans.
          {
            apply maponpaths_2.
            exact (pr122 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x))).
          }
          rewrite !assoc'.
          apply maponpaths.
          refine (!(nat_trans_ax α _ _ (f · g)) @ _).
          apply maponpaths.
          refine (!_).
          use iso_inv_on_right.
          exact (pr122 (HF (pr1 G₂ z) (pr1 G₁ z) (pr1 α z))).
        + apply cartesian_factorization_sfib_over.
        + rewrite functor_comp.
          rewrite !cartesian_factorization_sfib_over.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite (functor_comp G₁).
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite iso_after_iso_inv.
          apply id_left.
        + apply cartesian_factorization_sfib_commute.
        + rewrite !assoc'.
          rewrite cartesian_factorization_sfib_commute.
          rewrite !assoc.
          rewrite cartesian_factorization_sfib_commute.
          rewrite !assoc'.
          rewrite (functor_comp G₂).
          apply idpath.
    Qed.

    Definition street_fib_is_internal_sfib_cleaving_lift
      : C₀ --> C₁.
    Proof.
      use make_functor.
      - exact street_fib_is_internal_sfib_cleaving_lift_data.
      - exact street_fib_is_internal_sfib_cleaving_lift_is_functor.
    Defined.

    Definition street_fib_is_internal_sfib_cleaving_lift_mor_data
      : nat_trans_data
          street_fib_is_internal_sfib_cleaving_lift_data
          (pr1 G₂)
      := λ x, pr112 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x)).

    Definition street_fib_is_internal_sfib_cleaving_lift_mor_is_nat_trans
      : is_nat_trans _ _ street_fib_is_internal_sfib_cleaving_lift_mor_data.
    Proof.
      intros x y f ; cbn.
      apply cartesian_factorization_sfib_commute.
    Qed.

    Definition street_fib_is_internal_sfib_cleaving_lift_mor
      : street_fib_is_internal_sfib_cleaving_lift ==> G₂.
    Proof.
      use make_nat_trans.
      - exact street_fib_is_internal_sfib_cleaving_lift_mor_data.
      - exact street_fib_is_internal_sfib_cleaving_lift_mor_is_nat_trans.
    Defined.

    Definition street_fib_is_internal_sfib_cleaving_lift_over_nat_trans_data
      : nat_trans_data (street_fib_is_internal_sfib_cleaving_lift ∙ F) (pr1 G₁)
      := λ x, pr212 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x)).

    Definition street_fib_is_internal_sfib_cleaving_lift_over_is_nat_trans
      : is_nat_trans
          _ _
          street_fib_is_internal_sfib_cleaving_lift_over_nat_trans_data.
    Proof.
      intros x y f ; cbn.
      unfold street_fib_is_internal_sfib_cleaving_lift_over_nat_trans_data.
      rewrite cartesian_factorization_sfib_over.
      rewrite !assoc'.
      rewrite iso_after_iso_inv.
      rewrite id_right.
      apply idpath.
    Qed.

    Definition street_fib_is_internal_sfib_cleaving_lift_over_nat_trans
      : street_fib_is_internal_sfib_cleaving_lift ∙ F ⟹ pr1 G₁.
    Proof.
      use make_nat_trans.
      - exact street_fib_is_internal_sfib_cleaving_lift_over_nat_trans_data.
      - exact street_fib_is_internal_sfib_cleaving_lift_over_is_nat_trans.
    Defined.

    Definition street_fib_is_internal_sfib_cleaving_lift_cartesian
      : is_cartesian_2cell_sfib
          F
          street_fib_is_internal_sfib_cleaving_lift_mor.
    Proof.
      use pointwise_cartesian_is_cartesian.
      intro x.
      exact (pr222 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x))).
    Defined.

    Definition street_fib_is_internal_sfib_cleaving_lift_over
      : invertible_2cell
          (street_fib_is_internal_sfib_cleaving_lift · F)
          G₁.
    Proof.
      use nat_iso_to_invertible_2cell.
      use make_nat_iso.
      - exact street_fib_is_internal_sfib_cleaving_lift_over_nat_trans.
      - intro x.
        apply iso_is_iso.
    Defined.
  End Cleaving.

  Definition street_fib_is_internal_sfib_cleaving
    : internal_sfib_cleaving F.
  Proof.
    intros C₀ G₁ G₂ α.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (street_fib_is_internal_sfib_cleaving_lift α).
    - exact (street_fib_is_internal_sfib_cleaving_lift_mor α).
    - exact (street_fib_is_internal_sfib_cleaving_lift_over α).
    - exact (street_fib_is_internal_sfib_cleaving_lift_cartesian α).
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         exact (pr122 (HF (pr1 G₂ x) (pr1 G₁ x) (pr1 α x)))).
  Defined.

  Section IsCartesian.
    Context {C₀ : bicat_of_univ_cats}
            {G₁ G₂ : C₀ --> C₁}
            (α : G₁ ==> G₂)
            (Hα : is_cartesian_2cell_sfib F α).

    Definition pointwise_lift_functor_data
      : functor_data (pr1 C₀) (pr1 C₁).
    Proof.
      use make_functor_data.
      - exact (λ x, pr1 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x)))).
      - intros x y f ; cbn.
        use (cartesian_factorization_sfib
               _
               (pr222 (HF (pr1 G₂ y) (pr1 F (pr1 G₁ y)) (# (pr1 F) (pr1 α y))))).
        + exact (pr112 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x)))
                 · # (pr1 G₂) f).
        + exact (pr212 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x)))
                 · # (pr1 F) (# (pr1 G₁) f)
                 · inv_from_iso
                     (pr212 (HF (pr1 G₂ y) (pr1 F (pr1 G₁ y)) (# (pr1 F) (pr1 α y))))).
        + abstract
            (rewrite functor_comp ;
             rewrite (pr122 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x)))) ;
             rewrite !assoc' ;
             apply maponpaths ;
             rewrite <- (functor_comp F) ;
             etrans ;
             [ apply maponpaths ;
               exact (!(nat_trans_ax α _ _ f))
             | ] ;
             rewrite functor_comp ;
             apply maponpaths ;
             refine (!_) ;
             use iso_inv_on_right ;
             rewrite (pr122 (HF (pr1 G₂ y) (pr1 F (pr1 G₁ y)) (# (pr1 F) (pr1 α y)))) ;
             apply idpath).
    Defined.

    Definition pointwise_lift_functor_is_functor
      : is_functor pointwise_lift_functor_data.
    Proof.
      split.
      - intro x ; cbn.
        use (cartesian_factorization_sfib_unique
               _
               (pr222 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x))))).
        + exact (pr112 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x)))).
        + apply identity.
        + rewrite id_left.
          apply idpath.
        + rewrite cartesian_factorization_sfib_over.
          refine (!_).
          use iso_inv_on_left.
          rewrite id_left.
          rewrite (functor_id G₁).
          rewrite (functor_id F).
          apply id_right.
        + apply functor_id.
        + rewrite cartesian_factorization_sfib_commute.
          rewrite (functor_id G₂).
          apply id_right.
        + apply id_left.
      - intros x y z f g ; cbn.
        use (cartesian_factorization_sfib_unique
               _
               (pr222 (HF (pr1 G₂ z) (pr1 F (pr1 G₁ z)) (# (pr1 F) (pr1 α z))))).
        + exact (pr112 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x)))
                 · # (pr1 G₂) (f · g)).
        + exact (pr212 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x)))
                 · # (pr1 F) (# (pr1 G₁) (f · g))
                 · inv_from_iso
                     (pr212 (HF (pr1 G₂ z) (pr1 F (pr1 G₁ z)) (# (pr1 F) (pr1 α z))))).
        + rewrite functor_comp.
          rewrite (pr122 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x)))).
          rewrite !assoc'.
          apply maponpaths.
          rewrite <- (functor_comp F).
          etrans.
          {
            apply maponpaths.
            exact (!(nat_trans_ax α _ _ (f · g))).
          }
          rewrite functor_comp.
          apply maponpaths.
          refine (!_).
          use iso_inv_on_right.
          rewrite (pr122 (HF (pr1 G₂ z) (pr1 F (pr1 G₁ z)) (# (pr1 F) (pr1 α z)))).
          apply idpath.
        + apply cartesian_factorization_sfib_over.
        + rewrite functor_comp.
          rewrite !cartesian_factorization_sfib_over.
          rewrite (functor_comp G₁).
          rewrite (functor_comp F).
          rewrite !assoc'.
          do 2 apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite !assoc'.
          use iso_inv_on_right.
          apply idpath.
        + apply cartesian_factorization_sfib_commute.
        + rewrite !assoc'.
          rewrite cartesian_factorization_sfib_commute.
          rewrite !assoc.
          rewrite cartesian_factorization_sfib_commute.
          rewrite !assoc'.
          rewrite (functor_comp G₂).
          apply idpath.
    Qed.

    Definition pointwise_lift_functor
      : C₀ --> C₁.
    Proof.
      use make_functor.
      - exact pointwise_lift_functor_data.
      - exact pointwise_lift_functor_is_functor.
    Defined.

    Definition pointwise_lift_nat_trans_data
      : nat_trans_data pointwise_lift_functor_data (pr1 G₂)
      := λ x, pr112 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x))).

    Definition pointwise_lift_is_nat_trans
      : is_nat_trans _ _ pointwise_lift_nat_trans_data.
    Proof.
      intros x y f ; cbn.
      unfold pointwise_lift_nat_trans_data.
      apply cartesian_factorization_sfib_commute.
    Qed.

    Definition pointwise_lift_nat_trans
      : pointwise_lift_functor ==> G₂.
    Proof.
      use make_nat_trans.
      - exact pointwise_lift_nat_trans_data.
      - exact pointwise_lift_is_nat_trans.
    Defined.

    Definition pointwise_lift_nat_trans_is_cartesian_2cell
      : is_cartesian_2cell_sfib F pointwise_lift_nat_trans.
    Proof.
      use pointwise_cartesian_is_cartesian.
      intro x.
      exact (pr222 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x)))).
    Defined.

    Definition is_cartesian_2cell_sfib_pointwise_cartesian_over_data
      : nat_trans_data (G₁ ∙ F) (pointwise_lift_functor ∙ F).
    Proof.
      intro x.
      pose (i := pr212 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x)))).
      exact (iso_inv_from_iso i).
    Defined.

    Definition is_cartesian_2cell_sfib_pointwise_cartesian_over_laws
      : is_nat_trans
          _ _
          is_cartesian_2cell_sfib_pointwise_cartesian_over_data.
    Proof.
      intros x y f ; cbn.
      refine (!_).
      use iso_inv_on_right.
      rewrite !assoc.
      use iso_inv_on_left.
      rewrite cartesian_factorization_sfib_over.
      rewrite !assoc'.
      apply maponpaths.
      rewrite iso_after_iso_inv.
      rewrite id_right.
      apply idpath.
    Qed.

    Definition is_cartesian_2cell_sfib_pointwise_cartesian_over
      : G₁ ∙ F ⟹ pointwise_lift_functor ∙ F.
    Proof.
      use make_nat_trans.
      - exact is_cartesian_2cell_sfib_pointwise_cartesian_over_data.
      - exact is_cartesian_2cell_sfib_pointwise_cartesian_over_laws.
    Defined.

    Definition is_cartesian_2cell_sfib_pointwise_cartesian_inv2cell
      : invertible_2cell (G₁ · F) (pointwise_lift_functor · F).
    Proof.
      use nat_iso_to_invertible_2cell.
      use make_nat_iso.
      - exact is_cartesian_2cell_sfib_pointwise_cartesian_over.
      - intro.
        apply iso_is_iso.
    Defined.

    Definition is_cartesian_2cell_sfib_pointwise_cartesian_eq
      : α ▹ F
        =
        is_cartesian_2cell_sfib_pointwise_cartesian_inv2cell
        • (pointwise_lift_nat_trans ▹ F).
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      simpl.
      unfold pointwise_lift_nat_trans_data.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (pr122 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x)))).
      }
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply iso_after_iso_inv.
      }
      apply id_left.
    Qed.

    Definition is_cartesian_2cell_sfib_pointwise_cartesian
               (x : pr1 C₀)
      : is_cartesian_sfib F (pr1 α x).
    Proof.
      pose (i := invertible_between_cartesians
                   Hα
                   pointwise_lift_nat_trans_is_cartesian_2cell
                   is_cartesian_2cell_sfib_pointwise_cartesian_inv2cell
                   is_cartesian_2cell_sfib_pointwise_cartesian_eq).
      use is_cartesian_sfib_eq.
      - exact (nat_iso_pointwise_iso (invertible_2cell_to_nat_iso _ _ i) x
              · pr1 pointwise_lift_nat_trans x).
      - exact (cartesian_factorization_sfib_commute _ _ _ _ _).
      - use comp_is_cartesian_sfib.
        + apply iso_is_cartesian_sfib.
          apply iso_is_iso.
        + exact (pr222 (HF (pr1 G₂ x) (pr1 F (pr1 G₁ x)) (# (pr1 F) (pr1 α x)))).
    Defined.
  End IsCartesian.

  Definition street_fib_is_internal_sfib_lwhisker_is_cartesian
    : lwhisker_is_cartesian F.
  Proof.
    intros C₀ C₀' G H₁ H₂ α Hα.
    use pointwise_cartesian_is_cartesian.
    intro x ; cbn.
    apply is_cartesian_2cell_sfib_pointwise_cartesian.
    exact Hα.
  Defined.

  Definition street_fib_is_internal_sfib
    : internal_sfib F.
  Proof.
    split.
    - exact street_fib_is_internal_sfib_cleaving.
    - exact street_fib_is_internal_sfib_lwhisker_is_cartesian.
  Defined.
End StreetFibToInternalSFib.

Definition internal_sfib_weq_street_fib
           {C₁ C₂ : bicat_of_univ_cats}
           (F : C₁ --> C₂)
  : internal_sfib F ≃ street_fib F.
Proof.
  use weqimplimpl.
  - exact internal_sfib_is_street_fib.
  - exact street_fib_is_internal_sfib.
  - apply isaprop_internal_sfib.
    exact univalent_cat_is_univalent_2_1.
  - apply isaprop_street_fib.
    apply C₁.
Defined.

(**
 2. Internal Street Opfibrations
 *)
Section InternalSOpFibToStreetOpFib.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F : C₁ --> C₂}
          (HF : internal_sopfib F).

  Section InternalSOpFibToStreetOpFibFactor.
    Context {G₁ G₂ : (unit_category : bicat_of_univ_cats) --> C₁}
            {α : G₁ ==> G₂}
            (Hα : is_opcartesian_2cell_sopfib F α)
            {z : pr1 C₁}
            {g : pr1 G₁ tt --> z}
            {h : pr1 F (pr1 G₂ tt) --> pr1 F z}
            (q : # (pr1 F) g = # (pr1 F) (pr1 α tt) · h).

    Let Φ : unit_category ⟶ pr1 C₁
      := functor_from_unit z.

    Local Definition internal_sopfib_is_opcartesian_sopfib_factor_nat_trans_1
      : pr1 G₁ ⟹ Φ.
    Proof.
      use make_nat_trans.
      - intro x ; induction x.
        exact g.
      - abstract
          (intros x y f ; cbn ;
           induction x ; induction y ;
           cbn ;
           assert (p : f = identity _) ; [ apply isapropunit | ] ;
           rewrite p ;
           rewrite (functor_id G₁) ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Let ζ := internal_sopfib_is_opcartesian_sopfib_factor_nat_trans_1.

    Local Definition internal_sopfib_is_opcartesian_sopfib_factor_nat_trans_2
      : G₂ · F ==> Φ ∙ F.
    Proof.
      use make_nat_trans.
      - intros x ; induction x.
        exact h.
      - abstract
          (intros x y f ; cbn ;
           induction x ; induction y ;
           cbn ;
           assert (p : f = identity _) ; [ apply isapropunit | ] ;
           rewrite p ;
           rewrite (functor_id G₂) ;
           rewrite !(functor_id F) ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Let ξ := internal_sopfib_is_opcartesian_sopfib_factor_nat_trans_2.

    Local Lemma internal_sopfib_is_opcartesian_sopfib_factor_eq
      : post_whisker ζ F
        =
        nat_trans_comp _ _ _ (post_whisker α F) ξ.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; induction x.
      exact q.
    Qed.

    Let p := internal_sopfib_is_opcartesian_sopfib_factor_eq.

    Definition internal_sopfib_is_opcartesian_sopfib_factor
      : pr1 G₂ tt --> z
      := pr1 (is_opcartesian_2cell_sopfib_factor _ Hα ζ ξ p) tt.

    Definition internal_sopfib_is_opcartesian_sopfib_factor_over
      : # (pr1 F) internal_sopfib_is_opcartesian_sopfib_factor = h.
    Proof.
      exact (nat_trans_eq_pointwise
               (is_opcartesian_2cell_sopfib_factor_over _ Hα _ _ p)
               tt).
    Qed.

    Definition internal_sopfib_is_opcartesian_sopfib_factor_comm
      : pr1 α tt · internal_sopfib_is_opcartesian_sopfib_factor = g.
    Proof.
      exact (nat_trans_eq_pointwise
               (is_opcartesian_2cell_sopfib_factor_comm _ Hα _ _ p)
               tt).
    Qed.

    Local Definition internal_sopfib_is_opcartesian_sopfib_factor_unique_help
               (k : pr1 G₂ tt --> z)
      : pr1 G₂ ⟹ Φ.
    Proof.
      use make_nat_trans.
      - intro x ; induction x.
        exact k.
      - abstract
          (intros x y f ;
           induction x ; induction y ; cbn ;
           assert (r : f = identity _) ; [ apply isapropunit | ] ;
           rewrite r ;
           rewrite !(functor_id G₂) ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Definition internal_sopfib_is_opcartesian_sopfib_factor_unique
      : isaprop (∑ φ, # (pr1 F) φ = h × pr1 α tt · φ = g).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      refine (nat_trans_eq_pointwise
                (is_opcartesian_2cell_sopfib_factor_unique
                   _ Hα
                   Φ ζ ξ p
                   (internal_sopfib_is_opcartesian_sopfib_factor_unique_help (pr1 φ₁))
                   (internal_sopfib_is_opcartesian_sopfib_factor_unique_help (pr1 φ₂))
                   _ _ _ _)
                tt) ;
        (use nat_trans_eq ; [ apply homset_property | ]) ;
        intro x ; induction x ; cbn.
      - exact (pr12 φ₁).
      - exact (pr12 φ₂).
      - exact (pr22 φ₁).
      - exact (pr22 φ₂).
    Qed.
  End InternalSOpFibToStreetOpFibFactor.

  Definition internal_sopfib_is_opcartesian_sopfib
             {G₁ G₂ : (unit_category : bicat_of_univ_cats) --> C₁}
             {α : G₁ ==> G₂}
             (Hα : is_opcartesian_2cell_sopfib F α)
    : is_opcartesian_sopfib F (pr1 α tt).
  Proof.
    intros z g h q.
    use iscontraprop1.
    - exact (internal_sopfib_is_opcartesian_sopfib_factor_unique Hα q).
    - simple refine (_ ,, _ ,, _).
      + exact (internal_sopfib_is_opcartesian_sopfib_factor Hα q).
      + exact (internal_sopfib_is_opcartesian_sopfib_factor_over Hα q).
      + exact (internal_sopfib_is_opcartesian_sopfib_factor_comm Hα q).
  Defined.

  Section OpCleaving.
    Context {e : pr1 C₁}
            {b : pr1 C₂}
            (f : pr1 F e --> b).

    Definition internal_sopfib_is_street_opfib_nat_trans
      : functor_from_unit e ∙ F ⟹ functor_from_unit b.
    Proof.
      use make_nat_trans.
      - exact (λ _, f).
      - abstract
          (intros z₁ z₂ g ; cbn ;
           rewrite functor_id, id_left, id_right ;
           apply idpath).
    Defined.

    Let ℓ := pr1 HF _ _ _ internal_sopfib_is_street_opfib_nat_trans.

    Definition internal_sopfib_is_street_opfib_lift_ob
      : pr1 C₁
      := pr1 (pr1 ℓ) tt.

    Definition internal_sopfib_is_street_opfib_lift_mor
      : e --> internal_sopfib_is_street_opfib_lift_ob
      := pr1 (pr12 ℓ) tt.

    Definition internal_sopfib_is_street_opfib_lift_iso
      : iso b (pr1 F internal_sopfib_is_street_opfib_lift_ob)
      := nat_iso_pointwise_iso (invertible_2cell_to_nat_iso _ _ (pr122 ℓ)) tt.

    Definition internal_sopfib_is_street_opfib_lift_over
      : # (pr1 F) internal_sopfib_is_street_opfib_lift_mor
        =
        f · internal_sopfib_is_street_opfib_lift_iso
      := nat_trans_eq_pointwise (pr2 (pr222 ℓ)) tt.

    Definition internal_sopfib_is_street_opfib_lift_cartesian
      : is_opcartesian_sopfib F internal_sopfib_is_street_opfib_lift_mor
      := internal_sopfib_is_opcartesian_sopfib (pr1 (pr222 ℓ)).
  End OpCleaving.

  Definition internal_sopfib_is_street_opfib
    : street_opfib F.
  Proof.
    intros e b f.
    simple refine (_ ,, (_ ,, _) ,, _ ,, _) ; cbn.
    - exact (internal_sopfib_is_street_opfib_lift_ob f).
    - exact (internal_sopfib_is_street_opfib_lift_mor f).
    - exact (internal_sopfib_is_street_opfib_lift_iso f).
    - exact (internal_sopfib_is_street_opfib_lift_over f).
    - exact (internal_sopfib_is_street_opfib_lift_cartesian f).
  Defined.
End InternalSOpFibToStreetOpFib.

Section StreetOpFibToInternalSOpFib.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F : C₁ --> C₂}
          (HF : street_opfib F).

  Section IsOpCartesian.
    Context {C₀ : bicat_of_univ_cats}
            {G₁ G₂ : C₀ --> C₁}
            (α : G₁ ==> G₂)
            (Hα : ∏ (x : pr1 C₀), is_opcartesian_sopfib F (pr1 α x)).

    Section Factorization.
      Context {H : C₀ --> C₁}
              {β : G₁ ==> H}
              {δp : G₂ · F ==> H · F}
              (q : β ▹ F = (α ▹ F) • δp).

      Definition pointwise_opcartesian_is_opcartesian_factor_data
        : nat_trans_data (pr1 G₂) (pr1 H)
        := λ x,
           opcartesian_factorization_sopfib
             _
             (Hα x)
             (pr1 β x)
             (pr1 δp x)
             (nat_trans_eq_pointwise q x).

      Definition pointwise_opcartesian_is_opcartesian_factor_laws
        : is_nat_trans _ _ pointwise_opcartesian_is_opcartesian_factor_data.
      Proof.
        intros x y f ; unfold pointwise_opcartesian_is_opcartesian_factor_data ; cbn.
        pose (opcartesian_factorization_sopfib_commute
                F
                (Hα x) (pr1 β x) (pr1 δp x)
                (nat_trans_eq_pointwise q x))
          as p.
        pose (opcartesian_factorization_sopfib_commute
                F
                (Hα y) (pr1 β y) (pr1 δp y)
                (nat_trans_eq_pointwise q y))
          as p'.
        use (opcartesian_factorization_sopfib_unique
               _
               (Hα x)
               (pr1 β x · # (pr1 H) f)
               (pr1 δp x · # (pr1 F) (# (pr1 H) f))).
        - rewrite functor_comp.
          pose (r := nat_trans_eq_pointwise q x) ; cbn in r.
          etrans.
          {
            apply maponpaths_2.
            exact r.
          }
          clear r.
          rewrite !assoc'.
          apply idpath.
        - rewrite functor_comp.
          rewrite opcartesian_factorization_sopfib_over.
          exact (nat_trans_ax δp _ _ f).
        - rewrite !functor_comp.
          rewrite opcartesian_factorization_sopfib_over.
          apply idpath.
        - rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (!(nat_trans_ax α _ _ f)).
          }
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            exact p'.
          }
          exact (nat_trans_ax β _ _ f).
        - rewrite !assoc.
          apply maponpaths_2.
          exact p.
      Qed.

      Definition pointwise_opcartesian_is_opcartesian_factor
        : G₂ ==> H.
      Proof.
        use make_nat_trans.
        - exact pointwise_opcartesian_is_opcartesian_factor_data.
        - exact pointwise_opcartesian_is_opcartesian_factor_laws.
      Defined.

      Definition pointwise_opcartesian_is_opcartesian_over
        : pointwise_opcartesian_is_opcartesian_factor ▹ F = δp.
      Proof.
        use nat_trans_eq.
        {
          apply homset_property.
        }
        intro x ; cbn.
        apply opcartesian_factorization_sopfib_over.
      Qed.

      Definition pointwise_opcartesian_is_opcartesian_comm
        : α • pointwise_opcartesian_is_opcartesian_factor = β.
      Proof.
        use nat_trans_eq.
        {
          apply homset_property.
        }
        intro x ; cbn.
        apply opcartesian_factorization_sopfib_commute.
      Qed.

      Definition pointwise_opcartesian_is_opcartesian_unique
        : isaprop (∑ (δ : G₂ ==> H), δ ▹ F = δp × α • δ = β).
      Proof.
        use invproofirrelevance.
        intros δ₁ δ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply cellset_property.
        }
        use nat_trans_eq.
        {
          apply homset_property.
        }
        intro x.
        use (opcartesian_factorization_sopfib_unique
               _ (Hα x)
               (pr1 β x)
               (pr1 δp x)).
        - exact (nat_trans_eq_pointwise q x).
        - exact (nat_trans_eq_pointwise (pr12 δ₁) x).
        - exact (nat_trans_eq_pointwise (pr12 δ₂) x).
        - exact (nat_trans_eq_pointwise (pr22 δ₁) x).
        - exact (nat_trans_eq_pointwise (pr22 δ₂) x).
      Qed.
    End Factorization.

    Definition pointwise_opcartesian_is_opcartesian
      : is_opcartesian_2cell_sopfib F α.
    Proof.
      intros H β δp q.
      use iscontraprop1.
      - exact (pointwise_opcartesian_is_opcartesian_unique q).
      - simple refine (_ ,, _ ,, _).
        + exact (pointwise_opcartesian_is_opcartesian_factor q).
        + exact (pointwise_opcartesian_is_opcartesian_over q).
        + exact (pointwise_opcartesian_is_opcartesian_comm q).
    Defined.
  End IsOpCartesian.

  Section OpCleaving.
    Context {C₀ : bicat_of_univ_cats}
            {G₁ : C₀ --> C₁}
            {G₂ : C₀ --> C₂}
            (α : G₁ · F ==> G₂).

    Definition street_opfib_is_internal_sopfib_opcleaving_lift_data
      : functor_data (pr1 C₀) (pr1 C₁).
    Proof.
      use make_functor_data.
      - exact (λ x, pr1 (HF _ _ (pr1 α x))).
      - intros x y f ; cbn.
        use (opcartesian_factorization_sopfib
               _
               (pr222 (HF _ _ (pr1 α x)))).
        + exact (# (pr1 G₁) f · pr112 (HF _ _ (pr1 α y))).
        + exact (inv_from_iso (pr212 (HF _ _ (pr1 α x)))
                 · # (pr1 G₂) f
                 · pr212 (HF _ _ (pr1 α y))).
        + abstract
            (rewrite functor_comp ;
             rewrite (pr122 (HF _ _ (pr1 α x))) ;
             refine (maponpaths (λ z, _ · z) (pr122 (HF _ _ (pr1 α y))) @ _) ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             refine (nat_trans_ax α _ _ f @ _) ;
             rewrite !assoc' ;
             apply maponpaths ;
             rewrite !assoc ;
             rewrite iso_inv_after_iso ;
             rewrite id_left ;
             apply idpath).
    Defined.

    Definition street_opfib_is_internal_sopfib_opcleaving_lift_is_functor
      : is_functor street_opfib_is_internal_sopfib_opcleaving_lift_data.
    Proof.
      split.
      - intro x ; cbn.
        use (opcartesian_factorization_sopfib_unique
               _
               (pr222 (HF _ _ (pr1 α x)))).
        + exact (pr112 (HF _ _ (pr1 α x))).
        + apply identity.
        + rewrite id_right.
          apply idpath.
        + rewrite opcartesian_factorization_sopfib_over.
          refine (!_).
          rewrite (functor_id G₂).
          rewrite id_right.
          rewrite iso_after_iso_inv.
          apply idpath.
        + apply functor_id.
        + rewrite opcartesian_factorization_sopfib_commute.
          rewrite (functor_id G₁).
          apply id_left.
        + apply id_right.
      - intros x y z f g ; cbn.
        use (opcartesian_factorization_sopfib_unique
               _
               (pr222 (HF _ _ (pr1 α x)))).
        + exact (# (pr1 G₁) (f · g) · pr112 (HF _ _ (pr1 α z))).
        + exact (inv_from_iso (pr212 (HF _ _ (pr1 α x)))
                 · # (pr1 G₂) (f · g)
                 · pr212 (HF _ _ (pr1 α z))).
        + rewrite functor_comp.
          etrans.
          {
            apply maponpaths.
            exact (pr122 (HF _ _ (pr1 α z))).
          }
          rewrite !assoc.
          apply maponpaths_2.
          refine (nat_trans_ax α _ _ (f · g) @ _).
          apply maponpaths_2.
          use iso_inv_on_left.
          exact (pr122 (HF _ _ (pr1 α x))).
        + apply opcartesian_factorization_sopfib_over.
        + rewrite functor_comp.
          rewrite !opcartesian_factorization_sopfib_over.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite (functor_comp G₂).
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite iso_inv_after_iso.
          apply id_left.
        + apply opcartesian_factorization_sopfib_commute.
        + rewrite !assoc.
          rewrite opcartesian_factorization_sopfib_commute.
          rewrite !assoc'.
          rewrite opcartesian_factorization_sopfib_commute.
          rewrite !assoc.
          rewrite (functor_comp G₁).
          apply idpath.
    Qed.

    Definition street_opfib_is_internal_sopfib_opcleaving_lift
      : C₀ --> C₁.
    Proof.
      use make_functor.
      - exact street_opfib_is_internal_sopfib_opcleaving_lift_data.
      - exact street_opfib_is_internal_sopfib_opcleaving_lift_is_functor.
    Defined.

    Definition street_opfib_is_internal_sopfib_opcleaving_lift_mor_data
      : nat_trans_data
          (pr1 G₁)
          street_opfib_is_internal_sopfib_opcleaving_lift_data
      := λ x, pr112 (HF _ _ (pr1 α x)).

    Definition street_opfib_is_internal_sopfib_opcleaving_lift_mor_is_nat_trans
      : is_nat_trans _ _ street_opfib_is_internal_sopfib_opcleaving_lift_mor_data.
    Proof.
      intros x y f ; cbn.
      refine (!_).
      apply opcartesian_factorization_sopfib_commute.
    Qed.

    Definition street_opfib_is_internal_sopfib_opcleaving_lift_mor
      : G₁ ==> street_opfib_is_internal_sopfib_opcleaving_lift.
    Proof.
      use make_nat_trans.
      - exact street_opfib_is_internal_sopfib_opcleaving_lift_mor_data.
      - exact street_opfib_is_internal_sopfib_opcleaving_lift_mor_is_nat_trans.
    Defined.

    Definition street_opfib_is_internal_sopfib_opcleaving_lift_over_nat_trans_data
      : nat_trans_data (pr1 G₂) (street_opfib_is_internal_sopfib_opcleaving_lift ∙ F)
      := λ x, pr212 (HF _ _ (pr1 α x)).

    Definition street_opfib_is_internal_sopfib_opcleaving_lift_over_is_nat_trans
      : is_nat_trans
          _ _
          street_opfib_is_internal_sopfib_opcleaving_lift_over_nat_trans_data.
    Proof.
      intros x y f ; cbn.
      unfold street_opfib_is_internal_sopfib_opcleaving_lift_over_nat_trans_data.
      rewrite opcartesian_factorization_sopfib_over.
      rewrite !assoc.
      rewrite iso_inv_after_iso.
      rewrite id_left.
      apply idpath.
    Qed.

    Definition street_opfib_is_internal_sopfib_opcleaving_lift_over_nat_trans
      : pr1 G₂ ⟹ street_opfib_is_internal_sopfib_opcleaving_lift ∙ F.
    Proof.
      use make_nat_trans.
      - exact street_opfib_is_internal_sopfib_opcleaving_lift_over_nat_trans_data.
      - exact street_opfib_is_internal_sopfib_opcleaving_lift_over_is_nat_trans.
    Defined.

    Definition street_opfib_is_internal_sopfib_opcleaving_lift_opcartesian
      : is_opcartesian_2cell_sopfib
          F
          street_opfib_is_internal_sopfib_opcleaving_lift_mor.
    Proof.
      use pointwise_opcartesian_is_opcartesian.
      intro x.
      exact (pr222 (HF _ _ (pr1 α x))).
    Defined.

    Definition street_opfib_is_internal_sopfib_opcleaving_lift_over
      : invertible_2cell
          G₂
          (street_opfib_is_internal_sopfib_opcleaving_lift · F).
    Proof.
      use nat_iso_to_invertible_2cell.
      use make_nat_iso.
      - exact street_opfib_is_internal_sopfib_opcleaving_lift_over_nat_trans.
      - intro x.
        apply iso_is_iso.
    Defined.
  End OpCleaving.

  Definition street_opfib_is_internal_sopfib_opcleaving
    : internal_sopfib_opcleaving F.
  Proof.
    intros C₀ G₁ G₂ α.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (street_opfib_is_internal_sopfib_opcleaving_lift α).
    - exact (street_opfib_is_internal_sopfib_opcleaving_lift_mor α).
    - exact (street_opfib_is_internal_sopfib_opcleaving_lift_over α).
    - exact (street_opfib_is_internal_sopfib_opcleaving_lift_opcartesian α).
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         exact (pr122 (HF _ _ (pr1 α x)))).
  Defined.

  Section IsOpCartesian.
    Context {C₀ : bicat_of_univ_cats}
            {G₁ G₂ : C₀ --> C₁}
            (α : G₁ ==> G₂)
            (Hα : is_opcartesian_2cell_sopfib F α).

    Definition pointwise_oplift_functor_data
      : functor_data (pr1 C₀) (pr1 C₁).
    Proof.
      use make_functor_data.
      - exact (λ x, pr1 (HF _ _ (# (pr1 F) (pr1 α x)))).
      - intros x y f ; cbn.
        use (opcartesian_factorization_sopfib
               _
               (pr222 (HF _ _ (# (pr1 F) (pr1 α x))))).
        + exact (# (pr1 G₁) f · pr112 (HF _ _ (# (pr1 F) (pr1 α y)))).
        + exact (inv_from_iso (pr212 (HF _ _ (# (pr1 F) (pr1 α x))))
                 · # (pr1 F) (# (pr1 G₂) f)
                 · pr212 (HF _ _ (# (pr1 F) (pr1 α y)))).
        + abstract
            (rewrite functor_comp ;
             rewrite (pr122 (HF _ _ (# (pr1 F) (pr1 α x)))) ;
             rewrite !assoc ;
             etrans ;
             [ apply maponpaths ;
               exact (pr122 (HF _ _ (# (pr1 F) (pr1 α y))))
             | ] ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             rewrite <- !functor_comp ;
             etrans ;
             [ apply maponpaths ;
               exact (nat_trans_ax α _ _ f)
             | ] ;
             rewrite functor_comp ;
             rewrite !assoc' ;
             apply maponpaths ;
             rewrite !assoc ;
             rewrite iso_inv_after_iso ;
             rewrite id_left ;
             apply idpath).
    Defined.

    Definition pointwise_oplift_functor_is_functor
      : is_functor pointwise_oplift_functor_data.
    Proof.
      split.
      - intro x ; cbn.
        use (opcartesian_factorization_sopfib_unique
               _
               (pr222 (HF _ _ (# (pr1 F) (pr1 α x))))).
        + exact (pr112 (HF _ _ (# (pr1 F) (pr1 α x)))).
        + apply identity.
        + rewrite id_right.
          apply idpath.
        + rewrite opcartesian_factorization_sopfib_over.
          rewrite !assoc'.
          use iso_inv_on_right.
          rewrite id_right.
          rewrite (functor_id G₂).
          rewrite (functor_id F).
          apply id_left.
        + apply functor_id.
        + rewrite opcartesian_factorization_sopfib_commute.
          rewrite (functor_id G₁).
          apply id_left.
        + apply id_right.
      - intros x y z f g ; cbn.
        use (opcartesian_factorization_sopfib_unique
               _
               (pr222 (HF _ _ (# (pr1 F) (pr1 α x))))).
        + exact (# (pr1 G₁) (f · g)
                 · pr112 (HF _ _ (# (pr1 F) (pr1 α z)))).
        + exact (inv_from_iso
                   (pr212 (HF _ _ (# (pr1 F) (pr1 α x))))
                 · # (pr1 F) (# (pr1 G₂) (f · g))
                 · pr212 (HF _ _ (# (pr1 F) (pr1 α z)))).
        + rewrite functor_comp.
          rewrite (pr122 (HF _ _ (# (pr1 F) (pr1 α x)))).
          etrans.
          {
            apply maponpaths.
            exact (pr122 (HF _ _ (# (pr1 F) (pr1 α z)))).
          }
          rewrite !assoc.
          rewrite <- (functor_comp F).
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (nat_trans_ax α _ _ (f · g)).
          }
          rewrite functor_comp.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite iso_inv_after_iso.
          rewrite id_left.
          apply idpath.
        + apply opcartesian_factorization_sopfib_over.
        + rewrite functor_comp.
          rewrite !opcartesian_factorization_sopfib_over.
          rewrite (functor_comp G₂).
          rewrite (functor_comp F).
          rewrite !assoc'.
          do 2 apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite iso_inv_after_iso.
          apply id_left.
        + apply opcartesian_factorization_sopfib_commute.
        + rewrite !assoc.
          rewrite opcartesian_factorization_sopfib_commute.
          rewrite !assoc'.
          rewrite opcartesian_factorization_sopfib_commute.
          rewrite !assoc.
          rewrite (functor_comp G₁).
          apply idpath.
    Qed.

    Definition pointwise_oplift_functor
      : C₀ --> C₁.
    Proof.
      use make_functor.
      - exact pointwise_oplift_functor_data.
      - exact pointwise_oplift_functor_is_functor.
    Defined.

    Definition pointwise_oplift_nat_trans_data
      : nat_trans_data (pr1 G₁) pointwise_oplift_functor_data
      := λ x, pr112 (HF _ _ (# (pr1 F) (pr1 α x))).

    Definition pointwise_oplift_is_nat_trans
      : is_nat_trans _ _ pointwise_oplift_nat_trans_data.
    Proof.
      intros x y f ; cbn.
      unfold pointwise_oplift_nat_trans_data.
      refine (!_).
      apply opcartesian_factorization_sopfib_commute.
    Qed.

    Definition pointwise_oplift_nat_trans
      : G₁ ==> pointwise_oplift_functor.
    Proof.
      use make_nat_trans.
      - exact pointwise_oplift_nat_trans_data.
      - exact pointwise_oplift_is_nat_trans.
    Defined.

    Definition pointwise_oplift_nat_trans_is_opcartesian_2cell
      : is_opcartesian_2cell_sopfib F pointwise_oplift_nat_trans.
    Proof.
      use pointwise_opcartesian_is_opcartesian.
      intro x.
      exact (pr222 (HF _ _ (# (pr1 F) (pr1 α x)))).
    Defined.

    Definition is_opcartesian_2cell_sopfib_pointwise_opcartesian_over_data
      : nat_trans_data (pointwise_oplift_functor ∙ F) (G₂ ∙ F).
    Proof.
      intro x.
      pose (i := pr212 (HF _ _ (# (pr1 F) (pr1 α x)))).
      exact (iso_inv_from_iso i).
    Defined.

    Definition is_opcartesian_2cell_sopfib_pointwise_opcartesian_over_laws
      : is_nat_trans
          _ _
          is_opcartesian_2cell_sopfib_pointwise_opcartesian_over_data.
    Proof.
      intros x y f ; cbn.
      refine (!_).
      use iso_inv_on_right.
      rewrite !assoc.
      use iso_inv_on_left.
      rewrite opcartesian_factorization_sopfib_over.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite iso_inv_after_iso.
      rewrite id_left.
      apply idpath.
    Qed.

    Definition is_opcartesian_2cell_sopfib_pointwise_opcartesian_over
      : pointwise_oplift_functor ∙ F ⟹ G₂ ∙ F.
    Proof.
      use make_nat_trans.
      - exact is_opcartesian_2cell_sopfib_pointwise_opcartesian_over_data.
      - exact is_opcartesian_2cell_sopfib_pointwise_opcartesian_over_laws.
    Defined.

    Definition is_opcartesian_2cell_sopfib_pointwise_opcartesian_inv2cell
      : invertible_2cell (pointwise_oplift_functor · F) (G₂ · F).
    Proof.
      use nat_iso_to_invertible_2cell.
      use make_nat_iso.
      - exact is_opcartesian_2cell_sopfib_pointwise_opcartesian_over.
      - intro.
        apply iso_is_iso.
    Defined.

    Definition is_opcartesian_2cell_sopfib_pointwise_opcartesian_eq
      : α ▹ F
        =
        (pointwise_oplift_nat_trans ▹ F)
        • is_opcartesian_2cell_sopfib_pointwise_opcartesian_inv2cell.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      cbn.
      unfold pointwise_oplift_nat_trans_data.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (pr122 (HF _ _ (# (pr1 F) (pr1 α x)))).
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply iso_inv_after_iso.
      }
      apply id_right.
    Qed.

    Definition is_opcartesian_2cell_sfib_pointwise_opcartesian
               (x : pr1 C₀)
      : is_opcartesian_sopfib F (pr1 α x).
    Proof.
      pose (i := invertible_between_opcartesians
                   Hα
                   pointwise_oplift_nat_trans_is_opcartesian_2cell
                   is_opcartesian_2cell_sopfib_pointwise_opcartesian_inv2cell
                   is_opcartesian_2cell_sopfib_pointwise_opcartesian_eq).
      use is_opcartesian_sopfib_eq.
      - exact (pr1 pointwise_oplift_nat_trans x
               · nat_iso_pointwise_iso (invertible_2cell_to_nat_iso _ _ i) x).
      - exact (opcartesian_factorization_sopfib_commute _ _ _ _ _).
      - use comp_is_opcartesian_sopfib.
        + exact (pr222 (HF _ _ (# (pr1 F) (pr1 α x)))).
        + apply iso_is_opcartesian_sopfib.
          apply iso_is_iso.
    Qed.
  End IsOpCartesian.

  Definition street_opfib_is_internal_sopfib_lwhisker_is_opcartesian
    : lwhisker_is_opcartesian F.
  Proof.
    intros C₀ C₀' G H₁ H₂ α Hα.
    use pointwise_opcartesian_is_opcartesian.
    intro x ; cbn.
    apply is_opcartesian_2cell_sfib_pointwise_opcartesian.
    exact Hα.
  Defined.

  Definition street_opfib_is_internal_sopfib
    : internal_sopfib F.
  Proof.
    split.
    - exact street_opfib_is_internal_sopfib_opcleaving.
    - exact street_opfib_is_internal_sopfib_lwhisker_is_opcartesian.
  Defined.
End StreetOpFibToInternalSOpFib.

Definition internal_sopfib_weq_street_opfib
           {C₁ C₂ : bicat_of_univ_cats}
           (F : C₁ --> C₂)
  : internal_sopfib F ≃ street_opfib F.
Proof.
  use weqimplimpl.
  - exact internal_sopfib_is_street_opfib.
  - exact street_opfib_is_internal_sopfib.
  - apply isaprop_internal_sopfib.
    exact univalent_cat_is_univalent_2_1.
  - apply isaprop_street_opfib.
    apply C₁.
Defined.
