(********************************************************************************************

 Monoidal Adjunctions

 In this file, we define monoidal adjunctions. We define this notion in the following
 way: a monoidal adjunction  is adjunction of categories such that both functors are
 lax monoidal and such that the unit and counit are monoidal transformations. This is
 given in [monoidal_adjunction]. A reference for this notion is Section 5.14 in
 https://www.irif.fr/~mellies/mpri/mpri-ens/biblio/categorical-semantics-of-linear-logic.pdf
 Note: this notion is what you obtain by unfolding adjunctions internal to the
 bicategory of monoidal categories.

 However, in practice it is often useful to use the following characterization: an
 adjunction is monoidal if the left adjoint is a strong monoidal functor. A reference
 for this result is Lemma 13 in https://hal.science/hal-00154229/document. The relevant
 statements are [monoidal_adjunction_from_strong] and [is_strong_left_adjoint].

 We prove the same results for symmetric monoidal adjunctions.

 Contents
 1. Monoidal adjunctions
 2. Accessors and builders
 3. Left adjoints are strongly monoidal
 3.1. Preservation of the unit
 3.2. Preservation of the tensor
 4. If the left adjoint is strong, then the adjunction is monoidal
 5. Symmetric monoidal adjunctions
 6. Accessors
 7. Symmetric monoidal adjunctions from strong functors
 8. Symmetric monoidal adjunctions to comonads

 ********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

(**
 1. Monoidal adjunctions
 *)
Definition monoidal_adjunction
           {C₁ C₂ : category}
           (M₁ : monoidal C₁)
           (M₂ : monoidal C₂)
           (A : adjunction C₁ C₂)
           (L := left_adjoint A : C₁ ⟶ C₂)
           (R := right_adjoint A : C₂ ⟶ C₁)
           (η := adjunit A)
           (ε := adjcounit A)
  : UU
  := ∑ (HL : fmonoidal_lax M₁ M₂ L),
     ∑ (HR : fmonoidal_lax M₂ M₁ R),
     is_mon_nat_trans (identity_fmonoidal _) (comp_fmonoidal_lax HL HR) η
     ×
     is_mon_nat_trans (comp_fmonoidal_lax HR HL) (identity_fmonoidal _) ε.

(**
 2. Accessors and builders
 *)
Definition make_monoidal_adjunction
           {C₁ C₂ : category}
           {M₁ : monoidal C₁}
           {M₂ : monoidal C₂}
           {A : adjunction C₁ C₂}
           (L := left_adjoint A : C₁ ⟶ C₂)
           (R := right_adjoint A : C₂ ⟶ C₁)
           (η := adjunit A)
           (ε := adjcounit A)
           (HL : fmonoidal_lax M₁ M₂ L)
           (HR : fmonoidal_lax M₂ M₁ R)
           (Hη : is_mon_nat_trans
                   (identity_fmonoidal _)
                   (comp_fmonoidal_lax HL HR)
                   η)
           (Hε : is_mon_nat_trans
                   (comp_fmonoidal_lax HR HL)
                   (identity_fmonoidal _)
                   ε)
  : monoidal_adjunction M₁ M₂ A
  := HL ,, HR ,, Hη ,, Hε.

Section MonoidalAdjunctionAccessors.
  Context {C₁ C₂ : category}
          {M₁ : monoidal C₁}
          {M₂ : monoidal C₂}
          {A : adjunction C₁ C₂}
          (L := left_adjoint A : C₁ ⟶ C₂)
          (R := right_adjoint A : C₂ ⟶ C₁)
          (η := adjunit A)
          (ε := adjcounit A)
          (HA : monoidal_adjunction M₁ M₂ A).

  Definition fmonoidal_lax_left_adjoint
    : fmonoidal_lax M₁ M₂ L
    := pr1 HA.

  Definition fmonoidal_lax_right_adjoint
    : fmonoidal_lax M₂ M₁ R
    := pr12 HA.

  Proposition monoidal_adjunit
    : is_mon_nat_trans
        (identity_fmonoidal _)
        (comp_fmonoidal_lax
           fmonoidal_lax_left_adjoint
           fmonoidal_lax_right_adjoint)
        η.
  Proof.
    exact (pr122 HA).
  Qed.

  Proposition monoidal_adjcounit
    : is_mon_nat_trans
        (comp_fmonoidal_lax
           fmonoidal_lax_right_adjoint
           fmonoidal_lax_left_adjoint)
        (identity_fmonoidal _)
        ε.
  Proof.
    exact (pr222 HA).
  Qed.
End MonoidalAdjunctionAccessors.

(**
 3. Left adjoints are strongly monoidal
 *)
Section LeftAdjointStrong.
  Context {C₁ C₂ : category}
          {M₁ : monoidal C₁}
          {M₂ : monoidal C₂}
          {A : adjunction C₁ C₂}
          (L := left_adjoint A : C₁ ⟶ C₂)
          (R := right_adjoint A : C₂ ⟶ C₁)
          (η := adjunit A : functor_identity _ ⟹ L ∙ R)
          (ε := adjcounit A : R ∙ L ⟹ functor_identity _)
          (HA : monoidal_adjunction M₁ M₂ A)
          (HL := fmonoidal_lax_left_adjoint HA)
          (HR := fmonoidal_lax_right_adjoint HA)
          (Hη := monoidal_adjunit HA)
          (Hε := monoidal_adjcounit HA).

  (**
   3.1. Preservation of the unit
   *)
  Definition is_strong_left_adjoint_on_unit
    : L (monoidal_unit M₁) --> monoidal_unit M₂
    := #L (fmonoidal_preservesunit HR) · ε _.

  Proposition is_strong_left_adjoint_on_unit_laws
    : is_inverse_in_precat
        (fmonoidal_preservesunit HL)
        is_strong_left_adjoint_on_unit.
  Proof.
    split ; unfold is_strong_left_adjoint_on_unit.
    - rewrite !assoc.
      exact (pr2 Hε).
    - rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        exact (nat_trans_ax ε _ _ (fmonoidal_preservesunit HL)).
      }
      cbn -[L R].
      rewrite !assoc.
      rewrite <- functor_comp.
      refine (_ @ triangle_1_statement_from_adjunction A (monoidal_unit M₁)).
      apply maponpaths_2.
      apply maponpaths.
      refine (!(pr2 Hη) @ _).
      apply id_left.
  Qed.

  (**
   3.2. Preservation of the tensor
   *)
  Section PreservesTensor.
    Context (x y : C₁).

    Definition is_strong_left_adjoint_on_tensor
      : L (x ⊗_{M₁} y) --> L x ⊗_{M₂} L y
      := #L((η x ⊗^{M₁} η y)
            · fmonoidal_preservestensordata HR (L x) (L y))
         · ε _.

    Proposition is_strong_left_adjoint_on_tensor_laws
      : is_inverse_in_precat
          (fmonoidal_preservestensordata HL x y)
          is_strong_left_adjoint_on_tensor.
    Proof.
      assert (η (x ⊗_{M₁} y)
              =
              (η x ⊗^{M₁} η y)
              · fmonoidal_preservestensordata HR (L x) (L y)
              · #R (fmonoidal_preservestensordata HL x y))
        as pη.
      {
        refine (!(id_left _) @ pr1 Hη x y @ _).
        rewrite !assoc'.
        apply idpath.
      }
      assert (fmonoidal_preservestensordata HL (R(L x)) (R(L y))
              · #L (fmonoidal_preservestensordata HR (L x) (L y))
              · ε (L x ⊗_{M₂} L y)
              =
              ε (L x) ⊗^{M₂} ε (L y))
        as pε.
      {
        refine (pr1 Hε (L x) (L y) @ _).
        apply id_right.
      }
      split ; unfold is_strong_left_adjoint_on_tensor.
      - rewrite functor_comp.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          unfold functoronmorphisms1.
          cbn -[L R].
          rewrite functor_comp.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply fmonoidal_preservestensornatright.
          }
          rewrite !assoc'.
          apply maponpaths.
          refine (!_).
          apply fmonoidal_preservestensornatleft.
        }
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          exact pε.
        }
        rewrite !assoc.
        etrans.
        {
          refine (!_).
          apply bifunctor_distributes_over_comp ; apply M₂.
        }
        etrans.
        {
          apply maponpaths_2.
          apply (triangle_1_statement_from_adjunction A).
        }
        etrans.
        {
          apply maponpaths.
          apply (triangle_1_statement_from_adjunction A).
        }
        apply bifunctor_distributes_over_id ; apply M₂.
      - rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (nat_trans_ax ε).
        }
        cbn -[L R].
        rewrite !assoc.
        rewrite <- functor_comp.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (!pη).
        }
        apply (triangle_1_statement_from_adjunction A).
    Qed.
  End PreservesTensor.

  Definition is_strong_left_adjoint
    : fmonoidal M₁ M₂ L.
  Proof.
    refine (HL ,, _).
    split.
    - intros x y.
      use make_is_z_isomorphism.
      + exact (is_strong_left_adjoint_on_tensor x y).
      + exact (is_strong_left_adjoint_on_tensor_laws x y).
    - use make_is_z_isomorphism.
      + exact is_strong_left_adjoint_on_unit.
      + exact is_strong_left_adjoint_on_unit_laws.
  Defined.
End LeftAdjointStrong.

(**
 4. If the left adjoint is strong, then the adjunction is monoidal
 *)
Section MonoidalAdjunctionFromStrong.
  Context {C₁ C₂ : category}
          {M₁ : monoidal C₁}
          {M₂ : monoidal C₂}
          {A : adjunction C₁ C₂}
          (L := left_adjoint A : C₁ ⟶ C₂)
          (R := right_adjoint A : C₂ ⟶ C₁)
          (η := adjunit A : functor_identity _ ⟹ L ∙ R)
          (ε := adjcounit A : R ∙ L ⟹ functor_identity _)
          (HL : fmonoidal M₁ M₂ L).

  Definition right_adjoint_monoidal_data_from_strong
    : fmonoidal_data M₂ M₁ R.
  Proof.
    simple refine (_ ,, _).
    - intros x y.
      exact (η _
             · #R (inv_from_z_iso (_ ,, fmonoidal_preservestensorstrongly HL (R x) (R y))
                   · (ε x ⊗^{M₂} ε y))).
    - exact (η _ · #R (inv_from_z_iso (_ ,, fmonoidal_preservesunitstrongly HL))).
  Defined.

  Proposition right_adjoint_monoidal_from_strong_laws
    : fmonoidal_laxlaws right_adjoint_monoidal_data_from_strong.
  Proof.
    repeat split.
    - intros x y₁ y₂ g ; cbn -[L R].
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        exact (nat_trans_ax η _ _ (R x ⊗^{M₁}_{l} # R g)).
      }
      rewrite !assoc'.
      cbn -[L R].
      rewrite <- !(functor_comp R).
      do 2 apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          exact (when_bifunctor_becomes_leftwhiskering M₂ x g).
        }
        etrans.
        {
          refine (!_).
          apply bifunctor_distributes_over_comp ; apply M₂.
        }
        etrans.
        {
          apply maponpaths.
          refine (!_).
          exact (nat_trans_ax ε _ _ _).
        }
        rewrite id_right.
        etrans.
        {
          apply maponpaths_2.
          exact (!(id_left (ε x))).
        }
        etrans.
        {
          apply bifunctor_distributes_over_comp ; apply M₂.
        }
        cbn -[L R].
        apply maponpaths_2.
        exact (when_bifunctor_becomes_leftwhiskering M₂ _ _).
      }
      rewrite !assoc.
      apply maponpaths_2.
      use z_iso_inv_on_right ; cbn -[L R].
      rewrite !assoc.
      use z_iso_inv_on_left ; cbn -[L R].
      refine (!_).
      apply fmonoidal_preservestensornatleft.
    - intros x₁ x₂ y f ; cbn -[L R].
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        exact (nat_trans_ax η _ _ (# R f ⊗^{M₁}_{r} R y)).
      }
      rewrite !assoc'.
      cbn -[L R].
      rewrite <- !(functor_comp R).
      do 2 apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          exact (when_bifunctor_becomes_rightwhiskering M₂ y f).
        }
        etrans.
        {
          refine (!_).
          apply bifunctor_distributes_over_comp ; apply M₂.
        }
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          exact (nat_trans_ax ε _ _ _).
        }
        rewrite id_right.
        etrans.
        {
          apply maponpaths.
          exact (!(id_left (ε y))).
        }
        etrans.
        {
          apply bifunctor_distributes_over_comp ; apply M₂.
        }
        cbn -[L R].
        apply maponpaths_2.
        exact (when_bifunctor_becomes_rightwhiskering M₂ _ _).
      }
      rewrite !assoc.
      apply maponpaths_2.
      use z_iso_inv_on_right ; cbn -[L R].
      rewrite !assoc.
      use z_iso_inv_on_left ; cbn -[L R].
      refine (!_).
      apply fmonoidal_preservestensornatright.
    - intros x y z ; cbn -[L R].
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply (nat_trans_ax η _ _ (_ ⊗^{ M₁}_{r} _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply (nat_trans_ax η _ _ (_ · (_ ⊗^{ M₁}_{l} _))).
      }
      rewrite !assoc'.
      apply maponpaths.
      cbn -[L R].
      rewrite <- !functor_comp.
      apply maponpaths.
      rewrite !assoc'.
      rewrite !functor_comp.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply (strong_fmonoidal_preserves_associativity HL).
      }
      rewrite !assoc'.
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        refine (!_).
        apply (fmonoidal_preservestensornatleft HL).
      }
      rewrite !assoc'.
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (z_iso_inv_after_z_iso (_ ,, _)).
        }
        apply id_left.
      }
      etrans.
      {
        rewrite !functor_comp.
        do 4 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          unfold functoronmorphisms1.
          rewrite whiskerscommutes ; [ | apply M₂ ].
          apply idpath.
        }
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply (bifunctor_leftcomp M₂).
        }
        apply maponpaths.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- !functor_comp.
          apply (nat_trans_ax ε).
        }
        cbn -[L R].
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply (triangle_1_statement_from_adjunction A).
        }
        apply id_left.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply (bifunctor_leftcomp M₂).
        }
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (z_iso_inv_after_z_iso (_ ,, _)).
        }
        apply id_left.
      }
      use z_iso_inv_on_right ; cbn -[L R].
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        do 3 apply maponpaths_2.
        refine (!_).
        apply (fmonoidal_preservestensornatright HL).
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply (z_iso_inv_after_z_iso (_ ,, _)).
        }
        apply id_left.
      }
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply (bifunctor_rightcomp M₂).
        }
        apply maponpaths.
        rewrite !(functor_comp L).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- !functor_comp.
          apply (nat_trans_ax ε).
        }
        cbn -[L R].
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply (triangle_1_statement_from_adjunction A).
        }
        apply id_left.
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        apply (bifunctor_rightcomp M₂).
      }
      rewrite !assoc'.
      apply maponpaths.
      unfold functoronmorphisms1.
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply (bifunctor_leftcomp M₂).
        }
        rewrite !assoc.
        apply maponpaths_2.
        apply monoidal_associatornatleftright.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply monoidal_associatornatleft.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply monoidal_associatornatright.
      }
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply (bifunctor_rightcomp M₂).
      }
      rewrite whiskerscommutes ; [ | apply M₂ ].
      rewrite !assoc'.
      rewrite whiskerscommutes ; [ | apply M₂ ].
      rewrite !assoc.
      rewrite whiskerscommutes ; [ | apply M₂ ].
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        refine (!_).
        apply (bifunctor_rightcomp M₂).
      }
      refine (!_).
      etrans.
      {
        refine (!_).
        apply (bifunctor_rightcomp M₂).
      }
      apply maponpaths.
      rewrite <- whiskerscommutes ; [ | apply M₂ ].
      apply idpath.
    - intros x ; cbn -[L R].
      assert (# L lu^{M₁}_{R x}
              =
              inv_from_z_iso (_ ,, fmonoidal_preservestensorstrongly HL _ _)
              · (inv_from_z_iso (_ ,, fmonoidal_preservesunitstrongly HL) ⊗^{ M₂}_{r} L (R x))
              · lu^{M₂}_{L(R x)})
        as q.
      {
        pose (fmonoidal_preservesleftunitality HL (R x)) as p.
        cbn -[L R] in p.
        rewrite <- p.
        rewrite !assoc.
        refine (!(id_left _) @ _).
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc'.
          apply maponpaths.
          refine (!(bifunctor_rightcomp M₂ _ _ _ _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply (z_iso_after_z_iso_inv (_ ,, _)).
          }
          apply bifunctor_rightid.
        }
        rewrite id_right.
        apply (z_iso_after_z_iso_inv (_ ,, _)).
      }
      refine (_ @ id_right _).
      rewrite <- (triangle_2_statement_from_adjunction A).
      rewrite !assoc.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (nat_trans_ax η _ _ (lu^{M₁}_{R x})).
      }
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        rewrite !assoc.
        do 2 apply maponpaths_2.
        exact (nat_trans_ax η _ _ ((η I_{ M₁} · # R _) ⊗^{ M₁}_{r} R x)).
      }
      rewrite !assoc'.
      apply maponpaths.
      cbn -[L R].
      rewrite <- !functor_comp.
      apply maponpaths.
      rewrite q.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        unfold functoronmorphisms1.
        rewrite !assoc'.
        apply maponpaths.
        apply monoidal_leftunitornat.
      }
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      refine (!_).
      use z_iso_inv_on_right ; cbn -[L R].
      refine (!_).
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply fmonoidal_preservestensornatright.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply (z_iso_inv_after_z_iso (_ ,, _)).
      }
      rewrite id_left.
      etrans.
      {
        refine (!_).
        apply (bifunctor_rightcomp M₂).
      }
      apply maponpaths.
      rewrite functor_comp.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply (nat_trans_ax ε).
      }
      rewrite !assoc.
      refine (_ @ id_left _).
      cbn -[L R].
      apply maponpaths_2.
      apply (triangle_1_statement_from_adjunction A).
    - intros x ; cbn -[L R].
      assert (# L ru^{M₁}_{R x}
              =
              inv_from_z_iso (_ ,, fmonoidal_preservestensorstrongly HL _ _)
              · (L (R x) ⊗^{M₂}_{l} inv_from_z_iso (_ ,, fmonoidal_preservesunitstrongly HL))
              · ru^{M₂}_{L(R x)})
        as q.
      {
        pose (fmonoidal_preservesrightunitality HL (R x)) as p.
        cbn -[L R] in p.
        rewrite <- p.
        rewrite !assoc.
        refine (!(id_left _) @ _).
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc'.
          apply maponpaths.
          refine (!(bifunctor_leftcomp M₂ _ _ _ _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply (z_iso_after_z_iso_inv (_ ,, _)).
          }
          apply bifunctor_leftid.
        }
        rewrite id_right.
        apply (z_iso_after_z_iso_inv (_ ,, _)).
      }
      refine (_ @ id_right _).
      rewrite <- (triangle_2_statement_from_adjunction A).
      rewrite !assoc.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (nat_trans_ax η _ _ (ru^{M₁}_{R x})).
      }
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        rewrite !assoc.
        do 2 apply maponpaths_2.
        exact (nat_trans_ax η _ _ (R x ⊗^{M₁}_{l} (η I_{ M₁} · # R _))).
      }
      rewrite !assoc'.
      apply maponpaths.
      cbn -[L R].
      rewrite <- !functor_comp.
      apply maponpaths.
      pose (fmonoidal_preservesrightunitality HL (R x)) as p.
      rewrite q.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        unfold functoronmorphisms1.
        rewrite (whiskerscommutes M₂) ; [ | apply M₂ ].
        rewrite !assoc'.
        apply maponpaths.
        apply monoidal_rightunitornat.
      }
      rewrite !assoc.
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      refine (!_).
      use z_iso_inv_on_right ; cbn -[L R].
      refine (!_).
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply fmonoidal_preservestensornatleft.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply (z_iso_inv_after_z_iso (_ ,, _)).
      }
      rewrite id_left.
      etrans.
      {
        refine (!_).
        apply (bifunctor_leftcomp M₂).
      }
      apply maponpaths.
      rewrite functor_comp.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply (nat_trans_ax ε).
      }
      rewrite !assoc.
      refine (_ @ id_left _).
      cbn -[L R].
      apply maponpaths_2.
      apply (triangle_1_statement_from_adjunction A).
  Qed.

  Definition right_adjoint_monoidal_from_strong
    : fmonoidal_lax M₂ M₁ R
    := right_adjoint_monoidal_data_from_strong
       ,,
       right_adjoint_monoidal_from_strong_laws.

  Proposition monoidal_adjunction_from_strong_unit
    : is_mon_nat_trans
        (identity_fmonoidal M₁)
        (comp_fmonoidal_lax HL right_adjoint_monoidal_from_strong)
        η.
  Proof.
    split.
    - intros x y ; cbn -[L R].
      rewrite id_left.
      rewrite !assoc'.
      rewrite <- (functor_comp R).
      refine (!_).
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (nat_trans_ax η _ _ (adjunit A x ⊗^{M₁} adjunit A y)).
      }
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      cbn -[L R].
      rewrite <- functor_comp.
      rewrite <- functor_id.
      apply maponpaths.
      rewrite !assoc.
      refine (_ @ z_iso_after_z_iso_inv (_ ,, fmonoidal_preservestensorstrongly HL _ _)).
      apply maponpaths_2.
      refine (!_ @ id_right _).
      use z_iso_inv_on_right ; cbn -[L R].
      refine (!_).
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        unfold functoronmorphisms1.
        rewrite functor_comp.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (fmonoidal_preservestensornatright HL).
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!_).
        apply (fmonoidal_preservestensornatleft HL).
      }
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply (z_iso_inv_after_z_iso (_ ,, fmonoidal_preservestensorstrongly HL _ _)).
      }
      rewrite id_left.
      rewrite !assoc.
      etrans.
      {
        refine (!_).
        apply bifunctor_distributes_over_comp ; apply M₂.
      }
      refine (!_).
      etrans.
      {
        refine (!_).
        apply bifunctor_distributes_over_id ; apply M₂.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply (triangle_1_statement_from_adjunction A).
      }
      apply maponpaths_2.
      apply (triangle_1_statement_from_adjunction A).
    - unfold is_mon_nat_trans_unitlaw ; cbn -[L R].
      rewrite id_left.
      rewrite !assoc'.
      refine (!(id_right _) @ _).
      apply maponpaths.
      rewrite <- functor_comp.
      rewrite <- functor_id.
      apply maponpaths.
      refine (!_).
      apply z_iso_after_z_iso_inv.
  Qed.

  Proposition monoidal_adjunction_from_strong_counit
    : is_mon_nat_trans
        (comp_fmonoidal_lax right_adjoint_monoidal_from_strong HL)
        (identity_fmonoidal M₂)
        ε.
  Proof.
    split.
    - intros x y ; cbn -[L R].
      rewrite id_right.
      rewrite !(functor_comp R).
      rewrite !(functor_comp L).
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        apply (nat_trans_ax ε).
      }
      cbn -[L R].
      rewrite !assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        apply (nat_trans_ax ε).
      }
      cbn -[L R].
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply (triangle_1_statement_from_adjunction A).
      }
      rewrite id_left.
      apply (z_iso_inv_after_z_iso (_ ,, _)).
    - unfold is_mon_nat_trans_unitlaw ; cbn -[L R].
      rewrite functor_comp.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        apply (nat_trans_ax ε).
      }
      cbn -[L R].
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply (triangle_1_statement_from_adjunction A).
      }
      rewrite id_left.
      exact (z_iso_inv_after_z_iso
               (_ ,, fmonoidal_preservesunitstrongly HL)).
  Qed.

  Definition monoidal_adjunction_from_strong
    : monoidal_adjunction M₁ M₂ A.
  Proof.
    use make_monoidal_adjunction.
    - exact HL.
    - exact right_adjoint_monoidal_from_strong.
    - exact monoidal_adjunction_from_strong_unit.
    - exact monoidal_adjunction_from_strong_counit.
  Defined.
End MonoidalAdjunctionFromStrong.

(**
 5. Symmetric monoidal adjunctions
 *)
Definition is_sym_monoidal_adjunction
           {C₁ C₂ : category}
           {M₁ : monoidal C₁}
           {M₂ : monoidal C₂}
           (S₁ : symmetric M₁)
           (S₂ : symmetric M₂)
           {A : adjunction C₁ C₂}
           (HA : monoidal_adjunction M₁ M₂ A)
  : UU
  := is_symmetric_monoidal_functor S₁ S₂ (fmonoidal_lax_left_adjoint HA)
     ×
     is_symmetric_monoidal_functor S₂ S₁ (fmonoidal_lax_right_adjoint HA).

Definition sym_monoidal_adjunction
           {C₁ C₂ : category}
           {M₁ : monoidal C₁}
           {M₂ : monoidal C₂}
           (S₁ : symmetric M₁)
           (S₂ : symmetric M₂)
           (A : adjunction C₁ C₂)
  : UU
  := ∑ (HA : monoidal_adjunction M₁ M₂ A), is_sym_monoidal_adjunction S₁ S₂ HA.

(**
 6. Accessors
 *)
Section SymMonoidalAdjunctionAccessors.
  Context {C₁ C₂ : category}
          {M₁ : monoidal C₁}
          {M₂ : monoidal C₂}
          {S₁ : symmetric M₁}
          {S₂ : symmetric M₂}
          {A : adjunction C₁ C₂}
          (L := left_adjoint A : C₁ ⟶ C₂)
          (R := right_adjoint A : C₂ ⟶ C₁)
          (η := adjunit A)
          (ε := adjcounit A)
          {HA : monoidal_adjunction M₁ M₂ A}
          (HAA : is_sym_monoidal_adjunction S₁ S₂ HA).

  Definition is_symmetric_monoidal_functor_left_adjoint
    : is_symmetric_monoidal_functor S₁ S₂ (fmonoidal_lax_left_adjoint HA)
    := pr1 HAA.

  Definition is_symmetric_monoidal_functor_right_adjoint
    : is_symmetric_monoidal_functor S₂ S₁ (fmonoidal_lax_right_adjoint HA)
    := pr2 HAA.
End SymMonoidalAdjunctionAccessors.

#[reversible=no] Coercion sym_monoidal_adjunction_to_monoidal_adjunction
         {C₁ C₂ : category}
         {M₁ : monoidal C₁}
         {M₂ : monoidal C₂}
         {S₁ : symmetric M₁}
         {S₂ : symmetric M₂}
         {A : adjunction C₁ C₂}
         (HA : sym_monoidal_adjunction S₁ S₂ A)
  : monoidal_adjunction M₁ M₂ A
  := pr1 HA.

#[reversible=no] Coercion sym_monoidal_adjunction_to_is_symmetric
         {C₁ C₂ : category}
         {M₁ : monoidal C₁}
         {M₂ : monoidal C₂}
         {S₁ : symmetric M₁}
         {S₂ : symmetric M₂}
         {A : adjunction C₁ C₂}
         (HA : sym_monoidal_adjunction S₁ S₂ A)
  : is_sym_monoidal_adjunction S₁ S₂ HA
  := pr2 HA.

(**
 7. Symmetric monoidal adjunctions from strong functors
 *)
Section SymMonoidalAdjunctionFromStrong.
  Context {V₁ V₂ : sym_monoidal_cat}
          {A : adjunction V₁ V₂}
          (L := left_adjoint A : V₁ ⟶ V₂)
          (R := right_adjoint A : V₂ ⟶ V₁)
          (η := adjunit A : functor_identity _ ⟹ L ∙ R)
          (ε := adjcounit A : R ∙ L ⟹ functor_identity _)
          (HL : fmonoidal V₁ V₂ L)
          (HHL : is_symmetric_monoidal_functor V₁ V₂ HL).

  Proposition is_sym_monoidal_adjunction_from_strong
    : is_sym_monoidal_adjunction V₁ V₂ (monoidal_adjunction_from_strong HL).
  Proof.
    split.
    - exact HHL.
    - intros x y ; cbn.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply (nat_trans_ax η).
      }
      rewrite !assoc'.
      apply maponpaths.
      cbn.
      rewrite <- !functor_comp.
      apply maponpaths.
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply tensor_sym_mon_braiding.
      }
      rewrite !assoc.
      apply maponpaths_2.
      use z_iso_inv_on_right.
      rewrite !assoc.
      use z_iso_inv_on_left.
      cbn.
      refine (!_).
      apply HHL.
  Qed.

  Definition sym_monoidal_adjunction_from_strong
    : sym_monoidal_adjunction V₁ V₂ A
    := _ ,, is_sym_monoidal_adjunction_from_strong.
End SymMonoidalAdjunctionFromStrong.

(**
 8. Symmetric monoidal adjunctions to comonads
 *)
Lemma sym_monoidal_adjunction_to_sym_monoidal_cmd_comult
      {V₁ V₂ : sym_monoidal_cat}
      (A : adjunction V₁ V₂)
      (HA : sym_monoidal_adjunction V₁ V₂ A)
  : is_mon_nat_trans
      (comp_fmonoidal_lax
         (fmonoidal_lax_right_adjoint HA)
         (fmonoidal_lax_left_adjoint HA))
      (comp_fmonoidal_lax
         (comp_fmonoidal_lax
            (fmonoidal_lax_right_adjoint HA)
            (fmonoidal_lax_left_adjoint HA))
         (comp_fmonoidal_lax
            (fmonoidal_lax_right_adjoint HA)
            (fmonoidal_lax_left_adjoint HA)))
      (δ (Comonad_from_adjunction A)).
Proof.
  cbn.
  pose (is_mon_nat_trans_prewhisker
          (fmonoidal_lax_right_adjoint HA)
          (is_mon_nat_trans_postwhisker
             (monoidal_adjunit HA)
             (fmonoidal_lax_left_adjoint HA)))
    as H.
  split.
  - intros x y.
    refine (_ @ pr1 H x y @ _).
    + cbn.
      rewrite functor_id.
      rewrite id_right.
      apply idpath.
    + cbn.
      rewrite !assoc'.
      rewrite <- !functor_comp.
      rewrite !assoc'.
      rewrite <- !functor_comp.
      apply idpath.
  - refine (_ @ pr2 H @ _).
    + cbn.
      rewrite functor_id.
      rewrite id_right.
      apply idpath.
    + cbn.
      rewrite !assoc'.
      rewrite <- !functor_comp.
      rewrite !assoc'.
      rewrite <- !functor_comp.
      apply idpath.
Qed.

Definition sym_monoidal_adjunction_to_sym_monoidal_cmd
           {V₁ V₂ : sym_monoidal_cat}
           (A : adjunction V₁ V₂)
           (HA : sym_monoidal_adjunction V₁ V₂ A)
  : sym_monoidal_cmd V₂.
Proof.
  use make_symmetric_monoidal_comonad.
  - exact (Comonad_from_adjunction A).
  - exact (comp_fmonoidal_lax
             (fmonoidal_lax_right_adjoint HA)
             (fmonoidal_lax_left_adjoint HA)).
  - exact (is_symmetric_monoidal_comp
             (is_symmetric_monoidal_functor_right_adjoint HA)
             (is_symmetric_monoidal_functor_left_adjoint HA)).
  - exact (sym_monoidal_adjunction_to_sym_monoidal_cmd_comult A HA).
  - exact (monoidal_adjcounit HA).
Defined.
