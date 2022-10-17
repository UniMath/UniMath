Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Section OppositeOfFunctorCatToFunctorCatOfOpposite.

  Context (C D : category).

  Definition opfunctorcat_to_functorcatofoppcats_data
    : functor_data ([C,D]^opp) ([C^opp,D^opp]).
  Proof.
    use make_functor_data.
    - intro F.
      use make_functor.
      + exists (λ c, (pr1 F) c).
        exact (λ c1 c2 f, #(pr1 F) f).
      + abstract (split ; intro ; intros ; cbn ; [ apply functor_id | apply functor_comp ]).
    - intros F G α.
      exists (λ c, pr1 α c).
      intros c1 c2 f.
      exact (! pr2 α c2 c1 f).
  Defined.

  Definition opfunctorcat_to_functorcatofoppcats_is_functor
    : is_functor opfunctorcat_to_functorcatofoppcats_data.
  Proof.
    split ; intro ; intros ; (apply nat_trans_eq ;
      [ apply homset_property
      | intro ; apply idpath
      ]).
  Qed.

  Definition opfunctorcat_to_functorcatofoppcats
    : functor ([C,D]^opp) ([C^opp,D^opp])
    := opfunctorcat_to_functorcatofoppcats_data ,, opfunctorcat_to_functorcatofoppcats_is_functor.

End OppositeOfFunctorCatToFunctorCatOfOpposite.

Section OppositeOfFunctorCatFromFunctorCatOfOpposite.

  Context (C D : category).

  Definition opfunctorcat_from_functorcatofoppcats_data
    : functor_data ([C^opp,D^opp]) ([C,D]^opp).
  Proof.
    use make_functor_data.
    - intro F.
      use make_functor.
      + exists (λ c, (pr1 F) c).
        exact (λ c1 c2 f, #(pr1 F) f).
      + abstract (split ; intro ; intros ; cbn ; [ apply (functor_id F) | apply (functor_comp F) ]).
    - intros F G α.
      exists (λ c, pr1 α c).
      intros c1 c2 f.
      exact (! pr2 α c2 c1 f).
  Defined.

  Definition opfunctorcat_from_functorcatofoppcats_is_functor
    : is_functor opfunctorcat_from_functorcatofoppcats_data.
  Proof.
    split ; intro ; intros ; (apply nat_trans_eq ;
      [ apply homset_property
      | intro ; apply idpath
      ]).
  Qed.

  Definition opfunctorcat_from_functorcatofoppcats
    : functor ([C^opp,D^opp]) ([C,D]^opp)
    := opfunctorcat_from_functorcatofoppcats_data ,, opfunctorcat_from_functorcatofoppcats_is_functor.

End OppositeOfFunctorCatFromFunctorCatOfOpposite.

Section UnitCounit.

  Context (C D : category).

  Lemma counit_opfunctorcat_functorcatofoppcats
    : nat_trans (functor_composite
                   (opfunctorcat_to_functorcatofoppcats C D)
                   (opfunctorcat_from_functorcatofoppcats C D)
                )
                (functor_identity ([C, D]^opp)).
  Proof.
    use make_nat_trans.
    - intro.
      use make_nat_trans.
      + intro ; apply identity.
      + abstract (intro ; intros ; cbn ; apply (id_right _ @ ! id_left _)).
    - abstract (
          intro ; intros ; use nat_trans_eq ;
          [ apply homset_property
          | intro ; simpl ; apply (id_left _ @ ! id_right _) ]).
  Defined.

  Lemma unit_opfunctorcat_functorcatofoppcats
    : nat_trans
        (functor_identity [C^opp , D^opp])
        (functor_composite
           (opfunctorcat_from_functorcatofoppcats C D)
           (opfunctorcat_to_functorcatofoppcats C D)
        ).
  Proof.
    use make_nat_trans.
    - intro.
      use make_nat_trans.
      + intro ; apply identity.
      + abstract (intro ; intros ; cbn ; apply (id_left _ @ ! id_right _)).
    - abstract (
          intro ; intros ; use nat_trans_eq ;
          [ apply homset_property
          | intro ; simpl ; apply (id_left _ @ ! id_right _) ]).
  Defined.

End UnitCounit.


Section OppositeOfFunctorCatEquivFunctorCatOfOpposite.

  Context (C D : category).

  Definition opfunctorcat_adjdata_functorcatofoppcats
    : adjunction_data [C ^opp, D ^opp] ([C, D] ^opp).
  Proof.
    use make_adjunction_data.
    - exact (opfunctorcat_from_functorcatofoppcats C D).
    - exact (opfunctorcat_to_functorcatofoppcats C D).
    - exact (unit_opfunctorcat_functorcatofoppcats C D).
    - exact (counit_opfunctorcat_functorcatofoppcats C D).
  Defined.

  Lemma opfunctorcat_adjdata_functorcatofoppcats_form_adjunction
    :  form_adjunction
         (opfunctorcat_from_functorcatofoppcats C D)
         (opfunctorcat_to_functorcatofoppcats C D)
         (unit_opfunctorcat_functorcatofoppcats C D)
         (counit_opfunctorcat_functorcatofoppcats C D).
  Proof.
    split.
    - intro.
      use nat_trans_eq.
      { apply homset_property. }
      intro  ; apply id_left.
    - intro.
      use nat_trans_eq.
      { apply homset_property. }
      intro  ; apply id_left.
  Qed.

  Definition is_left_adjoint_opfunctorcat_from_functorcatofoppcats
    :  is_left_adjoint (opfunctorcat_from_functorcatofoppcats C D).
  Proof.
    exists (opfunctorcat_to_functorcatofoppcats C D).
    unfold are_adjoints.
    use tpair.
    - exists (unit_opfunctorcat_functorcatofoppcats C D).
      exact (counit_opfunctorcat_functorcatofoppcats C D).
    - exact opfunctorcat_adjdata_functorcatofoppcats_form_adjunction.
  Defined.

  Definition opfunctorcat_functorcatofoppcats_formequivalence
    : forms_equivalence opfunctorcat_adjdata_functorcatofoppcats.
  Proof.
    split.
    - intro.
      use make_is_z_isomorphism.
      + use make_nat_trans.
        * intro ; apply identity.
        * abstract (intro ; intros ; cbn ; apply (id_left _ @ ! id_right _)).
      + split ; (apply nat_trans_eq ; [ apply homset_property | intro ; apply id_right ]).
    - intro.
      use make_is_z_isomorphism.
      + use make_nat_trans.
        * intro ; apply identity.
        * abstract (intro ; intros ; cbn ; apply (id_right _ @ ! id_left _)).
      + split ; (apply nat_trans_eq ; [ apply homset_property | intro ; apply id_right ]).
  Defined.

  Definition opfunctorcat_equiv_functorcatofoppcats
    : equivalence_of_cats [C^opp,D^opp] ([C,D]^opp).
  Proof.
    use make_equivalence_of_cats.
    - exact opfunctorcat_adjdata_functorcatofoppcats.
    - exact opfunctorcat_functorcatofoppcats_formequivalence.
  Defined.

  Definition opfunctorcat_adjequiv_functorcatofoppcats
    : adj_equivalence_of_cats (opfunctorcat_from_functorcatofoppcats C D).
  Proof.
    exists is_left_adjoint_opfunctorcat_from_functorcatofoppcats.
    exact opfunctorcat_functorcatofoppcats_formequivalence.
  Defined.


End OppositeOfFunctorCatEquivFunctorCatOfOpposite.

Section PrecompositionFunctorOfOppositeFunctor.

  Context {A B : category} (C : category) (F : functor A B).

  (* In the following lemma we show that the following diagram commutes (up to a natural isomorphism):

     [B, C] ^opp      ⟶ [A, C] ^opp
       |                    |
       |                    |
     [B^opp, C^opp]   ⟶ [A^opp, C^opp]

   *)

  Definition functor_op_of_precomp_functor_factorizes_through_functorcatofopp_as_nat_trans
    : nat_trans
        (functor_op (pre_composition_functor A B C F))
        (functor_composite
          (opfunctorcat_to_functorcatofoppcats B C)
          (functor_composite
             (pre_composition_functor _ _ _ (functor_op F))
             (opfunctorcat_from_functorcatofoppcats A C))
        ).
  Proof.
    use make_nat_trans.
    - intro.
      use make_nat_trans.
      + intro ; apply identity.
      + abstract (intro ; intros ; apply (id_right _ @ ! id_left _)).
    - abstract (intro ; intros ; use nat_trans_eq ; [ apply homset_property | intro ; apply (id_left _ @ ! id_right _)]).
  Defined.

  Lemma functor_op_of_precomp_functor_factorizes_through_functorcatofopp_is_nat_z_iso
    : is_nat_z_iso functor_op_of_precomp_functor_factorizes_through_functorcatofopp_as_nat_trans.
  Proof.
    intro G.
    use make_is_z_isomorphism.
    - use make_nat_trans.
      + intro ; apply identity.
      + abstract (intro ; intros ; apply (id_right _ @ ! id_left _)).
    - abstract (split ; (use nat_trans_eq ; [ apply homset_property | intro ; apply id_right ])).
  Defined.

  Definition functor_op_of_precomp_functor_factorizes_through_functorcatofopp_nat_z_iso
    : nat_z_iso
        (functor_op (pre_composition_functor A B C F))
        (functor_composite
          (opfunctorcat_to_functorcatofoppcats B C)
          (functor_composite
             (pre_composition_functor _ _ _ (functor_op F))
             (opfunctorcat_from_functorcatofoppcats A C))
        )
    := make_nat_z_iso _ _ _ (functor_op_of_precomp_functor_factorizes_through_functorcatofopp_is_nat_z_iso).

End PrecompositionFunctorOfOppositeFunctor.

Section PostcompositionFunctorOfOppositeFunctor.

  Context {B C : category} (A : category) (F : functor B C).

  Definition functor_op_of_postcomp_functor_factorizes_through_functorcatofopp_as_nat_trans
    : nat_trans
        (functor_op (post_composition_functor A B C F))
        (functor_composite
          (opfunctorcat_to_functorcatofoppcats A B)
          (functor_composite
             (post_composition_functor _ _ _ (functor_op F))
             (opfunctorcat_from_functorcatofoppcats A C))
        ).
  Proof.
    use make_nat_trans.
    - intro.
      use make_nat_trans.
      + intro ; apply identity.
      + abstract (intro ; intros ; apply (id_right _ @ ! id_left _)).
    - abstract (intro ; intros ; use nat_trans_eq ; [ apply homset_property | intro ; apply (id_left _ @ ! id_right _)]).
  Defined.

  Lemma functor_op_of_postcomp_functor_factorizes_through_functorcatofopp_is_nat_z_iso
    : is_nat_z_iso functor_op_of_postcomp_functor_factorizes_through_functorcatofopp_as_nat_trans.
  Proof.
    intro G.
    use make_is_z_isomorphism.
    - use make_nat_trans.
      + intro ; apply identity.
      + abstract (intro ; intros ; apply (id_right _ @ ! id_left _)).
    - abstract (split ; (use nat_trans_eq ; [ apply homset_property | intro ; apply id_right ])).
  Defined.

  Definition functor_op_of_postcomp_functor_factorizes_through_functorcatofopp_nat_z_iso
    : nat_z_iso
        (functor_op (post_composition_functor A B C F))
        (functor_composite
          (opfunctorcat_to_functorcatofoppcats A B)
          (functor_composite
             (post_composition_functor _ _ _ (functor_op F))
             (opfunctorcat_from_functorcatofoppcats A C))
        )
    := make_nat_z_iso _ _ _ (functor_op_of_postcomp_functor_factorizes_through_functorcatofopp_is_nat_z_iso).

End PostcompositionFunctorOfOppositeFunctor.
