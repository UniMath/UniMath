From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.Monoidal.AlternativeDefinitions.MonoidalCategoriesTensored.
Require Import UniMath.CategoryTheory.Monoidal.AlternativeDefinitions.MonoidalFunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.AlternativeDefinitions.EquivalenceWhiskeredNonCurriedMonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.AlternativeDefinitions.MonoidalCategoriesReordered.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.CurriedMonoidalCategories.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.AssociatorUnitorsLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.FinalLayer.

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.CurriedMonoidalCategories.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.AssociatorUnitorsLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.FinalLayer.

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.EquivalenceMonCatCurried.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.EquivalenceWhiskeredCurried.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(*
Definition TODO {A : UU} : A.
Admitted.

Section EquivalenceMonCatNonCurried.

  Definition cmonoidal_to_noncurriedmonoidal
    :  ob UMONCAT ≃ ∑ C : monoidal_cat, is_univalent (monoidal_cat_cat C).
  Proof.
    refine (_ ∘ equivalence_cmon_structure_oblayer)%weq.

    refine (_ ∘ _)%weq.
    {
      use weqfibtototal.
      2: exact (λ C, cmon_equiv_wmon (pr1 C)).
    }

    refine (_ ∘ _)%weq.
    1: apply weqtotal2comm12.

    use weq_subtypes'.
    - refine (moncats0_equiv_uncurried ∘ moncats_equiv_moncats0 ∘ _)%weq.
      use weqfibtototal.
      intro C.
      exact (invweq (monoidal_struct_equiv_monoidal C)).
    - intro ; apply isaprop_is_univalent.
    - intro ; apply isaprop_is_univalent.
    - intro ; apply isrefl_logeq.
  Defined.

End EquivalenceMonCatNonCurried.

Section EquivalenceMonCatNonCurriedLaxFunctors.

  Lemma UMONCAT_2cell_equality
        {M N : ob UMONCAT} {F G : hom M N}
        (α β : (hom M N)⟦F,G⟧)
    : (∏ x : pr11 M,  (pr11 α) x = (pr11 β) x) -> α = β.
  Proof.
    intro p.
    repeat (use total2_paths_f).
    - apply funextsec ; intro x.
      exact (p x).
    - apply isaprop_is_nat_trans.
      apply homset_property.
    - repeat (apply funextsec ; intro) ; apply homset_property.
    - apply homset_property.
    - apply isapropunit.
    - apply isapropunit.
    - apply isapropunit.
    - apply isapropunit.
  Qed.

  Lemma LaxMonoidalFunctor_mor_equality
        {M N : monoidal_cat} {F G : LaxMonoidalFunctorCat M N}
        (α β : (LaxMonoidalFunctorCat M N)⟦F,G⟧)
    : (∏ x : pr11 M,  (pr111 α) x = (pr111 β) x) -> α = β.
  Proof.
    intro p.
    repeat (use total2_paths_f).
    - apply funextsec ; intro x.
      exact (p x).
    - apply isaprop_is_nat_trans.
      apply homset_property.
    - repeat (apply funextsec ; intro) ; apply homset_property.
    - apply homset_property.
    - apply isapropunit.
    - apply isapropunit.
    - apply isapropunit.
  Qed.

  Lemma tensor_on_hom_eq
        (M : ob UMONCAT)
        {x1 x2 y1 y2 : pr11 M}
        (f : (pr11 M)⟦x1,x2⟧) (g : (pr11 M)⟦y1,y2⟧)
    : tensor_on_hom (pr11 (pr112 M)) x1 x2 y1 y2 f g = # (pr121 (cmonoidal_to_noncurriedmonoidal M)) (f #, g).
  Proof.
    etrans.
    2: {  apply (tensor_comp (pr1 (pr112 M)) _ _ _ _ _ _ _ _ _ _). }
    rewrite id_right.
    now rewrite id_left.
  Qed.

  Definition cmonoidal_to_noncurried_functor_pt_data
             (M N : ob UMONCAT)
             {F : functor (pr11 M) (pr11 N)}
             (ptF : functor_tensor_disp_cat
                      (pr121 (cmonoidal_to_noncurriedmonoidal M))
                      (pr121 (cmonoidal_to_noncurriedmonoidal N)) F
             )
    :  preserves_tensor_data (pr1 (pr111 (pr2 M))) (pr1 (pr111 (pr2 N))) F
    := λ x y, pr1 ptF (x,y).

  Lemma cmonoidal_to_noncurried_functor_pt_nat
        (M N : ob UMONCAT)
             {F : functor (pr11 M) (pr11 N)}
             (ptF : functor_tensor_disp_cat
                      (pr121 (cmonoidal_to_noncurriedmonoidal M))
                      (pr121 (cmonoidal_to_noncurriedmonoidal N)) F
             )
    : preserves_tensor_nat (cmonoidal_to_noncurried_functor_pt_data M N ptF).
  Proof.
    intros x1 x2 y1 y2 f g.
    refine (_ @ ! pr2 ptF _ _ (f #, g) @ _).
    - apply maponpaths.
      apply (maponpaths (#F)).
      apply tensor_on_hom_eq.
    - apply maponpaths_2.
      exact (! tensor_on_hom_eq N (#F f) (#F g)).
  Qed.

  Definition cmonoidal_to_noncurried_functor_pt
             (M N : ob UMONCAT)
             {F : functor (pr11 M) (pr11 N)}
             (ptF : functor_tensor_disp_cat
                      (pr121 (cmonoidal_to_noncurriedmonoidal M))
                      (pr121 (cmonoidal_to_noncurriedmonoidal N)) F
             )
    : preserves_tensor (pr111 (pr2 M)) (pr111 (pr2 N)) F
    := _ ,, cmonoidal_to_noncurried_functor_pt_nat M N ptF.

  Lemma cmonoidal_to_noncurrier_preserves_lunitor
        (M N : ob UMONCAT)
        (F : LaxMonoidalFunctorCat
               (pr1 (cmonoidal_to_noncurriedmonoidal M))
               (pr1 (cmonoidal_to_noncurriedmonoidal N)))
    : preserves_lunitor
        (cmonoidal_to_noncurried_functor_pt M N (pr121 F),, pr221 F)
        (pr112 (pr12 M)) (pr112 (pr12 N)).
  Proof.
    intro x.
    refine (_ @ ! (pr112 F x)).
    do 2 apply maponpaths_2.
    apply tensor_on_hom_eq.
  Qed.

  Lemma cmonoidal_to_noncurrier_preserves_runitor
        (M N : ob UMONCAT)
        (F : LaxMonoidalFunctorCat
               (pr1 (cmonoidal_to_noncurriedmonoidal M))
               (pr1 (cmonoidal_to_noncurriedmonoidal N)))
    : preserves_runitor
        (cmonoidal_to_noncurried_functor_pt M N (pr121 F),, pr221 F)
        (pr212 (pr12 M)) (pr212 (pr12 N)).
  Proof.
    intro x.
    refine (_ @ ! (pr212 F x)).
    do 2 apply maponpaths_2.
    apply tensor_on_hom_eq.
  Qed.

  Lemma cmonoidal_to_noncurrier_preserves_associator
        (M N : ob UMONCAT)
        (F : LaxMonoidalFunctorCat
               (pr1 (cmonoidal_to_noncurriedmonoidal M))
               (pr1 (cmonoidal_to_noncurriedmonoidal N)))
    : preserves_associator
        (cmonoidal_to_noncurried_functor_pt M N (pr121 F),, pr221 F)
        (pr221 (pr2 M)) (pr221 (pr2 N)).
  Proof.
    intros x y z.
    etrans. {
      do 2 apply maponpaths_2.
      apply tensor_on_hom_eq.
    }
    refine (pr22 F x y z @ _).
    apply maponpaths_2.
    rewrite <- (tensor_on_hom_eq N).
    apply idpath.
  Admitted.

  Definition cmonoidal_to_noncurried_functor
             (M N : ob UMONCAT)
    :  LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
                             (pr1 (cmonoidal_to_noncurriedmonoidal N)) → UMONCAT ⟦ M, N ⟧.
  Proof.
    intro F.
    use tpair.
    { exact (pr11 F). }

    use tpair.
    - use tpair.
      + split.
        * apply cmonoidal_to_noncurried_functor_pt.
          apply (pr121 F).
        * exact (pr221 F).
      + repeat split.
        * apply cmonoidal_to_noncurrier_preserves_lunitor.
        * apply cmonoidal_to_noncurrier_preserves_runitor.
        * apply cmonoidal_to_noncurrier_preserves_associator.
    - exact tt.
  Defined.

  Definition cmonoidal_from_noncurried_functor (M N : ob UMONCAT)
    :  UMONCAT ⟦ M, N ⟧
       → LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
                               (pr1 (cmonoidal_to_noncurriedmonoidal N)).
  Proof.
    intro F.
    use tpair.
    - exists (pr1 F).
      split.
      + use tpair.
        * intro ; apply (pr1 (pr112 F)).
        * intros [x1 x2] [y1 y2] [f g].
          etrans. { apply maponpaths_2, (! tensor_on_hom_eq N _ _). }
          refine (! pr21 (pr112 F) x1 y1 x2 y2 f g @ _).
          simpl.
          do 2 apply maponpaths.
          apply tensor_on_hom_eq.
      + apply (pr2 (pr112 F)).
    - repeat split.
      + abstract (
            intro x ;
            refine (! (pr11 (pr212 F) x) @ _) ;
            do 2 apply maponpaths_2 ;
            apply (tensor_on_hom_eq N)).
      + abstract (
            intro x ;
            refine (! (pr21 (pr212 F) x) @ _) ;
            do 2 apply maponpaths_2 ;
            apply (tensor_on_hom_eq N)).
      + intros x y z.
        (*
        etrans. { do 2 apply maponpaths_2. apply (! tensor_on_hom_eq N _ _). }
        refine ((pr2 (pr212 F) x y z) @ _).
        apply maponpaths_2.
        apply maponpaths.
        apply (tensor_on_hom_eq N).
         *)
        apply TODO.
  Defined.

  Definition cmonoidal_from_noncurried_nattrans
             (M N : ob UMONCAT)
             { F G : hom M N }
             (α : hom M N ⟦ F, G ⟧)
    :  LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
                             (pr1 (cmonoidal_to_noncurriedmonoidal N))
                             ⟦ (λ F0 : hom M N, cmonoidal_from_noncurried_functor M N F0) F,
                               (λ F0 : hom M N, cmonoidal_from_noncurried_functor M N F0) G ⟧.
  Proof.
    use tpair.
    - exists (pr1 α).
      split.
      + intros x y.
        etrans. {
          apply maponpaths_2.
          apply (! tensor_on_hom_eq N _ _).
        }
        exact (! pr1 (pr112 α) x y).
      + exact (pr2 (pr112 α)).
    - repeat split.
  Defined.

  Definition cmonoidal_to_noncurried_nattrans
             (M N : UMONCAT)
             {F G : LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
        (pr1 (cmonoidal_to_noncurriedmonoidal N))}
             (α : LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
                                        (pr1 (cmonoidal_to_noncurriedmonoidal N)) ⟦ F, G ⟧)
    : (hom M N)⟦ (λ F0 : LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
              (pr1 (cmonoidal_to_noncurriedmonoidal N)), cmonoidal_to_noncurried_functor M N F0) F,
  (λ F0 : LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
                                (pr1 (cmonoidal_to_noncurriedmonoidal N)), cmonoidal_to_noncurried_functor M N F0) G ⟧.
  Proof.
    exists (pr11 α).
    use tpair.
    - use tpair.
      + split.
        * intros x y.
          etrans.
          2: {
            apply maponpaths_2.
            apply (! tensor_on_hom_eq N _ _).
          }
          exact (! pr121 α x y).
        * exact (pr221 α).
      + repeat split ; exact tt.
    - repeat split.
  Defined.

  Definition cmonoidal_to_noncurried_hom_data
             (M N : ob UMONCAT)
    : functor_data
        (hom M N)
        (LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
                                               (pr1 (cmonoidal_to_noncurriedmonoidal N))).
  Proof.
    use make_functor_data.
    - intro F.
      exact (cmonoidal_from_noncurried_functor M N F).
    - intros F G α.
      exact (cmonoidal_from_noncurried_nattrans M N α).
  Defined.

  Definition cmonoidal_from_noncurried_hom_data
             (M N : ob UMONCAT)
    : functor_data
        (LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
                               (pr1 (cmonoidal_to_noncurriedmonoidal N)))
        (hom M N).
  Proof.
    use make_functor_data.
    - intro F.
      exact (cmonoidal_to_noncurried_functor M N F).
    - intros F G α.
      exact (cmonoidal_to_noncurried_nattrans M N α).
  Defined.

  Lemma cmonoidal_to_noncurried_hom_is_functor
        (M N : ob UMONCAT)
    : is_functor (cmonoidal_to_noncurried_hom_data M N).
  Proof.
    split.
    - intro.
      apply LaxMonoidalFunctor_mor_equality.
      intro ; apply idpath.
    - intro ; intros.
      apply LaxMonoidalFunctor_mor_equality.
      intro ; apply idpath.
  Qed.

  Lemma cmonoidal_from_noncurried_hom_is_functor
        (M N : ob UMONCAT)
    : is_functor (cmonoidal_from_noncurried_hom_data M N).
  Proof.
    split.
    - intro.
      apply UMONCAT_2cell_equality.
      intro ; apply idpath.
    - intro ; intros.
      apply UMONCAT_2cell_equality.
      intro ; apply idpath.
  Qed.

  Definition cmonoidal_to_noncurried_hom
             (M N : ob UMONCAT)
    : functor
        (hom M N)
        (LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
                               (pr1 (cmonoidal_to_noncurriedmonoidal N)))
    := _ ,, cmonoidal_to_noncurried_hom_is_functor M N.

  Definition cmonoidal_from_noncurried_hom
             (M N : ob UMONCAT)
    : functor
        (LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
                               (pr1 (cmonoidal_to_noncurriedmonoidal N)))
        (hom M N)
    := _ ,, cmonoidal_from_noncurried_hom_is_functor M N.

  Definition cmonoidal_unit_noncurried_hom_data (M N : ob UMONCAT)
    : nat_trans_data (functor_identity (hom M N))
                (cmonoidal_to_noncurried_hom M N ∙ cmonoidal_from_noncurried_hom M N).
  Proof.
    intro F.
    exists (nat_trans_id _).
    use tpair.
    - use tpair.
      + use tpair.
        * intros x y.

          rewrite id_right.
          refine (! id_left _ @ _).
          apply maponpaths_2.
          etrans.
          2: { apply (! tensor_on_hom_eq N _ _). }
          exact (! functor_id (pr121 (cmonoidal_to_noncurriedmonoidal N)) (pr11 F x , pr11 F y)).
        * apply id_right.
      + repeat split.
    - exact tt.
  Defined.

  Definition cmonoidal_unit_noncurried_hom_is_nat_trans
             (M N : ob UMONCAT)
    : is_nat_trans _ _ (cmonoidal_unit_noncurried_hom_data M N).
  Proof.
    intro ; intros.
    use UMONCAT_2cell_equality.
    intro.
    exact (id_right _ @ ! id_left _).
  Qed.

  Definition cmonoidal_unit_noncurried_hom (M N : ob UMONCAT)
    : nat_trans (functor_identity (hom M N))
                (cmonoidal_to_noncurried_hom M N ∙ cmonoidal_from_noncurried_hom M N)
    := _ ,, cmonoidal_unit_noncurried_hom_is_nat_trans M N.

  Definition cmonoidal_counit_noncurried_hom_data (M N : ob UMONCAT)
    :  nat_trans_data
         (cmonoidal_from_noncurried_hom M N ∙ cmonoidal_to_noncurried_hom M N)
         (functor_identity (LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
                                                  (pr1 (cmonoidal_to_noncurriedmonoidal N)))).
  Proof.
    intro F.
    use tpair.
    - exists (nat_trans_id _).
      split.
      + intros x y.
        simpl ; rewrite id_right ; cbn.
        etrans. {
          apply maponpaths_2.
          etrans. {
            apply (! tensor_on_hom_eq N _ _).
          }
          apply tensor_id.
        }
        apply id_left.
      + apply id_right.
    - repeat (use tpair) ; exact tt.
  Defined.

  Definition cmonoidal_counit_noncurried_hom_is_nat_trans (M N : ob UMONCAT)
    :  is_nat_trans _ _ (cmonoidal_counit_noncurried_hom_data M N).
  Proof.
    intro ; intros.
    use LaxMonoidalFunctor_mor_equality.
    intro.
    exact (id_right _ @ ! id_left _).
  Qed.

  Definition cmonoidal_counit_noncurried_hom (M N : ob UMONCAT)
    :  nat_trans
         (cmonoidal_from_noncurried_hom M N ∙ cmonoidal_to_noncurried_hom M N)
         (functor_identity (LaxMonoidalFunctorCat (pr1 (cmonoidal_to_noncurriedmonoidal M))
                                                  (pr1 (cmonoidal_to_noncurriedmonoidal N))))
    := _ ,, cmonoidal_counit_noncurried_hom_is_nat_trans M N.

  Definition cmonoidal_formadjunction_noncurried (M N : ob UMONCAT)
    :  form_adjunction _ _ (cmonoidal_unit_noncurried_hom M N) (cmonoidal_counit_noncurried_hom M N).
  Proof.
    split.
    - intro ; intros.
      apply LaxMonoidalFunctor_mor_equality ; intro ; apply id_left.
    - intro ; intros.
      apply UMONCAT_2cell_equality ; intro ; apply id_left.
  Qed.

  Definition cmonoidal_formequivalence_noncurried (M N : ob UMONCAT)
    :  forms_equivalence
         (cmonoidal_to_noncurried_hom M N ,, cmonoidal_from_noncurried_hom M N,, cmonoidal_unit_noncurried_hom M N,, cmonoidal_counit_noncurried_hom M N).
  Proof.
    split ; intro.
    - use tpair.
      + repeat (use tpair).
        * apply nat_trans_id.
        * apply nat_trans_id.
        * intros x y.
          simpl.
          rewrite id_right.
          etrans.
          2: {
            apply maponpaths_2.
            apply (! tensor_id _ _ _).
          }
          apply (! id_left _).
        * apply id_right.
        * exact tt.
        * exact tt.
        * exact tt.
        * exact tt.
      + split ; apply UMONCAT_2cell_equality ; intro ; apply id_right.
    - use tpair.
      + repeat (use tpair).
        * apply nat_trans_id.
        * apply nat_trans_id.
        * intros x y.
          simpl.
          rewrite id_right.
          etrans. {
            apply maponpaths_2.
            apply (! tensor_on_hom_eq N _ _).
          }
          etrans. {
            apply maponpaths_2.
            apply (tensor_id _ _ _).
          }
          apply id_left.
        * apply id_right.
        * exact tt.
        * exact tt.
        * exact tt.
      + split.
        * apply LaxMonoidalFunctor_mor_equality.
          intro ; apply id_right.
        * apply LaxMonoidalFunctor_mor_equality.
          intro ; apply id_right.
  Defined.

  Definition cmonoidal_adjequiv_noncurried_hom
             (M N : ob UMONCAT)
    : adj_equivalence_of_cats (cmonoidal_to_noncurried_hom M N).
  Proof.
    use make_adj_equivalence_of_cats.
    - exact (cmonoidal_from_noncurried_hom M N).
    - exact (cmonoidal_unit_noncurried_hom M N).
    - exact (cmonoidal_counit_noncurried_hom M N).
    - exact (cmonoidal_formadjunction_noncurried M N).
    - exact (cmonoidal_formequivalence_noncurried M N).
  Defined.
End EquivalenceMonCatNonCurriedLaxFunctors.
*)
