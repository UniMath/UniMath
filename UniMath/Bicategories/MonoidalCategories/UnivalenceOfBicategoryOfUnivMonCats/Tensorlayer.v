(*
This is the second of a sequence of files with the purpose of showing that the bicategory of univalent monoidal categories is again univalent.
In this file we construct one side of the first displayed layer above the bicategory of univalent categories, more precisely:
The total category corresponding to this displayed layer is the univalent bicategory defined as followed:
- The objects are categories together with a binary operation (which will be the tensor product for the monoidal structure).
- The morphisms are functors which preserve the tensor in a lax/weak sense (i.e. a non-necessairly isomorphic morphism).
- The 2-cells are natural transformations which (at the unit) commute the tensor-preserving morphisms.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section Tensor.

  Definition tensor_data (C : univalent_category) : UU :=
    ∑ T : C -> C -> C, ∏ (x1 x2 y1 y2 : C), C⟦x1,x2⟧ -> C⟦y1,y2⟧ -> C⟦T x1 y1, T x2 y2⟧.

  Definition make_tensor_data {C : univalent_category} (T : C -> C -> C) (h : ∏ (x1 x2 y1 y2 : C), C⟦x1,x2⟧ -> C⟦y1,y2⟧ -> C⟦T x1 y1, T x2 y2⟧) : tensor_data C := (T,,h).

  Definition tensor_on_ob {C : univalent_category} (T : tensor_data C) : C -> C -> C := pr1 T.
  Notation "x ⊗_{ T } y" := (tensor_on_ob T x y) (at level 31).

  Definition tensor_on_hom {C : univalent_category} (T : tensor_data C)
    : ∏ (x1 x2 y1 y2 : C), C⟦x1,x2⟧ -> C⟦y1,y2⟧ -> C⟦x1 ⊗_{T} y1, x2 ⊗_{T} y2⟧ := pr2 T.
  Notation "f ⊗^{ T } g" := (tensor_on_hom T _ _ _ _ f g) (at level 31).

  Definition tensor_idax {C : univalent_category} (T : tensor_data C)
    := ∏ (x y : C), (identity x) ⊗^{T} (identity y) = identity (x ⊗_{T} y).

  Definition tensor_compax {C : univalent_category} (T : tensor_data C)
    := ∏ (x1 x2 x3 y1 y2 y3 : C) (f1 : C⟦x1,x2⟧) (f2 : C⟦x2,x3⟧) (g1 : C⟦y1,y2⟧) (g2 : C⟦y2,y3⟧),
      (f1 · f2) ⊗^{T} (g1 · g2) = (f1 ⊗^{T} g1) · (f2 ⊗^{T} g2).

  Definition tensor_ax {C : univalent_category} (T : tensor_data C) : UU
    := tensor_idax T × tensor_compax T.

  Definition tensor (C : univalent_category) : UU :=
    ∑ T : tensor_data C, tensor_ax T.

  Definition tensor_to_data {C : univalent_category} (T : tensor C) : tensor_data C := pr1 T.
  Coercion tensor_to_data : tensor >-> tensor_data.

  Definition tensor_to_ax {C : univalent_category} (T : tensor C) : tensor_ax T := pr2 T.

  Definition tensor_id {C : univalent_category} (T : tensor C) : tensor_idax T
    := pr1 (tensor_to_ax T).

  Definition tensor_comp {C : univalent_category} (T : tensor C) : tensor_compax T
    := pr2 (tensor_to_ax T).



  Definition preserves_tensor_data {C D : univalent_category} (TC : tensor_data C) (TD : tensor_data D) (F : functor C D) : UU :=
    ∏ (x y : C), D ⟦ F x ⊗_{TD} F y, F (x ⊗_{TC} y) ⟧.

  Definition preserves_tensor_nat {C D : univalent_category} {TC : tensor C} {TD : tensor D} {F : functor C D} (ptF : preserves_tensor_data TC TD F) : UU
    := ∏ (x1 x2 y1 y2 : C) (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      (ptF x1 y1) · (functor_on_morphisms F  (f ⊗^{TC} g)) = ((functor_on_morphisms F f) ⊗^{TD} (functor_on_morphisms F g)) · ptF x2 y2.

  Definition preserves_tensor  {C D : univalent_category} (TC : tensor C) (TD : tensor D) (F : functor C D) : UU
    := ∑ (ptF : preserves_tensor_data TC TD F), preserves_tensor_nat ptF.

  Definition preservestensor_into_preservestensordata {C D : univalent_category} {TC : tensor C} {TD : tensor D} {F : functor C D} (pt : preserves_tensor TC TD F)
    : preserves_tensor_data TC TD F := pr1 pt.
  Coercion preservestensor_into_preservestensordata : preserves_tensor >-> preserves_tensor_data.

  Lemma identityfunctor_preserves_tensor_data {C : univalent_category} (T : tensor C)
    : preserves_tensor_data T T (functor_identity C).
  Proof.
    intros x y.
    apply identity.
  Defined.

  Lemma identityfunctor_preserves_tensor_nat {C : univalent_category} (T : tensor C)
    : preserves_tensor_nat (identityfunctor_preserves_tensor_data T).
  Proof.
    intros x1 x2 y1 y2 f g.
    rewrite id_left.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition identityfunctor_preserves_tensor {C : univalent_category} (T : tensor C)
    : preserves_tensor T T (functor_identity C)
    := (identityfunctor_preserves_tensor_data T,, identityfunctor_preserves_tensor_nat T).

  Lemma compositions_preserves_tensor_data
        {C D E : univalent_category}
        {TC : tensor C} {TD : tensor D} {TE : tensor E}
        {F : functor C D} {G : functor D E}
        (ptF : preserves_tensor_data TC TD F) (ptG : preserves_tensor_data TD TE G)
    : preserves_tensor_data TC TE (functor_composite F G).
  Proof.
    intros x y.
    exact ((ptG (F x) (F y)) · (functor_on_morphisms G) (ptF x y)).
  Defined.

  Lemma compositions_preserves_tensor_nat
        {C D E : univalent_category}
        {TC : tensor C} {TD : tensor D} {TE : tensor E}
        {F : functor C D} {G : functor D E}
        (ptF : preserves_tensor TC TD F) (ptG : preserves_tensor TD TE G)
    : preserves_tensor_nat (compositions_preserves_tensor_data ptF ptG).
  Proof.
    intros x1 x2 y1 y2 f g.
    unfold compositions_preserves_tensor_data.
    simpl.
    rewrite assoc'.
    etrans. {
      apply cancel_precomposition.
      apply (pathsinv0 (functor_comp G _ _)).
    }
    rewrite (pr2 ptF).
    rewrite assoc.
    rewrite functor_comp.
    rewrite assoc.
    rewrite (pr2 ptG).
    apply idpath.
  Qed.

  Definition compositions_preserves_tensor
        {C D E : univalent_category}
        {TC : tensor C} {TD : tensor D} {TE : tensor E}
        {F : functor C D} {G : functor D E}
        (ptF : preserves_tensor TC TD F) (ptG : preserves_tensor TD TE G)
    : preserves_tensor TC TE (functor_composite F G)
    := (compositions_preserves_tensor_data ptF ptG,, compositions_preserves_tensor_nat ptF ptG).

  Definition preservestensor_commutes
             {C D : univalent_category}
             {TC : tensor C}
             {TD : tensor D}
             {F G : functor C D}
             (ptF : preserves_tensor_data TC TD F)
             (ptG : preserves_tensor_data TC TD G)
             (α : nat_trans F G)
    : UU := ∏ (x y : C),
    (ptF x y) ·  α (x ⊗_{TC} y)
    = (α x) ⊗^{TD} (α y) · (ptG x y).

  Definition identitynattrans_preservestensor_commutes
             {C D : univalent_category}
             {TC : tensor C}
             {TD : tensor D}
             {F : functor C D}
             (ptF : preserves_tensor_data TC TD F)
    : preservestensor_commutes ptF ptF (nat_trans_id F).
  Proof.
    intros x y.
    simpl.
    rewrite id_right.
    rewrite tensor_id.
    rewrite id_left.
    apply idpath.
  Qed.

End Tensor.

Module TensorLayerNotation.

  Notation "x ⊗_{ T } y" := (tensor_on_ob T x y) (at level 31).
  Notation "f ⊗^{ T } g" := (tensor_on_hom T _ _ _ _ f g) (at level 31).

End TensorLayerNotation.


Section TensorLayer.

  Import TensorLayerNotation.

  Definition catcatstensor_disp_ob_mor : disp_cat_ob_mor bicat_of_univ_cats.
  Proof.
    use tpair.
    - exact (λ C, tensor C).
    - exact (λ C D TC TD F, preserves_tensor TC TD F).
  Defined.

  Definition catcatstensor_disp_id_comp : disp_cat_id_comp bicat_of_univ_cats catcatstensor_disp_ob_mor.
  Proof.
    use tpair.
    - intros C TC.
      apply identityfunctor_preserves_tensor.
    - intros C D E F G TC TD TE.
      apply compositions_preserves_tensor.
  Defined.

  Definition catcatstensor_disp_catdata : disp_cat_data bicat_of_univ_cats
    := (catcatstensor_disp_ob_mor,,catcatstensor_disp_id_comp).

  Definition bicatcatstensor_disp_2cell_struct : disp_2cell_struct catcatstensor_disp_ob_mor.
  Proof.
    intros C D F G α TC TD.
    exact (λ ptF ptG, preservestensor_commutes (pr1 ptF) (pr1 ptG) α).
  Defined.

  Lemma isaprop_bicatcatstensor_disp_2cell_struct
        {C D : bicat_of_univ_cats}
        {F G : bicat_of_univ_cats ⟦C,D⟧ }
        {α : prebicat_cells bicat_of_univ_cats F G}
        {TC : catcatstensor_disp_catdata C}
        {TD : catcatstensor_disp_catdata D}
        (ptF : TC -->[ F] TD)
        (ptG : TC -->[ G] TD)
    : isaprop (bicatcatstensor_disp_2cell_struct C D F G α TC TD ptF ptG).
  Proof.
    unfold bicatcatstensor_disp_2cell_struct.
    unfold preservestensor_commutes.
    repeat (apply impred_isaprop ; intro).
    apply univalent_category_has_homsets.
  Qed.

  Definition bicatcatstensor_disp_prebicat_1_id_comp_cells
    :  disp_prebicat_1_id_comp_cells bicat_of_univ_cats
    := (catcatstensor_disp_catdata,, bicatcatstensor_disp_2cell_struct).

  Definition bicatcatstensor_disp_prebicat_ops : disp_prebicat_ops bicatcatstensor_disp_prebicat_1_id_comp_cells.
  Proof.
    use tpair.
    - intros C D F TC TD ptF.
      intros x y.
      etrans. { apply id_right. }
      simpl.
      rewrite tensor_id.
      rewrite id_left.
      apply idpath.
    - use tpair.
      + intros C D F TC TD ptF.
        intros x y.
        rewrite id_right.
        simpl.
        rewrite tensor_id.
        rewrite id_left.
        unfold identityfunctor_preserves_tensor_data.
        unfold compositions_preserves_tensor_data.
        rewrite functor_id.
        apply id_right.
      + use tpair.
        * intros C D F TC TD ptF.
          intros x y.
          rewrite id_right.
          cbn.
          unfold compositions_preserves_tensor_data.
          unfold identityfunctor_preserves_tensor_data.
          rewrite id_left.
          simpl.
          rewrite tensor_id.
          rewrite id_left.
          apply idpath.
        * use tpair.
          --  intros C D F TC TD ptF.
              intros x y.
              rewrite id_right.
              simpl.
              rewrite tensor_id.
              rewrite id_left.
              cbn.
              unfold compositions_preserves_tensor_data.
              cbn.
              unfold identityfunctor_preserves_tensor_data.
              rewrite functor_id.
              rewrite id_right.
              apply idpath.
          -- use tpair.
             ++ intros C D F TC TD ptF.
                intros x y.
                rewrite id_right.
                cbn.
                rewrite tensor_id.
                unfold compositions_preserves_tensor_data.
                unfold identityfunctor_preserves_tensor_data.
                simpl.
                rewrite id_left.
                rewrite id_left.
                apply idpath.
             ++ use tpair.
                ** intros C D E W F G H TC TD TE TW ptF ptG ptH.
                   intros x y.
                   simpl.
                   rewrite id_right.
                   rewrite tensor_id.
                   rewrite id_left.
                   cbn.
                   unfold compositions_preserves_tensor_data.
                   cbn.
                   rewrite assoc'.
                   rewrite functor_comp.
                   apply idpath.
                ** use tpair.
                   --- intros C D E W F G H TC TD TE TW ptF ptG ptH.
                       intros x y.
                       simpl.
                       rewrite id_right.
                       rewrite tensor_id.
                       rewrite id_left.
                       cbn.
                       unfold compositions_preserves_tensor_data.
                       cbn.
                       rewrite assoc'.
                       rewrite functor_comp.
                       apply idpath.
                   --- use tpair.
                       +++ intros C D F G H α β TC TD ptF ptG ptH ptcα ptcβ.
                           intros x y.
                               simpl.
                               rewrite assoc.
                               rewrite ptcα.
                               rewrite assoc'.
                               rewrite ptcβ.
                               rewrite assoc.
                               rewrite tensor_comp.
                               apply idpath.
                       +++ use tpair.
                           *** intros C D E F G H α TC TD TE ptF ptG ptH ptcα.
                               intros x y.
                               cbn.
                               unfold compositions_preserves_tensor_data.
                               rewrite assoc'.
                               rewrite (pr2 α).
                               rewrite assoc.
                               rewrite ptcα.
                               rewrite assoc.
                               apply idpath.
                           *** intros C D E F G H α TC TD TE ptF ptG ptH ptcα.
                               intros x y.
                               cbn.
                               unfold compositions_preserves_tensor_data.
                               rewrite assoc'.
                               etrans. {
                                 apply cancel_precomposition.
                                 apply (pathsinv0 (functor_comp _ _ _)).
                               }
                               etrans. {
                                 apply cancel_precomposition.
                                 apply maponpaths.
                                 apply ptcα.
                               }
                               rewrite assoc.
                               rewrite functor_comp.
                               rewrite assoc.
                               apply cancel_postcomposition.
                               cbn in *.
                               unfold preserves_tensor in ptF.
                               induction ptF as [ptF ptnatF].
                               induction ptG as [ptG ptnatG].
                               induction ptH as [ptH ptnatH].

                               cbn in *.
                               unfold bicatcatstensor_disp_2cell_struct in ptcα.
                               cbn in *.
                               unfold preserves_tensor_nat in ptnatF.

                               etrans. { apply ptnatH. }
                               cbn in *.
                               apply cancel_precomposition.
                               apply idpath.
  Defined.


  Definition bicatcatstensor_disp_prebicat_data : disp_prebicat_data bicat_of_univ_cats
    := (bicatcatstensor_disp_prebicat_1_id_comp_cells,, bicatcatstensor_disp_prebicat_ops).

  Definition bicatcatstensor_disp_prebicat_laws : disp_prebicat_laws bicatcatstensor_disp_prebicat_data.
  Proof.
    repeat split; intro; intros; apply isaprop_bicatcatstensor_disp_2cell_struct.
  Qed.

  Definition bicatcatstensor_disp_prebicat : disp_prebicat bicat_of_univ_cats
    := (bicatcatstensor_disp_prebicat_data,,bicatcatstensor_disp_prebicat_laws).

  Definition bicatcatstensor_disp_bicat : disp_bicat bicat_of_univ_cats.
  Proof.
    refine (bicatcatstensor_disp_prebicat,, _).
    intros C D F G α TC TD ptF ptG.
    apply isasetaprop.
    unfold disp_2cells.
    unfold bicatcatstensor_disp_prebicat.
    simpl.
    unfold bicatcatstensor_disp_2cell_struct.
    unfold preservestensor_commutes.
    repeat (apply impred_isaprop ; intro).
    apply univalent_category_has_homsets.
  Defined.


  (** We now show that this displayed bicategory is locally univalent *)
  Definition disp_inv_to_eq1
             {C D : bicat_of_univ_cats}
             {F : bicat_of_univ_cats⟦C,D⟧}
             {TC : bicatcatstensor_disp_bicat C}
             {TD : bicatcatstensor_disp_bicat D}
             (ptF ptG : TC -->[F] TD)
    : disp_invertible_2cell (id2_invertible_2cell F) ptF ptG -> pr1 ptF = pr1 ptG.
  Proof.
    intro i.
    apply funextsec ; intro ; apply funextsec ; intro.
    set (ix := (pr1 i) x x0).
    cbn in ix.
    rewrite id_right in ix.
    rewrite tensor_id in ix.
    rewrite id_left in ix.
    exact ix.
  Defined.

  Definition disp_inv_to_eq
             {C D : bicat_of_univ_cats}
             {F : bicat_of_univ_cats⟦C,D⟧}
             {TC : bicatcatstensor_disp_bicat C}
             {TD : bicatcatstensor_disp_bicat D}
             (ptF ptG : TC -->[F] TD)
    : disp_invertible_2cell (id2_invertible_2cell F) ptF ptG -> ptF = ptG.
  Proof.
    intro i.
    use total2_paths_b.
    - apply (disp_inv_to_eq1 ptF ptG i).
    - apply funextsec ; intro ; apply funextsec ; intro.
      set (ix := (pr1 i) x x0).
      cbn in ix.
      rewrite id_right in ix.
      rewrite tensor_id in ix.
      rewrite id_left in ix.
      repeat (use tpair).
      repeat (apply impred_isaprop ; intro).
      apply univalent_category_has_homsets.
  Defined.

  Theorem bicatcatstensor_disp_bicat_is_locally_univalent :
    disp_univalent_2_1 bicatcatstensor_disp_bicat.
  Proof.
    apply fiberwise_local_univalent_is_univalent_2_1.
    intros C D F TC TD ptF1 ptF2.
    use isweqimplimpl.
    - apply disp_inv_to_eq.
    - cbn in ptF1 ; cbn in ptF2.
      rewrite idpath_transportf.
      unfold preserves_tensor in ptF1 ; unfold preserves_tensor in ptF2.
      assert (pf : isaset (preserves_tensor TC TD F)). {
        apply isaset_total2.
        - repeat (apply impred_isaset ; intro).
          apply univalent_category_has_homsets.
        - intro pt.
          apply isasetaprop.
          repeat (apply impred_isaprop ; intro).
          apply univalent_category_has_homsets.
      }
      apply pf.
    - apply isaproptotal2.
      + intro.
        apply isaprop_is_disp_invertible_2cell.
      + intros.
        apply isaprop_bicatcatstensor_disp_2cell_struct.
  Defined.


  (** We now show that this displayed bicategory is globally univalent **)

  Definition tensor_iso {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ α : ∏ x y : C, z_iso (x ⊗_{TD} y) (x ⊗_{TC} y),
          ∏ {a1 a2 b1 b2 : C} (f : C⟦a1,a2⟧) (g : C⟦b1,b2⟧),
          (pr1 (α a1 b1))·(f ⊗^{TC} g) = (f ⊗^{TD} g)·(pr1 (α a2 b2)).

  Definition tensor_eq {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (α : ∏ x y : C, (x ⊗_{TD} y) = (x ⊗_{TC} y)),
    ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      (idtomor _ _ (α x1 y1)) · (f ⊗^{TC} g) = (f ⊗^{TD} g) · (idtomor _ _ (α x2 y2)).

  Definition tensor_eq' {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (α : ∏ x y : C, (x ⊗_{TD} y) = (x ⊗_{TC} y)),
    ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (! α x1 y1) (f ⊗^{TC} g)
      = (transportf _ (α x2 y2) (f ⊗^{TD} g)).

  Definition tensor_eq'' {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (α : ∏ x y : C, (x ⊗_{TD} y) = (x ⊗_{TC} y)),
    ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      f ⊗^{TC} g
      = transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (α x1 y1) (transportf _ (α x2 y2) (f ⊗^{TD} g)).

  Lemma tensor_eq_equiv_tensor_eq' {C : univalent_category} (TC TD : tensor C)
    : tensor_eq TC TD ≃ tensor_eq' TC TD.
  Proof.
    apply weq_subtypes_iff.
    - intro.
      repeat (apply impred_isaprop ; intro).
      apply homset_property.
    - intro.
      repeat (apply impred_isaprop ; intro).
      apply homset_property.
    - intro pob.
      use tpair.
      + intro phom.
        intros.
        set (q := phom _ _ _ _ f g).
        rewrite (! eq_idtoiso_idtomor _ _ _) in q.
        rewrite (! eq_idtoiso_idtomor _ _ _) in q.

        etrans. {
          apply (! idtoiso_precompose _ _ _ _ _ _).
        }
        etrans. {
          apply cancel_postcomposition.
          apply maponpaths.
          apply maponpaths.
          apply pathsinv0inv0.
        }
        etrans. { exact q. }
        apply idtoiso_postcompose.
      + intro phom.
        intros.
        set (q := phom _ _ _ _ f g).
        etrans. {
          apply cancel_postcomposition.
          apply (! eq_idtoiso_idtomor _ _ _).
        }
        rewrite (! idtoiso_precompose _ _ _ _ _ _) in q.
        rewrite (! idtoiso_postcompose _ _ _ _ _ _) in q.
        rewrite pathsinv0inv0 in q.
        etrans. { apply q. }
        apply cancel_precomposition.
        apply eq_idtoiso_idtomor.
  Defined.

  Lemma tensor_eq'_equiv_tensor_eq'' {C : univalent_category} (TC TD : tensor C)
    : tensor_eq' TC TD ≃ tensor_eq'' TC TD.
  Proof.
    apply weq_subtypes_iff.
    - intro.
      repeat (apply impred_isaprop ; intro).
      apply homset_property.
    - intro.
      repeat (apply impred_isaprop ; intro).
      apply homset_property.
    - intro pob.
      use tpair.
      + abstract (
            intro phom ;
            intros ;
            set (q := phom _ _ _ _ f g) ;
            apply (transportf_transpose_right (P := λ x : C, C ⟦ x, x2 ⊗_{ TC} y2 ⟧)) ;
            apply q).
      + abstract (
            intro phom ;
            intros ;
            set (q := phom _ _ _ _ f g) ;
            apply (transportf_transpose_left (P :=  (λ x : C, C ⟦ x, x2 ⊗_{ TC} y2 ⟧))) ;
            unfold transportb ;
            rewrite pathsinv0inv0 ;
            apply q).
  Defined.

  Lemma tensor_iso_equiv_tensor_eq {C : univalent_category} (TC TD : tensor C)
    : tensor_iso TC TD ≃ tensor_eq TC TD.
  Proof.
    Search ((∑ _ : _, _) ≃ (∑ _ : _, _)).
    use weqtotal2.
    - apply weqonsecfibers ; intro x ; apply weqonsecfibers ; intro y.
      use weq_iso.
      + apply isotoid.
        apply univalent_category_is_univalent.
      + apply idtoiso.
      + intro.
        apply idtoiso_isotoid.
      + intro.
        apply isotoid_idtoiso.
    - intro iso_tob.
      repeat (apply weqonsecfibers ; intro).
      use weq_iso.
      + intro p.
        etrans. {
          apply cancel_postcomposition.
          apply (! eq_idtoiso_idtomor _ _ _).
        }
        etrans. {
          apply cancel_postcomposition.
          apply maponpaths.
          apply idtoiso_isotoid.
        }
        etrans. {
          apply p.
        }

        apply cancel_precomposition.
        apply pathsinv0.
        etrans. { apply (! eq_idtoiso_idtomor _ _ _). }
        apply maponpaths.
        apply idtoiso_isotoid.
      + intro p.
        cbn in p.
        rewrite (! eq_idtoiso_idtomor _ _ _) in p.
        rewrite (! eq_idtoiso_idtomor _ _ _) in p.
        rewrite idtoiso_isotoid in p.
        rewrite idtoiso_isotoid in p.
        apply p.
      + intro ; apply homset_property.
      + intro ; apply homset_property.
  Defined.

  Lemma disp_eq_to_tensoriso {C : bicat_of_univ_cats} (TC TD : bicatcatstensor_disp_bicat C)
    : disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) TC TD -> tensor_iso TC TD.
  Proof.
    intro dae.
    induction dae as [[ptd ptnat] [data [ax equiv]]].
    induction data as [ptdinv [ptunit ptcounit]].
    cbn in *.

    repeat (use tpair).
    - intros x y.
      use make_z_iso.
      + exact (ptd x y).
      + exact (pr1 ptdinv x y).
      + use tpair.
        * set (t := ptcounit x y).
          cbn in t.
          unfold identityfunctor_preserves_tensor_data in t.
          rewrite id_right in t.
          rewrite tensor_id in t.
          rewrite id_right in t.
          unfold compositions_preserves_tensor_data in t.
          unfold functor_identity in t.
          exact t.
        * set (t := ! ptunit x y).
          cbn in t.
          unfold identityfunctor_preserves_tensor_data in t.
          rewrite id_left in t.
          rewrite tensor_id in t.
          rewrite id_left in t.
          unfold compositions_preserves_tensor_data in t.
          exact t.
    - intros x1 x2 y1 y2 f g.
      exact (ptnat x1 x2 y1 y2 f g).
  Defined.

  Lemma swap_nat_along_zisos {C : category} {x1 x2 y1 y2 : C}
      (p1 : z_iso x1 y1) (p2 : z_iso x2 y2) :
  ∏ (f: C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
    (pr1 p1) · g = f · (pr1 p2) -> (inv_from_z_iso p1) · f = g · (inv_from_z_iso p2) .
  Proof.
    intros f g p.
    apply z_iso_inv_on_right.
    rewrite assoc.
    apply z_iso_inv_on_left.
    apply p.
  Qed.

  Definition tensoriso_to_disp_eq {C : bicat_of_univ_cats} (TC TD : bicatcatstensor_disp_bicat C)
    : tensor_iso TC TD -> disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) TC TD.
  Proof.
    intro ti.
    use tpair.
    - use tpair.
      + intros x y.
        apply ti.
      + intros x1 x2 y1 y2 f g.
        exact ((pr2 ti) x1 x2 y1 y2 f g).

    (* disp_left_adjoint_equivalence *)
    - use tpair.
      + (* data *)
      repeat (use tpair).
      * intros x y.
        apply ti.
      *
        intros x1 x2 y1 y2 f g.
        induction ti as [n i].
        apply (swap_nat_along_zisos (n x1 y1) (n x2 y2) (f ⊗^{pr1 TD} g) (f ⊗^{pr1 TC} g)).
        exact (i x1 x2 y1 y2 f g).
      * intros x y.
        cbn.
        unfold identityfunctor_preserves_tensor_data.
        unfold compositions_preserves_tensor_data.
        rewrite id_left.
        rewrite tensor_id.
        rewrite id_left.
        apply (! z_iso_after_z_iso_inv ((pr1 ti x y))).
      * intros x y.
        cbn.
        unfold compositions_preserves_tensor_data.
        unfold identityfunctor_preserves_tensor_data.
        unfold compositions_preserves_tensor_data.
        rewrite id_right.
        rewrite tensor_id.
        rewrite id_left.
        cbn.
        apply (z_iso_inv_after_z_iso ((pr1 ti x y))).
      + (* axioms *)
        use tpair.
        * use tpair.
          -- abstract (repeat (apply funextsec ; intro) ;
             apply univalent_category_has_homsets).
          -- apply funextsec ; intro ; apply funextsec ; intro.
             apply univalent_category_has_homsets.
        * use tpair.
          -- use tpair.
             ++ intros x y.
                cbn.
                unfold compositions_preserves_tensor_data.
                unfold identityfunctor_preserves_tensor_data.
                cbn.
                rewrite id_right.
                rewrite id_right.
                rewrite tensor_id.
                apply (z_iso_after_z_iso_inv ((pr1 ti x y))).
             ++ use tpair.
                ** abstract (repeat (apply funextsec ; intro) ;
                   apply univalent_category_has_homsets).
                ** abstract (repeat (apply funextsec ; intro) ;
                   apply univalent_category_has_homsets).
          -- use tpair.
             ++ intros x y.
                cbn.
                unfold compositions_preserves_tensor_data.
                unfold identityfunctor_preserves_tensor_data.
                cbn.
                rewrite id_right.
                rewrite tensor_id.
                rewrite id_left.
                apply (! z_iso_inv_after_z_iso ((pr1 ti x y))).
             ++ use tpair.
                ** abstract (repeat (apply funextsec ; intro) ;
                   apply univalent_category_has_homsets).
                ** abstract (repeat (apply funextsec ; intro) ;
                   apply univalent_category_has_homsets).
  Defined.

  Lemma tensor_iso_disp_eq_equiv {C : bicat_of_univ_cats} (TC TD : bicatcatstensor_disp_bicat C)
    : disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) TC TD ≃ tensor_iso TC TD.
  Proof.
    use weq_iso.
    - intro dae.
      exact (disp_eq_to_tensoriso TC TD dae).
    - intro ti.
      apply (tensoriso_to_disp_eq TC TD ti).
    - intro dae.
      use subtypePath.
      + intro f.
        apply isaprop_disp_left_adjoint_equivalence.
        apply univalent_cat_is_univalent_2_1.
        apply bicatcatstensor_disp_bicat_is_locally_univalent.
      + apply idpath.
    - intro i.
      induction i.
      use subtypePath.
      + intro f.
        repeat (apply impred_isaprop ; intro).
        apply univalent_category_has_homsets.
      + repeat (apply funextsec ; intro).
        use subtypePath.
        * intro f.
          apply isaprop_is_z_isomorphism.
        * repeat (apply funextsec ; intro).
          apply idpath.
  Defined.

  Definition tensor_eqi'' {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (α : ∏ x y : C, (x ⊗_{TC} y) = (x ⊗_{TD} y)),
    ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      f ⊗^{TC} g
      = transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (! α x1 y1) (transportf _ (! α x2 y2) (f ⊗^{TD} g)).

  Lemma tensor_eq''_equiv_tensor_eqi'' {C : univalent_category} (TC TD : tensor C)
    : tensor_eq'' TC TD ≃ tensor_eqi'' TC TD.
  Proof.
    use weq_iso.
    - intro te.
      use tpair.
      + intros x y.
        exact (! pr1 te x y).
      + intros x1 x2 y1 y2 f g.
        rewrite pathsinv0inv0.
        rewrite pathsinv0inv0.
        apply (pr2 te).
    - intro tei.
      use tpair.
      + intros x y.
        exact (! pr1 tei x y).
      + intros x1 x2 y1 y2 f g.
        exact (pr2 tei _ _ _ _ f g).
    - intro te.
      use total2_paths_b.
      + repeat (apply funextsec ; intro).
        apply pathsinv0inv0.
      + repeat (apply funextsec ; intro).
        apply homset_property.
    - intro tei.
      use total2_paths_b.
      + repeat (apply funextsec ; intro).
        apply pathsinv0inv0.
      + repeat (apply funextsec ; intro).
        apply homset_property.
  Defined.

  (* The equivalences so far, hence, we are now reduced to showing tensor_eqi'' TC TD ≃ TC = TD *)
  Lemma disp_adj_equiv_tensor_eqi'' {C : bicat_of_univ_cats} (TC TD : bicatcatstensor_disp_bicat C)
    :  disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) TC TD ≃ tensor_eqi'' TC TD.
  Proof.

    set (i1 := tensor_iso_disp_eq_equiv TC TD).
    set (i2 := tensor_iso_equiv_tensor_eq TC TD).
    set (i3 := tensor_eq_equiv_tensor_eq' TC TD).
    set (i4 := tensor_eq'_equiv_tensor_eq'' TC TD).
    set (i5 := tensor_eq''_equiv_tensor_eqi'' TC TD).

    exact ((i5 ∘ i4 ∘ i3 ∘ i2 ∘ i1)%weq).
  Defined.

  (*** Until here, all good... ***)

  Lemma t_lemma {C : univalent_category} (TC TD : C -> C -> C)
        (TCh : ∏ x1 x2 y1 y2 : C, C ⟦ x1, x2 ⟧ → C ⟦ y1, y2 ⟧ → C ⟦ TC x1 y1, TC x2 y2 ⟧)
        (TDh : ∏ x1 x2 y1 y2 : C, C ⟦ x1, x2 ⟧ → C ⟦ y1, y2 ⟧ → C ⟦ TD x1 y1, TD x2 y2 ⟧)
        (p : TC = TD)
        (* (pf :  ∏ (x1 x2 y1 y2 : C) (f : C ⟦ x1, x2 ⟧) (g : C ⟦ y1, y2 ⟧)) *)
      : transportf
    (λ x : C → C → C,
     ∏ x1 x2 y1 y2 : C, C ⟦ x1, x2 ⟧ → C ⟦ y1, y2 ⟧ → C ⟦ x x1 y1, x x2 y2 ⟧)
    (funextsec (λ _ : C, C → C) TC TD
       (λ x : C,
        funextsec (λ _ : C, C) (TC x) (TD x) (* (λ x0 : C, pr1 te x x0) *)  (λ x0 : C, (toforallpaths _ _ _ ((toforallpaths _ _ _ p) x) x0))))
    TCh = TDh.
  Proof.
    induction p.
    cbn.
  Admitted.


  Lemma t_lemma' {C : univalent_category} (TC TD : C -> C -> C)
        (TCh : ∏ x1 x2 y1 y2 : C, C ⟦ x1, x2 ⟧ → C ⟦ y1, y2 ⟧ → C ⟦ TC x1 y1, TC x2 y2 ⟧)
        (TDh : ∏ x1 x2 y1 y2 : C, C ⟦ x1, x2 ⟧ → C ⟦ y1, y2 ⟧ → C ⟦ TD x1 y1, TD x2 y2 ⟧)
        (p : ∏ x y : C, TC x y = TD x y)
        (* (pf :  ∏ (x1 x2 y1 y2 : C) (f : C ⟦ x1, x2 ⟧) (g : C ⟦ y1, y2 ⟧)) *)
  :   transportf
    (λ x : C → C → C,
     ∏ x1 x2 y1 y2 : C, C ⟦ x1, x2 ⟧ → C ⟦ y1, y2 ⟧ → C ⟦ x x1 y1, x x2 y2 ⟧)
    (funextsec (λ _ : C, C → C) TC TD
       (λ x : C,
        funextsec (λ _ : C, C) (TC x) (TD x) (λ x0 : C, p x x0)))
    TCh = TDh.
  Proof.
    assert (pe : TC = TD). {
      repeat (apply funextsec ; intro).
      apply p.
    }

    use pathscomp0.
    3: { exact (t_lemma TC TD TCh TDh pe). }

    Search (transportf ?P _ ?x = transportf ?P _ ?x).
    apply transportf_paths.


  Definition tensor_eqi''_to_eq {C : univalent_category} (TC TD : tensor C) : tensor_eqi'' TC TD -> TC = TD.
  Proof.
    intro te.
    use total2_paths_f.
    - use total2_paths_f.
      + apply funextsec ; intro ; apply funextsec ; intro ; apply (pr1 te).
      + cbn in *.
        unfold tensor_eqi'' in te.

        use pathscomp0.
        3: {

          apply (t_lemma (pr11 TC) (pr11 TD) (pr21 TC) (pr21 TD)).
        }

        assert (pf :  (funextsec (λ _ : C, C → C) (pr11 TC) (pr11 TD)
       (λ x : C,
           funextsec (λ _ : C, C) ((pr11 TC) x) ((pr11 TD) x) (λ x0 : C, pr1 te x x0)))
                      =
                          (funextsec (λ _ : C, C → C) (pr11 TC) (pr11 TD)
       (λ x : C,
        funextsec (λ _ : C, C) ((pr11 TC) x) ((pr11 TD) x)
          (λ x0 : C,
           toforallpaths (λ _ : C, C) ((pr11 TC) x) ((pr11 TD) x)
                         (toforallpaths (λ _ : C, C → C) (pr11 TC) (pr11 TD) ?p x) x0)))
               ).


        (* exact (pr2 te). *)

    - use total2_paths_b.
      + abstract (repeat (apply impred_isaprop ; intro) ;
        apply homset_property).
      + abstract (repeat (apply impred_isaprop ; intro) ;
        apply homset_property).
  Defined.

















  Definition tensor_eqi''' {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (p : pr11 TC = pr11 TD), ∏ (x1 x2 y1 y2 : C) (f : C⟦x1,x2⟧)  (g : C⟦y1,y2⟧),
     transportf (λ x : C → C → C, C ⟦ x x1 y1, x x2 y2 ⟧)
    (funextsec (λ _ : C, C → C) (pr11 TC) (pr11 TD)
       (λ x : C,
        funextsec (λ _ : C, C) ((pr11 TC) x) ((pr11 TD) x) (λ x0 : C, (toforallpaths _ _ _ ((toforallpaths _ _ _ p) x) x0))))
    (f ⊗^{TC} g) = f ⊗^{TD} g.

  (* Definition tensor_eqi''_to_tensor_eqi''' {C : bicat_of_univ_cats} (TC TD : bicatcatstensor_disp_bicat C)
    : tensor_eqi'' TC TD -> tensor_eqi''' TC TD.
  Proof.
    intro te.
    use tpair.
    - repeat (apply funextsec ; intro).
      apply te.
    -  intros x1 x2 y1 y2 f g.
       unfold tensor_eqi'' in te.
       cbn in *.
       apply (transportf_transpose_left (P :=  (λ x : C → C → C, C ⟦ x x1 y1, x x2 y2 ⟧))).
       etrans. { apply (pr2 te). }
       unfold transportb.
       admit.
  Admitted. *)


  Lemma test' {C : univalent_category} (TC : C -> C -> C)
        (TCh : ∏ x1 x2 y1 y2 : C, C ⟦ x1, x2 ⟧ → C ⟦ y1, y2 ⟧ → C ⟦ TC x1 y1, TC x2 y2 ⟧)
    : ∏ x1 x2 y1 y2 : C, ∏ f : C⟦ x1, x2 ⟧, ∏ g : C⟦ y1, y2 ⟧,
    TCh _ _ _ _ f g =
  transportf (λ T : C → C → C, C ⟦ T x1 y1, T x2 y2 ⟧)
    (funextsec (λ _ : C, C → C) TC TC
       (λ x5 : C, funextsec (λ _ : C, C) _ _ (λ x6 : C, idpath (TC _ _))))
    (TCh _ _ _ _ f g).
  Proof.
    intros.

    assert (pf : funextsec (λ _ : C, C → C) TC TC
                           (λ x5 : C, funextsec
                                        (λ _ : C, C)
                                        (λ x6 : C, TC x5 x6)
                                        (λ x6 : C, TC x5 x6)
                                        (λ x6 : C, idpath (TC x5 x6))) = (idpath TC)). {
      admit.
    }
    rewrite pf.
    apply idpath_transportf.

  Admitted.

  Lemma test {C : univalent_category} (TC TD : C -> C -> C)
        (TCh : ∏ x1 x2 y1 y2 : C, C ⟦ x1, x2 ⟧ → C ⟦ y1, y2 ⟧ → C ⟦ TC x1 y1, TC x2 y2 ⟧)
        (TDh : ∏ x1 x2 y1 y2 : C, C ⟦ x1, x2 ⟧ → C ⟦ y1, y2 ⟧ → C ⟦ TD x1 y1, TD x2 y2 ⟧)
        (p : TC = TD)
        (pf :  ∏ (x1 x2 y1 y2 : C) (f : C ⟦ x1, x2 ⟧) (g : C ⟦ y1, y2 ⟧),
       transportf (λ x : C → C → C, C ⟦ x x1 y1, x x2 y2 ⟧)
         (funextsec (λ _ : C, C → C) TC TD
            (λ x : C,
             funextsec (λ _ : C, C) (TC x) (TD x)
               (λ x0 : C,
                toforallpaths (λ _ : C, C) (TC x) (TD x)
                  (toforallpaths (λ _ : C, C → C) TC TD p x) x0)))
         (TCh _ _ _ _ f g) = TDh _ _ _ _ f g)
    :
      transportf
    (λ x : C → C → C,
     ∏ x1 x2 y1 y2 : C, C ⟦ x1, x2 ⟧ → C ⟦ y1, y2 ⟧ → C ⟦ x x1 y1, x x2 y2 ⟧)
    p TCh = TDh.
  Proof.
    induction p.
    use pathscomp0.
    2: apply (idpath_transportf ( (λ x : C → C → C,
                                      ∏ x1 x2 y1 y2 : C, C ⟦ x1, x2 ⟧ → C ⟦ y1, y2 ⟧ → C ⟦ x x1 y1, x x2 y2 ⟧))).

    repeat (apply funextsec ; intro).
    set (q := pf _ _ _ _ x3 x4).
    cbn in q.
    use pathscomp0.
    3: exact q.
    apply test'.
  Defined.

  Definition tensor_eqi'''_to_eq {C : bicat_of_univ_cats} (TC TD : bicatcatstensor_disp_bicat C) : tensor_eqi''' TC TD -> TC = TD.
  Proof.
    intro te.
    use total2_paths_f.
    - use total2_paths_f.
      + exact (pr1 te).
      + cbn in *.
        unfold tensor_eqi''' in te.
        apply test.
        exact (pr2 te).

    - use total2_paths_b.
      + abstract (repeat (apply impred_isaprop ; intro) ;
        apply homset_property).
      + abstract (repeat (apply impred_isaprop ; intro) ;
        apply homset_property).
  Defined.

  Definition tensor_eqi''_to_eq {C : bicat_of_univ_cats} (TC TD : bicatcatstensor_disp_bicat C)
    : tensor_eqi'' TC TD -> tensor_eqi''' TC TD.
  Proof.
    intro tei.
    use tpair.
    - repeat (apply funextsec ; intro).
      apply tei.
    - cbn in *.
      intros.
      etrans. {
        apply maponpaths.
        exact (pr2 tei _ _ _ _ f g).
      }

       (*

        assert (H : ∏ x : C, (pr11 TC x) = (pr11 TD x)). {
          intro x.
          apply funextsec ; intro y.
          apply tei.
        }


        Check (transportf_funextfun
                 (X := C) (Y := C -> C)).
                 _ (pr11 TC) (pr11 TD)
                 H _

              ).

        set (P := λ j : C -> C,  )
        *)



    (* apply transport_at_domain_and_codomain_simultaniously. *)
      admit.
  Admitted.






  (* This is precisely equality of tensors which I have to show *)
  Definition tensor_e {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (p : pr11 TC = pr11 TD),
    transportf
    (λ x : C → C → C, ∏ x1 x2 y1 y2 : C, C ⟦ x1, x2 ⟧ → C ⟦ y1, y2 ⟧ → C ⟦ x x1 y1, x x2 y2 ⟧)
    p
    (pr21 TC) = pr21 TD.

  Definition tensor_e_to_pathpair {C : univalent_category} (TC TD : tensor C)
    : tensor_e TC TD ≃ TC = TD.
  Proof.
    use weq_iso.
    - intro te.
      use total2_paths_f.
      + use total2_paths_f.
        * exact (pr1 te).
        * exact (pr2 te).
      + use total2_paths_f.
        repeat (repeat (apply funextsec ; intro) ; apply homset_property).
        repeat (repeat (apply funextsec ; intro) ; apply homset_property).
    - intro pp.
      induction pp.
      use tpair.
      + apply idpath.
      + apply idpath.
    - intro te.
      use total2_paths_f.
      + Check pr1 te.

        exact (toforallpaths _ _ _ ((toforallpaths _ _ _ (pr1 te)) x) y).




      + apply maponpaths.
        Check (toforallpaths _ _ _ _ pp).
      + repeat (apply funextsec ; intro).

        Check (toforallpaths _ _ _ _ (pr1 pp)).

        set (q := (toforallpaths _ _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ ((toforallpaths _ _ _ (pr2 pp)) x) x0) x1) x2) x3) x4)).

        Check (pr2 pp).






  (* Definition tensor_e' {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (p : pr11 TC = pr11 TD), *)


  (* Lemma tensor_e_eq_eq {C : univalent_category} (TC TD : tensor C)
    : tensor_e TC TD ≃ TC = TD.
  Proof.
    use weq_iso.
      - intro te.
      use total2_paths_f.
      + use total2_paths_f.
        * apply (pr1 te).
        * apply (pr2 te).
      + use total2_paths_f.
        repeat (repeat (apply funextsec ; intro) ; apply homset_property).
        repeat (repeat (apply funextsec ; intro) ; apply homset_property).
    - intro e.
      induction e.
      use tpair.
      + apply idpath.
      + apply idpath.
    - intro te.
      use total2_paths_f.
      + cbn.
        unfold tensor_e in te.
        cbn.
        apply funextsec.


        * repeat (apply funextsec ; intro).
          apply homset_property.
   *)

    Definition tensor_e_to_tensor_eqi'' {C : univalent_category} (TC TD : tensor C)
    : tensor_e TC TD ≃ tensor_eqi'' TC TD.
    Proof.
      use weq_iso.
      - intro te.
        use tpair.
        + intros x y.
          exact (toforallpaths _ _ _ ((toforallpaths _ _ _ (pr1 te)) x) y).
        + intros x1 x2 y1 y2 f g.
          set (q := (toforallpaths _ _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ (toforallpaths _ _ _ ((toforallpaths _ _ _ (pr2 te)) x1) x2) y1) y2) f) g)).
          repeat (rewrite transportf_sec_constant  in q).
          use pathscomp0.
          3: {
            apply maponpaths.
            apply maponpaths.
            apply q.
          }
          apply pathsinv0.
          Search homot.

          Check fiber_paths.

          About total2_paths_equiv.

          Check PathPair TC TD.

            apply transportf_set.

          rewrite transport_functions_inv.


          About transport_functions.







  Lemma id_tensor_eqi'' {C : bicat_of_univ_cats} (T : bicatcatstensor_disp_bicat C)
    : tensor_eqi'' T T.
  Proof.
    use tpair.
    - intros x y.
      apply idpath.
    - intros ? ? ? ? f g.
      use pathscomp0.
      2: apply (! idpath_transportf _ _).
      apply idpath_transportf.
  Defined.

  Definition tensor_eqi''' {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (α : ∏ x y : C, (x ⊗_{TC} y) = (x ⊗_{TD} y)),
    ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      f ⊗^{TD} g
      = transportf (λ x : C, C⟦x , x2 ⊗_{TD} y2⟧) (α x1 y1) (transportf _ (α x2 y2) (f ⊗^{TC} g)).

  Lemma transport_at_domain_and_codomain_simultaniously {C : category} (F G : C -> C -> C)
        (p : ∏ x y : C, F x y = G x y)
        {x1 x2 y1 y2 : C}
        (f : C⟦G x1 y1, G x2 y2⟧) :
    transportf (λ a : C, C ⟦ a, F x2 y2 ⟧) (! p x1 y1) (transportf (λ b : C, C ⟦ G x1 y1, b ⟧) (! p x2 y2) f)
    = transportf (λ T : C → C → C, C ⟦ T x1 y1, T x2 y2 ⟧)
    (! funextsec (λ _ : C, C → C) F G
         (λ x : C, funextsec (λ _ : C, C) (F x) (G x) (λ y : C, p x y)))
    f.
  Proof.
    Check transport_f_f.

  Admitted.

  *)

  Definition tensor_eqi''_to_eq {C : bicat_of_univ_cats} (TC TD : bicatcatstensor_disp_bicat C)
    : tensor_eqi'' TC TD -> TC = TD.
  Proof.
    intro tei.
    use total2_paths_f.
    - use total2_paths_f.
      + admit. (*repeat (apply funextsec ; intro).
        apply (pr1 tei).*)
      + cbn.


        apply pathsinv0.
        unfold transportb.

        repeat (apply funextsec ; intro).
        unfold tensor_eqi'' in tei.
        repeat (rewrite transportf_sec_constant).



        etrans. {
          Check (pr2 tei).
        }
        unfold transportb.

        apply transport_at_domain_and_codomain_simultaniously.
    - use total2_paths_b.
      + abstract (repeat (apply impred_isaprop ; intro) ;
        apply homset_property).
      + abstract (repeat (apply impred_isaprop ; intro) ;
        apply homset_property).
  Defined.

  (* Definition tensor_eq''_to_eq {C : bicat_of_univ_cats} (TC TD : bicatcatstensor_disp_bicat C)
    : tensor_eq'' TC TD -> TC = TD.
  Proof.
    intro teq.
    use total2_paths_b.
    - use total2_paths_b.
      + repeat (apply funextsec ; intro).
        apply (! pr1 teq _ _).
      + repeat (apply funextsec ; intro).
        unfold tensor_eq'' in teq.
        etrans. {
          apply (pr2 teq).
        }
        unfold transportb.
        repeat (rewrite transportf_sec_constant).
        (* set (q := λ x y, ! pr1 teq x y). *)

        apply transport_at_domain_and_codomain_simultaniously.
    - use total2_paths_b.
      + abstract (repeat (apply impred_isaprop ; intro) ;
        apply homset_property).
      + abstract (repeat (apply impred_isaprop ; intro) ;
        apply homset_property).
  Defined. *)




  Definition tensor_eqi''_equiv_eq {C : bicat_of_univ_cats} (TC TD : bicatcatstensor_disp_bicat C)
    : tensor_eqi'' TC TD ≃ TC = TD.
  Proof.
    use weq_iso.
    - intro teq.
      exact (tensor_eqi''_to_eq _ _ teq).
    - intro eq.
      induction eq.
      exact (id_tensor_eqi'' TC).
    - intro teq.
      use total2_paths_b.
      + repeat (apply funextsec ; intro).

        unfold tensor_eqi''_to_eq.
        unfold id_tensor_eqi''.

        admit.
      + repeat (apply funextsec ; intro).
        admit.
    - intro eq.
      induction eq.
      admit.
  Admitted.


  (*** The end ***)
  Lemma bicatcattensor_disp_prebicat_is_globally_univalent : disp_univalent_2_0 bicatcatstensor_disp_bicat.
  Proof.
   intros C D equalcats TC TD.
   induction equalcats.
   use weqhomot.
   - set (i1 := tensor_iso_disp_eq_equiv TC TD).
     set (i2 := tensor_iso_equiv_tensor_eq TC TD).
     set (i3 := tensor_eq_equiv_tensor_eq' TC TD).
     set (i4 := tensor_eq'_equiv_tensor_eq'' TC TD).
     set (i5 := tensor_eq''_equiv_tensor_eqi'' TC TD).
     set (i6 := tensor_eqi''_equiv_eq TC TD).
     exact (invweq (i6 ∘ i5 ∘ i4 ∘ i3 ∘ i2 ∘ i1)%weq).
   - intro p.
     induction p.
     use subtypePath.
     + intro.
       apply (@isaprop_disp_left_adjoint_equivalence bicat_of_univ_cats  bicatcatstensor_disp_bicat).
       * exact univalent_cat_is_univalent_2_1.
       * exact bicatcatstensor_disp_bicat_is_locally_univalent.
     + use total2_paths_b.
       * repeat (apply funextsec ; intro).


         admit.
       * repeat (apply funextsec ; intro).
         apply homset_property.
 Admitted.

  Lemma bicatcatstensor_disp_prebicat_is_univalent_2 : disp_univalent_2 bicatcatstensor_disp_bicat.
  Proof.
    apply make_disp_univalent_2.
    - apply bicatcattensor_disp_prebicat_is_globally_univalent.
    - apply bicatcatstensor_disp_bicat_is_locally_univalent.
  Defined.

End TensorLayer.
