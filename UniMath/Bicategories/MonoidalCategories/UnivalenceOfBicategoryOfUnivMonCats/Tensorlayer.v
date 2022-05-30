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
        cbn.
        exact ((pr2 ti) x1 x2 y1 y2 f g).

    (* disp_left_adjoint_equivalence *)
    - (* cbn in *.*)
      use tpair.
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

  Lemma tensoriso_disp_eq_equiv {C : bicat_of_univ_cats} (TC TD : bicatcatstensor_disp_bicat C)
    : tensor_iso TC TD ≃ disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) TC TD.
  Proof.
    use make_weq.
    - intro ti.
      apply (tensoriso_to_disp_eq TC TD ti).
    - use isweq_iso.
      + intro dae.
        exact (disp_eq_to_tensoriso TC TD dae).
      + intro i.
        induction i.
        use subtypePath.
        * intro f.
          repeat (apply impred_isaprop ; intro).
          apply univalent_category_has_homsets.
        * repeat (apply funextsec ; intro).
          use subtypePath.
          -- intro f.
             apply isaprop_is_z_isomorphism.
          -- repeat (apply funextsec ; intro).
             apply idpath.
      + intro dae.
        use subtypePath.
        * intro f.
          apply isaprop_disp_left_adjoint_equivalence.
          apply univalent_cat_is_univalent_2_1.
          apply bicatcatstensor_disp_bicat_is_locally_univalent.
        * apply idpath.
  Defined.

  (* Check total2_paths_equiv. *)


  Definition tensor_eq' {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (α : ∏ x y : C, (x ⊗_{TD} y) = (x ⊗_{TC} y)),
    ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
       (transportf _ (α x2 y2) (f ⊗^{TD} g)) = transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (! α x1 y1) (f ⊗^{TC} g).

  Lemma t_lemma_fb {C : category} {x y : C} (pxy : x = y)
    :   transportf (precategory_morphisms x) pxy (identity x)
  · transportb (precategory_morphisms y) pxy (identity y) =
          identity x.
  Proof.
    induction pxy.
    etrans. {
      apply cancel_postcomposition.
      apply idpath_transportf.
    }
    etrans. { apply id_left. }
    apply idpath_transportf.
  Qed.

  Lemma t_lemma_bf {C : category} {x y : C} (pxy : x = y)
    :   transportb (precategory_morphisms y) pxy (identity y)
  · transportf (precategory_morphisms x) pxy (identity x) =
          identity y.
  Proof.
    induction pxy.
    etrans. {
      apply cancel_postcomposition.
      apply idpath_transportf.
    }
    etrans. { apply id_left. }
    apply idpath_transportf.
  Qed.

  Definition tensor_eq'_to_tensor_iso {C : univalent_category} (TC TD : tensor C)
    : tensor_eq' TC TD -> tensor_iso TC TD.
  Proof.
    intro teq.
    induction teq as [teo teh].
    use tpair.
    - intros x y.
      set (pxy := teo x y).
      (*
         induction pxy.
         exact (identity_z_iso (x ⊗_{TD} y)).
       *)

      use tpair.
      + exact (transportf _ pxy (identity _)).
      + use tpair.
        * exact (transportb _ pxy (identity _)).
        * use tpair.
          -- apply t_lemma_fb.
          -- apply t_lemma_bf.
    - intros x1 x2 y1 y2 f g.
      etrans. { apply TransportMorphisms.transport_compose. }
      etrans. { apply id_left. }
      apply pathsinv0.
      etrans. {
        apply ( ! TransportMorphisms.transport_target_postcompose _ _ _).
      }
      etrans. {
        apply maponpaths.
        apply id_right.
      }
      apply teh.
  Defined.

  Lemma transport_univ_id_to_iso {C : univalent_category} {x y : C} (p : x = y) :
    transportf (λ z : C, C⟦z,y⟧) (! pr11 (pr2 C x y (idtoiso p))) (identity y) = pr1 (idtoiso p).
  Proof.
    etrans. {
      apply (! idtoiso_precompose C _ _ _ (! pr11 (pr2 C x y (idtoiso p))) (identity y)).
    }
    etrans. {
      apply id_right.
    }

    induction p.
    cbn.
    etrans. {
      apply maponpaths.
      apply maponpaths.
      apply pathsinv0inv0.
    }
    etrans. {
      apply maponpaths.
      apply (pr21 ((pr2 C) x x (identity_iso x))).
    }
    apply idpath.
  Defined.

  Lemma transport_univ_id_to_iso' {C : univalent_category} {x y : C} (p : x = y) :
    transportf (λ z : C, C⟦x,z⟧) (pr11 (pr2 C x y (idtoiso p))) (identity x) = pr1 (idtoiso p).
  Proof.
    etrans. {
      apply (! idtoiso_postcompose C _ _ _ (pr11 (pr2 C x y (idtoiso p))) (identity x)).
    }
    etrans. {
      apply id_left.
    }

    induction p.
    cbn.

    etrans. {
      apply maponpaths.
      apply (pr21 ((pr2 C) x x (identity_iso x))).
    }
    apply idpath.
  Defined.

  Lemma transport_univ_id_to_iso'' {C : univalent_category} {x y : C} (p : x = y) :
    transportb (λ z : C, C⟦x,z⟧) (! pr11 (pr2 C x y (idtoiso p))) (identity x) = pr1 (idtoiso p).
  Proof.
    unfold transportb.
    etrans. {
      rewrite pathsinv0inv0.
      apply (! idtoiso_postcompose C _ _ _ (pr11 (pr2 C x y (idtoiso p))) (identity x)).
    }
    etrans. {
      apply id_left.
    }

    induction p.
    cbn.

    etrans. {
      apply maponpaths.
      apply (pr21 ((pr2 C) x x (identity_iso x))).
    }
    apply idpath.
  Defined.

  Lemma transport_univ_iso_to_id {C : univalent_category} {x y : C} (p : iso x y) :
    transportf (λ z : C, C⟦z,y⟧) (! pr11 (pr2 C x y p)) (identity y) = pr1 p.
  Proof.
    set (pxy := pr11 (pr2 C x y p)).
    set (i := idtoiso pxy).

    assert (pf : i = p). {
      exact (pr21 (pr2 C x y p)).
    }
    induction pf.
    apply transport_univ_id_to_iso.
  Defined.

  Lemma transport_univ_iso_to_id' {C : univalent_category} {x y : C} (p : iso x y) :
    transportf (λ z : C, C⟦x,z⟧) (pr11 (pr2 C x y p)) (identity x) = pr1 p.
  Proof.
    set (pxy := pr11 (pr2 C x y p)).
    set (i := idtoiso pxy).

    assert (pf : i = p). {
      exact (pr21 (pr2 C x y p)).
    }
    induction pf.
    apply transport_univ_id_to_iso'.
  Defined.

  Search (iso).

  Lemma transport_univ_iso_to_id'' {C : univalent_category} {x y : C} (p : iso y x) :
    transportb (λ z : C, C⟦x,z⟧) (pr11 (pr2 C y x p)) (identity x) = inv_from_iso p.
  Proof.
    (* set (pxy := ! pr11 (pr2 C y x p)).
    set (i := idtoiso pxy).

    assert (pf : pr1 i = inv_from_iso p). {
      apply (pr21 (pr2 C y x p)).
    }
    induction pf.
    apply transport_univ_id_to_iso''.
  Defined.*) Admitted.

  Lemma transport_univ_ziso_to_id {C : univalent_category} {x y : C} (p : z_iso x y) :
    transportf (λ z : C, C⟦z,y⟧) (! pr11 (pr2 C x y (z_iso_to_iso p))) (identity y) = pr1 p.
  Proof.
    apply transport_univ_iso_to_id.
  Defined.

  Lemma transport_univ_ziso_to_id' {C : univalent_category} {x y : C} (p : z_iso x y) :
    transportf (λ z : C, C⟦x,z⟧) (pr11 (pr2 C x y (z_iso_to_iso p))) (identity x) = pr1 p.
  Proof.
    apply transport_univ_iso_to_id'.
  Defined.

  Lemma transport_univ_ziso_to_id'' {C : univalent_category} {x y : C} (p : z_iso y x) :
    transportb (λ z : C, C⟦x,z⟧) (pr11 (pr2 C y x (z_iso_to_iso p))) (identity x)
               = inv_from_z_iso p. (* = pr12 p. *)
  Proof.
    etrans. {
      apply transport_univ_iso_to_id''.
    }
    apply id_right.
  Defined.

  Lemma transport_univ_ziso_to_id''' {C : univalent_category} {x y : C} (p : z_iso y x) :
    transportb (λ z : C, C⟦x,z⟧) (pr11 (pr2 C y x (z_iso_to_iso p))) (identity x)
               = pr12 p.
  Proof.
    apply transport_univ_ziso_to_id''.
  Defined.

  Definition tensor_iso_to_tensor_eq' {C : univalent_category} (TC TD : tensor C)
    : tensor_iso TC TD -> tensor_eq' TC TD.
  Proof.
    intro ti.
    use tpair.
    - intros x y.
      apply C.
      apply z_iso_to_iso.
      apply ti.
    - intros x1 x2 y1 y2 f g.
      cbn.
      set (n := pr2 ti x1 x2 y1 y2 f g).
      etrans. {
        apply maponpaths.
        apply (! id_right _).
      }

      etrans. {
        apply TransportMorphisms.transport_target_postcompose.
      }

      apply pathsinv0.
      etrans. {
        apply maponpaths.
        apply (! id_left _).
      }

      etrans. {
        apply TransportMorphisms.transport_source_precompose.
      }

      etrans. {
        apply cancel_postcomposition.
        apply transport_univ_ziso_to_id.
      }

      apply pathsinv0.
      etrans. {
        apply cancel_precomposition.
        apply transport_univ_ziso_to_id'.
      }
      exact (! n).
  Defined.

  Definition tensor_iso_equiv_tensor_eq' {C : univalent_category} (TC TD : tensor C)
    : tensor_iso TC TD ≃ tensor_eq' TC TD.
  Proof.
    use make_weq.
    - intro ti.
      exact (tensor_iso_to_tensor_eq' TC TD ti).
    - use isweq_iso.
      + intro te.
        exact (tensor_eq'_to_tensor_iso TC TD te).
      + intro ti.
        use subtypePath.
        * intro.
          repeat (apply impred_isaprop ; intro).
          apply univalent_category_has_homsets.
        * cbn.
          repeat (apply funextsec ; intro).
          cbn.
          use total2_paths_b.
          -- apply transport_univ_ziso_to_id'.
          -- use total2_paths_b.
             ++ etrans. {
                  apply transport_univ_ziso_to_id'''.
                }
                apply pathsinv0.
                etrans. {
                  apply ((pr1_transportf  (! transport_univ_ziso_to_id' (pr1 ti _ _))) ( (pr2 (pr1 ti _ _)))).
                }
                admit.
             ++ use total2_paths_b.
                apply univalent_category_has_homsets.
                apply univalent_category_has_homsets.

      + intro te.
        use subtypePath.
        * intro.
          repeat (apply impred_isaprop ; intro).
          apply univalent_category_has_homsets.
        * cbn.
          repeat (apply funextsec ; intro).
          admit.
  Admitted.

  Definition tensor_eq {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ te : pr11 TC = pr11 TD,
        ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
        transportf (λ x : C → C → C, C ⟦ x x1 y1, x x2 y2 ⟧) te (f ⊗^{TC} g) = f ⊗^{TD} g.

  (* Definition tensor_eq'' {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (α : ∏ x y : C, (x ⊗_{TD} y) = (x ⊗_{TC} y)),
    ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      f ⊗^{TD} g = transportb _ (α x2 y2) (transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (! α x1 y1) (f ⊗^{TC} g)).


  Lemma tensor_eq'_equiv_tensor_eq'' {C : univalent_category} (TC TD : tensor C)
    : tensor_eq' TC TD ≃ tensor_eq'' TC TD.
  Proof.
    unfold tensor_eq' ; unfold tensor_eq''.

    Search ((∑ _ : _, _) ≃ (∑ _ : _, _)).
    apply weqfibtototal.
    intros a.
    Search ((∏ _ : ?x, _) ≃ ∏ _ : ?x, _).
    repeat (apply weqonsecfibers ; intro).
    Search (_ = _ ≃ _ = _).
    use make_weq.
    - intro e.

      apply transportf_transpose_right.
      use pathscomp0.
      3: exact e.
      apply transportf_transpose_right.
      etrans. { apply transport_b_b. }
      rewrite pathsinv0r.
      apply idpath_transportf.
    - use isweq_iso.
      + intro e.
        apply transportf_transpose_left.
        apply e.
      + intro ; apply univalent_category_has_homsets.
      + intro ; apply univalent_category_has_homsets.
  Defined. *)

  Lemma transport_at_domain_and_codomain_simultaniously {C : category} (F G : C -> C -> C)
        (p : ∏ x y : C, G x y = F x y)
        {x1 x2 y1 y2 : C}
        (f : C⟦F x1 y1, F x2 y2⟧) :
     transportf (λ t : C → C → C, C ⟦ t x1 y1, t x2 y2 ⟧)
     (funextsec (λ _ : C, C → C) F G
     (λ x : C, funextsec (λ _ : C, C) (F x) (G x) (λ y : C, ! p x y))) f =
       transportb (precategory_morphisms (G x1 y1)) (p x2 y2)
             (transportf (λ x : C, C ⟦ x, F x2 y2 ⟧) (! p x1 y1) f).
  Proof.
    set (pxy1 := p x1 y1).
    set (pxy2 := p x2 y2).
  Admitted.

  Lemma tensor_eq'_to_tensor_eq {C : univalent_category} (TC TD : tensor C)
    : tensor_eq' TC TD -> tensor_eq TC TD.
  Proof.
    intro te.
    induction te as [teo teh].
    use tpair.
    - apply funextsec ; intro x ; apply funextsec ; intro y.
      set (txy := teo x y).
      exact (! txy).
    - repeat (intro).
      cbn.
      set (fig := (teh x1 x2 y1 y2 f g)).

      assert (fig1 : (f ⊗^{ TD} g) =
                       transportb (precategory_morphisms (x1 ⊗_{ TD} y1)) (teo x2 y2) (transportf (λ x : C, C ⟦ x, x2 ⊗_{ TC} y2 ⟧) (! teo x1 y1) (f ⊗^{ TC} g))). {
        apply transportf_transpose_right.
        unfold transportb.
        use pathscomp0.
        3: exact fig.
        apply transportf_transpose_right.
        etrans. { apply transport_b_b. }
        rewrite pathsinv0r.
        apply idpath_transportf.
      }
      use pathscomp0.
      3: exact (! fig1).
      apply transport_at_domain_and_codomain_simultaniously.
  Defined.

  Lemma funextsec_conv {A B : UU} (f g : A -> B) :
    (f=g -> ∏ x : A, f x = g x).
  Proof.
    intro e.
    induction e.
    intro x.
    apply idpath.
  Defined.

  Lemma funextsec_proof_equal {C : category} (F G : C -> C -> C) (p : F = G) :
     funextsec (λ _ : C, C → C) F G
    (λ x : C, funextsec (λ _ : C, C) (F x) (G x)
                        (λ y : C, ! funextsec_conv (G x) (F x) (funextsec_conv G F (! p) x) y)
    ) = p.
  Proof.
  Admitted.

  Lemma tensoronobequality_to_ptwequality {C : univalent_category} (TC TD : tensor C)
    : pr11 TC = pr11 TD -> ∏ x y : C, x ⊗_{TC} y = x ⊗_{TD} y.
  Proof.
    intro e.
    intros x y.
    apply funextsec_conv.
    apply funextsec_conv.
    apply e.
  Defined.

  Lemma tensor_eq_to_tensor_eq' {C : univalent_category} (TC TD : tensor C)
    : tensor_eq TC TD -> tensor_eq' TC TD.
  Proof.
    intro te.
    induction te as [teo teh].
    use tpair.
    - intros x y.
      apply tensoronobequality_to_ptwequality.
      exact (! teo).
    - repeat (intro).
      apply transportf_transpose_left.
      etrans. { apply (! teh _ _ _ _ f g). }
      use pathscomp0.
      3: apply transport_at_domain_and_codomain_simultaniously.

      assert (pf : (funextsec (λ _ : C, C → C) (tensor_on_ob TC) (tensor_on_ob TD)
                   (λ x : C, funextsec (λ _ : C, C) (tensor_on_ob TC x) (tensor_on_ob TD x)
                   (λ y : C, ! tensoronobequality_to_ptwequality TD TC (! teo) x y))) = teo).
      {
        unfold tensoronobequality_to_ptwequality.
        apply funextsec_proof_equal.
      }
      set (pg := ! pf).
      induction pg.
      apply idpath.
  Defined.

  Lemma runoutofnames {C : category} (F G : C -> C -> C) (p : ∏ x y : C, G x y = F x y) (x x0 : C)
    :  funextsec_conv (G x) (F x)
    (funextsec_conv G F
       (! funextsec (λ _ : C, C → C) F G
            (λ x1 : C, funextsec (λ _ : C, C) (F x1) (G x1) (λ y : C, ! p x1 y)))
       x) x0 = p x x0.
  Proof.
  Admitted.

  Definition tensor_eq_equiv_tensor_eq' {C : univalent_category} (TC TD : tensor C)
    : tensor_eq TC TD ≃ tensor_eq' TC TD.
  Proof.
    use make_weq.
    - exact (tensor_eq_to_tensor_eq' TC TD).
    - use isweq_iso.
      + exact (tensor_eq'_to_tensor_eq TC TD).
      + intro te.
        use subtypePath.
        * intro.
          repeat (apply impred_isaprop ; intro).
          apply univalent_category_has_homsets.
        * apply funextsec_proof_equal.
      + intro te.
        use subtypePath.
        * intro.
          repeat (apply impred_isaprop ; intro).
          apply univalent_category_has_homsets.
        * repeat (apply funextsec ; intro).
          apply runoutofnames.
  Defined.

  Definition runoutofnames2 {C : category} (F : C -> C -> C)
             {x1 x2 y1 y2 : C} (f : C⟦F x1 y1, F x2 y2⟧)
    : transportf (λ x : C → C → C, C ⟦ x x1 y1, x x2 y2 ⟧)
    (funextsec (λ _ : C, C → C) F F
       (λ x : C,
        funextsec (λ _ : C, C) (F x) (F x) (λ x0 : C, idpath (F x x0))))
    f = f.
  Proof.
  Admitted.

  Definition runoutofnames3 {C : category} (F G : C -> C -> C) (p : F = G)
             {x1 x2 y1 y2 : C} (f : C⟦F x1 y1, F x2 y2⟧) :
    transportf (λ x5 : C → C → C, C ⟦ x5 x1 y1, x5 x2 y2 ⟧) (! p)
               (transportf (λ x5 : C → C → C, C ⟦ x5 x1 y1, x5 x2 y2 ⟧) p f)
    = f.
  Proof.
    induction p.
    rewrite transport_f_f.
    rewrite pathsinv0r.
    apply idpath.
  Defined.

  Definition equiv_tensor_eq_on_hom {C : univalent_category} (TC TD : tensor C)
    :  TC = TD ≃ tensor_eq TC TD.
  Proof.
    use make_weq.
    - intro teq.
      induction teq.
      use tpair.
      + repeat (apply funextsec ; intro).
        apply idpath.
      + intros x1 x2 y1 y2 f g.
        apply runoutofnames2.
        (*
        set (_1 := eqtohomot teh x1).
        set (_2 := eqtohomot _1 x2).
        set (_3 := eqtohomot _2 y1).
        set (_4 := eqtohomot _3 y2).
        set (_5 := eqtohomot _4 f).
        set (_6 := eqtohomot _5 g).
        apply pathsinv0.
        etrans. { exact (! _6). }
        etrans. {
          repeat (rewrite transportf_sec_constant).
          apply idpath.
        }
        apply idpath. *)
    - use isweq_iso.
      + intro teq.
        use total2_paths_b.
        * use total2_paths_b.
          -- exact (pr1 teq).
          --  repeat (apply funextsec ; intro).
              induction teq as [teo teh].
              set (pf := teh _ _ _ _ x3 x4).
              apply pathsinv0.
              unfold transportb.
              repeat (rewrite transportf_sec_constant).
              etrans. {
                apply maponpaths.
                apply (! pf).
              }
              cbn.
              apply (runoutofnames3 (pr11 TC) (pr11 TD) teo (x3 ⊗^{TC} x4)).


        * use total2_paths_b.
          -- repeat (apply funextsec ; intro).
             apply univalent_category_has_homsets.
          -- repeat (apply funextsec ; intro).
             apply univalent_category_has_homsets.
      + intro te.
        induction te.
        admit.
      + intro te.
        admit.
  Definition identity_is_tensor_eq {C : univalent_category} (T : tensor C) :
    tensor_eq T T.
  Proof.
    use tpair.
    - apply idpath.
    - intros x1 x2 y1 y2 f g.
      apply (idpath_transportf  (λ x : C → C → C, C ⟦ x x1 y1, x x2 y2 ⟧)).
  Defined.

  Definition tensor_eq_to_eq {C : bicat_of_univ_cats} (TC TD : bicatcatstensor_disp_bicat C)
    : tensor_eq TC TD -> TC = TD.
  Proof.
    intro te.

    use total2_paths_b.
    use total2_paths_b.
    - exact (pr1 te).
    - apply transportb_transpose_right.
      etrans. {
        rewrite transportf_sec_constant.
        apply idpath.
      }
      apply funextsec ; intro x1.

      etrans. {
        rewrite transportf_sec_constant.
        apply idpath.
      }
      apply funextsec ; intro x2.

      etrans. {
        rewrite transportf_sec_constant.
        apply idpath.
      }
      apply funextsec ; intro y1.

      etrans. {
        rewrite transportf_sec_constant.
        apply idpath.
      }
      apply funextsec ; intro y2.

      etrans. {
        rewrite transportf_sec_constant.
        apply idpath.
      }

      apply funextsec ; intro f.

      etrans. {
        rewrite transportf_sec_constant.
        apply idpath.
      }
      apply funextsec ; intro g.
      exact ((pr2 te) _ _ _ _ f g).
    - use subtypePath.
      + intro.
        repeat (apply isapropdirprod)
        ; repeat (apply impred ; intro)
        ; repeat (apply univalent_category_has_homsets).
      + apply maponpaths.
        repeat (apply isapropdirprod)
        ; repeat (apply impred ; intro)
        ; repeat (apply univalent_category_has_homsets).
  Defined.

  Definition eq_equiv_tensor_eq {C : univalent_category} (TC TD : tensor C)
    : TC = TD ≃ tensor_eq TC TD.
  Proof.
    Check @weq_subtypes' (tensor_eq TC TD) (TC = TD).
    weqfibtototal

     use make_weq.
     - intro eq.
       induction eq.
       exact (identity_is_tensor_eq TC).
    - use isweq_iso.
      + intro teq.
        exact (tensor_eq_to_eq TC TD teq).
      + intro eq.
        induction eq.
        admit.
      + intro teq.
        cbn.
        Check  paths_rect (tensor C) TC (λ (TD0 : tensor C) (_ : TC = TD0), tensor_eq TC TD0)
    (identity_is_tensor_eq TC) TD (tensor_eq_to_eq TC TD teq).

        assert (isaprop (tensor_eq TC TD)). {
          unfold tensor_eq.
          Search (isaprop (∑ _ : _, _)).
          apply isaproptotal2.
          * Search (isPredicate).

        use total2_paths_b.
        * induction teq as [teo teh].
          cbn.








          (* eqo is a proof that the function pr11 TC : C -> C -> C equals to pr11 TD. *)
          (* Hence, eqo should be "equivalent" to being a proof that for all x, y : C, we have that the tensors are equals. Hence, I would suspect to be able to use
          admit.

        * repeat (apply funextsec ; intro).
          apply univalent_category_has_homsets.

      + intro eq.
        induction eq.
*)
*)


 Lemma bicatcattensor_disp_prebicat_is_globally_univalent : disp_univalent_2_0 bicatcatstensor_disp_bicat.
  Proof.
    (* intros C D equalcats IC ID.
    induction equalcats.
    use weqhomot.
    - set (i1 := iso_dispadjequiv_equivalence C IC ID).
      set (i2 := iso_z_iso_equivalence IC ID).
      set (i3 := (_ ,, (pr2 C) IC ID)).
      exact (i1 ∘ i2 ∘ i3)%weq.
    - intro p.
      induction p ; cbn.
      use subtypePath.
      + intro ; simpl.
        apply (@isaprop_disp_left_adjoint_equivalence bicat_of_univ_cats  bicatcatsunit_disp_bicat).
        * exact univalent_cat_is_univalent_2_1.
        * exact bicatcatsunit_disp_prebicat_is_locally_univalent.
      + apply idpath.
  Defined. *)
  Admitted.


  Lemma bicatcatstensor_disp_prebicat_is_univalent_2 : disp_univalent_2 bicatcatstensor_disp_bicat.
  Proof.
    apply make_disp_univalent_2.
    - apply bicatcattensor_disp_prebicat_is_globally_univalent.
    - apply bicatcatstensor_disp_bicat_is_locally_univalent.
  Defined.

End TensorLayer.
