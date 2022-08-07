(*
This is the second of a sequence of files with the purpose of showing that the bicategory of univalent monoidal categories is again univalent.
In this file we construct one side of the first displayed layer above the bicategory of univalent categories, more precisely:
The total category corresponding to this displayed layer is the univalent bicategory defined as follows:
- The objects are categories together with a binary operation (which will be the tensor product for the monoidal structure).
- The morphisms are functors which preserve the tensor in a lax/weak sense (i.e. a non-necessarily isomorphic morphism).
- The 2-cells are natural transformations which (at tensor products) commute the tensor-preserving morphisms.
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
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.CurriedMonoidalCategories.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import TensorNotation.

Section TensorLayer.

  Import TensorNotation.

  Definition disp_tensor_disp_ob_mor : disp_cat_ob_mor bicat_of_univ_cats.
  Proof.
    exists (λ C, tensor (C : univalent_category)).
    exact (λ C D TC TD F, preserves_tensor TC TD F).
  Defined.

  Definition disp_tensor_disp_id_comp : disp_cat_id_comp bicat_of_univ_cats disp_tensor_disp_ob_mor.
  Proof.
    split.
    - intros C TC.
      apply identityfunctor_preserves_tensor.
    - intros C D E F G TC TD TE.
      apply compositions_preserves_tensor.
  Defined.

  Definition disp_tensor_disp_catdata : disp_cat_data bicat_of_univ_cats
    := (disp_tensor_disp_ob_mor,,disp_tensor_disp_id_comp).

  Definition bidisp_tensor_disp_2cell_struct : disp_2cell_struct disp_tensor_disp_ob_mor.
  Proof.
    intros C D F G α TC TD.
    exact (λ ptF ptG, preservestensor_commutes (pr1 ptF) (pr1 ptG) α).
  Defined.

  Lemma isaprop_bidisp_tensor_disp_2cell_struct
        {C D : bicat_of_univ_cats}
        {F G : bicat_of_univ_cats ⟦C,D⟧ }
        {α : prebicat_cells bicat_of_univ_cats F G}
        {TC : disp_tensor_disp_catdata C}
        {TD : disp_tensor_disp_catdata D}
        (ptF : TC -->[ F] TD)
        (ptG : TC -->[ G] TD)
    : isaprop (bidisp_tensor_disp_2cell_struct C D F G α TC TD ptF ptG).
  Proof.
    apply isaprop_preservestensor_commutes.
  Qed.

  Definition bidisp_tensor_disp_prebicat_1_id_comp_cells
    :  disp_prebicat_1_id_comp_cells bicat_of_univ_cats
    := (disp_tensor_disp_catdata,, bidisp_tensor_disp_2cell_struct).

  Definition bidisp_tensor_disp_prebicat_ops : disp_prebicat_ops bidisp_tensor_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat split.
    - intros C D F TC TD ptF.
      apply identitynattrans_preservestensor_commutes.
    - intros C D F TC TD ptF.
      intros x y.
      rewrite id_right.
      simpl.
      rewrite tensor_id.
      rewrite id_left.
      unfold identityfunctor_preserves_tensor_data.
      unfold compositions_preserves_tensor_data.
      rewrite functor_id.
      apply id_right.
    - intros C D F TC TD ptF.
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
    - intros C D F TC TD ptF.
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
    - intros C D F TC TD ptF.
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
    - intros C D E W F G H TC TD TE TW ptF ptG ptH.
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
    - intros C D E W F G H TC TD TE TW ptF ptG ptH.
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
    - intros C D F G H α β TC TD ptF ptG ptH ptcα ptcβ.
      intros x y.
      simpl.
      rewrite assoc.
      rewrite ptcα.
      rewrite assoc'.
      rewrite ptcβ.
      rewrite assoc.
      rewrite tensor_comp.
      apply idpath.
    - intros C D E F G H α TC TD TE ptF ptG ptH ptcα.
      intros x y.
      cbn.
      unfold compositions_preserves_tensor_data.
      rewrite assoc'.
      rewrite (pr2 α).
      rewrite assoc.
      rewrite ptcα.
      rewrite assoc.
      apply idpath.
    - intros C D E F G H α TC TD TE ptF ptG ptH ptcα.
      intros x y.
      cbn.
      unfold compositions_preserves_tensor_data.
      rewrite assoc'.
      etrans. {
        apply maponpaths.
        apply (pathsinv0 (functor_comp _ _ _)).
      }
      etrans. {
        do 2 apply maponpaths.
        apply ptcα.
      }
      rewrite assoc.
      rewrite functor_comp.
      rewrite assoc.
      apply cancel_postcomposition.
      etrans. { apply (pr2 ptH). }
      apply maponpaths.
      apply idpath.
  Defined.

  Definition bidisp_tensor_disp_prebicat_data : disp_prebicat_data bicat_of_univ_cats
    := (bidisp_tensor_disp_prebicat_1_id_comp_cells,, bidisp_tensor_disp_prebicat_ops).

  Definition bidisp_tensor_disp_prebicat_laws : disp_prebicat_laws bidisp_tensor_disp_prebicat_data.
  Proof.
    repeat split; intro; intros; apply isaprop_bidisp_tensor_disp_2cell_struct.
  Qed.

  Definition bidisp_tensor_disp_prebicat : disp_prebicat bicat_of_univ_cats
    := (bidisp_tensor_disp_prebicat_data,,bidisp_tensor_disp_prebicat_laws).

  Definition bidisp_tensor_disp_bicat : disp_bicat bicat_of_univ_cats.
  Proof.
    refine (bidisp_tensor_disp_prebicat,, _).
    intros C D F G α TC TD ptF ptG.
    apply isasetaprop.
    unfold disp_2cells.
    unfold bidisp_tensor_disp_prebicat.
    simpl.
    unfold bidisp_tensor_disp_2cell_struct.
    unfold preservestensor_commutes.
    repeat (apply impred_isaprop ; intro).
    apply univalent_category_has_homsets.
  Defined.


  (** We now show that this displayed bicategory is locally univalent *)
  Definition disp_inv_to_eq1
             {C D : bicat_of_univ_cats}
             {F : bicat_of_univ_cats⟦C,D⟧}
             {TC : bidisp_tensor_disp_bicat C}
             {TD : bidisp_tensor_disp_bicat D}
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
             {TC : bidisp_tensor_disp_bicat C}
             {TD : bidisp_tensor_disp_bicat D}
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
      repeat (apply impred_isaprop ; intro).
      apply univalent_category_has_homsets.
  Defined.

  Theorem bidisp_tensor_disp_bicat_is_locally_univalent :
    disp_univalent_2_1 bidisp_tensor_disp_bicat.
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
        apply isaprop_bidisp_tensor_disp_2cell_struct.
  Defined.


  (** We now show that this displayed bicategory is globally univalent **)

  Definition tensor_iso {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ α : ∏ x y : C, z_iso (x ⊗_{TD} y) (x ⊗_{TC} y),
          ∏ (a1 a2 b1 b2 : C) (f : C⟦a1,a2⟧) (g : C⟦b1,b2⟧),
          (pr1 (α a1 b1)) · (f ⊗^{TC} g) = (f ⊗^{TD} g) · (pr1 (α a2 b2)).

  Definition tensor_eq {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (α : ∏ x y : C, (x ⊗_{TD} y) = (x ⊗_{TC} y)),
    ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      (idtomor _ _ (α x1 y1)) · (f ⊗^{TC} g) = (f ⊗^{TD} g) · (idtomor _ _ (α x2 y2)).

  Definition tensor_eq' {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (α : ∏ x y : C, (x ⊗_{TD} y) = (x ⊗_{TC} y)),
    ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (! α x1 y1) (f ⊗^{TC} g)
      = (transportf _ (α x2 y2) (f ⊗^{TD} g)).


  Lemma idtomor_to_transport {C : univalent_category} (TC TD : tensor C)
        (α : ∏ x y : C, (x ⊗_{TD} y) = (x ⊗_{TC} y))
        {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧)
    : (idtomor _ _ (α x1 y1)) · (f ⊗^{TC} g) = (f ⊗^{TD} g) · (idtomor _ _ (α x2 y2))
      -> transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (! α x1 y1) (f ⊗^{TC} g)
        = (transportf _ (α x2 y2) (f ⊗^{TD} g)).
  Proof.
    intro q.
    rewrite (! eq_idtoiso_idtomor _ _ _) in q.
    rewrite (! eq_idtoiso_idtomor _ _ _) in q.
    etrans. {
      apply (! idtoiso_precompose _ _ _ _ _ _).
    }
    etrans. {
      apply cancel_postcomposition.
      do 2 apply maponpaths.
      apply pathsinv0inv0.
    }
    etrans. { exact q. }
    apply idtoiso_postcompose.
  Qed.

  Lemma transport_to_idtomor {C : univalent_category} (TC TD : tensor C)
        (α : ∏ x y : C, (x ⊗_{TD} y) = (x ⊗_{TC} y))
        {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧)
    : transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (! α x1 y1) (f ⊗^{TC} g)
      = (transportf _ (α x2 y2) (f ⊗^{TD} g))
      -> (idtomor _ _ (α x1 y1)) · (f ⊗^{TC} g) = (f ⊗^{TD} g) · (idtomor _ _ (α x2 y2)).
  Proof.
    intro q.
    etrans. {
      apply cancel_postcomposition.
      apply (! eq_idtoiso_idtomor _ _ _).
    }
    rewrite (! idtoiso_precompose _ _ _ _ _ _) in q.
    rewrite (! idtoiso_postcompose _ _ _ _ _ _) in q.
    rewrite pathsinv0inv0 in q.
    etrans. { apply q. }
    apply maponpaths.
    apply eq_idtoiso_idtomor.
  Qed.

  Lemma tensor_eq_equiv_tensor_eq' {C : univalent_category} (TC TD : tensor C)
    : tensor_eq' TC TD ≃ tensor_eq TC TD.
  Proof.
    apply weq_subtypes_iff.
    - intro.
      repeat (apply impred_isaprop ; intro).
      apply homset_property.
    - intro.
      repeat (apply impred_isaprop ; intro).
      apply homset_property.
    - intro pob.
      split.
      + intros q ? ? ? ? f g.
        apply transport_to_idtomor.
        exact (q _ _ _ _ f g).
      + intros q ? ? ? ? f g.
        apply idtomor_to_transport.
        exact (q _ _ _ _ f g).
  Defined.

  Definition tensor_eq'' {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (α : ∏ x y : C, (x ⊗_{TD} y) = (x ⊗_{TC} y)),
    ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      f ⊗^{TC} g
      = transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (α x1 y1) (transportf _ (α x2 y2) (f ⊗^{TD} g)).

  Lemma transport_to_transport_f_f {C : univalent_category} (TC TD : tensor C)
        (α : ∏ x y : C, (x ⊗_{TD} y) = (x ⊗_{TC} y))
        {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧)
    : transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (! α x1 y1) (f ⊗^{TC} g)
      = transportf _ (α x2 y2) (f ⊗^{TD} g)
      -> f ⊗^{TC} g
        = transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (α x1 y1) (transportf _ (α x2 y2) (f ⊗^{TD} g)).
  Proof.
    intro q.
    apply (transportf_transpose_right (P := λ x : C, C ⟦ x, x2 ⊗_{ TC} y2 ⟧)).
    exact q.
  Qed.

  Lemma transport_f_f_to_transport {C : univalent_category} (TC TD : tensor C)
        (α : ∏ x y : C, (x ⊗_{TD} y) = (x ⊗_{TC} y))
        {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧)
    : f ⊗^{TC} g
      = transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (α x1 y1) (transportf _ (α x2 y2) (f ⊗^{TD} g))
      -> transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (! α x1 y1) (f ⊗^{TC} g)
      = (transportf _ (α x2 y2) (f ⊗^{TD} g)).
  Proof.
    intro q.
    apply (transportf_transpose_left (P :=  (λ x : C, C ⟦ x, x2 ⊗_{ TC} y2 ⟧))).
    unfold transportb.
    rewrite pathsinv0inv0.
    apply q.
  Qed.

  Lemma tensor_eq'_equiv_tensor_eq'' {C : univalent_category} (TC TD : tensor C)
    : tensor_eq'' TC TD  ≃ tensor_eq' TC TD.
  Proof.
    apply weq_subtypes_iff.
    - intro.
      repeat (apply impred_isaprop ; intro).
      apply homset_property.
    - intro.
      repeat (apply impred_isaprop ; intro).
      apply homset_property.
    - intro pob.
      split.
      + intros q ? ? ? ? f g.
        apply transport_f_f_to_transport.
        exact (q _ _ _ _ f g).
      + intros q ? ? ? ? f g.
        apply transport_to_transport_f_f.
        exact (q _ _ _ _ f g).
  Defined.

  Lemma tensor_iso_equiv_tensor_eq {C : univalent_category} (TC TD : tensor C)
    : tensor_eq TC TD ≃ tensor_iso TC TD.
  Proof.
    use weqtotal2.
    - apply weqonsecfibers ; intro x ; apply weqonsecfibers ; intro y.
      use weq_iso.
      + apply idtoiso.
      + apply isotoid.
        apply univalent_category_is_univalent.
      + intro.
        apply isotoid_idtoiso.
      + intro.
        apply idtoiso_isotoid.
    - intro iso_tob.
      repeat (apply weqonsecfibers ; intro).
      use weq_iso.
      + intro p.
        cbn in p.
        rewrite (! eq_idtoiso_idtomor _ _ _) in p.
        rewrite (! eq_idtoiso_idtomor _ _ _) in p.
        apply p.
      + intro p.
        etrans. {
          apply cancel_postcomposition.
          apply (! eq_idtoiso_idtomor _ _ _).
        }
        etrans. { apply p. }
        apply cancel_precomposition.
        apply eq_idtoiso_idtomor.
      + intro ; apply homset_property.
      + intro ; apply homset_property.
  Defined.

  Lemma disp_eq_to_tensoriso {C : bicat_of_univ_cats} (TC TD : bidisp_tensor_disp_bicat C)
    : disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) TC TD -> tensor_iso TC TD.
  Proof.
    intro dae.
    induction dae as [[ptd ptnat] [data [ax equiv]]].
    induction data as [ptdinv [ptunit ptcounit]].
    cbn in *.

    use tpair.
    - intros x y.
      use make_z_iso.
      + exact (ptd x y).
      + exact (pr1 ptdinv x y).
      + split.
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

  Definition tensoriso_to_disp_eq {C : bicat_of_univ_cats} (TC TD : bidisp_tensor_disp_bicat C)
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
      * intros x1 x2 y1 y2 f g.
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
        rewrite id_right.
        rewrite tensor_id.
        rewrite id_left.
        cbn.
        apply (z_iso_inv_after_z_iso ((pr1 ti x y))).
      + (* axioms *)
        split.
        * split.
          -- abstract (repeat (apply funextsec ; intro) ;
             apply univalent_category_has_homsets).
          -- apply funextsec ; intro ; apply funextsec ; intro.
             apply univalent_category_has_homsets.
        * split.
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
             ++ split.
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
             ++ split.
                ** abstract (repeat (apply funextsec ; intro) ;
                   apply univalent_category_has_homsets).
                ** abstract (repeat (apply funextsec ; intro) ;
                   apply univalent_category_has_homsets).
  Defined.

  Lemma tensor_iso_disp_eq_equiv {C : bicat_of_univ_cats} (TC TD : bidisp_tensor_disp_bicat C)
    : tensor_iso TC TD ≃ disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) TC TD.
  Proof.
    use weq_iso.
    - intro ti.
      apply (tensoriso_to_disp_eq TC TD ti).
    - intro dae.
      exact (disp_eq_to_tensoriso TC TD dae).
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
    - intro dae.
      use subtypePath.
      + intro f.
        apply isaprop_disp_left_adjoint_equivalence.
        apply univalent_cat_is_univalent_2_1.
        apply bidisp_tensor_disp_bicat_is_locally_univalent.
      + apply idpath.
  Defined.

  Definition tensor_eqi'' {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (α : ∏ x y : C, (x ⊗_{TC} y) = (x ⊗_{TD} y)),
    ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      f ⊗^{TC} g
      = transportf (λ x : C, C⟦x , x2 ⊗_{TC} y2⟧) (! α x1 y1) (transportf _ (! α x2 y2) (f ⊗^{TD} g)).

  Lemma tensor_eq''_equiv_tensor_eqi'' {C : univalent_category} (TC TD : tensor C)
    : tensor_eqi'' TC TD ≃ tensor_eq'' TC TD.
  Proof.
    use weq_iso.
    - intro tei.
      use tpair.
      + intros x y.
        exact (! pr1 tei x y).
      + intros x1 x2 y1 y2 f g.
        exact (pr2 tei _ _ _ _ f g).
    - intro te.
      use tpair.
      + intros x y.
        exact (! pr1 te x y).
      + intros x1 x2 y1 y2 f g.
        rewrite pathsinv0inv0.
        rewrite pathsinv0inv0.
        apply (pr2 te).
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

  Definition tensor_eqi''' {C : univalent_category} (TC TD : tensor C) : UU
    := ∑ (α : ∏ x y : C, (x ⊗_{TC} y) = (x ⊗_{TD} y)),
    ∏ {x1 x2 y1 y2 : C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      transportf (λ x : C, C⟦x , x2 ⊗_{TD} y2⟧) (α x1 y1) (transportf (λ x : C, C⟦x1 ⊗_{TC} y1 , x⟧) (α x2 y2) (f ⊗^{TC} g)) = (f ⊗^{TD} g).

  Lemma independent_transportation_commutes {C : univalent_category}
        {F G : C -> C -> C}
        {x1 x2 y1 y2 : C}
        (p1 : F x1 y1 = G x1 y1)
        (p2 : F x2 y2 = G x2 y2)
        (f : C⟦F x1 y1, F x2 y2⟧)
    :  transportf (λ c : C, C ⟦ G x1 y1, c ⟧) p2
    (transportf (λ c : C, C ⟦ c, F x2 y2 ⟧) p1 f) =
  transportf (λ c : C, C ⟦ c, G x2 y2 ⟧) p1
             (transportf (λ c : C, C ⟦ F x1 y1, c ⟧) p2 f).
  Proof.
    induction p1 ; induction p2.
    apply idpath.
  Qed.

  Lemma tensor_eqi''_equiv_tensor_eqi''' {C : univalent_category} (TC TD : tensor C)
    : tensor_eqi''' TC TD ≃ tensor_eqi'' TC TD.
  Proof.
    apply weqfibtototal.
    intro.
    repeat (apply weqonsecfibers ; intro).
    use weq_iso.
    - intro q.
      apply pathsinv0.
      etrans. {
        apply maponpaths.
        apply maponpaths.
        exact (! q).
      }
      rewrite (! independent_transportation_commutes _ _ _).
      rewrite transport_f_f.
      rewrite pathsinv0r.
      rewrite idpath_transportf.
      rewrite transport_f_f.
      rewrite pathsinv0r.
      apply idpath_transportf.
    - intro q.
      etrans. {
        apply maponpaths.
        apply maponpaths.
        exact q.
      }
      rewrite (! independent_transportation_commutes _ _ _).
      rewrite transport_f_f.
      rewrite pathsinv0l.
      rewrite idpath_transportf.
      rewrite transport_f_f.
      rewrite pathsinv0l.
      apply idpath_transportf.
    - intro q.
      apply homset_property.
    - intro q.
      apply homset_property.
  Defined.

  Lemma transport_of_bifunctor_map_is_pointwise {C : univalent_category}
      {F0 G0 : ob C -> ob C -> ob C}
      (F1 : ∏ x1 x2 y1 y2 : ob C, C⟦x1,x2⟧ -> C⟦y1,y2⟧ -> C⟦F0 x1 y1, F0 x2 y2⟧)
      (gamma : F0  = G0)
      {x1 x2 y1 y2 : ob C} (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧) :
  transportf (fun T : C -> C -> C =>
                ∏ a1 a2 b1 b2 : C, C⟦a1,a2⟧ -> C⟦b1,b2⟧ -> C⟦T a1 b1, T a2 b2⟧)
             gamma F1 x1 x2 y1 y2 f g =
    double_transport
      (toforallpaths (λ _ : ob C, C) (F0 x1) (G0 x1) (toforallpaths (λ _ : ob C, C -> C) F0 G0 gamma x1) y1)
      (toforallpaths (λ _ : ob C, C) (F0 x2) (G0 x2) (toforallpaths (λ _ : ob C, C -> C) F0 G0 gamma x2) y2)
                   (F1 _ _ _ _ f g).
  Proof.
    induction gamma.
    apply idpath.
  Qed.

  Definition tensor_eqi'''_to_eq1 {C : univalent_category} (TC TD : tensor C) : tensor_eqi''' TC TD -> pr11 TC = pr11 TD.
  Proof.
    intro te.
    apply funextsec ; intro ; apply funextsec ; intro ; apply (pr1 te).
  Defined.

  Definition tensor_eqi'''_to_eq {C : univalent_category} (TC TD : tensor C) : tensor_eqi''' TC TD -> TC = TD.
  Proof.
    intro te.
    use total2_paths_f.
    - use total2_paths_f.
      + (* apply funextsec ; intro ; apply funextsec ; intro ; apply (pr1 te). *)
        exact (tensor_eqi'''_to_eq1 TC TD te).
      + repeat (apply funextsec ; intro).
        etrans.
        2: apply (pr2 te).

        etrans. {
          apply transport_of_bifunctor_map_is_pointwise.
        }
        unfold double_transport.
        unfold tensor_eqi'''_to_eq1.
        rewrite toforallpaths_funextsec.
        rewrite toforallpaths_funextsec.
        rewrite toforallpaths_funextsec.
        apply independent_transportation_commutes.
    - use total2_paths_f.
      + abstract (repeat (apply impred_isaprop ; intro) ;
        apply homset_property).
      + abstract (repeat (apply impred_isaprop ; intro) ;
        apply homset_property).
  Defined.

  Lemma id_tensor_eqi'''_2 {C : univalent_category} (TC TD : tensor C)
    : pr11 TC = pr11 TD ->  ∏ x y : C, x ⊗_{ TC} y = x ⊗_{ TD} y.
  Proof.
    intros p x y.
    exact (toforallpaths _ _ _ (toforallpaths _ _ _ p x) y).
  Defined.

  Lemma id_tensor_eqi'''_1 {C : univalent_category} (TC TD : tensor C)
    : TC = TD ->  ∏ x y : C, x ⊗_{ TC} y = x ⊗_{ TD} y.
  Proof.
    intros p.
    set (eqonob := base_paths _ _ (base_paths _ _ p)).
    (* exact (toforallpaths _ _ _ (toforallpaths _ _ _ eqonob x) y). *)
    exact (id_tensor_eqi'''_2 TC TD eqonob).
  Defined.

  Lemma id_tensor_eqi''' {C : bicat_of_univ_cats} (TC TD : bidisp_tensor_disp_bicat C)
    : TC = TD -> tensor_eqi''' TC TD.
  Proof.
    intro p.
    (* induction p. *)
    use tpair.
    - exact (id_tensor_eqi'''_1 TC TD p).

      (* induction p.
      apply idpath. *)
    - intros ? ? ? ? f g.
      induction p.
      etrans.
      2: apply (! idpath_transportf _ _).
      apply idpath_transportf.
  Defined.

  Lemma total2_paths_idpath {A : UU} {B : A -> UU} (x : ∑ y : A, B y)
    : total2_paths_f (idpath (pr1 x)) (idpath_transportf B (pr2 x)) = idpath x.
  Proof.
    apply idpath.
  Qed.

  Lemma maponpaths_total {A : UU} {B : A -> UU} (x : ∑ y : A, B y)
        (p0 : pr1 x = pr1 x) (p1 : transportf B p0 (pr2 x) = pr2 x)
        (q0 : pr1 x = pr1 x) (q1 : transportf B q0 (pr2 x) = pr2 x)
    : p0=q0 ->  (∏ a : A, isaset (B a)) -> total2_paths_f p0 p1 = total2_paths_f q0 q1.
  Proof.
    intro k0.
    induction k0.
    intro pfset.
    apply maponpaths.
    apply pfset.
  Qed.

  Lemma cancellation_lemma {A B : UU} (a : A) (b : B) (f : A -> B) (g : B -> A)
    : (∏ b0 : B, f (g b0) = b0) -> g (f a) = g(b) -> f a = b.
  Proof.
    intros i e.
    set (k0 := ! i (f a)).
    rewrite e in k0.
    exact (k0 @ i b).
  Qed.

  Lemma funextsec_id'' {C : univalent_category} (T : C -> C -> C)
    : ∏ x : C, toforallpaths (λ _ : C,C) _ _ (funextsec (λ _ : C, C) (T x) (T x) (λ x0 : C, idpath (T x x0))) =
        toforallpaths (λ _ : C, C) _ _ (toforallpaths (λ _ : C, C → C) T T (idpath T) x).
  Proof.
    intro x.
    etrans. {
      apply toforallpaths_funextsec.
    }
    apply funextsec ; intro y.
    apply idpath.
  Qed.

  Lemma funextsec_id' {C : univalent_category} (T : C -> C -> C)
    : toforallpaths (λ _ : C, C → C) T T (
        (funextsec (λ _ : C, C → C) T T
                (λ x : C, funextsec (λ _ : C, C) (T x) (T x) (λ x0 : C, idpath (T x x0))))) = toforallpaths (λ _ : C, C → C) T T (idpath T).
  Proof.
    etrans. {
      apply toforallpaths_funextsec.
    }
    apply funextsec ; intro x.
    apply (cancellation_lemma _ _ _ (toforallpaths (λ _: C,C) (T x) (T x))).
    - intro q.
      apply funextsec_toforallpaths.
    - apply funextsec_id''.
  Qed.

  Lemma funextsec_id {C : univalent_category} {T : C -> C -> C}
    : funextsec (λ _ : C, C → C) T T
                (λ x : C, funextsec (λ _ : C, C) (T x) (T x) (λ x0 : C, idpath (T x x0)))
      = idpath T.
  Proof.
    apply (cancellation_lemma _ _ _ (toforallpaths (λ _ : C, C -> C) T T)).
    - intro q.
      apply funextsec_toforallpaths.
    - apply funextsec_id'.
  Qed.

  Lemma id_to_teqi'''_to_id
        {C : bicat_of_univ_cats}
        {TC TD : bidisp_tensor_disp_bicat C}
        (p : TC = TD)
    : tensor_eqi'''_to_eq TC TD (id_tensor_eqi''' TC TD p) = p.
  Proof.
    unfold tensor_eqi'''_to_eq.
    unfold id_tensor_eqi'''.
    induction p.
    use pathscomp0.
    3: apply total2_paths_idpath.

    apply maponpaths_total.
    - use pathscomp0.
      3: apply total2_paths_idpath.
      apply maponpaths_total.
      + apply funextsec_id.
      + intro T.
        repeat (apply impred_isaset ; intro).
        apply homset_property.
    - intro T.
      apply isaset_dirprod; repeat (repeat (apply impred_isaset ; intro) ; apply isasetaprop ; apply homset_property).
  Qed.

  Lemma pr_id_tensor_eqi'''_funextsec {C : univalent_category} {TC TD : tensor C} (p : TC = TD) (x y : C)
    : pr1 (id_tensor_eqi''' TC TD p) x y = id_tensor_eqi'''_1 TC TD p x y.
  Proof.
    apply idpath.
  Qed.

  Lemma distributer {C : univalent_category} {TC TD : tensor C} (p : tensor_eqi''' TC TD)
    :  id_tensor_eqi'''_1 TC TD (tensor_eqi'''_to_eq TC TD p) = id_tensor_eqi'''_2 TC TD (tensor_eqi'''_to_eq1 TC TD p).
  Proof.
    unfold id_tensor_eqi'''_1.
    apply maponpaths.
    etrans. {
      apply maponpaths.
      apply base_total2_paths.
    }
    apply base_total2_paths.
  Qed.

  Lemma distributer_funext {C : univalent_category} {TC TD : tensor C} (p : tensor_eqi''' TC TD) (x y : C)
    :  id_tensor_eqi'''_1 TC TD (tensor_eqi'''_to_eq TC TD p) x y = id_tensor_eqi'''_2 TC TD (tensor_eqi'''_to_eq1 TC TD p) x y.
  Proof.
    rewrite distributer.
    apply idpath.
  Qed.

  Lemma teqi'''_to_id_to_teqi'''
        {C : bicat_of_univ_cats}
        {TC TD : bidisp_tensor_disp_bicat C}
        (p : tensor_eqi''' TC TD)
    : id_tensor_eqi''' TC TD (tensor_eqi'''_to_eq TC TD p) = p.
  Proof.
    use total2_paths_f.
    - apply funextsec ; intro x ; apply funextsec ; intro y.
      etrans. {
        apply pr_id_tensor_eqi'''_funextsec.
      }
      etrans. {
        apply distributer_funext.
      }
      unfold id_tensor_eqi'''_2.
      unfold tensor_eqi'''_to_eq1.
      rewrite toforallpaths_funextsec.
      rewrite toforallpaths_funextsec.
      apply idpath.
    - repeat (apply funextsec ; intro).
      apply homset_property.
  Qed.

  Definition tensor_eqi'''_equiv_eq {C : bicat_of_univ_cats} (TC TD : bidisp_tensor_disp_bicat C)
    : TC = TD ≃ tensor_eqi''' TC TD.
  Proof.
    use weq_iso.
    - intro eq.
      exact (id_tensor_eqi''' TC TD eq).
    - intro teq.
      exact (tensor_eqi'''_to_eq _ _ teq).
    - intro eq.
      apply id_to_teqi'''_to_id.
    - intro teq.
      apply teqi'''_to_id_to_teqi'''.
  Defined.

  Lemma bicatcattensor_disp_prebicat_is_globally_univalent : disp_univalent_2_0 bidisp_tensor_disp_bicat.
  Proof.
   intros C D equalcats TC TD.
   induction equalcats.
   use weqhomot.
   - set (i1 := tensor_iso_disp_eq_equiv TC TD).
     set (i2 := tensor_iso_equiv_tensor_eq TC TD).
     set (i3 := tensor_eq_equiv_tensor_eq' TC TD).
     set (i4 := tensor_eq'_equiv_tensor_eq'' TC TD).
     set (i5 := tensor_eq''_equiv_tensor_eqi'' TC TD).
     set (i6 := tensor_eqi''_equiv_tensor_eqi''' TC TD).
     set (i7 := tensor_eqi'''_equiv_eq TC TD).
     exact ((i1 ∘ i2 ∘ i3 ∘ i4 ∘ i5 ∘ i6 ∘ i7)%weq).
   - intro p.
     induction p.
     use subtypePath.
     + intro.
       apply (@isaprop_disp_left_adjoint_equivalence bicat_of_univ_cats  bidisp_tensor_disp_bicat).
       * exact univalent_cat_is_univalent_2_1.
       * exact bidisp_tensor_disp_bicat_is_locally_univalent.
     + use total2_paths_b.
       * repeat (apply funextsec ; intro).
         apply idpath.
       * repeat (apply funextsec ; intro).
         apply homset_property.
  Qed.

  Lemma bidisp_tensor_disp_prebicat_is_univalent_2 : disp_univalent_2 bidisp_tensor_disp_bicat.
  Proof.
    apply make_disp_univalent_2.
    - apply bicatcattensor_disp_prebicat_is_globally_univalent.
    - apply bidisp_tensor_disp_bicat_is_locally_univalent.
  Defined.

  Definition bidisp_tensor_disp_2cells_isaprop : disp_2cells_isaprop bidisp_tensor_disp_bicat.
  Proof.
    intros C D F G α TC TD ptC ptD.
    apply isaprop_bidisp_tensor_disp_2cell_struct.
  Qed.

  Definition bidisp_tensor_disp_locally_groupoid : disp_locally_groupoid bidisp_tensor_disp_bicat.
  Proof.
    unfold disp_locally_groupoid.
    intros C D F G α TC TD ptC ptD ptc.
    unfold is_disp_invertible_2cell.
    use tpair.
    - intros x y.

      set (α_natiso := (invertible_2cell_to_nat_z_iso F G α)).
      set (αxy_iso := pr2 α_natiso (tensor_on_ob (TC : tensor (C : univalent_category)) x y)).

      etrans. {
        apply cancel_precomposition.
        apply (! id_right _).
      }

      etrans. {
        apply cancel_precomposition.
        apply cancel_precomposition.
        exact (! pr12 αxy_iso).
      }

      use pathscomp0.
      3: { apply (id_right). }
      use pathscomp0.
      3: {
        apply cancel_precomposition.
        exact (pr12 αxy_iso).
      }

      etrans. {
        apply cancel_precomposition.
        apply assoc.
      }
      etrans. { apply assoc. }
      use pathscomp0.
      3: apply assoc'.

      apply cancel_postcomposition.

      etrans. {
        apply cancel_precomposition.
        apply (pr22 αxy_iso).
      }
      etrans. { apply id_right. }

      use pathscomp0.
      3: {
        rewrite assoc'.
        apply cancel_precomposition.
        apply (! ptc x y).
      }
      use pathscomp0.
      3: {
        rewrite assoc.
        apply cancel_postcomposition.
        apply tensor_comp.
      }

      use pathscomp0.
      3: {
        apply cancel_postcomposition.
        apply maponpaths.
        apply (! pr22 (pr2 α_natiso y)).
      }
      set (αx_iso := pr22 (pr2 α_natiso x)).

      assert (pf : ∏ (x y z w : (D : univalent_category))
                     (f : (D : univalent_category)⟦x,y⟧)
                     (f' : (D : univalent_category)⟦x,y⟧)
                     (g : (D : univalent_category)⟦z,w⟧),
                 f=f' -> tensor_on_hom (TD : tensor (D : univalent_category)) x y z w f g = tensor_on_hom (TD : tensor (D : univalent_category)) _ _ _ _ f' g). {
        intros ? ? ? ? ? ? ? p.
        induction p.
        apply idpath.
      }

      use pathscomp0.
      3: {
        apply cancel_postcomposition.
        apply (! pf _ _ _ _ _ _ _ αx_iso).
      }
      rewrite tensor_id.
      apply (! id_left _).
    - use tpair.
      + apply isaprop_bidisp_tensor_disp_2cell_struct.
      + apply isaprop_bidisp_tensor_disp_2cell_struct.
  Qed.

End TensorLayer.
