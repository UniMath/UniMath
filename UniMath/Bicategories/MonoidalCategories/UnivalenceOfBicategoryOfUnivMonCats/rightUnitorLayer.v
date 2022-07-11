(*
This is one file which leads to showing that the bicategory of univalent monoidal categories is again univalent.
In this file we construct one side of the second displayed layer above the bicategory of univalent categories, more precisely:
The total category corresponding to this displayed layer is the univalent bicategory defined as followed:
- The objects are categories (already equipped with a tensor and unit) together with the data of a natural transformation from this category to itself (which will be the right unitor for the monoidal structure).
- The morphisms expresses a naturality condition.
- The 2-cells are trivial.
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

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.Tensorlayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.Unitlayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceOfBicategoryOfUnivMonCats.TensorUnitlayer.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section RightUnitor.

  Import TensorUnitNotations.

  Local Definition tu_cat := bicatcatstensorunit_total.
  Local Definition uc (C : tu_cat) : univalent_category := pr1 C.

  Definition runitor_data (C : tu_cat) : UU
    := ∏ x : (uc C), (uc C)⟦x ⊗_{C} I_{C}, x⟧.

  Definition runitor_nat {C : tu_cat} (ru : runitor_data C) : UU
    := ∏ {x y : uc C} (f : (uc C)⟦x,y⟧), (f ⊗^{C} (identity I_{C})) · (ru y) = (ru x) · f.

  Definition runitor (C : tu_cat) : UU
    := ∑ lu : runitor_data C, runitor_nat lu.

  Definition preserves_runitor {C D : tu_cat} (ruC : runitor C) (ruD : runitor D) (F : tu_cat⟦C, D⟧)
    : UU := ∏ x : uc C,
        ((identity ((pr1 F : functor _ _) x)) ⊗^{D} pu_{F}) · (pt_{F} x I_{C}) · (functor_on_morphisms (pr1 F : functor _ _) (pr1 ruC x)) = pr1 ruD ((pr1 F : functor _ _) x).

  Definition id_preserves_runitor {C : tu_cat} (ruC : runitor C)
    : preserves_runitor ruC ruC (identity C).
  Proof.
    intro x.
    etrans. {
      apply cancel_postcomposition.
      apply id_right.
    }
    etrans. {
      apply cancel_postcomposition.
      apply tensor_id.
    }
    apply id_left.
  Qed.

  Definition comp_preserves_runitor {C D E : tu_cat}
             (ruC : runitor C) (ruD : runitor D) (ruE : runitor E)
             {F : tu_cat⟦C,D⟧} {G : tu_cat⟦D,E⟧}
             (pruF : preserves_runitor ruC ruD F)
             (pruG : preserves_runitor ruD ruE G)
    : preserves_runitor ruC ruE (F · G).
  Proof.
    intro x.

    use pathscomp0.
    3: exact (pruG ((pr1 F : functor (uc C) (uc D)) x)).

    etrans. {
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      cbn in *.
      assert (pf :  (identity (pr1 G (pr1 F x))) =  (identity (pr1 G (pr1 F x)))· (identity (pr1 G (pr1 F x)))). {
        apply (! id_right _).
      }
      rewrite pf.
      apply (pr2 (pr212 E)).
    }

    rewrite assoc'.
    rewrite assoc'.
    use pathscomp0.
    3: {
      apply assoc.
    }
    apply cancel_precomposition.
    unfold compositions_preserves_tensor_data.
    use pathscomp0.
    3: {
      apply cancel_precomposition.
      apply maponpaths.
      exact (pruF x).
    }
    cbn in *.
    unfold compositions_preserves_tensor_data.

    use pathscomp0.
    3: {
      apply cancel_precomposition.
      apply (! functor_comp _ _ _).
    }

    rewrite assoc.
    rewrite assoc.
    rewrite assoc.
    apply cancel_postcomposition.

    use pathscomp0.
    3: {
      apply cancel_precomposition.
      apply (! functor_comp _ _ _).
    }

    use pathscomp0.
    3: { apply assoc'. }
    apply cancel_postcomposition.

    use pathscomp0.
    3: {
      apply (! (pr212 G) _ _ _ _ (identity (pr1 F x)) (pu_{F})).
      (* this is naturality of G preserving the tensor *)
    }
    apply cancel_postcomposition.
    rewrite (! functor_id _ _).
    apply idpath.
  Qed.

  Definition isaprop_preserves_runitor {C D : tu_cat} (ruC : runitor C) (ruD : runitor D) (F : tu_cat⟦C,D⟧) : isaprop (preserves_runitor ruC ruD F).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply univalent_category_has_homsets.
  Qed.


End RightUnitor.

Section RightUnitorLayer.

  Definition catcatsru_disp_ob_mor : disp_cat_ob_mor tu_cat.
  Proof.
    use tpair.
    - exact (λ C, runitor C).
    - exact (λ C D ruC ruD F, preserves_runitor ruC ruD F).
  Defined.

  Definition catcatsru_disp_id_comp : disp_cat_id_comp tu_cat catcatsru_disp_ob_mor.
  Proof.
    use tpair.
    - intros C ru.
      apply id_preserves_runitor.
    - intros C D E F G ruC ruD ruE pruF pruG x.
      apply (comp_preserves_runitor ruC ruD ruE pruF pruG).
  Defined.


  Definition catcatsru_disp_cat_data : disp_cat_data tu_cat
    := (catcatsru_disp_ob_mor,, catcatsru_disp_id_comp).

  Definition bicatcatsru_disp_2cell_struct : disp_2cell_struct catcatsru_disp_cat_data.
  Proof.
    intros C D F G a ruC ruD pruF pruG.
    exact unit.
  Defined.

  Definition bicatcatsru_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells tu_cat
    := (catcatsru_disp_cat_data,, bicatcatsru_disp_2cell_struct).

  Definition bicatcatsru_disp_prebicat_ops : disp_prebicat_ops bicatcatsru_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat (use tpair ; intros ; try (exact tt)).
    intros C D E W F G H IC ID IE IW puF puG puH.
    exact tt.
  Qed.

  Definition bicatcatsru_disp_prebicat_data : disp_prebicat_data tu_cat
    := (bicatcatsru_disp_prebicat_1_id_comp_cells,, bicatcatsru_disp_prebicat_ops).

  Definition bicatcatsru_disp_prebicat_laws : disp_prebicat_laws bicatcatsru_disp_prebicat_data.
  Proof.
    repeat split; intro; intros; apply isapropunit.
  Qed.

  Definition bicatcatsru_disp_prebicat : disp_prebicat tu_cat
    := (bicatcatsru_disp_prebicat_data,,bicatcatsru_disp_prebicat_laws).

  Definition bicatcatsru_disp_bicat : disp_bicat tu_cat.
  Proof.
    refine (bicatcatsru_disp_prebicat,, _).
    intros C D F G α ruC ruD pruF pruG.
    apply isasetunit.
  Defined.

  Lemma bicatcatsru_disp_prebicat_is_locally_univalent : disp_univalent_2_1 bicatcatsru_disp_bicat.
  Proof.
    intros C D F G pfFisG ruF ruG pruF pruG.
    induction pfFisG.
    apply isweqimplimpl.
    - intros α.
      apply isaprop_preserves_runitor.
    - apply isasetaprop.
      apply isaprop_preserves_runitor.
    - apply invproofirrelevance.
      intro ; intro.
      use subtypePath.
      + intro x0.
        apply isaprop_is_disp_invertible_2cell.
      + apply isapropunit.
  Qed.

  Definition ru_equal {C : tu_cat} (ru1 ru2 : bicatcatsru_disp_bicat C) : UU
    := ∏ x : (pr1 C : univalent_category), (pr1 ru1) x = (pr1 ru2) x.

  Definition disp_adj_equiv_to_ru_equal {C : tu_cat} (ru1 ru2 : bicatcatsru_disp_bicat C)
    : disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) ru1 ru2 -> ru_equal ru1 ru2.
  Proof.
    intro dae.
    intro x.
    induction dae as [pru [adj_data [adj_ax adj_eq]]].
    induction adj_data as [inv [unit counit]].
    cbn in *.

    set (p := pru x).
    cbn in p.
    rewrite tensor_id in p.
    rewrite id_left in p.
    unfold identityfunctor_preserves_tensor_data in p.
    rewrite id_left in p.
    exact p.
  Defined.

  Definition ru_equal_to_disp_adj_equiv {C : tu_cat} (ru1 ru2 : bicatcatsru_disp_bicat C)
    : ru_equal ru1 ru2 -> disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) ru1 ru2.
  Proof.
    intro rue.
    use tpair.
    - intro x.
      etrans. {
        apply cancel_postcomposition.
        apply cancel_postcomposition.
        apply tensor_id.
      }
      etrans. {
        apply cancel_postcomposition.
        apply id_left.
      }
      unfold identityfunctor_preserves_tensor_data.
      etrans. { apply id_left. }
      exact (rue x).
    - use tpair.
      + (* data *)
        repeat (use tpair).
        * intro x.

          etrans. {
            apply cancel_postcomposition.
            apply cancel_postcomposition.
            apply tensor_id.
          }
          etrans. {
            apply cancel_postcomposition.
            apply id_left.
          }
          unfold identityfunctor_preserves_tensor_data.
          etrans. { apply id_left. }
          exact (! rue x).
        * exact tt.
        * exact tt.
      + (* axioms *)
        use tpair.
        -- use tpair.
           ++ apply isapropunit.
           ++ apply isapropunit.
        -- use tpair.
           ++ use tpair.
              ** exact tt.
              ** use tpair.
                 --- apply isapropunit.
                 --- apply isapropunit.
           ++ use tpair.
              ** exact tt.
              ** use tpair.
                 --- apply isapropunit.
                 --- apply isapropunit.
  Defined.

  Definition disp_adj_equiv_equivalence_ru_equal {C : tu_cat} (ru1 ru2 : bicatcatsru_disp_bicat C)
    : ru_equal ru1 ru2 ≃ disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) ru1 ru2.
  Proof.
    use make_weq.
    - intro rue.
      exact (ru_equal_to_disp_adj_equiv _ _ rue).
    - use isweq_iso.
      + intro dae.
        exact (disp_adj_equiv_to_ru_equal _ _ dae).
      + intro rue.
        use funextsec ; intro.
        apply univalent_category_has_homsets.
      + intro dae.
        use subtypePath.
        * intro.
          apply isaprop_disp_left_adjoint_equivalence.
          Search (is_univalent_2_1 tu_cat).
          apply bicatcatstensorunit_is_univalent_2.
          apply bicatcatsru_disp_prebicat_is_locally_univalent.
        * use funextsec ; intro.
          apply univalent_category_has_homsets.
  Defined.

  Definition ru_equal_to_equal {C : tu_cat} (ru1 ru2 : bicatcatsru_disp_bicat C)
    : ru_equal ru1 ru2 → ru1 = ru2.
  Proof.
    intro rue.
    use total2_paths_f.
    - apply funextsec ; intro x.
      exact (rue x).
    - repeat (apply funextsec ; intro).
      apply univalent_category_has_homsets.
  Defined.

  Definition equal_to_ru_equal {C : tu_cat} (ru1 ru2 : bicatcatsru_disp_bicat C)
    : ru1 = ru2 -> ru_equal ru1 ru2.
  Proof.
    intro rue.
    induction rue.
    intro x.
    apply idpath.
  Defined.

  Definition ru_equal_equivalent_equal {C : tu_cat} (ru1 ru2 : bicatcatsru_disp_bicat C)
    : ru1 = ru2 ≃ ru_equal ru1 ru2.
  Proof.
    use make_weq.
    - intro rue.
      exact (equal_to_ru_equal _ _ rue).
    - use isweq_iso.
      + intro rue.
        exact (ru_equal_to_equal _ _ rue).
      + intro rue.
        induction rue.
        unfold ru_equal_to_equal.
        unfold equal_to_ru_equal.
        unfold bicatcatsru_disp_bicat in ru1.
        use pathscomp0.
        3: {
          apply total2_paths_idpath.
        }
        apply maponpaths_total.
        * apply (cancellation_lemma _ _ _ (toforallpaths _ (pr1 ru1) (pr1 ru1))).
          -- intro p.
             apply funextsec_toforallpaths.
          -- etrans. { apply toforallpaths_funextsec. }
             apply funextsec ; intro x.
             apply idpath.
        * intro l.
          unfold runitor_nat.
          repeat (apply impred_isaset ; intro).
          apply isasetaprop.
          apply homset_property.
      + intro rue.
        apply funextsec ; intro.
        apply univalent_category_has_homsets.
  Defined.

  Lemma bicatcatsru_disp_prebicat_is_globally_univalent : disp_univalent_2_0 bicatcatsru_disp_bicat.
  Proof.
    intros C D equalcats ruC ruD.
    induction equalcats.
    use weqhomot.
    - (* rewrite idpath_transportf. *)
      set (i1 := ru_equal_equivalent_equal ruC ruD).
      set (i2 := disp_adj_equiv_equivalence_ru_equal ruC ruD).
      exact (i2 ∘ i1)%weq.
    - intro p.
      induction p ; cbn.
      use subtypePath.
      + intro ; simpl.
        apply (@isaprop_disp_left_adjoint_equivalence _  bicatcatsru_disp_bicat).
        * apply bicatcatstensorunit_is_univalent_2.
        * exact bicatcatsru_disp_prebicat_is_locally_univalent.
      + apply funextsec ; intro x.
        apply univalent_category_has_homsets.
  Qed.

  Lemma bicatcatsru_disp_prebicat_is_univalent_2 : disp_univalent_2 bicatcatsru_disp_bicat.
  Proof.
    apply make_disp_univalent_2.
    - apply bicatcatsru_disp_prebicat_is_globally_univalent.
    - apply bicatcatsru_disp_prebicat_is_locally_univalent.
  Defined.

End RightUnitorLayer.
