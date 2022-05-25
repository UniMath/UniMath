(*
This is the thirth of a sequence of files with the purpose of showing that the bicategory of univalent monoidal categories is again univalent.
In this file we construct one side of the second displayed layer above the bicategory of univalent categories, more precisely:
The total category corresponding to this displayed layer is the univalent bicategory defined as followed:
- The objects are categories (already equipped with a tensor and unit) together with the data of a natural transformation from this category to itself (which will be the left unitor for the monoidal structure).
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

Section LeftUnitor.

  Import TensorUnitNotations.

  Local Definition tu_cat := bicatcatstensorunit_total.
  Local Definition uc (C : tu_cat) : univalent_category := pr1 C.

  Definition lunitor_data (C : tu_cat) : UU
    := ∏ x : (uc C), (uc C)⟦I_{C} ⊗_{C} x, x⟧.

  Definition lunitor_nat {C : tu_cat} (lu : lunitor_data C) : UU
    := ∏ {x y : uc C} (f : (uc C)⟦x,y⟧), ((identity I_{C}) ⊗^{C} f) · (lu y) = (lu x) · f.

  Definition lunitor (C : tu_cat) : UU
    := ∑ lu : lunitor_data C, lunitor_nat lu.

  (* Definition lunitor_ludata {C : tu_cat} (lu : lunitor C) : lunitor_data C := pr1 lu.
  Coercion lunitor_ludata : lunitor >-> lunitor_data. *)

  Definition preserves_lunitor {C D : tu_cat} (luC : lunitor C) (luD : lunitor D) (F : tu_cat⟦C, D⟧)
    : UU := ∏ x : uc C,
        (pu_{F} ⊗^{D} (identity ((pr1 F : functor _ _) x))) · (pt_{F} I_{C} x) · (functor_on_morphisms (pr1 F : functor _ _) (pr1 luC x)) = pr1 luD ((pr1 F : functor _ _) x).

  Definition isaprop_preserves_lunitor {C D : tu_cat} (luC : lunitor C) (luD : lunitor D) (F : tu_cat⟦C,D⟧) : isaprop (preserves_lunitor luC luD F).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply univalent_category_has_homsets.
  Qed.


End LeftUnitor.

Section LeftUnitorLayer.

  Definition catcatslu_disp_ob_mor : disp_cat_ob_mor tu_cat.
  Proof.
    use tpair.
    - exact (λ C, lunitor C).
    - exact (λ C D luC luD F, preserves_lunitor luC luD F).
  Defined.

  Definition catcatslu_disp_id_comp : disp_cat_id_comp tu_cat catcatslu_disp_ob_mor.
  Proof.
    use tpair.
    - intros C lu.
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
    - intros C D E F G luC luD luE pluF pluG x.
      admit.
  Admitted.


  Definition catcatslu_disp_cat_data : disp_cat_data tu_cat
    := (catcatslu_disp_ob_mor,, catcatslu_disp_id_comp).

  Definition bicatcatslu_disp_2cell_struct : disp_2cell_struct catcatslu_disp_cat_data.
  Proof.
    intros C D F G a luC luD pluF pluG.
    exact unit.
  Defined.

  Definition bicatcatslu_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells tu_cat
    := (catcatslu_disp_cat_data,, bicatcatslu_disp_2cell_struct).

  Definition bicatcatslu_disp_prebicat_ops : disp_prebicat_ops bicatcatslu_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat (use tpair ; intros ; try (exact tt)).
    intros C D E W F G H IC ID IE IW puF puG puH.
    exact tt.
  Qed.

  Definition bicatcatslu_disp_prebicat_data : disp_prebicat_data tu_cat
    := (bicatcatslu_disp_prebicat_1_id_comp_cells,, bicatcatslu_disp_prebicat_ops).

  Definition bicatcatslu_disp_prebicat_laws : disp_prebicat_laws bicatcatslu_disp_prebicat_data.
  Proof.
    repeat split; intro; intros; apply isapropunit.
  Qed.

  Definition bicatcatslu_disp_prebicat : disp_prebicat tu_cat
    := (bicatcatslu_disp_prebicat_data,,bicatcatslu_disp_prebicat_laws).

  Definition bicatcatslu_disp_bicat : disp_bicat tu_cat.
  Proof.
    refine (bicatcatslu_disp_prebicat,, _).
    intros C D F G α luC luD pluF pluG.
    apply isasetunit.
  Defined.

  Lemma bicatcatslu_disp_prebicat_is_locally_univalent : disp_univalent_2_1 bicatcatslu_disp_bicat.
  Proof.
    intros C D F G pfFisG luF luG pluF pluG.
    induction pfFisG.
    apply isweqimplimpl.
    - intros α.
      apply isaprop_preserves_lunitor.
    - apply isasetaprop.
      apply isaprop_preserves_lunitor.
    - apply invproofirrelevance.
      intro ; intro.
      use subtypePath.
      + intro x0.
        apply isaprop_is_disp_invertible_2cell.
      + apply isapropunit.
  Qed.

  Definition lu_equal {C : tu_cat} (lu1 lu2 : bicatcatslu_disp_bicat C) : UU
    := ∏ x : (pr1 C : univalent_category), (pr1 lu1) x = (pr1 lu2) x.

  Definition disp_adj_equiv_to_lu_equal {C : tu_cat} (lu1 lu2 : bicatcatslu_disp_bicat C)
    : disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) lu1 lu2 -> lu_equal lu1 lu2.
  Proof.
    intro dae.
    intro x.
    induction dae as [plu [adj_data [adj_ax adj_eq]]].
    induction adj_data as [inv [unit counit]].
    cbn in *.

    set (p := plu x).
    cbn in p.
    rewrite tensor_id in p.
    rewrite id_left in p.
    unfold identityfunctor_preserves_tensor_data in p.
    rewrite id_left in p.
    exact p.
  Defined.

  Definition lu_equal_to_disp_adj_equiv {C : tu_cat} (lu1 lu2 : bicatcatslu_disp_bicat C)
    : lu_equal lu1 lu2 -> disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) lu1 lu2.
  Proof.
    intro lue.
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
      exact (lue x).
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
          exact (! lue x).
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

  Definition disp_adj_equiv_equivalence_lu_equal {C : tu_cat} (lu1 lu2 : bicatcatslu_disp_bicat C)
    : lu_equal lu1 lu2 ≃ disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) lu1 lu2.
  Proof.
    use make_weq.
    - intro lue.
      exact (lu_equal_to_disp_adj_equiv _ _ lue).
    - use isweq_iso.
      + intro dae.
        exact (disp_adj_equiv_to_lu_equal _ _ dae).
      + intro lue.
        use funextsec ; intro.
        apply univalent_category_has_homsets.
      + intro dae.
        use subtypePath.
        * intro.
          apply isaprop_disp_left_adjoint_equivalence.
          Search (is_univalent_2_1 tu_cat).
          apply bicatcatstensorunit_is_univalent_2.
          apply bicatcatslu_disp_prebicat_is_locally_univalent.
        * use funextsec ; intro.
          apply univalent_category_has_homsets.
  Defined.

  Definition lu_equal_to_equal {C : tu_cat} (lu1 lu2 : bicatcatslu_disp_bicat C)
    : lu_equal lu1 lu2 → lu1 = lu2.
  Proof.
    intro lue.
    use total2_paths_b.
    - apply funextsec ; intro x.
      exact (lue x).
    - repeat (apply funextsec ; intro).
      apply univalent_category_has_homsets.
  Defined.

  Definition equal_to_lu_equal {C : tu_cat} (lu1 lu2 : bicatcatslu_disp_bicat C)
    : lu1 = lu2 -> lu_equal lu1 lu2.
  Proof.
    intro lue.
    induction lue.
    intro x.
    apply idpath.
  Defined.

  Definition lu_equal_equivalent_equal {C : tu_cat} (lu1 lu2 : bicatcatslu_disp_bicat C)
    : lu1 = lu2 ≃ lu_equal lu1 lu2.
  Proof.
    use make_weq.
    - intro lue.
      exact (equal_to_lu_equal _ _ lue).
    - use isweq_iso.
      + intro lue.
        exact (lu_equal_to_equal _ _ lue).
      + intro lue.
        induction lue.

        admit.
      + intro lue.
        apply funextsec ; intro.
        apply univalent_category_has_homsets.

  Admitted.


  Lemma bicatcatslu_disp_prebicat_is_globally_univalent : disp_univalent_2_0 bicatcatslu_disp_bicat.
  Proof.
    intros C D equalcats luC luD.
    induction equalcats.
    use weqhomot.
    - (* rewrite idpath_transportf. *)
      set (i1 := lu_equal_equivalent_equal luC luD).
      set (i2 := disp_adj_equiv_equivalence_lu_equal luC luD).
      exact (i2 ∘ i1)%weq.
    - intro p.
      induction p ; cbn.
      use subtypePath.
      + intro ; simpl.
        apply (@isaprop_disp_left_adjoint_equivalence _  bicatcatslu_disp_bicat).
        * apply bicatcatstensorunit_is_univalent_2.
        * exact bicatcatslu_disp_prebicat_is_locally_univalent.
      + apply funextsec ; intro x.
        apply univalent_category_has_homsets.
  Qed.

  Lemma bicatcatslu_disp_prebicat_is_univalent_2 : disp_univalent_2 bicatcatslu_disp_bicat.
  Proof.
    apply make_disp_univalent_2.
    - apply bicatcatslu_disp_prebicat_is_globally_univalent.
    - apply bicatcatslu_disp_prebicat_is_locally_univalent.
  Defined.
