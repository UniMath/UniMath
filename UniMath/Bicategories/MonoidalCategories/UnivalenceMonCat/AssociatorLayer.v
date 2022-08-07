(*
This is one file which leads to showing that the bicategory of univalent monoidal categories is again univalent.
In this file we construct one side of the second displayed layer above the bicategory of univalent categories, more precisely:
The total category corresponding to this displayed layer is the univalent bicategory defined as followed:
- The objects are categories (already equipped with a tensor and unit) together with the data (and naturality) of the associator.
- The morphisms express a preservation condition of the associator.
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

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.CurriedMonoidalCategories.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.UnitLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.TensorUnitLayer.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section AssociatorLayer.

  Definition disp_ass_disp_ob_mor : disp_cat_ob_mor tu_cat.
  Proof.
    use tpair.
    - exact (λ C, associator (tu C)).
    - exact (λ C D αC αD F, preserves_associator (ftu F) αC αD).
  Defined.

  Definition disp_ass_disp_id_comp : disp_cat_id_comp tu_cat disp_ass_disp_ob_mor.
  Proof.
    use tpair.
    - intros C α.
      apply id_preserves_associator.
    - intros C D E F G aC aD aE paF paG x y z.
      apply (comp_preserves_associator paF paG).
  Qed.

  Definition disp_ass_disp_cat_data : disp_cat_data tu_cat
    := (disp_ass_disp_ob_mor,, disp_ass_disp_id_comp).

  Definition bidisp_ass_disp_2cell_struct : disp_2cell_struct disp_ass_disp_cat_data.
  Proof.
    intros C D F G a assC assD passF passG.
    exact unit.
  Defined.

  Definition bidisp_ass_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells tu_cat
    := (disp_ass_disp_cat_data,, bidisp_ass_disp_2cell_struct).

  Definition bidisp_ass_disp_prebicat_ops : disp_prebicat_ops bidisp_ass_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat (use tpair ; intros ; try (exact tt)).
    intros C D E W F G H IC ID IE IW puF puG puH.
    exact tt.
  Qed.

  Definition bidisp_ass_disp_prebicat_data : disp_prebicat_data tu_cat
    := (bidisp_ass_disp_prebicat_1_id_comp_cells,, bidisp_ass_disp_prebicat_ops).

  Definition bidisp_ass_disp_prebicat_laws : disp_prebicat_laws bidisp_ass_disp_prebicat_data.
  Proof.
    repeat split; intro; intros; apply isapropunit.
  Qed.

  Definition bidisp_ass_disp_prebicat : disp_prebicat tu_cat
    := (bidisp_ass_disp_prebicat_data,,bidisp_ass_disp_prebicat_laws).

  Definition bidisp_ass_disp_bicat : disp_bicat tu_cat.
  Proof.
    refine (bidisp_ass_disp_prebicat,, _).
    intros C D F G α assC assD passF passG.
    apply isasetunit.
  Defined.

  Lemma bidisp_ass_disp_prebicat_is_locally_univalent : disp_univalent_2_1 bidisp_ass_disp_bicat.
  Proof.
    intros C D F G pfFisG assF assG passF passG.
    induction pfFisG.
    apply isweqimplimpl.
    - intros α.
      apply isaprop_preserves_associator.
    - apply isasetaprop.
      apply isaprop_preserves_associator.
    - apply invproofirrelevance.
      intro ; intro.
      use subtypePath.
      + intro x0.
        apply isaprop_is_disp_invertible_2cell.
      + apply isapropunit.
  Qed.

  Definition ass_equal {C : tu_cat} (ass1 ass2 : bidisp_ass_disp_bicat C) : UU
    := ∏ x y z : (pr1 C : univalent_category), (pr1 ass1) x y z = (pr1 ass2) x y z.

  Definition disp_adj_equiv_to_ass_equal {C : tu_cat} (ass1 ass2 : bidisp_ass_disp_bicat C)
    : disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) ass1 ass2 -> ass_equal ass1 ass2.
  Proof.
    intro dae.
    intros x y z.
    induction dae as [pass [adj_data [adj_ax adj_eq]]].
    induction adj_data as [inv [unit counit]].
    cbn in *.

    set (p := pass x y z).
    cbn in p.
    unfold identityfunctor_preserves_tensor_data in p.
    rewrite id_right in p.
    rewrite id_right in p.
    rewrite tensor_id in p.
    rewrite id_left in p.
    rewrite tensor_id in p.
    rewrite id_right in p.
    exact p.
  Defined.

  Definition ass_equal_to_disp_adj_equiv {C : tu_cat} (ass1 ass2 : bidisp_ass_disp_bicat C)
    : ass_equal ass1 ass2 -> disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) ass1 ass2.
  Proof.
    intro asse.
    use tpair.
    - intros x y z.
      etrans. {
        apply cancel_postcomposition.
        apply cancel_postcomposition.
        apply tensor_id.
      }
      etrans. {
        apply cancel_postcomposition.
        apply id_left.
      }
      cbn.
      unfold identityfunctor_preserves_tensor_data.

      etrans. { apply id_left. }
      apply pathsinv0.

      etrans. {
        apply cancel_postcomposition.
        apply cancel_precomposition.
        apply tensor_id.
      }
      etrans. {
        apply id_right.
      }
      etrans. {
        apply id_right.
      }
      exact (! asse x y z).
    - use tpair.
      + (* data *)
        repeat (use tpair).
        * intros x y z.

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
          apply pathsinv0.

          etrans. {
            apply cancel_postcomposition.
            apply cancel_precomposition.
            apply tensor_id.
          }
          etrans. {
            apply id_right.
          }
          etrans. {
            apply id_right.
          }
          exact (asse x y z).
        * exact tt.
        * exact tt.
      + (* axioms *)
        use tpair.
        -- split; apply isapropunit.
        -- split; (use tpair; [exact tt | split; apply isapropunit]).
  Defined.

  Definition disp_adj_equiv_equivalence_ass_equal {C : tu_cat} (ass1 ass2 : bidisp_ass_disp_bicat C)
    : ass_equal ass1 ass2 ≃ disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) ass1 ass2.
  Proof.
    use make_weq.
    - intro asse.
      exact (ass_equal_to_disp_adj_equiv _ _ asse).
    - use isweq_iso.
      + intro dae.
        exact (disp_adj_equiv_to_ass_equal _ _ dae).
      + intro asse.
        repeat (use funextsec ; intro).
        apply univalent_category_has_homsets.
      + intro dae.
        use subtypePath.
        * intro.
          apply isaprop_disp_left_adjoint_equivalence.
          apply bidisp_tensorunit_is_univalent_2.
          apply bidisp_ass_disp_prebicat_is_locally_univalent.
        * repeat (use funextsec ; intro).
          apply univalent_category_has_homsets.
  Defined.

  Definition ass_equal_to_equal {C : tu_cat} (ass1 ass2 : bidisp_ass_disp_bicat C)
    : ass_equal ass1 ass2 → ass1 = ass2.
  Proof.
    intro asse.
    use total2_paths_f.
    - repeat (apply funextsec ; intro).
      apply asse.
    - repeat (apply funextsec ; intro).
      apply univalent_category_has_homsets.
  Defined.

  Definition equal_to_ass_equal {C : tu_cat} (ass1 ass2 : bidisp_ass_disp_bicat C)
    : ass1 = ass2 -> ass_equal ass1 ass2.
  Proof.
    intro asse.
    induction asse.
    intros x y z.
    apply idpath.
  Defined.

  Definition ass_equal_equivalent_equal {C : tu_cat} (ass1 ass2 : bidisp_ass_disp_bicat C)
    : ass1 = ass2 ≃ ass_equal ass1 ass2.
  Proof.
    use make_weq.
    - intro asse.
      exact (equal_to_ass_equal _ _ asse).
    - use isweq_iso.
      + intro asse.
        exact (ass_equal_to_equal _ _ asse).
      + intro asse.
        induction asse.
        use pathscomp0.
        3: {
          apply total2_paths_idpath.
        }
        unfold ass_equal_to_equal.
        unfold equal_to_ass_equal.

        apply maponpaths_total.
        * apply (cancellation_lemma _ _ _ (toforallpaths _ (pr1 ass1) (pr1 ass1))).
          -- intro p.
             apply funextsec_toforallpaths.
          -- etrans. { apply toforallpaths_funextsec. }
             apply funextsec ; intro x.
             apply (cancellation_lemma _ _ _ (toforallpaths _ (pr1 ass1 x) (pr1 ass1 x))).
             ++ intro p.
                apply funextsec_toforallpaths.
             ++ etrans. { apply toforallpaths_funextsec. }
                apply funextsec ; intro y.
                apply (cancellation_lemma _ _ _ (toforallpaths _ (pr1 ass1 x y) (pr1 ass1 x y))).
                ** intro p.
                   apply funextsec_toforallpaths.
                ** etrans. { apply toforallpaths_funextsec. }
                   apply funextsec ; intro z.
                   apply idpath.
        * intro l.
          unfold associator_nat.
          repeat (apply impred_isaset ; intro).
          apply isasetaprop.
          apply homset_property.
      + intro asse.
        repeat (apply funextsec ; intro).
        apply univalent_category_has_homsets.
  Defined.

  Lemma bidisp_ass_disp_prebicat_is_globally_univalent : disp_univalent_2_0 bidisp_ass_disp_bicat.
  Proof.
    intros C D equalcats assC assD.
    induction equalcats.
    use weqhomot.
    - (* rewrite idpath_transportf. *)
      set (i1 := ass_equal_equivalent_equal assC assD).
      set (i2 := disp_adj_equiv_equivalence_ass_equal assC assD).
      exact (i2 ∘ i1)%weq.
    - intro p.
      induction p ; cbn.
      use subtypePath.
      + intro ; simpl.
        apply (@isaprop_disp_left_adjoint_equivalence _  bidisp_ass_disp_bicat).
        * apply bidisp_tensorunit_is_univalent_2.
        * exact bidisp_ass_disp_prebicat_is_locally_univalent.
      + repeat (apply funextsec ; intro).
        apply univalent_category_has_homsets.
  Qed.

  Lemma bidisp_ass_disp_prebicat_is_univalent_2 : disp_univalent_2 bidisp_ass_disp_bicat.
  Proof.
    apply make_disp_univalent_2.
    - apply bidisp_ass_disp_prebicat_is_globally_univalent.
    - apply bidisp_ass_disp_prebicat_is_locally_univalent.
  Defined.

End AssociatorLayer.
