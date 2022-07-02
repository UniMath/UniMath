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

Section Associator.

  Import TensorUnitNotations.

  Local Definition tu_cat := bicatcatstensorunit_total.
  Local Definition uc (C : tu_cat) : univalent_category := pr1 C.

  Definition associator_data (C : tu_cat) : UU
    := ∏ x y z : (uc C), (uc C)⟦(x ⊗_{C} y) ⊗_{C} z, x ⊗_{C} (y ⊗_{C} z)⟧.

  Definition associator_nat {C : tu_cat} (α : associator_data C) : UU
    := ∏ (x x' y y' z z' : uc C), ∏ (f : (uc C)⟦x,x'⟧) (g : (uc C)⟦y,y'⟧) (h : (uc C)⟦z,z'⟧),
       (α x y z)· (f ⊗^{C} (g ⊗^{C} h)) = ((f ⊗^{C} g) ⊗^{C} h) · (α x' y' z').

  Definition associator (C : tu_cat) : UU
    := ∑ α : associator_data C, associator_nat α.

  Definition preserves_associator {C D : tu_cat} (αC : associator C) (αD : associator D) (F : tu_cat⟦C, D⟧) : UU :=  ∏ (x y z : uc C),
      ((pr112 F x y) ⊗^{D} (identity ((pr1 F : functor _ _) z)))
        · (pr112 F (x ⊗_{C} y) z)
        · (functor_on_morphisms (pr1 F : functor _ _) (pr1 αC x y z))
      = (pr1 αD ((pr1 F : functor _ _) x) ((pr1 F : functor _ _) y) ((pr1 F : functor _ _) z))
          · ((identity ((pr1 F : functor _ _) x)) ⊗^{D} (pr112 F y z))
          · (pr112 F x (y ⊗_{C} z)).

  Definition isaprop_preserves_associator {C D : tu_cat} (αC : associator C) (αD : associator D) (F : tu_cat⟦C,D⟧) : isaprop (preserves_associator αC αD F).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply univalent_category_has_homsets.
  Qed.


End Associator.

Section AssociatorLayer.

  Definition catcatsass_disp_ob_mor : disp_cat_ob_mor tu_cat.
  Proof.
    use tpair.
    - exact (λ C, associator C).
    - exact (λ C D αC αD F, preserves_associator αC αD F).
  Defined.

  Definition catcatsass_disp_id_comp : disp_cat_id_comp tu_cat catcatsass_disp_ob_mor.
  Proof.
    use tpair.
    - intros C α.
      intros x y z.
      etrans. {
          apply cancel_postcomposition.
          apply id_right.
      }
      etrans. {
          apply cancel_postcomposition.
          apply tensor_id.
      }
      etrans. {
        apply id_left.
      }

      apply pathsinv0.
      etrans. {
        apply cancel_postcomposition.
        apply cancel_precomposition.
        apply tensor_id.
      }
      etrans. {
        apply cancel_postcomposition.
        apply id_right.
      }
      apply id_right.
    -
      admit.
  Admitted.


  Definition catcatsass_disp_cat_data : disp_cat_data tu_cat
    := (catcatsass_disp_ob_mor,, catcatsass_disp_id_comp).

  Definition bicatcatsass_disp_2cell_struct : disp_2cell_struct catcatsass_disp_cat_data.
  Proof.
    intros C D F G a assC assD passF passG.
    exact unit.
  Defined.

  Definition bicatcatsass_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells tu_cat
    := (catcatsass_disp_cat_data,, bicatcatsass_disp_2cell_struct).

  Definition bicatcatsass_disp_prebicat_ops : disp_prebicat_ops bicatcatsass_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat (use tpair ; intros ; try (exact tt)).
    intros C D E W F G H IC ID IE IW puF puG puH.
    exact tt.
  Qed.

  Definition bicatcatsass_disp_prebicat_data : disp_prebicat_data tu_cat
    := (bicatcatsass_disp_prebicat_1_id_comp_cells,, bicatcatsass_disp_prebicat_ops).

  Definition bicatcatsass_disp_prebicat_laws : disp_prebicat_laws bicatcatsass_disp_prebicat_data.
  Proof.
    repeat split; intro; intros; apply isapropunit.
  Qed.

  Definition bicatcatsass_disp_prebicat : disp_prebicat tu_cat
    := (bicatcatsass_disp_prebicat_data,,bicatcatsass_disp_prebicat_laws).

  Definition bicatcatsass_disp_bicat : disp_bicat tu_cat.
  Proof.
    refine (bicatcatsass_disp_prebicat,, _).
    intros C D F G α assC assD passF passG.
    apply isasetunit.
  Defined.

  Lemma bicatcatsass_disp_prebicat_is_locally_univalent : disp_univalent_2_1 bicatcatsass_disp_bicat.
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

  Definition ass_equal {C : tu_cat} (ass1 ass2 : bicatcatsass_disp_bicat C) : UU
    := ∏ x y z : (pr1 C : univalent_category), (pr1 ass1) x y z = (pr1 ass2) x y z.

  Definition disp_adj_equiv_to_ass_equal {C : tu_cat} (ass1 ass2 : bicatcatsass_disp_bicat C)
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

  Definition ass_equal_to_disp_adj_equiv {C : tu_cat} (ass1 ass2 : bicatcatsass_disp_bicat C)
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

  Definition disp_adj_equiv_equivalence_ass_equal {C : tu_cat} (ass1 ass2 : bicatcatsass_disp_bicat C)
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
          Search (is_univalent_2_1 tu_cat).
          apply bicatcatstensorunit_is_univalent_2.
          apply bicatcatsass_disp_prebicat_is_locally_univalent.
        * repeat (use funextsec ; intro).
          apply univalent_category_has_homsets.
  Defined.

  Definition ass_equal_to_equal {C : tu_cat} (ass1 ass2 : bicatcatsass_disp_bicat C)
    : ass_equal ass1 ass2 → ass1 = ass2.
  Proof.
    intro asse.
    use total2_paths_f.
    - repeat (apply funextsec ; intro).
      apply asse.
    - repeat (apply funextsec ; intro).
      apply univalent_category_has_homsets.
  Defined.

  Definition equal_to_ass_equal {C : tu_cat} (ass1 ass2 : bicatcatsass_disp_bicat C)
    : ass1 = ass2 -> ass_equal ass1 ass2.
  Proof.
    intro asse.
    induction asse.
    intros x y z.
    apply idpath.
  Defined.

  Definition ass_equal_equivalent_equal {C : tu_cat} (ass1 ass2 : bicatcatsass_disp_bicat C)
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

  Lemma bicatcatsass_disp_prebicat_is_globally_univalent : disp_univalent_2_0 bicatcatsass_disp_bicat.
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
        apply (@isaprop_disp_left_adjoint_equivalence _  bicatcatsass_disp_bicat).
        * apply bicatcatstensorunit_is_univalent_2.
        * exact bicatcatsass_disp_prebicat_is_locally_univalent.
      + repeat (apply funextsec ; intro).
        apply univalent_category_has_homsets.
  Qed.

  Lemma bicatcatsass_disp_prebicat_is_univalent_2 : disp_univalent_2 bicatcatsass_disp_bicat.
  Proof.
    apply make_disp_univalent_2.
    - apply bicatcatsass_disp_prebicat_is_globally_univalent.
    - apply bicatcatsass_disp_prebicat_is_locally_univalent.
  Defined.

End AssociatorLayer.
