Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.Bicategories.Core.Bicat.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesReordered.

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.CurriedMonoidalCategories.

Import BifunctorNotations.

Section TensorEquivalence.

  Local Definition ctensor (C : category) := CurriedMonoidalCategories.tensor C.
  Identity Coercion ctensor_to_tensor: ctensor >-> CurriedMonoidalCategories.tensor.
  Local Definition wtensor (C : category) := MonoidalCategoriesWhiskered.tensor C.
  Identity Coercion wtensor_to_tensor: wtensor >-> MonoidalCategoriesWhiskered.tensor.

  Context {C : category}.

  Definition wtensor_to_ctensor (T : wtensor C)
    : ctensor C.
  Proof.
    repeat (use tpair).
    - apply T.
    - intros x1 x2 y1 y2 f g.
      exact (f ⊗^{T} g).
    - intros x y.
      apply (bifunctor_distributes_over_id
               (C := C)
               (bifunctor_leftid T)
               (bifunctor_rightid T)
            ).
    - intros x1 x2 x3 y1 y2 y3 f1 f2 g1 g2.
      apply (bifunctor_distributes_over_comp
               (C := C)
               (bifunctor_leftcomp T)
               (bifunctor_rightcomp T)
               (bifunctor_equalwhiskers T)
            ).
  Defined.

  Definition ctensor_to_wtensor (T : ctensor C)
    : wtensor C.
  Proof.
    repeat (use tpair).
    - apply T.
    - intros x ? ? g.
      exact ((tensor_on_hom (pr1 T)) _ _ _ _ (identity x) g).
    - intros y ? ? f.
      exact ((tensor_on_hom (pr1 T)) _ _ _ _ f (identity y)).
    - intro ; intro.
      apply tensor_id.
    - intro ; intro.
      apply tensor_id.
    - intro ; intros.
      use pathscomp0.
      3: apply tensor_comp.
      rewrite id_right.
      apply idpath.
    - intro ; intros.
      use pathscomp0.
      3: apply tensor_comp.
      rewrite id_right.
      apply idpath.
    - intros ? ? ? ? f g.
      use pathscomp0.
      3: apply tensor_comp.
      rewrite id_right.
      rewrite id_left.
      etrans. {
        apply (! tensor_comp _ _ _ _ _ _ _ _ _ _ _).
      }
      rewrite id_right.
      apply maponpaths.
      apply id_left.
  Defined.

  (* Lemma transport_of_right_partial_bifunctor_map_is_pointwise
      {F0 G0 : ob C -> ob C -> ob C}
      (F1 : ∏ y x1 x2 : ob C, C⟦x1,x2⟧ -> C⟦F0 x1 y, F0 x2 y⟧)
      (gamma : F0  = G0)
      {x1 x2 : ob C} (y : C) (f : C⟦x1,x2⟧) :
  transportf (fun T : C -> C -> C =>
                ∏ b a1 a2 : C, C⟦a1,a2⟧ -> C⟦T a1 b, T a2 b⟧)
             gamma F1 y x1 x2 f =
    double_transport
      (toforallpaths (λ _ : ob C, C) (F0 x1) (G0 x1) (toforallpaths (λ _ : ob C, C -> C) F0 G0 gamma x1) y)
      (toforallpaths (λ _ : ob C, C) (F0 x2) (G0 x2) (toforallpaths (λ _ : ob C, C -> C) F0 G0 gamma x2) y)
                   (F1 _ _ _ f).
  Proof.
    induction gamma.
    apply idpath.
  Qed.

  Lemma transport_of_left_partial_bifunctor_map_is_pointwise
      {F0 G0 : ob C -> ob C -> ob C}
      (F1 : ∏ x y1 y2 : ob C, C⟦y1,y2⟧ -> C⟦F0 x y1, F0 x y2⟧)
      (gamma : F0  = G0)
      {y1 y2 : ob C} (x : C) (g : C⟦y1,y2⟧) :
  transportf (fun T : C -> C -> C =>
                ∏ a b1 b2 : C, C⟦b1,b2⟧ -> C⟦T a b1, T a b2⟧)
             gamma F1 x y1 y2 g =
    double_transport
      (toforallpaths (λ _ : ob C, C) (F0 x) (G0 x) (toforallpaths (λ _ : ob C, C -> C) F0 G0 gamma x) y1)
      (toforallpaths (λ _ : ob C, C) (F0 x) (G0 x) (toforallpaths (λ _ : ob C, C -> C) F0 G0 gamma x) y2)
                   (F1 x y1 y2 g).
  Proof.
    induction gamma.
    apply idpath.
  Qed. *)

  Definition w_c_wtensor (T : wtensor C)
    : ctensor_to_wtensor (wtensor_to_ctensor T) = T.
  Proof.
    repeat (use total2_paths_f) ; try (repeat (apply impred_isaprop ; intro) ; apply homset_property).
    - apply idpath.
    - abstract (rewrite idpath_transportf ;
      repeat (apply funextsec ; intro) ;
      simpl ;
      unfold functoronmorphisms1 ;
      rewrite bifunctor_rightid ;
      apply id_left).
    - rewrite pr2_transportf.
      rewrite (idpath_transportf ((λ a : C → C → C, ∏ b a1 a2 : C, C ⟦ a1, a2 ⟧ → C ⟦ a a1 b, a a2 b ⟧))).
      repeat (apply funextsec ; intro).
      rewrite transportf_const.
      simpl.
      unfold functoronmorphisms1.
      rewrite bifunctor_leftid.
      apply id_right.
  Qed.

  Definition c_w_ctensor (T : ctensor C)
    : wtensor_to_ctensor (ctensor_to_wtensor T) = T.
  Proof.
    repeat (use total2_paths_f).
    - apply idpath.
    - rewrite idpath_transportf.
      repeat (apply funextsec ; intro).
      refine ((! pr22 T _ _ _ _ _ _ _ _ _ _) @ _).
      rewrite id_right.
      apply maponpaths.
      apply id_left.
    - repeat (apply impred_isaprop ; intro).
      apply homset_property.
    - repeat (apply impred_isaprop ; intro).
      apply homset_property.
  Qed.

  Definition tensor_equivalence
    : ctensor C ≃ wtensor C.
  Proof.
    use weq_iso.
    - apply ctensor_to_wtensor.
    - apply wtensor_to_ctensor.
    - intro. apply c_w_ctensor.
    - intro. apply w_c_wtensor.
  Defined.

End TensorEquivalence.

Section MonoidalCategoryEquivalence.

  Definition tensor_unit_equivalence (C : category)
    : CurriedMonoidalCategories.tensor_unit C ≃ MonoidalCategoriesReordered.tensor_unit C.
  Proof.
    apply weqtotal2.
    - apply tensor_equivalence.
    - intro.
      apply idweq.
  Defined.

  Definition tensor_unit_unitors_associator_equivalence (C : category)
    :  CurriedMonoidalCategories.tensor_unit_unitors_associator C ≃ MonoidalCategoriesReordered.tensor_unit_unitors_associator C.
  Proof.
    use weqtotal2.
    { exact (tensor_unit_equivalence C). }
    intro tu.
    repeat (use weqdirprodf) ; apply idweq.
    use weqtotal2.
    { apply idweq. }
    intro α.
    use weq_iso.
    {
      intro αnat.
      repeat split.
      - intros x y z1 z2 h.
        refine (αnat x x y y z1 z2 (identity x) (identity y) h @ _).
        apply cancel_postcomposition.
        rewrite tensor_id.
        apply idpath.
      - intros x1 x2 y z f.
        refine (_ @ αnat x1 x2 y y z z f (identity y) (identity z)).
        apply cancel_precomposition.
        rewrite tensor_id.
        apply idpath.
      - intros x y1 y2 z g.
        apply (αnat x x y1 y2 z z (identity x) g (identity z)).
    }
    {
      intro αnat.
      intro ; intros.
      refine (_ @ (associator_nat2 (pr1 αnat) (pr12 αnat) (pr22 αnat) f g h) @ _).
      - simpl.
        unfold functoronmorphisms1.
        apply cancel_precomposition.

        etrans.
        2: {
          apply maponpaths.
          apply maponpaths.
          apply tensor_comp.
        }
        rewrite id_left.
        rewrite id_right.

        refine (_ @ tensor_comp _ _ _ _ _ _ _ _ _ _ _).
        rewrite id_right.
        apply maponpaths.
        apply (! id_left _).
      - simpl.
        unfold functoronmorphisms1.
        apply cancel_postcomposition.
        cbn.


        etrans. {
          apply cancel_postcomposition.
          apply maponpaths_2.
          apply (! tensor_comp _ _ _ _ _ _ _ _ _ _ _).
        }
        rewrite id_right.
        rewrite id_left.
        etrans. {
          apply (! tensor_comp _ _ _ _ _ _ _ _ _ _ _).
        }
        rewrite id_right.
        apply maponpaths.
        apply id_left.
    }
    {
      intro.
      repeat (apply funextsec ; intro).
      apply homset_property.
    }
    intro.
    assert (q : isaprop (associator_nat_leftwhisker
        (idweq (MonoidalCategoriesWhiskered.associator_data (tensor_unit_equivalence C tu)) α)
      × associator_nat_rightwhisker
          (idweq (MonoidalCategoriesWhiskered.associator_data (tensor_unit_equivalence C tu)) α)
        × associator_nat_leftrightwhisker
        (idweq (MonoidalCategoriesWhiskered.associator_data (tensor_unit_equivalence C tu)) α))).
    {
      repeat (apply isapropdirprod) ; repeat (apply impred_isaprop ; intro) ; apply homset_property.
    }
    apply q.
  Defined.

  Lemma isaprop_lax_monoidal_leftunitor_inverse {C : category}
        (luua :  MonoidalCategoriesReordered.tensor_unit_unitors_associator C)
    : isaprop (lax_monoidal_leftunitor_inverse luua).
  Proof.
    apply isaproptotal2.
    {
      intro.
      apply impred_isaprop ; intro.
      apply Isos.isaprop_is_inverse_in_precat.
    }
    intros lui0 lui1 l0 l1.
    apply funextsec ; intro.
    use Isos.inverse_unique_precat.
    - apply luua.
    - apply l0.
    - apply l1.
  Defined.

  Lemma isaprop_lax_monoidal_rightunitor_inverse {C : category}
        (luua :  MonoidalCategoriesReordered.tensor_unit_unitors_associator C)
    : isaprop (lax_monoidal_rightunitor_inverse luua).
  Proof.
    apply isaproptotal2.
    {
      intro.
      apply impred_isaprop ; intro.
      apply Isos.isaprop_is_inverse_in_precat.
    }
    intros lui0 lui1 l0 l1.
    apply funextsec ; intro.
    use Isos.inverse_unique_precat.
    - apply luua.
    - apply l0.
    - apply l1.
  Defined.

  Lemma isaprop_lax_monoidal_associator_inverse {C : category}
        (luua :  MonoidalCategoriesReordered.tensor_unit_unitors_associator C)
    : isaprop (lax_monoidal_associator_inverse luua).
  Proof.
    apply isaproptotal2.
    {
      intro.
      repeat (apply impred_isaprop ; intro).
      apply Isos.isaprop_is_inverse_in_precat.
    }
    intros lui0 lui1 l0 l1.
    repeat (apply funextsec ; intro).
    use Isos.inverse_unique_precat.
    - apply luua.
    - apply l0.
    - apply l1.
  Defined.

  Definition wmon_equivalent_monreorderd (C : category)
    : CurriedMonoidalCategories.mon_structure C ≃ MonoidalCategoriesReordered.monoidal_struct C.
  Proof.
    use weqtotal2.
    { apply tensor_unit_unitors_associator_equivalence. }
    intro.
    repeat (apply weqdirprodf).
    - apply weqimplimpl ; try (intro ; assumption) ; (try apply isaprop_triangle).
    - apply weqimplimpl ; try (intro ; assumption) ; (try apply isaprop_pentagon).
    - use weq_iso.
      + intro lui.
        exists (λ c, pr1 (lui c)).
        intro ; apply lui.
      + intro lui.
        intro c.
        exists ((pr1 lui) c).
        apply ((pr2 lui) c).
      + intro ; apply isaprop_lunitor_invertible.
      + intro ; apply isaprop_lax_monoidal_leftunitor_inverse.
    - use weq_iso.
      + intro rui.
        exists (λ c, pr1 (rui c)).
        intro ; apply rui.
      + intro rui.
        intro c.
        exists ((pr1 rui) c).
        apply ((pr2 rui) c).
      + intro ; apply isaprop_runitor_invertible.
      + intro ; apply isaprop_lax_monoidal_rightunitor_inverse.
    - use weq_iso.
      + intro ai.
        exists (λ c1 c2 c3, pr1 (ai c1 c2 c3)).
        intro ; apply ai.
      + intro ai.
        intros c1 c2 c3.
        exists ((pr1 ai) c1 c2 c3).
        apply ((pr2 ai) c1 c2 c3).
      + intro ; apply isaprop_associator_invertible.
      + intro ; apply isaprop_lax_monoidal_associator_inverse.
  Defined.

End MonoidalCategoryEquivalence.

Section MonoidalFunctorEquivalence.

End MonoidalFunctorEquivalence.

Section StrongMonoidalFunctorEquivalence.

End StrongMonoidalFunctorEquivalence.
