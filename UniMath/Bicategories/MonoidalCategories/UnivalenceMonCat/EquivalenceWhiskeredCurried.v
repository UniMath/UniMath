Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesReordered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.

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

    apply weqimplimpl.
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
      repeat (apply isapropdirprod) ; repeat (apply impred_isaprop ; intro) ; apply homset_property.
    }
    repeat (apply isapropdirprod) ; repeat (apply impred_isaprop ; intro) ; apply homset_property.
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

  Definition cmon_equiv_monreordered (C : category)
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

  Definition cmonoidal_to_cmonoidalreordered
             {C : category} (M : CurriedMonoidalCategories.mon_structure C)
    : MonoidalCategoriesReordered.monoidal_struct C := cmon_equiv_monreordered C M.

  Definition cmonoidal_to_cmonoidalReordered
             {C : category} (M : MonoidalCategoriesReordered.monoidal_struct C)
    : CurriedMonoidalCategories.mon_structure C
    := invmap (cmon_equiv_monreordered C) M.

  Definition cmon_equiv_wmon (C : category)
    : CurriedMonoidalCategories.mon_structure C ≃ MonoidalCategoriesWhiskered.monoidal C
    := (monoidal_struct_equiv_monoidal C ∘ cmon_equiv_monreordered C)%weq.

  Definition cmonoidal_to_wmonoidal
             {C : category} (M : CurriedMonoidalCategories.mon_structure C)
    : MonoidalCategoriesWhiskered.monoidal C := cmon_equiv_wmon C M.

  Definition wmonoidal_to_cmonoidal
             {C : category} (M : MonoidalCategoriesWhiskered.monoidal C)
    : CurriedMonoidalCategories.mon_structure C
    := invmap (cmon_equiv_wmon C) M.

End MonoidalCategoryEquivalence.

Section MonoidalFunctorEquivalence.

  Context {C D : category} (F : functor C D)
          (MC : CurriedMonoidalCategories.mon_structure C)
          (MD : CurriedMonoidalCategories.mon_structure D).

  Definition cmonfunctor : UU := CurriedMonoidalCategories.functor_lax_monoidal F MC MD.
  Definition wmonfunctordata : UU
    := MonoidalFunctorsWhiskered.fmonoidal_data
         (cmonoidal_to_wmonoidal MC)
         (cmonoidal_to_wmonoidal MD)
         F.

  Definition wmonfunctorlaws (MF : wmonfunctordata)
    := MonoidalFunctorsWhiskered.fmonoidal_laxlaws MF.

  Definition wmonfunctor : UU
    := MonoidalFunctorsWhiskered.fmonoidal_lax
         (cmonoidal_to_wmonoidal MC)
         (cmonoidal_to_wmonoidal MD)
         F.

  Definition cmonfunctor_to_wmonfunctordata
    : cmonfunctor -> wmonfunctordata.
  Proof.
    intro cmf.
    split; red; intros; apply cmf.
  Defined.

  Definition cmonfunctor_to_wmonfunctorlaws (cmf : cmonfunctor)
    : wmonfunctorlaws (cmonfunctor_to_wmonfunctordata cmf).
  Proof.
    split.
    - intros x y1 y2 g.
      etrans.
      2: { apply pathsinv0. exact ((pr211 cmf) x x y1 y2 (identity x) g). }
      unfold leftwhiskering_on_morphisms.
      cbn.
      do 2 apply maponpaths_2.
      apply (! functor_id F x).
    - split.
      + intros x1 x2 y f.
        etrans.
        2: { apply pathsinv0. exact (pr211 cmf x1 x2 y y f (identity y)). }
        unfold rightwhiskering_on_morphisms.
        cbn.
        apply maponpaths_2.
        apply maponpaths.
        apply (! functor_id F y).
      + repeat split; red; intros; apply (pr2 cmf).
  Qed.

  Definition cmonfunctor_to_wmonfunctor
    : cmonfunctor -> wmonfunctor
    := (λ cmf, cmonfunctor_to_wmonfunctordata cmf ,, cmonfunctor_to_wmonfunctorlaws cmf).

  Definition wmonfunctor_to_cmontensorunitfunctor
    : wmonfunctor -> functor_tensor_unit MC MD F.
  Proof.
    intro wmf.
    split.
    - exists (pr11 wmf).
      intros x1 x2 y1 y2 f g.

      assert (p0 : #F (tensor_on_hom MC _ _ _ _ f g)
                   = #F (tensor_on_hom MC _ _ _ _ f (identity y1))
                      · #F (tensor_on_hom MC _ _ _ _ (identity x2) g)).
      {
        etrans.
        2: { apply functor_comp. }
        apply maponpaths.
        refine (_ @ tensor_comp _ _ _ _ _ _ _ f (identity x2) (identity y1) g).
        etrans.
        2: { apply maponpaths_2 ; apply (! id_right _). }
        apply maponpaths ; apply (! id_left _).
      }
      etrans. { apply maponpaths ; apply p0. }
      etrans. { apply assoc. }
      etrans. { apply maponpaths_2 ; apply (! pr122 wmf x1 x2 y1 f). }
      etrans. { apply assoc'. }
      etrans. { apply maponpaths ; apply (! pr12 wmf x2 y1 y2 g). }
      etrans. { apply assoc. }
      apply maponpaths_2.
      etrans.
      2: {
        do 2 apply maponpaths.
        apply id_left.
      }
      etrans.
      2: {
        apply maponpaths_2.
        apply maponpaths.
        apply id_right.
      }

      etrans.
      2: {
        apply maponpaths.
        apply (! functor_comp _ _ _).
      }
      etrans.
      2: {
        apply maponpaths_2.
        apply (! functor_comp _ _ _).
      }
      refine (_ @ ! tensor_comp _ _ _ _ _ _ _ _ _ _ _).
      etrans.
      2: {
        apply maponpaths.
        apply maponpaths_2.
        apply (! functor_id _ _).
      }
      apply maponpaths_2.

      etrans.
      2: {
        apply maponpaths.
        apply (! functor_id _ _).
      }
      apply idpath.
    - exact (pr21 wmf).
  Defined.

  Definition wmonfunctor_to_cmonfunctor
    : wmonfunctor -> cmonfunctor.
  Proof.
    intro wmf.
    exists (wmonfunctor_to_cmontensorunitfunctor wmf).
    repeat split ; apply (pr2 wmf).
  Defined.

  Lemma cwcmf (cmf : cmonfunctor)
    : wmonfunctor_to_cmonfunctor (cmonfunctor_to_wmonfunctor cmf) = cmf.
  Proof.
    repeat (use total2_paths_f) ; try (apply idpath) ; try (repeat (apply funextsec ; intro) ; apply homset_property).
    rewrite transportf_const.
    apply idpath.
  Qed.

  Lemma wcwmf (cmf : wmonfunctor)
    : cmonfunctor_to_wmonfunctor (wmonfunctor_to_cmonfunctor cmf) = cmf.
  Proof.
    repeat (use total2_paths_f) ; try (apply idpath) ; try (repeat (apply funextsec ; intro) ; apply homset_property).
  Qed.

  Definition cmonfunctor_equiv_wmonfunctor
    : cmonfunctor ≃ wmonfunctor.
  Proof.
    use weq_iso.
    - apply cmonfunctor_to_wmonfunctor.
    - apply wmonfunctor_to_cmonfunctor.
    - intro ; apply cwcmf.
    - intro ; apply wcwmf.
  Defined.

End MonoidalFunctorEquivalence.

Section StrongMonoidalFunctorEquivalence.

  Context {C D : category} (F : functor C D)
          (MC : CurriedMonoidalCategories.mon_structure C)
          (MD : CurriedMonoidalCategories.mon_structure D).

  Definition csmonfunctor : UU := CurriedMonoidalCategories.functor_strong_monoidal F MC MD.
  Definition wsmonfunctor : UU
    := MonoidalFunctorsWhiskered.fmonoidal
         (cmonoidal_to_wmonoidal MC)
         (cmonoidal_to_wmonoidal MD)
         F.

  Definition csmonfunctor_equiv_wsmonfunctor
    : csmonfunctor ≃ wsmonfunctor.
  Proof.
    unfold csmonfunctor ; unfold wsmonfunctor.
    unfold functor_strong_monoidal ; unfold fmonoidal.
    use weqtotal2.
    { apply cmonfunctor_equiv_wmonfunctor. }
    intro cmf.
    apply weqimplimpl.
    - intro csmf.
      split.
      + do 2 intro ; apply (pr2 csmf).
      + apply (pr1 csmf).
    - intro csmf.
      split.
      + apply (pr2 csmf).
      + do 2 intro ; apply (pr1 csmf).
    - apply isaprop_functor_strong.
    - apply isapropdirprod ; repeat (apply impred_isaprop ; intro) ; apply Isos.isaprop_is_z_isomorphism.
  Defined.

End StrongMonoidalFunctorEquivalence.
