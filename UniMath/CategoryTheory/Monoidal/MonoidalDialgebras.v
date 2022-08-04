Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalSectionsWhiskered.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section FixTwoMonoidalFunctors.

  Import BifunctorNotations.
  Import MonoidalNotations.
  Import DisplayedBifunctorNotations.
  Import DisplayedMonoidalNotations.

  Context {A B : category}
          {V : monoidal A} {W : monoidal B}
          {F G : A ⟶ B}
          (Fm : fmonoidal V W F) (Gm : fmonoidal_lax V W G).

  Local Definition base_disp : disp_cat A := dialgebra_disp_cat F G.

  Local Lemma base_disp_cells_isaprop (x y : A) (f : A⟦ x, y ⟧)
        (xx : base_disp x) (yy : base_disp y): isaprop (xx -->[ f] yy).
  Proof.
    intros Hyp Hyp'.
    apply B.
  Qed.

  Definition dialgebra_disp_tensor_op {a a' : A} (f : base_disp a) (f' : base_disp a') : base_disp (a ⊗_{ V} a').
  Proof.
    refine (_ · fmonoidal_preservestensordata Gm a a').
    refine (pr1 (fmonoidal_preservestensorstrongly Fm a a') · _).
    exact (f ⊗^{W} f').
  Defined.

  Lemma dialgebra_disp_tensor_comp_aux1 {a a2 a2' : A} {h': a2 --> a2'}
    (f : base_disp a) (f' : base_disp a2) (g' : base_disp a2')
    : f'-->[h'] g' -> dialgebra_disp_tensor_op f f' -->[ a ⊗^{V}_{l} h' ] dialgebra_disp_tensor_op f g'.
  Proof.
    intro Hyp'.
    cbn in Hyp'.
    cbn. unfold dialgebra_disp_tensor_op.
    etrans.
    { repeat rewrite assoc'. do 2 apply maponpaths. apply pathsinv0, fmonoidal_preservestensornatleft. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    { rewrite bifunctor_equalwhiskers. unfold functoronmorphisms2.
      repeat rewrite assoc'.
      do 2 apply maponpaths.
      apply bifunctor_equalwhiskers. }
    rewrite bifunctor_equalwhiskers.
    unfold functoronmorphisms2.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    assert (aux := fmonoidal_preservestensornatleft Fm a a2 a2' h').
    apply (z_iso_inv_on_right _ _ _ (_,,fmonoidal_preservestensorstrongly Fm a a2)) in aux.
    rewrite assoc in aux.
    apply pathsinv0 in aux.
    apply (z_iso_inv_on_left _ _ _ _ (_,,fmonoidal_preservestensorstrongly Fm a a2')) in aux.
    etrans.
    2: { apply cancel_postcomposition.
         apply aux. }
    clear aux.
    do 2 rewrite assoc'.
    apply maponpaths.
    do 2 rewrite <- bifunctor_leftcomp.
    apply maponpaths.
    exact Hyp'.
  Qed.

  Lemma dialgebra_disp_tensor_comp_aux2 {a1 a1' a : A} {h: a1 --> a1'}
    (f : base_disp a1) (f' : base_disp a) (g : base_disp a1')
    : f -->[h] g -> dialgebra_disp_tensor_op f f' -->[ h ⊗^{V}_{r} a ] dialgebra_disp_tensor_op g f'.
  Proof.
    intro Hyp.
    cbn in Hyp.
    cbn. unfold dialgebra_disp_tensor_op.
    etrans.
    { repeat rewrite assoc'. do 2 apply maponpaths. apply pathsinv0, fmonoidal_preservestensornatright. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    { unfold functoronmorphisms1.
      repeat rewrite assoc'.
      do 2 apply maponpaths.
      apply pathsinv0, bifunctor_equalwhiskers. }
    unfold functoronmorphisms1.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    assert (aux := fmonoidal_preservestensornatright Fm _ _ a h).
    apply (z_iso_inv_on_right _ _ _ (_,,fmonoidal_preservestensorstrongly Fm a1 a)) in aux.
    rewrite assoc in aux.
    apply pathsinv0 in aux.
    apply (z_iso_inv_on_left _ _ _ _ (_,,fmonoidal_preservestensorstrongly Fm a1' a)) in aux.
    etrans.
    2: { apply cancel_postcomposition.
         apply aux. }
    clear aux.
    do 2 rewrite assoc'.
    apply maponpaths.
    do 2 rewrite <- bifunctor_rightcomp.
    apply maponpaths.
    exact Hyp.
  Qed.

  (** the following "morally right" formulation does not follow the division into the two whiskerings
  Lemma dialgebra_disp_tensor_comp_aux {a1 a2 a1' a2' : A} {h: a1 --> a1'} {h': a2 --> a2'}
    (f : base_disp a1) (f' : base_disp a2) (g : base_disp a1') (g' : base_disp a2')
    : f -->[h] g -> f'-->[h'] g' -> dialgebra_disp_tensor_op f f' -->[ h ⊗^{V} h' ] dialgebra_disp_tensor_op g g'.
  Proof.
    intros Hyp Hyp'.
    hnf in Hyp, Hyp' |- *.
    unfold dialgebra_disp_tensor_op.
    *)

  Definition dialgebra_disp_tensor : disp_tensor base_disp V.
  Proof.
    use make_disp_bifunctor.
    - use make_disp_bifunctor_data.
      + intros a a' f f'. exact (dialgebra_disp_tensor_op f f').
      + intros; apply dialgebra_disp_tensor_comp_aux1; assumption.
      + intros; apply dialgebra_disp_tensor_comp_aux2; assumption.
    - red. repeat split; red; intros; apply base_disp_cells_isaprop.
  Defined.

  Definition dialgebra_disp_unit: base_disp I_{ V}
    := pr1 (fmonoidal_preservesunitstrongly Fm) · fmonoidal_preservesunit Gm.

  Lemma dialgebra_disp_leftunitor_data : disp_leftunitor_data dialgebra_disp_tensor dialgebra_disp_unit.
  Proof.
    intros a f.
    cbn. unfold dialgebra_disp_unit, dialgebra_disp_tensor_op.
    rewrite bifunctor_equalwhiskers. unfold functoronmorphisms2.
    rewrite bifunctor_rightcomp.
    set (aux1 := fmonoidal_preservesleftunitality Gm a).
    etrans.
    { repeat rewrite assoc'. do 3 apply maponpaths.
      rewrite assoc.
      exact aux1. }
    clear aux1.
    apply (z_iso_inv_on_right _ _ _ (_,,fmonoidal_preservestensorstrongly Fm I_{V} a)).
    cbn.
    set (aux2 := fmonoidal_preservesleftunitality Fm a).
    etrans.
    { rewrite assoc. apply cancel_postcomposition.
      apply pathsinv0, bifunctor_equalwhiskers. }
    unfold functoronmorphisms1.
    rewrite assoc'.
    etrans.
    { apply maponpaths.
      apply monoidal_leftunitornat. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    rewrite <- aux2. clear aux2.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    rewrite <- bifunctor_rightcomp.
    etrans.
    { apply cancel_postcomposition.
      apply maponpaths.
      apply  (z_iso_after_z_iso_inv (_,,fmonoidal_preservesunitstrongly Fm)). }
    rewrite bifunctor_rightid.
    apply id_left.
  Qed.

  Lemma dialgebra_disp_leftunitorinv_data : disp_leftunitorinv_data dialgebra_disp_tensor dialgebra_disp_unit.
  Proof.
  Admitted.

  Lemma dialgebra_disp_rightunitor_data : disp_rightunitor_data dialgebra_disp_tensor dialgebra_disp_unit.
  Proof.
  Admitted.

  Lemma dialgebra_disp_rightunitorinv_data : disp_rightunitorinv_data dialgebra_disp_tensor dialgebra_disp_unit.
  Proof.
  Admitted.

  Lemma dialgebra_disp_associator_data : disp_associator_data dialgebra_disp_tensor.
  Proof.
  Admitted.

  Lemma dialgebra_disp_associatorinv_data : disp_associatorinv_data dialgebra_disp_tensor.
  Proof.
  Admitted.

  Definition dialgebra_disp_monoidal_data : disp_monoidal_data base_disp V.
  Proof.
    exists dialgebra_disp_tensor.
    exists dialgebra_disp_unit.
    exists dialgebra_disp_leftunitor_data.
    exists dialgebra_disp_leftunitorinv_data.
    exists dialgebra_disp_rightunitor_data.
    exists dialgebra_disp_rightunitorinv_data.
    exists dialgebra_disp_associator_data.
    exact dialgebra_disp_associatorinv_data.
  Defined.

  Lemma dialgebra_disp_leftunitor_law :
    disp_leftunitor_law dlu^{ dialgebra_disp_monoidal_data} dluinv^{ dialgebra_disp_monoidal_data}.
  Proof.
    repeat (split; try (red; intros; apply base_disp_cells_isaprop)); try apply base_disp_cells_isaprop.
  Qed.

  Lemma dialgebra_disp_rightunitor_law :
    disp_rightunitor_law dru^{ dialgebra_disp_monoidal_data} druinv^{ dialgebra_disp_monoidal_data}.
  Proof.
    repeat (split; try (red; intros; apply base_disp_cells_isaprop)); try apply base_disp_cells_isaprop.
  Qed.

  Lemma dialgebra_disp_associator_law :
    disp_associator_law dα^{ dialgebra_disp_monoidal_data} dαinv^{ dialgebra_disp_monoidal_data}.
  Proof.
    repeat (split; try (red; intros; apply base_disp_cells_isaprop)); try apply base_disp_cells_isaprop.
  Qed.

  Definition dialgebra_disp_monoidal : disp_monoidal base_disp V.
  Proof.
    exists dialgebra_disp_monoidal_data.
    split.
    exact dialgebra_disp_leftunitor_law.
    split; [ exact dialgebra_disp_rightunitor_law |].
    split; [ exact dialgebra_disp_associator_law |].
    (** now we benefit from working in a displayed monoidal category *)
    split; red; intros; apply base_disp_cells_isaprop.
  Defined.

  Definition dialgebra_monoidal : monoidal (dialgebra F G) := total_monoidal dialgebra_disp_monoidal.


  Section IntoMonoidalSection.

    Context (α : F ⟹ G).

    Definition is_mon_nat_trans : UU :=
      (∏ (a a' : A), fmonoidal_preservestensordata Fm a a' · α (a ⊗_{V} a') = α a ⊗^{W} α a' · fmonoidal_preservestensordata Gm a a') × fmonoidal_preservesunit Fm · α I_{V} = fmonoidal_preservesunit Gm.

    Context (ismnt : is_mon_nat_trans).

    Let ismnt_tensor := pr1 ismnt.
    Let ismnt_unit := pr2 ismnt.

    Lemma monnattrans_to_monoidal_section_data :
      smonoidal_data V dialgebra_disp_monoidal (nat_trans_to_section F G α).
    Proof.
      split.
      - intros a a'. cbn. unfold dialgebra_disp_tensor_op.
        do 2 rewrite functor_id. rewrite id_left, id_right.
        rewrite assoc'. rewrite <- ismnt_tensor.
        rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          apply  (z_iso_after_z_iso_inv (_,,fmonoidal_preservestensorstrongly Fm a a')).
        }
        apply id_left.
      - cbn. unfold dialgebra_disp_unit.
        do 2 rewrite functor_id. rewrite id_left, id_right.
        cbn in ismnt_unit.
        rewrite <- ismnt_unit.
        rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          apply  (z_iso_after_z_iso_inv (_,,fmonoidal_preservesunitstrongly Fm)). }
        apply id_left.
    Qed.

    Lemma monnattrans_to_monoidal_section_laws :
      smonoidal_laxlaws V dialgebra_disp_monoidal monnattrans_to_monoidal_section_data.
      Proof.
        repeat split; red; intros; apply base_disp_cells_isaprop.
      Qed.

    Lemma monnattrans_to_monoidal_section_strongtensor :
      smonoidal_strongtensor V dialgebra_disp_monoidal
      (smonoidal_preserves_tensor V dialgebra_disp_monoidal monnattrans_to_monoidal_section_data).
    Proof.
      intros a a'.
      use tpair.
      - cbn. unfold dialgebra_disp_tensor_op. apply pathsinv0.
        (* now as for [monnattrans_to_monoidal_section_data] *)
        do 2 rewrite functor_id. rewrite id_left, id_right.
        rewrite assoc'. rewrite <- ismnt_tensor.
        rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          apply (z_iso_after_z_iso_inv (_,,fmonoidal_preservestensorstrongly Fm a a')).
        }
        apply id_left.
      - split; apply base_disp_cells_isaprop.
    Qed.

    Lemma monnattrans_to_monoidal_section_strongunit :
      smonoidal_strongunit V dialgebra_disp_monoidal
      (smonoidal_preserves_unit V dialgebra_disp_monoidal monnattrans_to_monoidal_section_data).
    Proof.
      use tpair.
      - cbn. unfold dialgebra_disp_unit.
        do 2 rewrite functor_id. rewrite id_left, id_right.
        cbn in ismnt_unit.
        rewrite <- ismnt_unit.
        rewrite assoc. apply pathsinv0.
        etrans.
        { apply cancel_postcomposition.
          apply  (z_iso_after_z_iso_inv (_,,fmonoidal_preservesunitstrongly Fm)). }
        apply id_left.
      - split; apply base_disp_cells_isaprop.
    Qed.

    Definition monnattrans_to_monoidal_section :
      smonoidal V dialgebra_disp_monoidal (nat_trans_to_section F G α).
    Proof.
      use tpair.
      - exact (monnattrans_to_monoidal_section_data,,monnattrans_to_monoidal_section_laws).
      - split.
        + exact monnattrans_to_monoidal_section_strongtensor.
        + exact monnattrans_to_monoidal_section_strongunit.
    Defined.

  End IntoMonoidalSection.

  Section FromMonoidalSection.

    Context (sd: section_disp (dialgebra_disp_cat F G)).
    Context (ms: smonoidal_data V dialgebra_disp_monoidal sd).

    Definition nattrans_from_ms : F ⟹ G := section_to_nat_trans F G sd.

    Lemma nattrans_from_ms_is_mon_nat_trans : is_mon_nat_trans nattrans_from_ms.
    Proof.
      split.
      - intros a a'.
        assert (aux := smonoidal_preserves_tensor _ _ ms a a').
        cbn in aux.
        unfold dialgebra_disp_tensor_op in aux.
        do 2 rewrite functor_id in aux.
        rewrite id_left, id_right in aux.
        unfold nattrans_from_ms.
        cbn.
        etrans.
        { apply maponpaths.
          apply pathsinv0, aux. }
        repeat rewrite assoc.
        apply cancel_postcomposition.
        etrans.
        { apply cancel_postcomposition.
          apply (z_iso_inv_after_z_iso (_,,fmonoidal_preservestensorstrongly Fm a a')). }
        apply id_left.
      - cbn.
        assert (aux := smonoidal_preserves_unit _ _ ms).
        cbn in aux.
        unfold dialgebra_disp_unit in aux.
        do 2 rewrite functor_id in aux.
        rewrite id_left, id_right in aux.
        etrans.
        { apply maponpaths.
          apply pathsinv0, aux. }
        rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          apply (z_iso_inv_after_z_iso (_,,fmonoidal_preservesunitstrongly Fm)). }
        apply id_left.
    Qed.

  End FromMonoidalSection.

  Section RoundtripForSDData.

      Local Definition source_type: UU := ∑ α : F ⟹ G, is_mon_nat_trans α.
      Local Definition target_type: UU := ∑ sd: section_disp (dialgebra_disp_cat F G),
            smonoidal_data V dialgebra_disp_monoidal sd.

      Local Definition source_to_target : source_type -> target_type.
      Proof.
        intro ass. destruct ass as [α ismnt].
        exists (nat_trans_to_section F G α).
        exact (monnattrans_to_monoidal_section_data α ismnt).
      Defined.

      Local Definition target_to_source : target_type -> source_type.
      Proof.
        intro ass. destruct ass as [sd ms].
        exists (nattrans_from_ms sd).
        exact (nattrans_from_ms_is_mon_nat_trans sd ms).
      Defined.

      Local Lemma roundtrip1 (ass: source_type): target_to_source (source_to_target ass) = ass.
      Proof.
        destruct ass as [α [ismnt_tensor ismnt_unit]].
        use total2_paths_f.
        - cbn.
          unfold nattrans_from_ms.
          apply UniMath.CategoryTheory.categories.Dialgebras.roundtrip1_with_sections.
        - cbn.
          match goal with |- @paths ?ID _ _ => set (goaltype := ID); simpl in goaltype end.
          assert (Hprop: isaprop goaltype).
          2: { apply Hprop. }
          apply isapropdirprod.
          + apply impred. intro a.
            apply impred. intro a'.
            apply B.
          + apply B.
      Qed.

      Local Lemma roundtrip2 (ass: target_type): source_to_target (target_to_source ass) = ass.
      Proof.
        destruct ass as [sd ms].
        use total2_paths_f.
        - cbn.
          unfold nattrans_from_ms.
          apply UniMath.CategoryTheory.categories.Dialgebras.roundtrip2_with_sections.
        - cbn.
          match goal with |- @paths ?ID _ _ => set (goaltype := ID); simpl in goaltype end.
          assert (Hprop: isaprop goaltype).
          2: { apply Hprop. }
          apply isapropdirprod.
          + unfold section_preserves_tensor_data.
            apply impred. intro a.
            apply impred. intro a'.
            apply base_disp_cells_isaprop.
          + unfold section_preserves_unit.
            apply base_disp_cells_isaprop.
      Qed.

    End RoundtripForSDData.

End FixTwoMonoidalFunctors.
