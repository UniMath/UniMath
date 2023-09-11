(** **********************************************************

Ralph Matthes

August 2022
*)

(** **********************************************************

Contents :

- constructs a displayed monoidal category that is displayed over the dialgebras, its total
  category is called the monoidal dialgebras

 ************************************************************)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.MonoidalSections.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.MonoidalFunctorLifting.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

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
  (** it is expected that [Fm] could just be an oplax monoidal functor *)

  Local Definition base_disp : disp_cat A := dialgebra_disp_cat F G.

  Local Lemma base_disp_cells_isaprop (x y : A) (f : A⟦x, y⟧)
        (xx : base_disp x) (yy : base_disp y): isaprop (xx -->[f] yy).
  Proof.
    intros Hyp Hyp'.
    apply B.
  Qed.

  Definition dialgebra_disp_tensor_op {a a' : A} (f : base_disp a) (f' : base_disp a') : base_disp (a ⊗_{V} a').
  Proof.
    refine (_ · fmonoidal_preservestensordata Gm a a').
    refine (pr1 (fmonoidal_preservestensorstrongly Fm a a') · _).
    exact (f ⊗^{W} f').
  Defined.

  Lemma dialgebra_disp_tensor_comp_aux1 {a a2 a2' : A} {h': a2 --> a2'}
    (f : base_disp a) (f' : base_disp a2) (g' : base_disp a2')
    : f'-->[h'] g' -> dialgebra_disp_tensor_op f f' -->[a ⊗^{V}_{l} h'] dialgebra_disp_tensor_op f g'.
  Proof.
    intro Hyp'.
    cbn in Hyp'.
    cbn. unfold dialgebra_disp_tensor_op.
    etrans.
    { repeat rewrite assoc'. do 2 apply maponpaths. apply pathsinv0, fmonoidal_preservestensornatleft. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    { rewrite (bifunctor_equalwhiskers W). unfold functoronmorphisms2.
      repeat rewrite assoc'.
      do 2 apply maponpaths.
      apply (bifunctor_equalwhiskers W). }
    rewrite (bifunctor_equalwhiskers W).
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
    do 2 rewrite <- (bifunctor_leftcomp W).
    apply maponpaths.
    exact Hyp'.
  Qed.

  Lemma dialgebra_disp_tensor_comp_aux2 {a1 a1' a : A} {h: a1 --> a1'}
    (f : base_disp a1) (f' : base_disp a) (g : base_disp a1')
    : f -->[h] g -> dialgebra_disp_tensor_op f f' -->[h ⊗^{V}_{r} a] dialgebra_disp_tensor_op g f'.
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
      apply pathsinv0, (bifunctor_equalwhiskers W). }
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
    do 2 rewrite <- (bifunctor_rightcomp W).
    apply maponpaths.
    exact Hyp.
  Qed.

  (** the following "morally right" formulation does not follow the division into the two whiskerings
  Lemma dialgebra_disp_tensor_comp_aux {a1 a2 a1' a2' : A} {h: a1 --> a1'} {h': a2 --> a2'}
    (f : base_disp a1) (f' : base_disp a2) (g : base_disp a1') (g' : base_disp a2')
    : f -->[h] g -> f'-->[h'] g' -> dialgebra_disp_tensor_op f f' -->[h ⊗^{V} h'] dialgebra_disp_tensor_op g g'.
  Proof.
    intros Hyp Hyp'.
    hnf in Hyp, Hyp' |- *.
    unfold dialgebra_disp_tensor_op.
    *)

  Definition dialgebra_disp_tensor : disp_tensor base_disp V.
  Proof.
    use make_disp_bifunctor_locally_prop.
    - apply is_locally_propositional_dialgebra_disp_cat.
    - use make_disp_bifunctor_data.
      + intros a a' f f'. exact (dialgebra_disp_tensor_op f f').
      + intros; apply dialgebra_disp_tensor_comp_aux1; assumption.
      + intros; apply dialgebra_disp_tensor_comp_aux2; assumption.
  Defined.

  Definition dialgebra_disp_unit: base_disp I_{ V}
    := pr1 (fmonoidal_preservesunitstrongly Fm) · fmonoidal_preservesunit Gm.

  Lemma dialgebra_disp_leftunitor_data : disp_leftunitor_data dialgebra_disp_tensor dialgebra_disp_unit.
  Proof.
    intros a f.
    cbn. unfold dialgebra_disp_unit, dialgebra_disp_tensor_op.
    rewrite (bifunctor_equalwhiskers W). unfold functoronmorphisms2.
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
      apply pathsinv0, (bifunctor_equalwhiskers W). }
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
    rewrite <- (bifunctor_rightcomp W).
    etrans.
    { apply cancel_postcomposition.
      apply maponpaths.
      apply  (z_iso_after_z_iso_inv (_,,fmonoidal_preservesunitstrongly Fm)). }
    rewrite bifunctor_rightid.
    apply id_left.
  Qed.

  Lemma dialgebra_disp_rightunitor_data : disp_rightunitor_data dialgebra_disp_tensor dialgebra_disp_unit.
  Proof.
    intros a f.
    cbn. unfold dialgebra_disp_unit, dialgebra_disp_tensor_op.
    unfold functoronmorphisms1.
    rewrite (bifunctor_leftcomp W).
    set (aux1 := fmonoidal_preservesrightunitality Gm a).
    etrans.
    { repeat rewrite assoc'. do 3 apply maponpaths.
      rewrite assoc.
      exact aux1. }
    clear aux1.
    apply (z_iso_inv_on_right _ _ _ (_,,fmonoidal_preservestensorstrongly Fm a I_{V})).
    cbn.
    set (aux2 := fmonoidal_preservesrightunitality Fm a).
    etrans.
    { rewrite assoc. apply cancel_postcomposition.
      apply (bifunctor_equalwhiskers W). }
    unfold functoronmorphisms2.
    rewrite assoc'.
    etrans.
    { apply maponpaths.
      apply monoidal_rightunitornat. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    rewrite <- aux2. clear aux2.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    rewrite <- (bifunctor_leftcomp W).
    etrans.
    { apply cancel_postcomposition.
      apply maponpaths.
      apply  (z_iso_after_z_iso_inv (_,,fmonoidal_preservesunitstrongly Fm)). }
    rewrite bifunctor_leftid.
    apply id_left.
  Qed.

  Lemma dialgebra_disp_associator_data : disp_associator_data dialgebra_disp_tensor.
  Proof.
    intros a1 a2 a3 f1 f2 f3.
    cbn. unfold dialgebra_disp_tensor_op.
    etrans.
    { rewrite (bifunctor_equalwhiskers W).
      unfold functoronmorphisms2.
      rewrite bifunctor_rightcomp.
      repeat rewrite assoc'.
      do 3 apply maponpaths.
      rewrite assoc.
      apply fmonoidal_preservesassociativity. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    2: { unfold functoronmorphisms1 at 1.
         rewrite (bifunctor_leftcomp W).
         apply idpath. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    rewrite bifunctor_leftcomp.
    rewrite bifunctor_rightcomp.
    etrans.
    { apply cancel_postcomposition.
      rewrite assoc.
      apply cancel_postcomposition.
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, bifunctor_equalwhiskers. }
    unfold functoronmorphisms1 at 1.
    repeat rewrite assoc'.
    apply (z_iso_inv_on_right _ _ _ (_,,fmonoidal_preservestensorstrongly Fm _ _)).
    cbn.
    transparent assert (aux1 : (z_iso (F (a1 ⊗_{V} a2) ⊗_{W} F a3) ((F a1 ⊗_{W} F a2) ⊗_{W} F a3))).
    { exists (pr1 (fmonoidal_preservestensorstrongly Fm a1 a2) ⊗^{W}_{r} F a3).
      exists (fmonoidal_preservestensordata Fm a1 a2 ⊗^{W}_{r} F a3).
      split.
      - rewrite <- (bifunctor_rightcomp W).
        etrans.
        { apply maponpaths.
          apply (z_iso_after_z_iso_inv (_,,fmonoidal_preservestensorstrongly Fm a1 a2)). }
        apply (bifunctor_rightid W).
      - rewrite <- (bifunctor_rightcomp W).
        etrans.
        { apply maponpaths.
          apply (z_iso_inv_after_z_iso (_,,fmonoidal_preservestensorstrongly Fm a1 a2)). }
        apply (bifunctor_rightid W).
    }
    apply pathsinv0, (z_iso_inv_to_left _ _ _ aux1).
    cbn.
    clear aux1.
    etrans.
    { repeat rewrite assoc.
      do 4 apply cancel_postcomposition.
      apply fmonoidal_preservesassociativity. }
    etrans.
    { repeat rewrite assoc.
      do 3 apply cancel_postcomposition.
      repeat rewrite assoc'.
      do 2 apply maponpaths.
      apply (z_iso_inv_after_z_iso (_,,fmonoidal_preservestensorstrongly Fm a1 _)). }
    rewrite id_right.
    etrans.
    2: { rewrite assoc. apply cancel_postcomposition. apply (bifunctor_equalwhiskers W). }
    etrans; [| apply (associator_nat2 W)].
    repeat rewrite assoc'.
    apply maponpaths.
    unfold functoronmorphisms1 at 2.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    transparent assert (aux2 : (z_iso (G a1 ⊗_{W} F (a2 ⊗_{V} a3)) (G a1 ⊗_{W} (F a2 ⊗_{W} F a3)))).
    { exists (G a1 ⊗^{W}_{l} pr1 (fmonoidal_preservestensorstrongly Fm a2 a3)).
      exists (G a1 ⊗^{W}_{l} fmonoidal_preservestensordata Fm a2 a3).
      split.
      - rewrite <- (bifunctor_leftcomp W).
        etrans.
        { apply maponpaths.
          apply (z_iso_after_z_iso_inv (_,,fmonoidal_preservestensorstrongly Fm a2 a3)). }
        apply (bifunctor_leftid W).
      - rewrite <- (bifunctor_leftcomp W).
        etrans.
        { apply maponpaths.
          apply (z_iso_inv_after_z_iso (_,,fmonoidal_preservestensorstrongly Fm a2 a3)). }
        apply (bifunctor_leftid W).
    }
    apply (z_iso_inv_to_right _ _ _ _ aux2).
    cbn.
    clear aux2.
    apply pathsinv0, (bifunctor_equalwhiskers W).
  Qed.

  Definition dialgebra_disp_monoidal_data : disp_monoidal_data base_disp V.
  Proof.
    use make_disp_monoidal_data_groupoidal.
    - apply groupoidal_dialgebra_disp_cat.
    - exact dialgebra_disp_tensor.
    - exact dialgebra_disp_unit.
    - exact dialgebra_disp_leftunitor_data.
    - exact dialgebra_disp_rightunitor_data.
    - exact dialgebra_disp_associator_data.
  Defined.

  Definition dialgebra_disp_monoidal : disp_monoidal base_disp V.
  Proof.
    use make_disp_monoidal_locally_prop.
    - apply is_locally_propositional_dialgebra_disp_cat.
    - exact dialgebra_disp_monoidal_data.
  Defined.

  Definition dialgebra_monoidal : monoidal (dialgebra F G) := total_monoidal dialgebra_disp_monoidal.

  Definition dialgebra_monoidal_pr1 : fmonoidal dialgebra_monoidal V (dialgebra_pr1 F G)
    := projection_fmonoidal dialgebra_disp_monoidal.

  Section IntoMonoidalSection.

    Context (α : F ⟹ G) (ismnt : is_mon_nat_trans Fm Gm α).

    Let ismnt_tensor : is_mon_nat_trans_tensorlaw Fm Gm α := pr1 ismnt.
    Let ismnt_unit : is_mon_nat_trans_unitlaw Fm Gm α := pr2 ismnt.

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

    Lemma nattrans_from_ms_is_mon_nat_trans : is_mon_nat_trans Fm Gm nattrans_from_ms.
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

  (** the following lemma should be instance of a construction with lifting *)
  Lemma dialgebra_nat_trans_is_mon_nat_trans :
    is_mon_nat_trans (comp_fmonoidal_lax dialgebra_monoidal_pr1 Fm)
                     (comp_fmonoidal_lax dialgebra_monoidal_pr1 Gm)
                     (dialgebra_nat_trans F G).
  Proof.
    split.
    + intros a a'.
      unfold fmonoidal_preservestensordata. cbn.
      unfold fmonoidal_preservestensordata.
      unfold projection_preserves_tensordata.
      cbn.
      unfold dialgebra_nat_trans_data.
      do 2 rewrite functor_id.
      do 2 rewrite id_right.
      unfold dialgebra_disp_tensor_op.
      etrans.
      { repeat rewrite assoc. do 2 apply cancel_postcomposition.
        apply (pr12 (fmonoidal_preservestensorstrongly Fm (pr1 a) (pr1 a'))). }
      rewrite id_left.
      apply idpath.
    + unfold is_mon_nat_trans_unitlaw.
      unfold fmonoidal_preservesunit. cbn.
      unfold fmonoidal_preservesunit.
      unfold projection_preserves_unit.
      cbn.
      unfold dialgebra_disp_unit.
      do 2 rewrite functor_id.
      do 2 rewrite id_right.
      etrans.
      { rewrite assoc. apply cancel_postcomposition.
        apply (pr12 (fmonoidal_preservesunitstrongly Fm)). }
      unfold fmonoidal_preservesunit.
      apply id_left.
  Qed.


  Section RoundtripForSDData.

      Local Definition source_type: UU := ∑ α : F ⟹ G, is_mon_nat_trans Fm Gm α.
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

Section MonoidalNatTransToDialgebraLifting.

  Context {C1 C2 C3 : category}
          {M1 : monoidal C1}
          {M2 : monoidal C2}
          {M3 : monoidal C3}
          {F G : C2 ⟶ C3}
          {Fm : fmonoidal M2 M3 F}
          {Gm : fmonoidal M2 M3 G}
          {K : C1 ⟶ C2}
          {Km : fmonoidal M1 M2 K}
          {α : K ∙ F ⟹ K ∙ G}
          (αm : is_mon_nat_trans (comp_fmonoidal Km Fm) (comp_fmonoidal Km Gm) α).

  Definition monoidal_nat_trans_to_dialgebra_lifting_data
    : flmonoidal_data Km (dialgebra_disp_monoidal Fm Gm) (nat_trans_to_dialgebra_lifting K α).
  Proof.
    use tpair.
    - intros x y.
      cbn.
      unfold dialgebra_disp_tensor_op.
      rewrite ! assoc'.
      etrans. {
        apply maponpaths.
        exact (! pr1 αm x y).
      }
      cbn.

      etrans. {
        do 2 rewrite assoc.
        do 2 apply maponpaths_2.
        apply (pr2 (fmonoidal_preservestensorstrongly Fm (K x) (K y))).
      }
      rewrite assoc'.
      apply id_left.
    - cbn.
      unfold dialgebra_disp_unit.
      etrans. {
        rewrite assoc'.
        apply maponpaths.
        exact (! pr2 αm).
      }

      cbn.

      etrans. {
        do 2 rewrite assoc.
        do 2 apply maponpaths_2.
        apply (pr2 (fmonoidal_preservesunitstrongly Fm)).
      }
      rewrite assoc'.
      apply id_left.
  Qed.

  Lemma monoidal_nat_trans_to_dialgebra_lifting_laxlaws
    : flmonoidal_laxlaws Km (dialgebra_disp_monoidal Fm Gm) (nat_trans_to_dialgebra_lifting K α)
                          monoidal_nat_trans_to_dialgebra_lifting_data.
  Proof.
    repeat split ; intro ; intros ; apply homset_property.
  Qed.

  Definition monoidal_nat_trans_to_dialgebra_lifting
    : flmonoidal_lax Km (dialgebra_disp_monoidal Fm Gm) (nat_trans_to_dialgebra_lifting K α).
  Proof.
    exists monoidal_nat_trans_to_dialgebra_lifting_data.
    exact monoidal_nat_trans_to_dialgebra_lifting_laxlaws.
  Defined.

  Lemma monoidal_nat_trans_to_dialgebra_lifting_stronglaws
    : fl_stronglaws Km (dialgebra_disp_monoidal Fm Gm) (nat_trans_to_dialgebra_lifting K α) monoidal_nat_trans_to_dialgebra_lifting (pr2 Km).
  Proof.
    split.
    - intros x y.
      use tpair.
      + cbn.

        transparent assert (pfG_is_z_iso : (is_z_isomorphism ( (# G)%Cat (inv_from_z_iso (fmonoidal_preservestensordata Km x y,, fmonoidal_preservestensorstrongly (_,, pr2 Km) x y))))).
        {
          use functor_on_is_z_isomorphism.
          apply is_z_iso_inv_from_z_iso.
        }
        use (z_iso_inv_to_right _ _ _ _ (_ ,, pfG_is_z_iso)).

        transparent assert (pfF_is_z_iso : (is_z_isomorphism ((# F)%Cat
    (inv_from_z_iso
       (fmonoidal_preservestensordata Km x y,, fmonoidal_preservestensorstrongly (_,, pr2 Km) x y))))).
        {
          use functor_on_is_z_isomorphism.
          apply is_z_iso_inv_from_z_iso.
        }

        rewrite assoc'.
        use (z_iso_inv_to_left _ _ _ (_ ,, pfF_is_z_iso)).
        exact (! pr1 monoidal_nat_trans_to_dialgebra_lifting_data x y).
      + repeat (apply funextsec ; intro).
        split ; apply base_disp_cells_isaprop.
    - use tpair.
      + cbn.

        transparent assert (pfL_is_z_iso :
                             (is_z_isomorphism ( (# F)%Cat (inv_from_z_iso (fmonoidal_preservesunit Km,, fmonoidal_preservesunitstrongly (_ ,, pr2 Km)))))
                           ).
        {
          use functor_on_is_z_isomorphism.
          apply is_z_iso_inv_from_z_iso.
        }

        use (z_iso_inv_to_left _ _ _ (_ ,, pfL_is_z_iso)).

        transparent assert (pfR_is_z_iso
                             : (is_z_isomorphism
                                  ((# G)%Cat (inv_from_z_iso (fmonoidal_preservesunit Km,, fmonoidal_preservesunitstrongly (_,, pr2 Km)))))).
        {
          use functor_on_is_z_isomorphism.
          apply is_z_iso_inv_from_z_iso.
        }

        rewrite assoc.
        use (z_iso_inv_to_right _ _ _ _ (_ ,, pfR_is_z_iso)).
        exact (! pr2 monoidal_nat_trans_to_dialgebra_lifting_data).
      + split ; apply base_disp_cells_isaprop.
  Qed.

  Definition monoidal_nat_trans_to_dialgebra_lifting_strong
    : flmonoidal Km (dialgebra_disp_monoidal Fm Gm) (nat_trans_to_dialgebra_lifting K α) (pr2 Km).
  Proof.
    exists monoidal_nat_trans_to_dialgebra_lifting.
    exact monoidal_nat_trans_to_dialgebra_lifting_stronglaws.
  Defined.

  Definition monoidal_nat_trans_to_dialgebra
    : fmonoidal_lax _ _ (nat_trans_to_dialgebra K α)
    := functorlifting_fmonoidal_lax _ _ _ monoidal_nat_trans_to_dialgebra_lifting.

  Definition monoidal_nat_trans_to_dialgebra_strong
    : fmonoidal _ _ (nat_trans_to_dialgebra K α)
    := functorlifting_fmonoidal _ _ _ monoidal_nat_trans_to_dialgebra_lifting_strong.

End MonoidalNatTransToDialgebraLifting.

Section MonoidalDialgebraLiftingToNatTrans.

  Context {C1 C2 C3 : category}
          {M1 : monoidal C1}
          {M2 : monoidal C2}
          {M3 : monoidal C3}
          {F G : C2 ⟶ C3}
          {Fm : fmonoidal M2 M3 F}
          {Gm : fmonoidal M2 M3 G}
          {K : C1 ⟶ C2}
          {Km : fmonoidal M1 M2 K}
          {fl : functor_lifting (dialgebra_disp_cat F G) K}
          (Fl : flmonoidal_lax Km
                               (dialgebra_disp_monoidal Fm Gm)
                               fl).

  Let α : K ∙ F ⟹ K ∙ G := dialgebra_lifting_to_nat_trans _ fl.

  Definition monoidal_dialgebra_lifting_to_monoidal_nat_trans
    : is_mon_nat_trans (comp_fmonoidal Km Fm) (comp_fmonoidal Km Gm) α.
  Proof.
    split.
    - intros x y.
      cbn.

      etrans. {
        rewrite assoc'.
        apply maponpaths.
        exact (! pr11 Fl x y).
      }

      cbn.
      do 2 rewrite assoc.
      apply maponpaths_2.
      unfold dialgebra_disp_tensor_op.
      cbn.
      do 2 rewrite assoc.
      etrans. {
        do 2 apply maponpaths_2.
        apply (fmonoidal_preservestensorstrongly Fm (K x) (K y)).
      }
      rewrite assoc'.
      apply id_left.
    - red. cbn.
      etrans. {
        rewrite assoc'.
        apply maponpaths.
        exact (! pr21 Fl).
      }

      rewrite assoc.
      apply maponpaths_2.

      cbn.
      unfold dialgebra_disp_unit.
      rewrite assoc.
      etrans. {
        apply maponpaths_2.
        apply  (fmonoidal_preservesunitstrongly Fm).
      }
      apply id_left.
  Qed.

  (* Definition monoidal_dialgebra_lifting_to_invertible_monoidal_nat_trans *)

End MonoidalDialgebraLiftingToNatTrans.

Section RoundtripForLiftingData.

  Context {C1 C2 C3 : category}
          {M1 : monoidal C1}
          {M2 : monoidal C2}
          {M3 : monoidal C3}
          {F G : C2 ⟶ C3}
          {Fm : fmonoidal M2 M3 F}
          {Gm : fmonoidal M2 M3 G}
          {K : C1 ⟶ C2}
          {Km : fmonoidal M1 M2 K}.

  Local Definition source_type': UU
    := ∑ α : K ∙ F ⟹ K ∙ G,
        is_mon_nat_trans (comp_fmonoidal Km Fm) (comp_fmonoidal Km Gm) α.

  Local Definition target_type': UU
    := ∑ fl : functor_lifting (dialgebra_disp_cat F G) K,
        flmonoidal_lax Km (dialgebra_disp_monoidal Fm Gm) fl.

  Local Definition target_type_s': UU
    := ∑ fl : functor_lifting (dialgebra_disp_cat F G) K,
        flmonoidal Km (dialgebra_disp_monoidal Fm Gm) fl (pr2 Km).

  Local Definition source_to_target'
    : source_type' -> target_type'
    := λ α, _ ,, monoidal_nat_trans_to_dialgebra_lifting (pr2 α).

  Local Definition target_to_source'
    : target_type' -> source_type'
    := λ fl, _ ,, monoidal_dialgebra_lifting_to_monoidal_nat_trans (pr2 fl).

  Local Definition source_to_target_s'
    : source_type' -> target_type_s'.
  Proof.
    intro α.
    use tpair.
    2: apply (monoidal_nat_trans_to_dialgebra_lifting_strong (pr2 α)).
  Defined.

  Local Definition target_to_source_s'
    : target_type_s' -> source_type'
    := λ fl, _ ,, monoidal_dialgebra_lifting_to_monoidal_nat_trans (pr2 fl).

  Local Lemma roundtrip1' (ass: source_type')
    : target_to_source' (source_to_target' ass) = ass.
  Proof.
    use total2_paths_f.
    - apply UniMath.CategoryTheory.categories.Dialgebras.roundtrip1_with_liftings.
    - apply isaprop_is_mon_nat_trans.
  Qed.

  Local Lemma roundtrip1_s' (ass: source_type')
    : target_to_source_s' (source_to_target_s' ass) = ass.
  Proof.
    use total2_paths_f.
    - apply UniMath.CategoryTheory.categories.Dialgebras.roundtrip1_with_liftings.
    - apply isaprop_is_mon_nat_trans.
  Qed.

  Local Lemma roundtrip2' (ass: target_type')
    : source_to_target' (target_to_source' ass) = ass.
  Proof.
    use total2_paths_f.
    - apply UniMath.CategoryTheory.categories.Dialgebras.roundtrip2_with_liftings.
    - use flmonoidal_equality ; intros ; apply homset_property.
  Qed.

  Local Lemma roundtrip2_s' (ass: target_type_s')
    : source_to_target_s' (target_to_source_s' ass) = ass.
  Proof.
    use total2_paths_f.
    - apply UniMath.CategoryTheory.categories.Dialgebras.roundtrip2_with_liftings.
    - use flmonoidal_strong_equality ; intros ; apply homset_property.
  Qed.

End RoundtripForLiftingData.
