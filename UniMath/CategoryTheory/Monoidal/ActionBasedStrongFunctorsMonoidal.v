(** shows that action-based strong functors can be perceived as strong monoidal functors from the monoidal category that is acting on the underlying categories to a suitable monoidal category

This means that the requirement on strength is that it behaves as a ``homomorphism'' w.r.t. the
monoidal structures.

Work in progress: the characterization in the non-monoidal case seems to need more 2-categorical knowledge
(instead of bicategorical one), and the monoidal case will only extend this problem, which is why there is now only
a construction of a strong monoidal functor from a parameterized distributivity and no construction in the
other direction; also that construction depends on 6 unproven equations between natural transformations
(all in the construction of the unitors and associator of the monoidal target category)

Author: Ralph Matthes 2021

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.EndofunctorsMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Actions.
Require Import UniMath.CategoryTheory.Monoidal.ActionBasedStrength.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Local Open Scope cat.

Section UpstreamAux.
  (** this section presents auxiliary results that are even more abstracted from the situation at hand *)

  Context {C A1 A2 A3 A4 : precategory}.
  Context (hsA2 : has_homsets A2).
  Context (hsA3 : has_homsets A3).
  Context (hsA4 : has_homsets A4).

  Lemma assoc_precomp_precomp_mor (G : A1 ⟶ A2)(G' : A2 ⟶ A3)(H1 H2 : A3 ⟶ A4)(η: H1 ⟹ H2):
    # (pre_composition_functor _ _ _ hsA2 hsA4 G)
      (# (pre_composition_functor _ _ _ hsA3 hsA4 G') η) =
      # (pre_composition_functor _ _ _ hsA3 hsA4
                                 (pre_composition_functor _ _ _ hsA2 hsA3 G G')) η.
  Proof.
    cbn.
    apply nat_trans_eq; try exact hsA4.
    intro a.
    apply idpath.
  Qed.

  Corollary assoc_precomp_precomp_mor_special (G : A1 ⟶ A2)(G' : A2 ⟶ A3)(F : C ⟶ [A3, A4, hsA4])
            (c c': C) (f: C⟦c,c'⟧):
    # (pre_composition_functor _ _ _ hsA2 hsA4 G)
      (# (pre_composition_functor _ _ _ hsA3 hsA4 G') (# F f)) =
      # (pre_composition_functor _ _ _ hsA3 hsA4
                                 (pre_composition_functor _ _ _ hsA2 hsA3 G G'))
        (# F f).
  Proof.
    apply assoc_precomp_precomp_mor.
  Qed.


  Lemma assoc_postcomp_postcomp_mor (H1 H2 : A1 ⟶ A2)(η: H1 ⟹ H2)(G : A2 ⟶ A3)(G' : A3 ⟶ A4):
    # (post_composition_functor _ _ _ hsA3 hsA4 G')
      (# (post_composition_functor _ _ _ hsA2 hsA3 G) η) =
      # (post_composition_functor _ _ _ hsA2 hsA4
                                  (post_composition_functor _ _ _ hsA3 hsA4 G' G)) η.
    Proof.
    cbn.
    apply nat_trans_eq; try exact hsA4.
    intro a.
    apply idpath.
  Qed.


  Lemma exchange_postcomp_precomp_mor (G : A1 ⟶ A2)(H1 H2 : A2 ⟶ A3)(η: H1 ⟹ H2)(G' : A3 ⟶ A4):
    # (post_composition_functor _ _ _ hsA3 hsA4 G')
      (# (pre_composition_functor _ _ _ hsA2 hsA3 G) η) =
      # (pre_composition_functor _ _ _ hsA2 hsA4 G)
        (# (post_composition_functor _ _ _ hsA3 hsA4 G') η).
  Proof.
    cbn.
    apply nat_trans_eq; try exact hsA4.
    intro a.
    apply idpath.
  Qed.

  Corollary exchange_postcomp_precomp_mor_special (G : A1 ⟶ A2)(F : C ⟶ [A2, A3, hsA3])(G' : A3 ⟶ A4)
            (c c' : C)(f : C ⟦ c, c' ⟧):
    # (pre_composition_functor A1 A2 A4 hsA2 hsA4 G)
      (# (post_composition_functor A2 A3 A4 hsA3 hsA4 G') (# F f)) =
      # (post_composition_functor A1 A3 A4 hsA3 hsA4 G')
        (# (pr1
              (functor_compose (functor_category_has_homsets A2 A3 hsA3)
                               (functor_category_has_homsets A1 A3 hsA3) F
                               (pre_composition_functor A1 A2 A3 hsA2 hsA3 G))) f).
  Proof.
    intros.
    apply pathsinv0.
    apply exchange_postcomp_precomp_mor.
  Qed.

(** as background information only: *)
  Lemma exchange_postcomp_precomp_ob_special (G : A1 ⟶ A2)(F : C ⟶ [A2, A3, hsA3])(G' : A3 ⟶ A4) (c: C):
    (pre_composition_functor _ _ _ hsA2 hsA4 G) (post_composition_functor _ _ _ hsA3 hsA4 G' (F c)) =
      (post_composition_functor _ _ _ hsA3 hsA4 G')
        (pr1(functor_compose (functor_category_has_homsets A2 A3 hsA3)
                                (functor_category_has_homsets A1 A3 hsA3)
                                F (pre_composition_functor _ _ _  hsA2 hsA3 G)) c).
  Proof.
    cbn.
    apply pathsinv0, functor_assoc.
  Qed.

End UpstreamAux.

Section Upstream.
  (** this section has nothing to do with monoidal categories but is dictated by the aims of this file *)

  Context {C A A' : precategory}.
  Context (hs : has_homsets A').

  Context (H H' : C ⟶ [A, A', hs]).

  Definition trafotarget_disp_cat_ob_mor: disp_cat_ob_mor C.
  Proof.
    use make_disp_cat_ob_mor.
    - intro c. exact ([A, A', hs]⟦(H c : A ⟶ A'), (H' c : A ⟶ A')⟧).
    - intros c c' α β f.
      exact (α · (# H' f) = (# H f) · β).
  Defined.

  Lemma trafotarget_disp_cat_id_comp: disp_cat_id_comp C trafotarget_disp_cat_ob_mor.
  Proof.
    split.
    - intros c α.
      red. unfold trafotarget_disp_cat_ob_mor, make_disp_cat_ob_mor. hnf.
      do 2 rewrite functor_id.
      rewrite id_left. apply id_right.
    - intros c1 c2 c3 f g α1 α2 α3 Hypf Hypg.
      red. red in Hypf, Hypg.
      unfold trafotarget_disp_cat_ob_mor, make_disp_cat_ob_mor in Hypf, Hypg |- *.
      hnf in Hypf, Hypg |- *.
      do 2 rewrite functor_comp.
      rewrite assoc.
      rewrite Hypf.
      rewrite <- assoc.
      rewrite Hypg.
      apply assoc.
   Qed.

  Definition trafotarget_disp_cat_data: disp_cat_data C :=
    trafotarget_disp_cat_ob_mor ,, trafotarget_disp_cat_id_comp.

  Lemma trafotarget_disp_cells_isaprop (x y : C) (f : C ⟦ x, y ⟧)
        (xx : trafotarget_disp_cat_data x) (yy : trafotarget_disp_cat_data y):
    isaprop (xx -->[ f] yy).
  Proof.
    intros Hyp Hyp'.
    apply (functor_category_has_homsets _ _ hs).
  Qed.

  Lemma trafotarget_disp_cat_axioms: disp_cat_axioms C trafotarget_disp_cat_data.
  Proof.
    repeat split; intros; try apply trafotarget_disp_cells_isaprop.
    apply isasetaprop.
    apply trafotarget_disp_cells_isaprop.
  Qed.

  Definition trafotarget_disp: disp_precat C := trafotarget_disp_cat_data ,, trafotarget_disp_cat_axioms.

  Definition trafotarget_precat: precategory := total_precategory trafotarget_disp.

  Definition has_homsets_trafotarget_precat (hsC: has_homsets C): has_homsets trafotarget_precat.
  Proof.
    apply (total_category_has_homsets(C:=C,,hsC) trafotarget_disp).
  Defined.

  Definition forget_from_trafotarget: trafotarget_precat ⟶ C := pr1_category trafotarget_disp.

  Section TheEquivalence.

    (** a naive specification of the target of the bijection *)
    Definition trafotarget_with_eq: UU := ∑ N: C ⟶ trafotarget_precat,
      functor_data_from_functor _ _ (functor_composite N forget_from_trafotarget) =
        functor_data_from_functor _ _ (functor_identity C).

    (** a "pedestrian" definition *)
    Definition nat_trafo_to_functor (η: H ⟹ H'): C ⟶ trafotarget_precat.
    Proof.
      use make_functor.
      - use make_functor_data.
        + intro c.
          exact (c ,, η c).
        + intros c c' f.
          exists f.
          red. unfold trafotarget_disp. hnf.
          apply pathsinv0, nat_trans_ax.
      - split; red.
        + intro c.
          use total2_paths_f.
          * cbn. apply idpath.
          * apply (functor_category_has_homsets _ _ hs).
        + intros c1 c2 c3 f f'.
          use total2_paths_f.
          * cbn. apply idpath.
          * apply (functor_category_has_homsets _ _ hs).
    Defined.

    (** an immediate consequence *)
    Definition nat_trafo_to_functor_with_eq (η: H ⟹ H'): trafotarget_with_eq.
    Proof.
      exists (nat_trafo_to_functor η).
      apply idpath.
    Defined.

    (** we can also use the infrastructure of displayed categories given homsets
        (is that inherently necessary or only a limitation of the library?) *)
    Definition nat_trafo_to_section_v1 (hsC: has_homsets C)(η: H ⟹ H'):
      @functor_lifting (C,,hsC) (C,,hsC) trafotarget_disp (functor_identity C).
    Proof.
      use tpair.
      - use tpair.
        + intro c. exact (η c).
        + intros c c' f.
          red. unfold reindex_disp_cat, trafotarget_disp. hnf.
          apply pathsinv0, nat_trans_ax.
      - split.
        + intro c.
          apply (functor_category_has_homsets _ _ hs).
        + intros c1 c2 c3 f f'.
          apply (functor_category_has_homsets _ _ hs).
    Defined.

    Definition nat_trafo_to_section (hsC: has_homsets C)(η: H ⟹ H'):
      @section_disp (C,,hsC) trafotarget_disp.
    Proof.
      use tpair.
      - use tpair.
        + intro c. exact (η c).
        + intros c c' f.
          red. unfold reindex_disp_cat, trafotarget_disp. hnf.
          apply pathsinv0, nat_trans_ax.
      - split.
        + intro c.
          apply (functor_category_has_homsets _ _ hs).
        + intros c1 c2 c3 f f'.
          apply (functor_category_has_homsets _ _ hs).
    Defined.

    Definition nat_trafo_to_functor_through_section_v1 (hsC: has_homsets C)(η: H ⟹ H'): C ⟶ trafotarget_precat :=
      @lifted_functor (C,,hsC) (C,,hsC) trafotarget_disp (functor_identity C) (nat_trafo_to_section_v1 hsC η).

    Definition nat_trafo_to_functor_through_section (hsC: has_homsets C)(η: H ⟹ H'): C ⟶ trafotarget_precat :=
      @section_functor (C,,hsC) trafotarget_disp (nat_trafo_to_section hsC η).

    (** the analogous immediate consequence *)
    Definition nat_trafo_to_functor_through_section_with_eq (hsC: has_homsets C) (η: H ⟹ H'): trafotarget_with_eq.
    Proof.
      exists (nat_trafo_to_functor_through_section hsC η).
      apply idpath.
    Defined.

    (** the other direction in naive form *)
    Definition functor_to_nat_trafo_aux (N: C ⟶ trafotarget_precat):
      (functor_composite (functor_composite N forget_from_trafotarget) H) ⟹
      (functor_composite (functor_composite N forget_from_trafotarget) H').
  Proof.
    use make_nat_trans.
    - intro c. exact (pr2 (N c)).
    - intros c c' f.
      cbn.
      assert (Ninst := pr2 (# N f)).
      cbn in Ninst.
      apply pathsinv0, Ninst.
  Defined.

    (** correct the typing by rewriting *)
  Definition functor_to_nat_trafo_with_eq (Ne: trafotarget_with_eq): H ⟹ H'.
  Proof.
    induction Ne as [N HypN].
    set (aux := functor_to_nat_trafo_aux N).
    change (functor_composite (functor_identity C) H ⟹ functor_composite (functor_identity C) H').
    cbn.
    cbn in HypN.
    rewrite <- HypN.
    exact aux.
  Defined.

    Local Lemma roundtrip1_with_eq (η: H ⟹ H'):
      functor_to_nat_trafo_with_eq (nat_trafo_to_functor_with_eq η) = η.
  Proof.
    apply (nat_trans_eq (functor_category_has_homsets _ _ hs)).
    intro c.
    apply (nat_trans_eq hs).
    intro a.
    cbn.
    apply idpath.
  Qed.

    (** what we do NOT get:
    Local Lemma roundtrip2_with_eq (hsC: has_homsets C) (hs'C: isaset C) (Ne: trafotarget_with_eq):
      nat_trafo_to_functor_with_eq (functor_to_nat_trafo_with_eq Ne) = Ne.
*)

    (** *** using sections in the framework display categories *)
    Definition section_to_nat_trafo (hsC: has_homsets C):
      @section_disp (C,,hsC) trafotarget_disp -> H ⟹ H'.
    Proof.
      intro sd.
      induction sd as [[sdob sdmor] [sdid sdcomp]].
      use make_nat_trans.
      - intro c. exact (sdob c).
      - intros c c' f.
        assert (aux := sdmor c c' f). apply pathsinv0. exact aux.
    Defined.

    Local Lemma roundtrip1_with_sections (hsC: has_homsets C) (η: H ⟹ H'):
      section_to_nat_trafo hsC (nat_trafo_to_section hsC η) = η.
    Proof.
      apply (nat_trans_eq (functor_category_has_homsets _ _ hs)).
      intro c.
      apply idpath.
    Qed.

    Local Lemma roundtrip2_with_sections (hsC: has_homsets C) (sd: @section_disp (C,,hsC) trafotarget_disp):
      nat_trafo_to_section hsC (section_to_nat_trafo hsC sd) = sd.
    Proof.
      induction sd as [[sdob sdmor] [sdid sdcomp]].
      unfold nat_trafo_to_section, section_to_nat_trafo.
      cbn.
      use total2_paths_f; simpl.
      - use total2_paths_f; simpl.
        + apply idpath.
        + cbn.
          assert (Hyp: ∏ c c' f, ! (! sdmor c c' f) = sdmor c c' f).
          * intros.
    Abort. (* hopefully only for lack of time *)

    (** *** a "pedestrian" variant of the whole approach without type-level rewriting *)
    Definition trafotarget_with_iso: UU := ∑ N: C ⟶ trafotarget_precat,
          nat_z_iso (functor_composite N forget_from_trafotarget) (functor_identity C).

    Definition nat_trafo_to_functor_with_iso (η: H ⟹ H'): trafotarget_with_iso.
    Proof.
      exists (nat_trafo_to_functor η).
      use tpair.
      - use make_nat_trans.
        + intro c. apply identity.
        + intros c c' f. cbn. rewrite id_left. apply id_right.
      - intro c.
        apply is_z_isomorphism_identity.
    Defined.

    (** and the other direction *)
    Definition functor_to_nat_trafo_with_iso_data (N : C ⟶ trafotarget_precat)
               (HypN : nat_z_iso (N ∙ forget_from_trafotarget) (functor_identity C)): nat_trans_data H H'.
    Proof.
      intro c.
      set (trans := pr2 (N c)).
      induction HypN as [τ Hτ].
      set (Hτinst := Hτ c).
      set (τinst := τ c).
      cbn in trans.
      cbn in τinst.
      induction Hτinst as [τ'c [H1 H2]].
      cbn in τ'c.
      refine (nat_trans_comp _ _ _ _ (nat_trans_comp _ _ _ trans _)).
      - exact (# H τ'c).
      - exact (# H' τinst).
    Defined.

    Lemma functor_to_nat_trafo_with_iso_data_is_nat_trans (N : C ⟶ trafotarget_precat)
          (HypN : nat_z_iso (N ∙ forget_from_trafotarget) (functor_identity C)):
      is_nat_trans _ _ (functor_to_nat_trafo_with_iso_data N HypN).
    Proof.
      intros c c' f.
      cbn.
      unfold nat_trans_comp. cbn.
      apply nat_trans_eq; try exact hs.
      intro a.
      cbn.
      assert (aux : # H f · (# H (pr1 (pr2 HypN c')) ·
               ((pr2 (N c') : [A, A', hs] ⟦ H (pr1 (N c')), H' (pr1 (N c'))⟧) · # H' (pr1 HypN c'))) =
                    # H (pr1 (pr2 HypN c)) ·
               ((pr2 (N c): [A, A', hs] ⟦ H (pr1 (N c)), H' (pr1 (N c))⟧) · # H' (pr1 HypN c)) · # H' f).
      2: { apply (maponpaths pr1) in aux. apply toforallpaths in aux. apply aux. }
      set (α1 := # H f); set (F2 := pr1 (pr2 HypN c')); set (α2 := # H F2); set (α3 := pr2 (N c')); set (F4 := pr1 HypN c'); set (α4 := # H' F4).
      set (F5 := pr1 (pr2 HypN c)); set (α5 := # H F5); set (α6 := pr2 (N c)); set (F7 := pr1 HypN c); set (α7 := # H' F7); set (α8 := # H' f).
      set (F7iso := F7 ,, pr2 HypN c: z_iso ((N ∙ forget_from_trafotarget) c) (functor_identity C c)).
      set (α7iso := functor_on_z_iso H' F7iso).
      set (F4iso := F4 ,, pr2 HypN c': z_iso ((N ∙ forget_from_trafotarget) c') (functor_identity C c')).
      set (α4iso := functor_on_z_iso H' F4iso).
      etrans.
      { rewrite assoc. apply cancel_postcomposition. apply pathsinv0, functor_comp. }
      etrans.
      2: { rewrite <- assoc. apply maponpaths. rewrite <- assoc. apply maponpaths.
           apply functor_comp. }
      set (F2iso := z_iso_inv F4iso).
      rewrite assoc.
      apply (z_iso_inv_to_right _ _ _ _ α4iso).
      change (inv_from_z_iso α4iso) with (# H' F2).
      set (F5iso := z_iso_inv F7iso).
      set (α5iso := functor_on_z_iso H F5iso).
      rewrite <- assoc.
      apply (z_iso_inv_to_left _ _ _ α5iso).
      change (inv_from_z_iso α5iso) with (# H F7).
      etrans.
      { rewrite assoc. apply cancel_postcomposition.
        apply pathsinv0, functor_comp. }
      etrans.
      2: { rewrite <- assoc. apply maponpaths, functor_comp. }
      rewrite assoc.
      assert (HypNnatinst := nat_trans_ax (pr1 HypN) c c' f).
      cbn in HypNnatinst.
      assert (aux : F7 · f · F2 = pr1 (# N f)).
      { apply (z_iso_inv_to_right _ _ _ _ F2iso).
        apply pathsinv0. exact HypNnatinst. }
      etrans.
      { apply cancel_postcomposition.
        apply maponpaths.
        exact aux. }
      etrans.
      2: { do 2 apply maponpaths.
           apply pathsinv0. exact aux. }
      assert (Nnatinst := pr2 (# N f)).
      apply pathsinv0.
      exact Nnatinst.
  Qed.

  Definition functor_to_nat_trafo_with_iso (Ne: trafotarget_with_iso): H ⟹ H'.
  Proof.
    induction Ne as [N HypN].
    exact (functor_to_nat_trafo_with_iso_data N HypN,,
                                              functor_to_nat_trafo_with_iso_data_is_nat_trans N HypN).
  Defined.

  Local Lemma roundtrip1 (η: H ⟹ H'): functor_to_nat_trafo_with_iso (nat_trafo_to_functor_with_iso η) = η.
  Proof.
    apply nat_trans_eq; try exact (functor_category_has_homsets _ _ hs).
    intro c.
    apply nat_trans_eq; try exact hs.
    intro a.
    cbn.
    rewrite (functor_id H).
    rewrite (functor_id H').
     rewrite id_right. apply id_left.
  Qed.

  (* the following lemma cannot hold with the weak assumption of having an iso only, we should rather watch out
     for an equivalence
  Local Lemma roundtrip2_naive (hsC: has_homsets C) (Ne: trafotarget_with_iso): nat_trafo_to_functor_with_iso (functor_to_nat_trafo_with_iso Ne) = Ne.
  Proof.
    induction Ne as [N HypN].
    use total2_paths_f.
    - cbn.
      apply functor_eq; try apply (has_homsets_trafotarget_precat hsC).
      use functor_data_eq.
      + intro c.
        cbn.
        show_id_type.
        use total2_paths_f.
        * cbn.
          apply pathsinv0.
          (* we only have iso, not equality *)
   *)

  (** the object mapping of both functors is pointwise z_isomorphic *)
  Definition roundtrip2_on_ob (hsC: has_homsets C) (Ne: trafotarget_with_iso) (c: C) : z_iso (pr111 (nat_trafo_to_functor_with_iso (functor_to_nat_trafo_with_iso Ne)) c) (pr111 Ne c).
  Proof.
    induction Ne as [N HypN].
    use make_z_iso.
    - cbn.
      use tpair.
      + exact (pr1 (pr2 HypN c)).
      + cbn.
        apply nat_trans_eq; try exact hs.
        intro a.
        cbn.
        do 2 rewrite <- assoc.
        apply maponpaths.
        assert (aux: (pr2 (N c): [A, A', hs] ⟦ H (pr1 (N c)), H' (pr1 (N c))⟧) · (# H' (pr1 HypN c) · # H' (pr1 (pr2 HypN c))) = pr2 ((pr11 N) c)).
        2: { apply (maponpaths pr1) in aux. apply toforallpaths in aux. apply aux. }
        etrans.
        { apply maponpaths. apply pathsinv0, functor_comp. }
        etrans.
        { do 2 apply maponpaths.
          set (theiso := pr1 HypN c ,, pr2 HypN c: z_iso ((N ∙ forget_from_trafotarget) c) (functor_identity C c)).
          apply (z_iso_inv_after_z_iso theiso). }
        rewrite functor_id.
        apply id_right.
    - cbn.
      use tpair.
      + exact (pr1 HypN c).
      + cbn.
        apply nat_trans_eq; try exact hs.
        intro a.
        cbn.
        do 2 rewrite assoc.
        apply cancel_postcomposition.
        assert (aux: pr2 ((pr11 N) c) = # H (pr1 HypN c) · # H (pr1 (pr2 HypN c)) · pr2 (N c)).
        2: { apply (maponpaths pr1) in aux. apply toforallpaths in aux. apply aux. }
        rewrite <- (functor_comp H).
        set (theiso := pr1 HypN c ,, pr2 HypN c: z_iso ((N ∙ forget_from_trafotarget) c) (functor_identity C c)).
        match goal with | [ |- _ = ?f1 · _ ] => set (aux := f1) end.
        assert (Hyp: aux = # H (identity _)).
        { unfold aux. apply maponpaths.
          apply (z_iso_inv_after_z_iso theiso). }
        rewrite functor_id in Hyp.
        rewrite Hyp.
        apply pathsinv0.
        apply (id_left (pr2 (N c): [A, A', hs] ⟦ H (pr1 (N c)), H' (pr1 (N c))⟧)).
    - split.
      + (* show_id_type. *)
        use total2_paths_f.
        * cbn.
          set (theiso := pr1 HypN c ,, pr2 HypN c: z_iso ((N ∙ forget_from_trafotarget) c) (functor_identity C c)).
          apply (z_iso_after_z_iso_inv theiso).
        * cbn.
          (* show_id_type. *)
          apply (functor_category_has_homsets _ _ hs).
      + use total2_paths_f.
        * cbn.
          set (theiso := pr1 HypN c ,, pr2 HypN c: z_iso ((N ∙ forget_from_trafotarget) c) (functor_identity C c)).
          apply (z_iso_inv_after_z_iso theiso).
        * cbn.
          apply (functor_category_has_homsets _ _ hs).
  Defined.

  (** roundtrip_on_mor will have to adapt everything by the iso given through roundtrip_on_mor *)

  End TheEquivalence.

End Upstream.

Section Main.

Context (Mon_V : monoidal_precat).

Local Definition I := monoidal_precat_unit Mon_V.
Local Definition tensor := monoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)).

Section Action.

Context {A: precategory}.
Context (hsA : has_homsets A).

Context (FA: strong_monoidal_functor Mon_V (monoidal_precat_of_endofunctors hsA)).


End Action.

Section Functor.

Context {A A': precategory}.
Context (hsA : has_homsets A) (hsA' : has_homsets A').

Context (FA: strong_monoidal_functor Mon_V (monoidal_precat_of_endofunctors hsA)).
Context (FA': strong_monoidal_functor Mon_V (monoidal_precat_of_endofunctors hsA')).

Context (G : A ⟶ A').

Local Definition precompG := pre_composition_functor _ _ _ hsA' hsA' G.
Local Definition postcompG {C: precategory} := post_composition_functor C _ _ hsA hsA' G.

Let H := param_distributivity_dom Mon_V hsA' FA' G.
Let H' := param_distributivity_codom Mon_V hsA hsA' FA G.

Definition montrafotarget_precat: precategory := trafotarget_precat hsA' H H'.

Definition montrafotarget_unit: montrafotarget_precat.
Proof.
  exists I.
  exact (param_distr_triangle_eq_variant0_RHS Mon_V hsA hsA' FA FA' G).
Defined.

Lemma montrafotarget_tensor_comp_aux (v w v' w': Mon_V) (f: Mon_V⟦v,v'⟧) (g: Mon_V⟦w,w'⟧)
      (η : trafotarget_disp hsA' H H' v) (π : trafotarget_disp hsA' H H' w)
      (η' : trafotarget_disp hsA' H H' v') (π' : trafotarget_disp hsA' H H' w')
      (Hyp: η  -->[ f] η') (Hyp': π -->[ g] π'):
  (param_distr_pentagon_eq_body_variant_RHS Mon_V hsA hsA' FA FA' G v w η π:
     pr1 (trafotarget_disp hsA' H H') (v ⊗ w))
    -->[ # tensor (f,, g : pr1 Mon_V ⊠ pr1 Mon_V ⟦ v,, w, v',, w' ⟧)]
    param_distr_pentagon_eq_body_variant_RHS Mon_V hsA hsA' FA FA' G v' w' η' π'.
Proof.
  unfold mor_disp in Hyp, Hyp' |- *.
  hnf in Hyp, Hyp' |- *.
  unfold param_distr_pentagon_eq_body_variant_RHS, param_distr_pentagon_eq_body_RHS.
  change (ActionBasedStrength.precompF hsA' G) with precompG.
  change (ActionBasedStrength.postcompF hsA hsA' G) with (postcompG(C:=A)).
  match goal with | [ |- ?Hαinv · (?Hγ · ?Hδ · ?Hβ) · ?Hε = _ ] => set (αinv := Hαinv);
     set (γ := Hγ); set (δ:= Hδ); set (β := Hβ); set (ε1 := Hε) end.
  match goal with | [ |- _ = ?Hε · (?Hαinv · (?Hγ · ?Hδ · ?Hβ)) ] => set (αinv' := Hαinv);
           set (γ' := Hγ); set (δ':= Hδ); set (β' := Hβ); set (ε2 := Hε) end.
  set (αinviso := prewhisker_with_μ_inv_z_iso Mon_V hsA' FA' G v w).
  rewrite <- assoc.
  apply pathsinv0.
  apply (z_iso_inv_to_left _ _ _ αinviso).
  unfold inv_from_z_iso.
  set (α := # precompG (lax_monoidal_functor_μ FA' (v,, w))).
  change (pr12 αinviso) with α.
  set (fg := (f #, g)).
  assert (μFA'natinst := nat_trans_ax (lax_monoidal_functor_μ FA') _ _ fg).
  simpl in μFA'natinst.
  assert (μFAnatinst := nat_trans_ax (lax_monoidal_functor_μ FA) _ _ fg).
  simpl in μFAnatinst.
  change (# (functorial_composition hsA hsA) (# FA f #, # FA g) · lax_monoidal_functor_μ FA (v',, w') =
          lax_monoidal_functor_μ FA (v,, w) · # FA (# (MonoidalFunctors.tensor_C Mon_V) fg)) in μFAnatinst.
  change (# (functorial_composition hsA' hsA') (# FA' f #, # FA' g) · lax_monoidal_functor_μ FA' (v',, w') =
            lax_monoidal_functor_μ FA' (v,, w) · # FA' (# (MonoidalFunctors.tensor_C Mon_V) fg)) in μFA'natinst.
  set (ε2better := # precompG (# (functor_composite tensor FA') fg)).
  transparent assert (ε2betterok : (ε2 = ε2better)).
  { apply idpath. }
  rewrite ε2betterok.
  rewrite assoc.
  apply (maponpaths (# precompG)) in μFA'natinst.
  apply pathsinv0 in μFA'natinst.
  do 2 rewrite functor_comp in μFA'natinst.
  etrans.
  { apply cancel_postcomposition.
    exact μFA'natinst. }
  clear ε2 μFA'natinst ε2better ε2betterok.
  rewrite <- assoc.
  etrans.
  { apply maponpaths.
    rewrite assoc.
    apply cancel_postcomposition.
    unfold αinv'.
    apply pathsinv0.
    apply (functor_comp precompG). }
  etrans.
  { apply maponpaths.
    apply cancel_postcomposition.
    apply maponpaths.
    set (μFA'pointwise := nat_z_iso_pointwise_z_iso (strong_monoidal_functor_μ FA') (v',, w')).
    apply (z_iso_inv_after_z_iso μFA'pointwise). }
  clear αinv αinv' αinviso α.
  rewrite functor_id.
  rewrite id_left.
  match goal with | [ |- ?Hσ · _ = _ ] => set (σ' := Hσ) end.
  etrans.
  2: { (* Fail apply assoc. *)
    use assoc. }
  set (ε1better := # postcompG (# (functor_composite tensor FA) fg)).
  transparent assert (ε1betterok : (ε1 = ε1better)).
  { apply idpath. }
  rewrite ε1betterok.
  apply (maponpaths (# postcompG)) in μFAnatinst.
  do 2 rewrite functor_comp in μFAnatinst.
  etrans.
  2: { apply maponpaths.
       unfold β, ε1better.
       exact μFAnatinst. }
  clear β μFAnatinst ε1 ε1better ε1betterok.
  match goal with | [ |- _ = _ · (_ · ?Hβ'twin) ] => set (β'twin := Hβ'twin) end.
  change β'twin with β'.
  clear β'twin.
  etrans.
  2: { apply pathsinv0. (* Fail apply assoc. *) use assoc. }
  etrans.
  { (* Fail apply assoc. *) use assoc. }
  (* Fail apply cancel_postcomposition. *) use cancel_postcomposition.
  clear β'.
  unfold σ'.
  rewrite functorial_composition_pre_post.
  clear σ'.
  rewrite functor_comp.
  match goal with | [ |- ?Hσ'1 · ?Hσ'2 · _  = _ · ?Hσ ] => set (σ'1 := Hσ'1); set (σ'2 := Hσ'2); set (σ := Hσ) end.
  apply (maponpaths (# (post_composition_functor A A' A' hsA' hsA' ((FA' w'): [A', A', hsA'])))) in Hyp.
  do 2 rewrite functor_comp in Hyp.
  apply pathsinv0 in Hyp.
  assert (Hypvariant: σ'2 · γ' = # (post_composition_functor A A' A' hsA' hsA' (FA' w')) η
                       · # (post_composition_functor A A' A' hsA' hsA' (FA' w')) (# H' f)).
  { etrans.
    2: { exact Hyp. }
    (* Fail apply cancel_postcomposition. *) use cancel_postcomposition.
    apply exchange_postcomp_precomp_mor_special. }
  clear Hyp.
  intermediate_path (σ'1 · (σ'2 · γ') · δ').
  { repeat rewrite <- assoc.
    apply idpath. }
  rewrite Hypvariant.
  clear σ'2 γ' Hypvariant.
  unfold H', param_distributivity_codom.
  change (ActionBasedStrength.postcompF hsA hsA' G) with (postcompG(C:=A)).
  match goal with | [ |- _ · (?Hγw' · ?Hι') · _ = _ ] => set (γw' := Hγw'); set (ι' := Hι')  end.
  intermediate_path (((σ'1 · γw') · ι') · δ').
  { repeat rewrite <- assoc.
    apply maponpaths.
    apply pathsinv0.
    (* Fail apply assoc. *) use assoc. }
  etrans.
  { do 2 apply cancel_postcomposition.
    apply pathsinv0.
    assert (auxhorcomp := functorial_composition_pre_post _ _ _ hsA' hsA' _ _ _ _ η (# FA' g)).
    assert (σ'1ok : σ'1 = # (pre_composition_functor A A' A' hsA' hsA' (H v)) (# FA' g)).
    { apply assoc_precomp_precomp_mor. }
    rewrite σ'1ok. unfold γw'. apply auxhorcomp. }
  rewrite functorial_composition_post_pre.
  clear σ'1 γw'.
  change (# (post_composition_functor A A' A' hsA' hsA' (FA' w)) η) with γ.
  rewrite <- assoc.
  match goal with | [ |- _ · ?Hν' · _ = _ ] => set (ν' := Hν')  end.
  intermediate_path (γ · (ν' · (ι' · δ'))).
  { apply pathsinv0.
    (* Fail apply assoc. *) use assoc. }
  intermediate_path (γ · (δ · σ)).
  2: { (* Fail apply assoc. *) use assoc. }
  apply maponpaths.
  set (ν'better := # (pre_composition_functor A A' A' hsA' hsA' (H' v)) (# FA' g)).
  change ν' with ν'better.
  clear ν'.
  unfold σ. rewrite functorial_composition_pre_post.
  clear σ.
  rewrite functor_comp.
  rewrite assoc.
  match goal with | [ |- _ = _ · (?Hσ1 · ?Hσ2) ] => set (σ1 := Hσ1); set (σ2 := Hσ2) end.
  apply (maponpaths (# (pre_composition_functor A A A' hsA hsA' ((FA v): [A, A, hsA])))) in Hyp'.
  do 2 rewrite functor_comp in Hyp'.
  assert (Hypvariant: δ · σ1 = # (pre_composition_functor A A A' hsA hsA' (FA v)) (# H g)
       · # (pre_composition_functor A A A' hsA hsA' (FA v)) π').
  { etrans.
    2: { exact Hyp'. }
    apply maponpaths.
    change (σ1 = # (pre_composition_functor A A A' hsA hsA' (FA v))
                   (# (post_composition_functor A A A' hsA hsA' G) (# FA g))).
    apply exchange_postcomp_precomp_mor. }
  clear Hyp'.
  intermediate_path (δ · σ1 · σ2).
  2: { apply pathsinv0. (* Fail apply assoc. *) use assoc. }
  rewrite Hypvariant.
  clear δ σ1 Hypvariant.
  match goal with | [ |- _ = ?Hν'variant · ?Hδ'π' · _] => set (ν'variant := Hν'variant); set (δ'π' := Hδ'π') end.
  assert (ν'variantok: ν'variant = ν'better).
  { change (# (pre_composition_functor A A A' hsA hsA' (FA v)) (# (pre_composition_functor A A' A' hsA' hsA' G) (# FA' g)) =
           # (pre_composition_functor A A' A' hsA' hsA' (pre_composition_functor A A A' hsA hsA' (FA v) G)) (# FA' g)).
    apply assoc_precomp_precomp_mor.
  }
  rewrite ν'variantok.
  clear ν'variant ν'variantok.
  rewrite <- assoc.
  intermediate_path (ν'better · (δ'π' · σ2)).
  2: { (* Fail apply assoc. *) use assoc. }
  apply maponpaths.
  clear ν'better.
  assert (auxhorcomp' := functorial_composition_pre_post _ _ _ hsA hsA' _ _ _ _ (# FA f) π').
  rewrite functorial_composition_post_pre in auxhorcomp'.
  change (# (pre_composition_functor A A A' hsA hsA' (FA v')) π') with δ' in auxhorcomp'.
  change (# (pre_composition_functor A A A' hsA hsA' (FA v)) π') with δ'π' in auxhorcomp'.
  assert (ι'ok: ι' = # (post_composition_functor A A A' hsA hsA' (H w')) (# FA f)).
  { change (# (post_composition_functor A A' A' hsA' hsA' (FA' w'))
              (# (post_composition_functor A A A' hsA hsA' G) (# FA f)) =
              # (post_composition_functor A A A' hsA hsA'
                                          (post_composition_functor A A' A' hsA' hsA' (FA' w') G))
                (# FA f)).
    apply assoc_postcomp_postcomp_mor.
  }
  assert (σ2ok: σ2 = # (post_composition_functor A A A' hsA hsA' (H' w')) (# FA f)).
  { change (σ2 = # (post_composition_functor A A A' hsA hsA'
                                             (post_composition_functor _ _ _ hsA hsA' G (FA w'))) (# FA f)).
    apply assoc_postcomp_postcomp_mor. }
  rewrite ι'ok, σ2ok.
  clear ι' σ2 ι'ok σ2ok.
  exact auxhorcomp'.
Qed.

Definition montrafotarget_tensor_data: functor_data (montrafotarget_precat ⊠ montrafotarget_precat) montrafotarget_precat.
Proof.
  use make_functor_data.
  + intro vηwπ.
    induction vηwπ as [[v η] [w π]].
    exists (v ⊗ w).
    exact (param_distr_pentagon_eq_body_variant_RHS Mon_V hsA hsA' FA FA' G v w η π).
  + intros vηwπ vηwπ' fgHyps. induction vηwπ as [[v η] [w π]]. induction vηwπ' as [[v' η'] [w' π']].
    induction fgHyps as [[f Hyp] [g Hyp']].
    use tpair.
    * exact (# tensor (f #, g)).
    * cbv beta in |- *.
      unfold pr2.
      apply montrafotarget_tensor_comp_aux; [exact Hyp | exact Hyp'].
Defined.

Lemma montrafotarget_tensor_data_is_functor: is_functor montrafotarget_tensor_data.
Proof.
  split.
  + intro vηwπ.
    use total2_paths_f.
    * cbn.
      etrans.
      { apply maponpaths. apply binprod_id. }
      apply functor_id.
    * apply (isaset_nat_trans hsA').
  + intros vηwπ1 vηwπ2 vηwπ3 fgHyps fgHyps'.
    use total2_paths_f.
    * cbn.
      etrans.
      { apply maponpaths. apply binprod_comp. }
      apply functor_comp.
    * apply (isaset_nat_trans hsA').
Qed.


Definition montrafotarget_tensor: montrafotarget_precat ⊠ montrafotarget_precat ⟶ montrafotarget_precat :=
  montrafotarget_tensor_data ,, montrafotarget_tensor_data_is_functor.

(** we have the definition of the tensor product, but there are also six pending statements for the justification
    of the operations of the monoidal category - this does not concern their laws but their built-in proofs *)

Lemma montrafotarget_monprecat_left_unitor_aux1 (vη : montrafotarget_precat):
  pr2 (I_pretensor montrafotarget_tensor montrafotarget_unit vη)
      -->[monoidal_precat_left_unitor Mon_V (pr1 vη)]
      pr2 (functor_identity montrafotarget_precat vη).
Proof.
  unfold mor_disp. unfold trafotarget_disp. hnf.
  induction vη as [v η].
  change ([A, A', hsA']⟦H v, H' v⟧) in η.
  etrans.
  2: { apply maponpaths. cbn. apply idpath. }
  simpl. (* not cbn! *)
  unfold param_distr_pentagon_eq_body_variant_RHS, param_distr_triangle_eq_variant0_RHS, param_distr_pentagon_eq_body_RHS.
  rewrite functor_comp.
  match goal with | [ |- ?Hl1 · (?Hl2 · ?Hl3 · ?Hl4 · ?Hl5) · ?Hl6 = ?Hr1 · _] => set (l1 := Hl1); set (l2 := Hl2); set (l3 := Hl3); set (l4 := Hl4); set (l5 := Hl5); set (l6 := Hl6); set (r1 := Hr1) end.
  (* repeat rewrite <- assoc. still cannot incorporate l6 *)
Admitted.

Lemma montrafotarget_monprecat_left_unitor_aux2 (vη : montrafotarget_precat):
  pr2 (functor_identity montrafotarget_precat vη)
      -->[pr1 (pr2 (monoidal_precat_left_unitor Mon_V) (pr1 vη))]
      pr2 (I_pretensor montrafotarget_tensor montrafotarget_unit vη).
Proof.
  unfold mor_disp. unfold trafotarget_disp. hnf.
  induction vη as [v η].
  change ([A, A', hsA']⟦H v, H' v⟧) in η.
  etrans.
  { apply cancel_postcomposition. cbn. apply idpath. }
  simpl. (* not cbn! *)
  unfold param_distr_pentagon_eq_body_variant_RHS, param_distr_triangle_eq_variant0_RHS, param_distr_pentagon_eq_body_RHS.
  rewrite functor_comp.
  apply pathsinv0.
  match goal with | [ |- ?Hl1 · (?Hl2 · (?Hl3 · ?Hl4 · ?Hl5 · ?Hl6)) = _ · ?Hr2] => set (l1 := Hl1); set (l2 := Hl2); set (l3 := Hl3); set (l4 := Hl4); set (l5 := Hl5); set (l6 := Hl6); set (r2 := Hr2) end.
  (* repeat rewrite assoc. yields  l1 · (l2 · (l3 · l4 · l5 · l6)) to the left *)
Admitted.

Lemma montrafotarget_monprecat_right_unitor_aux1 (vη : montrafotarget_precat):
  pr2 (I_posttensor montrafotarget_tensor montrafotarget_unit vη)
      -->[monoidal_precat_right_unitor Mon_V (pr1 vη)]
      pr2 (functor_identity montrafotarget_precat vη).
Proof.
  unfold mor_disp. unfold trafotarget_disp. hnf.
  induction vη as [v η].
  change ([A, A', hsA']⟦H v, H' v⟧) in η.
  etrans.
  2: { apply maponpaths. cbn. apply idpath. }
  simpl. (* not cbn! *)
  unfold param_distr_pentagon_eq_body_variant_RHS, param_distr_triangle_eq_variant0_RHS, param_distr_pentagon_eq_body_RHS.
  rewrite functor_comp.
  match goal with | [ |- ?Hl1 · (?Hl2 · (?Hl3 · ?Hl4) · ?Hl5) · ?Hl6 = ?Hr1 · _] => set (l1 := Hl1); set (l2 := Hl2); set (l3 := Hl3); set (l4 := Hl4); set (l5 := Hl5); set (l6 := Hl6); set (r1 := Hr1) end.
  (* repeat rewrite assoc. and repeat rewrite <- assoc. work incompletely *)
Admitted.

Lemma montrafotarget_monprecat_right_unitor_aux2 (vη : montrafotarget_precat):
  pr2 (functor_identity montrafotarget_precat vη)
      -->[pr1 (pr2 (monoidal_precat_right_unitor Mon_V) (pr1 vη))]
      pr2 (I_posttensor montrafotarget_tensor montrafotarget_unit vη).
Proof.
  unfold mor_disp. unfold trafotarget_disp. hnf.
  induction vη as [v η].
  change ([A, A', hsA']⟦H v, H' v⟧) in η.
  etrans.
  { apply cancel_postcomposition. cbn. apply idpath. }
  simpl. (* not cbn! *)
  unfold param_distr_pentagon_eq_body_variant_RHS, param_distr_triangle_eq_variant0_RHS, param_distr_pentagon_eq_body_RHS.
  rewrite functor_comp.
  apply pathsinv0.
  match goal with | [ |- ?Hl1 · (?Hl2 · (?Hl3 · (?Hl4 · ?Hl5) · ?Hl6)) = _ · ?Hr2] => set (l1 := Hl1); set (l2 := Hl2); set (l3 := Hl3); set (l4 := Hl4); set (l5 := Hl5); set (l6 := Hl6); set (r2 := Hr2) end.
  (* same comment on assoc as before *)
Admitted.

Lemma montrafotarget_monprecat_associator_aux1 (vηs : (montrafotarget_precat ⊠ montrafotarget_precat) ⊠ montrafotarget_precat):
  pr2 (assoc_left montrafotarget_tensor vηs)
      -->[monoidal_precat_associator Mon_V ((pr111 vηs,, pr121 vηs),, pr12 vηs)]
      pr2 (assoc_right montrafotarget_tensor vηs).
Proof.
  unfold mor_disp. unfold trafotarget_disp. hnf.
  induction vηs as [[[v1 η1] [v2 η2]] [v3 η3]].
  change ([A, A', hsA']⟦H v1, H' v1⟧) in η1.
  change ([A, A', hsA']⟦H v2, H' v2⟧) in η2.
  change ([A, A', hsA']⟦H v3, H' v3⟧) in η3.
  simpl. (* not cbn! *)
  unfold param_distr_pentagon_eq_body_variant_RHS, param_distr_triangle_eq_variant0_RHS, param_distr_pentagon_eq_body_RHS.
  do 2 rewrite functor_comp.
  match goal with | [ |- _ · (_ · ?Hlpart · _ · _) · _  = _] => set (lpart := Hlpart) end.
  set (lpartbetter :=
         # (post_composition_functor A A' A' hsA' hsA' (FA' v3))
           (# (post_composition_functor A A' A' hsA' hsA' (FA' v2)) η1) ·
           # (post_composition_functor A A' A' hsA' hsA' (FA' v3))
           (# (pre_composition_functor A A A' hsA hsA' (FA v1)) η2) ·
           # (post_composition_functor A A' A' hsA' hsA' (FA' v3))
           (# (ActionBasedStrength.postcompF hsA hsA' G) (lax_monoidal_functor_μ FA (v1,, v2)))).
  assert (lpartbetterok: lpart = lpartbetter).
  { unfold lpart, lpartbetter.
    etrans.
    { use functor_comp. }
    use cancel_postcomposition. (* does not work with apply *)
(* earlier attempt:
   match goal with | [ |- ?Hlpart1 · ?Hlpart2 = _ · ?Hrpart3] => set (lpart1 := Hlpart1); set (lpart2 := Hlpart2); set (rpart3 := Hrpart3) end.
    change rpart3 with lpart2. clear rpart3.
    use (cancel_postcomposition _ _ lpart2). *)
    use functor_comp.
  }
  rewrite lpartbetterok. unfold lpartbetter. clear lpart lpartbetter lpartbetterok.
  match goal with | [ |- _ = _ · (_ · (_ · (_ · ?Hrpart) · _)) ] => set (rpart := Hrpart) end.
  set (rpartbetter :=
         # (pre_composition_functor A A A' hsA hsA' (FA v1))
           (# (post_composition_functor A A' A' hsA' hsA' (FA' v3)) η2) ·
           # (pre_composition_functor A A A' hsA hsA' (FA v1))
           (# (pre_composition_functor A A A' hsA hsA' (FA v2)) η3) ·
           # (pre_composition_functor A A A' hsA hsA' (FA v1))
           (# (ActionBasedStrength.postcompF hsA hsA' G) (lax_monoidal_functor_μ FA (v2,, v3)))).
  assert (rpartbetterok: rpart = rpartbetter).
  { unfold rpart, rpartbetter.
    etrans.
    { use functor_comp. }
    use cancel_postcomposition.
    use functor_comp.
  }
  rewrite rpartbetterok. unfold rpartbetter. clear rpart rpartbetter rpartbetterok.
  match goal with | [ |- ?Hl1 · (?Hl2 · (?Hl3 · ?Hl4 · ?Hl5) · ?Hl6 · ?Hl7) · ?Hl8  = _] => set (l1 := Hl1); set (l2 := Hl2); set (l3 := Hl3); set (l4 := Hl4); set (l5 := Hl5); set (l6 := Hl6); set (l7 := Hl7); set (l8 := Hl8) end.
  match goal with | [ |- _ = ?Hr1 · (?Hr2 · (?Hr3 · (?Hr4 · (?Hr5 · ?Hr6 · ?Hr7)) · ?Hr8))] => set (r1 := Hr1); set (r2 := Hr2); set (r3 := Hr3); set (r4 := Hr4); set (r5 := Hr5); set (r6 := Hr6); set (r7 := Hr7); set (r8 := Hr8) end.
  (* same comment on assoc as before *)
Admitted.

Lemma montrafotarget_monprecat_associator_aux2 (vηs : (montrafotarget_precat ⊠ montrafotarget_precat) ⊠ montrafotarget_precat):
  pr2 (assoc_right montrafotarget_tensor vηs)
      -->[pr1 (pr2 (monoidal_precat_associator Mon_V) ((pr111 vηs,, pr121 vηs),, pr12 vηs))]
      pr2 (assoc_left montrafotarget_tensor vηs).
Proof.
  unfold mor_disp. unfold trafotarget_disp. hnf.
  induction vηs as [[[v1 η1] [v2 η2]] [v3 η3]].
  change ([A, A', hsA']⟦H v1, H' v1⟧) in η1.
  change ([A, A', hsA']⟦H v2, H' v2⟧) in η2.
  change ([A, A', hsA']⟦H v3, H' v3⟧) in η3.
  simpl. (* not cbn! *)
  unfold param_distr_pentagon_eq_body_variant_RHS, param_distr_triangle_eq_variant0_RHS, param_distr_pentagon_eq_body_RHS.
  do 2 rewrite functor_comp.
  match goal with | [ |- _ · (_ · (_ · ?Hlpart) · _) · _  = _] => set (lpart := Hlpart) end.
  set (lpartbetter :=
         # (pre_composition_functor A A A' hsA hsA' (FA v1))
           (# (post_composition_functor A A' A' hsA' hsA' (FA' v3)) η2) ·
           # (pre_composition_functor A A A' hsA hsA' (FA v1))
           (# (pre_composition_functor A A A' hsA hsA' (FA v2)) η3) ·
           # (pre_composition_functor A A A' hsA hsA' (FA v1))
           (# (ActionBasedStrength.postcompF hsA hsA' G) (lax_monoidal_functor_μ FA (v2,, v3)))).
  assert (lpartbetterok: lpart = lpartbetter).
  { unfold lpart, lpartbetter.
    etrans.
    { use functor_comp. }
    use cancel_postcomposition. (* does not work with apply *)
    use functor_comp.
  }
  rewrite lpartbetterok. unfold lpartbetter. clear lpart lpartbetter lpartbetterok.
  match goal with | [ |- _ = _ · (_ · (_ · ?Hrpart · _ · _)) ] => set (rpart := Hrpart) end.
  set (rpartbetter :=
         # (post_composition_functor A A' A' hsA' hsA' (FA' v3))
           (# (post_composition_functor A A' A' hsA' hsA' (FA' v2)) η1) ·
           # (post_composition_functor A A' A' hsA' hsA' (FA' v3))
           (# (pre_composition_functor A A A' hsA hsA' (FA v1)) η2) ·
           # (post_composition_functor A A' A' hsA' hsA' (FA' v3))
           (# (ActionBasedStrength.postcompF hsA hsA' G) (lax_monoidal_functor_μ FA (v1,, v2)))).
  assert (rpartbetterok: rpart = rpartbetter).
  { unfold rpart, rpartbetter.
    etrans.
    { use functor_comp. }
    use cancel_postcomposition.
    use functor_comp.
  }
  rewrite rpartbetterok. unfold rpartbetter. clear rpart rpartbetter rpartbetterok.
  match goal with | [ |- ?Hl1 · (?Hl2 · (?Hl3 · (?Hl4 · ?Hl5 · ?Hl6)) · ?Hl7) · ?Hl8  = _] => set (l1 := Hl1); set (l2 := Hl2); set (l3 := Hl3); set (l4 := Hl4); set (l5 := Hl5); set (l6 := Hl6); set (l7 := Hl7); set (l8 := Hl8) end.
  match goal with | [ |- _ = ?Hr1 · (?Hr2 · (?Hr3 · (?Hr4 · ?Hr5 · ?Hr6) · ?Hr7 · ?Hr8))] => set (r1 := Hr1); set (r2 := Hr2); set (r3 := Hr3); set (r4 := Hr4); set (r5 := Hr5); set (r6 := Hr6); set (r7 := Hr7); set (r8 := Hr8) end.
  (* same comment on assoc as before *)
  (* an unhelpful test:
  apply nat_trans_eq; try exact hsA'.
  intro a.
  cbn.
  show_id_type. *)
Admitted.

Definition montrafotarget_monprecat_left_unitor: left_unitor montrafotarget_tensor montrafotarget_unit.
Proof.
  use make_nat_z_iso.
  + use make_nat_trans.
    * intro vη.
      exists (monoidal_precat_left_unitor Mon_V (pr1 vη)).
      (* another reasoning in functorial calculus needed *)
      apply montrafotarget_monprecat_left_unitor_aux1.
    * intros vη vη' fg.
      use total2_paths_f.
      -- cbn. apply (nat_trans_ax (monoidal_precat_left_unitor Mon_V)).
      -- apply (isaset_nat_trans hsA').
  + intro vη.
    use make_is_z_isomorphism.
    * exists (pr1 (pr2 (monoidal_precat_left_unitor Mon_V) (pr1 vη))).
      (* another reasoning in functorial calculus needed *)
      apply montrafotarget_monprecat_left_unitor_aux2.
    * split.
      -- use total2_paths_f.
         ++ cbn. apply (pr2 (pr2 (monoidal_precat_left_unitor Mon_V) (pr1 vη))).
         ++ apply (isaset_nat_trans hsA').
      -- use total2_paths_f.
         ++ cbn. apply (pr2 (pr2 (monoidal_precat_left_unitor Mon_V) (pr1 vη))).
         ++ apply (isaset_nat_trans hsA').
Defined.

(* the right unitor is analogous *)
Definition montrafotarget_monprecat_right_unitor: right_unitor montrafotarget_tensor montrafotarget_unit.
Proof.
  use make_nat_z_iso.
  + use make_nat_trans.
    * intro vη.
      exists (monoidal_precat_right_unitor Mon_V (pr1 vη)).
      (* another reasoning in functorial calculus needed *)
      apply montrafotarget_monprecat_right_unitor_aux1.
    * intros vη vη' fg.
      use total2_paths_f.
      -- cbn. apply (nat_trans_ax (monoidal_precat_right_unitor Mon_V)).
      -- apply (isaset_nat_trans hsA').
  + intro vη.
    use make_is_z_isomorphism.
    * exists (pr1 (pr2 (monoidal_precat_right_unitor Mon_V) (pr1 vη))).
      (* another reasoning in functorial calculus needed *)
      apply montrafotarget_monprecat_right_unitor_aux2.
    * split.
      -- use total2_paths_f.
         ++ cbn. apply (pr2 (pr2 (monoidal_precat_right_unitor Mon_V) (pr1 vη))).
         ++ apply (isaset_nat_trans hsA').
      -- use total2_paths_f.
         ++ cbn. apply (pr2 (pr2 (monoidal_precat_right_unitor Mon_V) (pr1 vη))).
         ++ apply (isaset_nat_trans hsA').
Defined.

Definition montrafotarget_monprecat_associator: associator montrafotarget_tensor.
Proof.
  use make_nat_z_iso.
  + use make_nat_trans.
    * intro vηs.
      exists (monoidal_precat_associator Mon_V ((pr111 vηs,,pr121 vηs),,pr12 vηs)).
      (* another reasoning in functorial calculus needed *)
      apply montrafotarget_monprecat_associator_aux1.
    * intros vηs vηs' fgs.
      use total2_paths_f.
      -- cbn. exact (pr21 (monoidal_precat_associator Mon_V) ((pr111 vηs,, pr121 vηs),, pr12 vηs)
                         ((pr111 vηs',, pr121 vηs'),, pr12 vηs') ((pr111 fgs,, pr121 fgs),, pr12 fgs)).
      -- apply (isaset_nat_trans hsA').
  + intro vηs.
    use make_is_z_isomorphism.
    * exists (pr1 (pr2 (monoidal_precat_associator Mon_V) ((pr111 vηs,, pr121 vηs),, pr12 vηs))).
      (* another reasoning in functorial calculus needed *)
      apply montrafotarget_monprecat_associator_aux2.
    * split.
      -- use total2_paths_f.
         ++ cbn. apply (pr2 (pr2 (monoidal_precat_associator Mon_V) ((pr111 vηs,, pr121 vηs),, pr12 vηs))).
         ++ apply (isaset_nat_trans hsA').
      --  use total2_paths_f.
          ++ cbn. apply (pr2 (pr2 (monoidal_precat_associator Mon_V) ((pr111 vηs,, pr121 vηs),, pr12 vηs))).
          ++ apply (isaset_nat_trans hsA').
Defined.

Lemma montrafotarget_monprecat_triangle_eq: triangle_eq montrafotarget_tensor montrafotarget_unit
   montrafotarget_monprecat_left_unitor montrafotarget_monprecat_right_unitor montrafotarget_monprecat_associator.
Proof.
  intros vη wη'.
  use total2_paths_f.
  + cbn. assert (triangleinst := pr1 (monoidal_precat_eq Mon_V) (pr1 vη) (pr1 wη')).
    exact triangleinst.
  + apply (isaset_nat_trans hsA').
Qed.

Lemma montrafotarget_monprecat_pentagon_eq: pentagon_eq montrafotarget_tensor montrafotarget_monprecat_associator.
Proof.
  intros vη1 vη2 vη3 vη4.
  use total2_paths_f.
  + cbn. assert (pentagoninst := pr2 (monoidal_precat_eq Mon_V) (pr1 vη1) (pr1 vη2) (pr1 vη3) (pr1 vη4)).
    exact pentagoninst.
  + apply (isaset_nat_trans hsA').
Qed.

Definition montrafotarget_monprecat: monoidal_precat := mk_monoidal_precat montrafotarget_precat
               montrafotarget_tensor montrafotarget_unit montrafotarget_monprecat_left_unitor
               montrafotarget_monprecat_right_unitor montrafotarget_monprecat_associator
               montrafotarget_monprecat_triangle_eq montrafotarget_monprecat_pentagon_eq.

Section IntoMonoidalFunctor.

  Context (δ: parameterized_distributivity_nat Mon_V hsA hsA' FA FA' G)
          (δtr_eq: param_distr_triangle_eq Mon_V hsA hsA' FA FA' G δ)
          (δpe_eq: param_distr_pentagon_eq Mon_V hsA hsA' FA FA' G δ).

Definition lmf_from_param_distr_functor: Mon_V ⟶ montrafotarget_monprecat.
Proof.
  apply (nat_trafo_to_functor hsA' H H' δ).
Defined.

(** we come to an important element of the whole construction - the triangle law enters here *)
Lemma lmf_from_param_distr_ε_aux:
    pr2 (MonoidalFunctors.I_D montrafotarget_monprecat)
    -->[ id pr1 (MonoidalFunctors.I_D montrafotarget_monprecat)]
    pr2 (lmf_from_param_distr_functor (MonoidalFunctors.I_C Mon_V)).
Proof.
  unfold mor_disp. unfold trafotarget_disp. hnf.
  do 2 rewrite functor_id.
  rewrite id_right. rewrite id_left.
  simpl. (* not cbn! *)
  apply param_distr_triangle_eq_variant0_follows in δtr_eq.
  red in δtr_eq.
  unfold MonoidalFunctors.I_C. unfold ActionBasedStrength.I in δtr_eq.
  etrans.
  2: { apply pathsinv0. exact δtr_eq. }
  apply idpath.
Qed.

Definition lmf_from_param_distr_ε:
    pr1 montrafotarget_monprecat ⟦ MonoidalFunctors.I_D montrafotarget_monprecat,
                       lmf_from_param_distr_functor (MonoidalFunctors.I_C Mon_V) ⟧ :=
  (identity _),, lmf_from_param_distr_ε_aux.

(** we come to the crucial element of the whole construction - the pentagon law enters here *)
Lemma lmf_from_param_distr_μ_aux (vw : Mon_V ⊠ Mon_V):
  pr2 (monoidal_functor_map_dom Mon_V montrafotarget_monprecat lmf_from_param_distr_functor vw)
      -->[id pr1 (monoidal_functor_map_dom Mon_V montrafotarget_monprecat lmf_from_param_distr_functor vw)]
  pr2 (monoidal_functor_map_codom Mon_V montrafotarget_monprecat lmf_from_param_distr_functor vw).
Proof.
  unfold mor_disp. unfold trafotarget_disp. hnf.
  red in δpe_eq.
  do 2 rewrite functor_id.
  rewrite id_left, id_right.
  simpl. (* not cbn! *)
  assert (δpe_eqinst := δpe_eq (pr1 vw) (pr2 vw)).
  apply param_distr_pentagon_eq_body_variant_follows in δpe_eqinst.
  unfold param_distr_pentagon_eq_body_variant in δpe_eqinst.
  unfold MonoidalFunctors.tensor_C. unfold ActionBasedStrength.tensor in δpe_eqinst.
  change (pr1 vw, pr2 vw) with vw in δpe_eqinst.
  apply pathsinv0. exact δpe_eqinst.
Qed.

Definition lmf_from_param_distr_μ_data: nat_trans_data
    (monoidal_functor_map_dom Mon_V montrafotarget_monprecat lmf_from_param_distr_functor)
    (monoidal_functor_map_codom Mon_V montrafotarget_monprecat lmf_from_param_distr_functor).
Proof.
  intro vw.
  exists (identity _).
  apply lmf_from_param_distr_μ_aux.
Defined.

Lemma lmf_from_param_distr_μ_data_is_nat: is_nat_trans _ _ lmf_from_param_distr_μ_data.
Proof.
  intros vw vw' fg.
  use total2_paths_f.
  - cbn. rewrite id_left. apply id_right.
  - apply (isaset_nat_trans hsA').
Qed.

Definition lmf_from_param_distr_μ: monoidal_functor_map Mon_V montrafotarget_monprecat lmf_from_param_distr_functor :=
  lmf_from_param_distr_μ_data ,, lmf_from_param_distr_μ_data_is_nat.

Lemma lmf_from_param_distr_assoc: monoidal_functor_associativity Mon_V
                              montrafotarget_monprecat lmf_from_param_distr_functor lmf_from_param_distr_μ.
Proof.
  intros u v w.
  use total2_paths_f.
  * cbn. do 2 rewrite id_right.
    etrans.
    { apply cancel_postcomposition. apply maponpaths.
      exact (binprod_id (u ⊗ v) w). }
    rewrite (functor_id tensor).
    etrans.
    2: { do 2 apply maponpaths. apply pathsinv0, binprod_id. }
    rewrite (functor_id tensor).
    rewrite id_right. apply id_left.
  * apply (isaset_nat_trans hsA').
Qed.

Lemma lmf_from_param_distr_unital: monoidal_functor_unitality Mon_V montrafotarget_monprecat
              lmf_from_param_distr_functor lmf_from_param_distr_ε lmf_from_param_distr_μ.
Proof.
  intro v. split.
  - use total2_paths_f.
    + cbn.
      rewrite id_right.
      etrans.
      2: { apply cancel_postcomposition. apply maponpaths. apply pathsinv0, binprod_id. }
      rewrite (functor_id tensor).
      apply pathsinv0, id_left.
    + apply (isaset_nat_trans hsA').
  - use total2_paths_f.
    + cbn.
      rewrite id_right.
      etrans.
      2: { apply cancel_postcomposition. apply maponpaths. apply pathsinv0, binprod_id. }
      rewrite (functor_id tensor).
      apply pathsinv0, id_left.
    + apply (isaset_nat_trans hsA').
Qed.

Definition lmf_from_param_distr: lax_monoidal_functor Mon_V montrafotarget_monprecat :=
  mk_lax_monoidal_functor _ _ lmf_from_param_distr_functor lmf_from_param_distr_ε lmf_from_param_distr_μ
                          lmf_from_param_distr_assoc lmf_from_param_distr_unital.

(* now similar but not identical code to above for triangle *)
Lemma smf_from_param_distr_is_strong1_aux: pr2 (lmf_from_param_distr (MonoidalFunctors.I_C Mon_V)) -->[id I]
                                           pr2 (MonoidalFunctors.I_D montrafotarget_monprecat).
Proof.
  unfold mor_disp. unfold trafotarget_disp. hnf.
  do 2 rewrite functor_id.
  rewrite id_right. rewrite id_left.
  cbn.
  apply param_distr_triangle_eq_variant0_follows in δtr_eq.
  red in δtr_eq.
  unfold MonoidalFunctors.I_C. unfold ActionBasedStrength.I in δtr_eq.
  exact δtr_eq.
Qed.

Definition smf_from_param_distr_is_strong1_inv: pr1 montrafotarget_monprecat
   ⟦ lmf_from_param_distr (MonoidalFunctors.I_C Mon_V), MonoidalFunctors.I_D montrafotarget_monprecat ⟧.
Proof.
  exists (identity I).
  apply smf_from_param_distr_is_strong1_aux.
Defined.

Lemma smf_from_param_distr_is_strong1_inv_ok: is_inverse_in_precat (lax_monoidal_functor_ϵ lmf_from_param_distr)
                                                                        smf_from_param_distr_is_strong1_inv.
Proof.
  split.
  - use total2_paths_f.
    + cbn. apply id_right.
    + apply (isaset_nat_trans hsA').
  - use total2_paths_f.
    + cbn. apply id_right.
    + apply (isaset_nat_trans hsA').
Qed.

Definition smf_from_param_distr_is_strong1: is_z_isomorphism (lax_monoidal_functor_ϵ lmf_from_param_distr) :=
  smf_from_param_distr_is_strong1_inv ,, smf_from_param_distr_is_strong1_inv_ok.


(* now similar but not identical code to above for pentagon *)
Lemma smf_from_param_distr_is_strong2_aux (vw : Mon_V ⊠ Mon_V):
  pr2 (monoidal_functor_map_codom Mon_V montrafotarget_monprecat lmf_from_param_distr vw)
      -->[id pr1 (monoidal_functor_map_codom Mon_V montrafotarget_monprecat lmf_from_param_distr vw)]
  pr2 (monoidal_functor_map_dom Mon_V montrafotarget_monprecat lmf_from_param_distr vw).
Proof.
  unfold mor_disp. unfold trafotarget_disp. hnf.
  red in δpe_eq.
  do 2 rewrite functor_id.
  rewrite id_left, id_right.
  simpl.
  assert (δpe_eqinst := δpe_eq (pr1 vw) (pr2 vw)).
  apply param_distr_pentagon_eq_body_variant_follows in δpe_eqinst.
  unfold param_distr_pentagon_eq_body_variant in δpe_eqinst.
  unfold MonoidalFunctors.tensor_C. unfold ActionBasedStrength.tensor in δpe_eqinst.
  change (pr1 vw, pr2 vw) with vw in δpe_eqinst.
  exact δpe_eqinst.
Qed.

Definition smf_from_param_distr_is_strong2_inv (vw : Mon_V ⊠ Mon_V): montrafotarget_monprecat
   ⟦ monoidal_functor_map_codom Mon_V montrafotarget_monprecat lmf_from_param_distr vw,
     monoidal_functor_map_dom Mon_V montrafotarget_monprecat lmf_from_param_distr vw ⟧.
Proof.
  exists (identity _).
  apply smf_from_param_distr_is_strong2_aux.
Defined.

Lemma smf_from_param_distr_is_strong2_inv_ok (vw : Mon_V ⊠ Mon_V): is_inverse_in_precat
   (lax_monoidal_functor_μ lmf_from_param_distr vw) (smf_from_param_distr_is_strong2_inv vw).
Proof.
  split.
  - use total2_paths_f.
    + cbn. apply id_right.
    + apply (isaset_nat_trans hsA').
  - use total2_paths_f.
    + cbn. apply id_right.
    + apply (isaset_nat_trans hsA').
Qed.


Definition smf_from_param_distr_is_strong2: is_nat_z_iso (lax_monoidal_functor_μ lmf_from_param_distr) :=
  fun vw => (smf_from_param_distr_is_strong2_inv vw ,, smf_from_param_distr_is_strong2_inv_ok vw).

Definition smf_from_param_distr_parts: strong_monoidal_functor Mon_V montrafotarget_monprecat :=
  lmf_from_param_distr,, (smf_from_param_distr_is_strong1 ,, smf_from_param_distr_is_strong2).

End IntoMonoidalFunctor.

Definition smf_from_param_distr:
  parameterized_distributivity Mon_V hsA hsA' FA FA' G -> strong_monoidal_functor Mon_V montrafotarget_monprecat.
Proof.
  intro δs.
  induction δs as [δ [δtr_eq δpe_eq]].
  exact (smf_from_param_distr_parts δ δtr_eq δpe_eq).
Defined.

End Functor.


End Main.
