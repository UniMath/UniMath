(** shows that action-based strong functors can be perceived as strong monoidal functors from the monoidal category that is acting on the underlying categories to a suitable monoidal category

This means that the requirement on strength is that it behaves as a ``homomorphism'' w.r.t. the
monoidal structures.

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

Section Upstream.
  (** this section has nothing to do with monoidal categories but is dictated by the aims of this file *)

  Context {C A A' : precategory}.
  Context (hs : has_homsets A').

  Context (H H' : C ⟶ [A, A', hs]).

  Definition trafotarget_disp_cat_ob_mor: disp_cat_ob_mor C.
  Proof.
    use make_disp_cat_ob_mor.
    - intro c. exact (nat_trans (H c : A ⟶ A') (H' c : A ⟶ A')).
    - intros c c' α β f.
      exact (nat_trans_comp _ _ _ α (# H' f) = nat_trans_comp _ _ _ (# H f) β).
  Defined.

  Lemma trafotarget_disp_cat_id_comp: disp_cat_id_comp C trafotarget_disp_cat_ob_mor.
  Proof.
    split.
    - intros c α.
      red. cbn. rewrite (functor_id H). rewrite (functor_id H').
      apply nat_trans_eq; try exact hs.
      intro a. cbn. rewrite id_left. apply id_right.
    - intros c1 c2 c3 f g α1 α2 α3 Hypf Hypg.
      red. cbn. rewrite (functor_comp H). rewrite (functor_comp H').
      apply nat_trans_eq; try exact hs.
      intro a.
      cbn.
      apply (maponpaths pr1) in Hypf.
      apply toforallpaths in Hypf.
      assert (Hypfinst := Hypf a).
      apply (maponpaths pr1) in Hypg.
      apply toforallpaths in Hypg.
      assert (Hypginst := Hypg a).
      cbn in Hypfinst, Hypginst.
      rewrite assoc.
      rewrite Hypfinst.
      rewrite <- assoc.
      rewrite Hypginst.
      apply assoc.
  Qed.

  Definition trafotarget_disp_cat_data: disp_cat_data C :=
    trafotarget_disp_cat_ob_mor ,, trafotarget_disp_cat_id_comp.

  Lemma trafotarget_disp_cells_isaprop (x y : C) (f : C ⟦ x, y ⟧)
        (xx : trafotarget_disp_cat_data x) (yy : trafotarget_disp_cat_data y):
    isaprop (xx -->[ f] yy).
  Proof.
    cbn. intros Hyp Hyp'.
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

    Definition trafotarget_with_eq: UU := ∑ N: C ⟶ trafotarget_precat,
      functor_data_from_functor _ _ (functor_composite N forget_from_trafotarget) =
      functor_data_from_functor _ _ (functor_identity C).

    Definition nat_trafo_to_functor (η: H ⟹ H'): C ⟶ trafotarget_precat.
    Proof.
      use make_functor.
      - use make_functor_data.
        + intro c.
          exact (c ,, η c).
        + intros c c' f.
          exists f.
          cbn.
          assert (Hyp := nat_trans_ax η _ _ f).
          apply pathsinv0.
          exact Hyp.
      - split; red.
        + intro c. cbn.
          use total2_paths_f.
          * apply idpath.
          * apply (functor_category_has_homsets _ _ hs).
        + intros c1 c2 c3 f f'. cbn.
          use total2_paths_f.
          * apply idpath.
          * apply (functor_category_has_homsets _ _ hs).
    Defined.


  Definition nat_trafo_to_functor_with_eq (η: H ⟹ H'): trafotarget_with_eq.
  Proof.
    exists (nat_trafo_to_functor η).
    apply idpath.
  Defined.

  (*
  Definition functor_to_nat_trafo (Ne: trafotarget_with_eq): H ⟹ H'.
  Proof.
    induction Ne as [N HypN].
    use make_nat_trans.
    - intro c.
      set (trans := pr2 (N c)).
      apply (maponpaths pr1) in HypN.
      apply toforallpaths in HypN.
      assert (HypNinst := HypN c).
      cbn in HypNinst.
      cbn in trans.
      rewrite <- HypNinst.
      exact trans.
    - intros c c' f.
      cbn.
      assert (Ninst := pr2 (# N f)).
      cbn in Ninst.
      set  (HypNc := toforallpaths (λ _ : C, C) (λ a : C, pr1 (N a)) (λ a : C, a) (maponpaths pr1 HypN) c).
      set  (HypNc' := toforallpaths (λ _ : C, C) (λ a : C, pr1 (N a)) (λ a : C, a) (maponpaths pr1 HypN) c').
      assert (HypN2 := HypN).
      show_id_type.
      match goal with | [ H1: @paths ?ID _ _ |- _ ]  => set (TYPE' := ID)  ; simpl in TYPE' end.
      assert (HypN2' := fiber_paths HypN2).
*)
      (* no hope for progress *)

   Definition trafotarget_with_iso: UU := ∑ N: C ⟶ trafotarget_precat,
      nat_z_iso (functor_composite N forget_from_trafotarget) (functor_identity C).

  Definition nat_trafo_to_functor_with_iso (η: H ⟹ H'): trafotarget_with_iso.
  Proof.
    exists (nat_trafo_to_functor η).
    cbn.
    use tpair.
    - use make_nat_trans.
      + intro c. apply identity.
      + intros c c' f. cbn. rewrite id_left. apply id_right.
    - cbn.
      + intro c.
        apply is_z_isomorphism_identity.
  Defined.

  Definition functor_to_nat_trafo_with_iso (Ne: trafotarget_with_iso): H ⟹ H'.
  Proof.
    induction Ne as [N HypN].
    use make_nat_trans.
    - intro c.
      set (trans := pr2 (N c)).
      induction HypN as [τ Hτ].
      set (Hτinst := Hτ c).
      set (τinst := τ c).
      cbn in trans.
      cbn in τinst.
      induction Hτinst as [τ'c [H1 H2]].
      cbn in τ'c.
      refine (nat_trans_comp _ _ _ _ (nat_trans_comp _ _ _ trans _)).
      + exact (# H τ'c).
      + exact (# H' τinst).
    - intros c c' f.
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
  Defined.

  Local Lemma roundtrip1 (η: H ⟹ H'): functor_to_nat_trafo_with_iso (nat_trafo_to_functor_with_iso η) = η.
  Proof.
    apply nat_trans_eq; try exact (functor_category_has_homsets _ _ hs).
    intro c.
    cbn.
    rewrite (functor_id H).
    rewrite (functor_id H').
    apply nat_trans_eq; try exact hs.
    intro a.
    cbn.
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

Context {A A': precategory}.
Context (hsA : has_homsets A) (hsA' : has_homsets A').

Context (FA: strong_monoidal_functor Mon_V (monoidal_precat_of_endofunctors hsA)).
Context (FA': strong_monoidal_functor Mon_V (monoidal_precat_of_endofunctors hsA')).

Context (G : A ⟶ A').

Let H := param_distributivity_dom Mon_V hsA' FA' G.
Let H' := param_distributivity_codom Mon_V hsA hsA' FA G.

Definition montrafotarget_precat: precategory := trafotarget_precat hsA' H H'.

Definition montrafotarget_unit: montrafotarget_precat.
Proof.
  exists I.
  red. cbn.
  exact (param_distr_triangle_eq_variant0_RHS Mon_V hsA hsA' FA FA' G).
Defined.

(* the following let mechanism does not help in the intended use for helping the type-checker
Let nat_trans_type_RL (F0: A'⟶A') (F1: A⟶A): UU:= [A, A', hsA'] ⟦functor_compose hsA' hsA' G F0, functor_compose hsA hsA' F1 G⟧.
Let nat_trans_type_LL (F0 F1: A⟶A): UU:= [A, A', hsA'] ⟦functor_compose hsA hsA' F0 G, functor_compose hsA hsA' F1 G⟧.
 *)
Local Notation "RL[ F0 ',' F1 ]" := ([A, A', hsA'] ⟦functor_compose hsA' hsA' G F0, functor_compose hsA hsA' F1 G⟧) (at level 25).
Local Notation "LL[ F0 ',' F1 ]" := ([A, A', hsA'] ⟦functor_compose hsA hsA' F0 G, functor_compose hsA hsA' F1 G⟧) (at level 25).
Local Notation "RR[ F0 ',' F1 ]" := ([A, A', hsA'] ⟦functor_compose hsA' hsA' G F0, functor_compose hsA' hsA' G F1⟧) (at level 25).


Lemma montrafotarget_tensor_comp_aux (v w v' w': Mon_V) (f: Mon_V⟦v,v'⟧) (g: Mon_V⟦w,w'⟧)
      (η : trafotarget_disp hsA' H H' v) (π : trafotarget_disp hsA' H H' w)
      (η' : trafotarget_disp hsA' H H' v') (π' : trafotarget_disp hsA' H H' w')
      (Hyp: η  -->[ f] η') (Hyp': π -->[ g] π'):
  (param_distr_pentagon_eq_body_variant_RHS Mon_V hsA hsA' FA FA' G v w η π:
     pr1 (trafotarget_disp hsA' H H') (v ⊗ w))
    -->[ # tensor (f,, g : pr1 Mon_V ⊠ pr1 Mon_V ⟦ v,, w, v',, w' ⟧)]
    param_distr_pentagon_eq_body_variant_RHS Mon_V hsA hsA' FA FA' G v' w' η' π'.
Proof.
  change (RL[ FA' v, FA v]) in η.
  change (RL[ FA' w, FA w]) in π.
  change (RL[ FA' v', FA v']) in η'.
  change (RL[ FA' w', FA w']) in π'.
  change (η · (post_whisker (# FA f) G: LL[ FA v, FA v']) = (pre_whisker G (# FA' f): RR[FA' v,FA' v']) · η') in Hyp.
  change (π · (post_whisker (# FA g) G: LL[ FA w, FA w']) = (pre_whisker G (# FA' g): RR[FA' w,FA' w']) · π') in Hyp'.
  change param_distr_pentagon_eq_body_variant_RHS with param_distr_pentagon_eq_body_variant_RHS_in_steps.
  unfold mor_disp.
  hnf.
  match goal with | [ |- _ = ?RHS ] => set (rhs := RHS) end.
  change ((param_distr_pentagon_eq_body_variant_RHS_in_steps Mon_V hsA hsA' FA FA' G v w η π) · (post_whisker (# FA (# tensor ((f,, g): pr1 Mon_V ⊠ pr1 Mon_V ⟦ (v,,w), (v',,w') ⟧))) G:LL[FA (tensor (v,, w)),FA (tensor (v',, w'))]) = rhs).
  match goal with | [ |- ?LHS = _ ] => set (lhs := LHS) end.
  change (lhs = (pre_whisker G (# FA' (# tensor ((f,, g): pr1 Mon_V ⊠ pr1 Mon_V ⟦ (v,,w), (v',,w') ⟧))): RR[FA' (tensor (v,, w)),FA' (tensor (v',, w'))]) · (param_distr_pentagon_eq_body_variant_RHS_in_steps Mon_V hsA hsA' FA FA' G v' w' η' π')).
  unfold lhs.
  unfold param_distr_pentagon_eq_body_variant_RHS_in_steps.
  unfold param_distr_pentagon_eq_body_RHS_in_steps.
  clear rhs lhs.
  match goal with |- @paths ?ID _ _ => set (typeofeq := ID); simpl in typeofeq end.
  assert (typeofeqok: typeofeq = RL[ FA' (tensor (v,,w)), FA (tensor (v',,w'))]) by apply idpath.
  (* goal presented as:
pre_whisker G (strong_monoidal_functor_μ_inv FA' (v,, w))
  · (post_whisker η (FA' w) · pre_whisker (FA v) π · post_whisker (lax_monoidal_functor_μ FA (v,, w)) G)
  · post_whisker (# FA (# tensor (f,, g))) G =
  pre_whisker G (# FA' (# tensor (f,, g)))
  · (pre_whisker G (strong_monoidal_functor_μ_inv FA' (v',, w'))
     · (post_whisker η' (FA' w') · pre_whisker (FA v') π' · post_whisker (lax_monoidal_functor_μ FA (v',, w')) G))
with abbreviated hypotheses:
Hyp : η · post_whisker (# FA f) G = pre_whisker G (# FA' f) · η'
Hyp' : π · post_whisker (# FA g) G = pre_whisker G (# FA' g) · π'
 *)
        set (vw := v,,w). set (vw' := v',,w'). set (fg := f,,g).
(* I have a lengthy proof on paper. *)
        match goal with | [ |- ?Hαinv · (?Hγ · ?Hδ · ?Hβ) · ?Hε = _ ] => set (αinv := Hαinv);
           set (γ := Hγ); set (δ:= Hδ); set (β := Hβ); set (ε1 := Hε) end.
        match goal with | [ |- _ = ?Hε · (?Hαinv · (?Hγ · ?Hδ · ?Hβ)) ] => set (αinv' := Hαinv);
           set (γ' := Hγ); set (δ':= Hδ); set (β' := Hβ); set (ε2 := Hε) end.
(* all these natural transformations have wrong types: they are transformations between functor_data,
   not elements of the functor category. *)
        set (αinviso := prewhisker_with_μ_inv_z_iso Mon_V hsA' FA' G v w).
        transparent assert (αinvisook : (pr1 αinviso = αinv)).
        { apply idpath. }
        rewrite <- assoc.
        apply pathsinv0.
        rewrite <- αinvisook.
        (* one has to reconstruct all the constituents as morphisms of the functor category
        set (help := z_iso_inv_to_left(C:=[A, A', hsA']) _ _ _ αinviso (γ · δ · β · ε1:[A, A', hsA']⟦_,_⟧) (ε2 · (αinv' · (γ' · δ' · β')))).
       *)
Admitted.

Definition montrafotarget_tensor: montrafotarget_precat ⊠ montrafotarget_precat ⟶ montrafotarget_precat.
Proof.
  use make_functor.
  - use make_functor_data.
    + intro vηwπ.
      induction vηwπ as [[v η] [w π]].
      exists (v ⊗ w).
      cbn in η, π. cbn.
      exact (param_distr_pentagon_eq_body_variant_RHS Mon_V hsA hsA' FA FA' G v w η π).
    + intros vηwπ vηwπ' fgHyps. induction vηwπ as [[v η] [w π]]. induction vηwπ' as [[v' η'] [w' π']].
      induction fgHyps as [[f Hyp] [g Hyp']].
      use tpair.
      * exact (# tensor ((f,,g): pr1 Mon_V ⊠ pr1 Mon_V ⟦ (v,,w), (v',,w') ⟧)).
      * change ((param_distr_pentagon_eq_body_variant_RHS Mon_V hsA hsA' FA FA' G v w η π: pr1 (trafotarget_disp hsA' H H') (v⊗w)) -->[(# tensor (f,, g : pr1 Mon_V ⊠ pr1 Mon_V ⟦ v,, w, v',, w' ⟧))] (param_distr_pentagon_eq_body_variant_RHS Mon_V hsA hsA' FA FA' G v' w' η' π')).
        apply montrafotarget_tensor_comp_aux; [exact Hyp | exact Hyp'].
  - split.
    + red. intro vηwπ.
      (* show_id_type. *)
      use total2_paths_f.
      * cbn.
        etrans.
        { apply maponpaths. apply binprod_id. }
        apply functor_id.
      * cbn.
        (* show_id_type. *)
        apply (functor_category_has_homsets _ _ hsA' (functor_compose hsA' hsA' G (FA' (pr11 vηwπ ⊗ pr12 vηwπ)))
                                            (functor_compose _ _ (FA (pr11 vηwπ ⊗ pr12 vηwπ)) G)).
    + red. intros vηwπ1 vηwπ2 vηwπ3 fgHyps fgHyps'.
      use total2_paths_f.
      * cbn.
        etrans.
        { apply maponpaths. apply binprod_comp. }
        apply functor_comp.
      * apply (functor_category_has_homsets _ _ hsA' (functor_compose hsA' hsA' G (FA' (pr11 vηwπ1 ⊗ pr12 vηwπ1)))
                                            (functor_compose _ _ (FA (pr11 vηwπ3 ⊗ pr12 vηwπ3)) G)).
Defined.

Definition montrafotarget_monprecat: monoidal_precat.
Proof.
  use (mk_monoidal_precat montrafotarget_precat montrafotarget_tensor montrafotarget_unit).
  - use make_nat_z_iso.
    + use make_nat_trans.
      * intro vη.
        exists (monoidal_precat_left_unitor Mon_V (pr1 vη)).
        (* another reasoning in functorial calculus needed *)
        admit.
      * intros vη vη' fg.
        use total2_paths_f.
        -- cbn. apply (nat_trans_ax (monoidal_precat_left_unitor Mon_V)).
        -- apply (functor_category_has_homsets _ _ hsA' (functor_compose hsA' hsA' G (FA' (I ⊗ pr1 vη)))
                                               (functor_compose _ _ (FA (pr1 vη')) G)).
    + intro vη.
      use make_is_z_isomorphism.
      * exists (pr1 (pr2 (monoidal_precat_left_unitor Mon_V) (pr1 vη))).
        (* another reasoning in functorial calculus needed *)
        admit.
      * split.
        -- use total2_paths_f.
           ++ cbn. apply (pr2 (pr2 (monoidal_precat_left_unitor Mon_V) (pr1 vη))).
           ++ (* show_id_type. *)
             apply (functor_category_has_homsets _ _ hsA' (functor_compose hsA' hsA' G (FA' (I ⊗ pr1 vη)))
                                                 (functor_compose hsA hsA' (FA (I ⊗ pr1 vη)) G)).
        -- use total2_paths_f.
           ++ cbn. apply (pr2 (pr2 (monoidal_precat_left_unitor Mon_V) (pr1 vη))).
           ++ (* show_id_type. *)
             apply (functor_category_has_homsets _ _ hsA' (functor_compose hsA' hsA' G (FA' (pr1 vη)))
                                                 (functor_compose _ _ (FA (pr1 vη)) G)).
  - (* the right unitor is analogous *) use make_nat_z_iso.
    + use make_nat_trans.
      * intro vη.
        exists (monoidal_precat_right_unitor Mon_V (pr1 vη)).
        (* another reasoning in functorial calculus needed *)
        admit.
      * intros vη vη' fg.
        use total2_paths_f.
        -- cbn. apply (nat_trans_ax (monoidal_precat_right_unitor Mon_V)).
        -- apply (functor_category_has_homsets _ _ hsA' (functor_compose hsA' hsA' G (FA' (pr1 vη ⊗ I)))
                                               (functor_compose _ _ (FA (pr1 vη')) G)).
    + intro vη.
      use make_is_z_isomorphism.
      * exists (pr1 (pr2 (monoidal_precat_right_unitor Mon_V) (pr1 vη))).
        (* another reasoning in functorial calculus needed *)
        admit.
      * split.
        -- use total2_paths_f.
           ++ cbn. apply (pr2 (pr2 (monoidal_precat_right_unitor Mon_V) (pr1 vη))).
           ++ (* show_id_type. *)
             apply (functor_category_has_homsets _ _ hsA' (functor_compose hsA' hsA' G (FA' (pr1 vη ⊗ I)))
                                                 (functor_compose hsA hsA' (FA (pr1 vη ⊗ I)) G)).
        -- use total2_paths_f.
           ++ cbn. apply (pr2 (pr2 (monoidal_precat_right_unitor Mon_V) (pr1 vη))).
           ++ (* show_id_type. *)
             apply (functor_category_has_homsets _ _ hsA' (functor_compose hsA' hsA' G (FA' (pr1 vη)))
                                                 (functor_compose _ _ (FA (pr1 vη)) G)).
  - use make_nat_z_iso.
    + use make_nat_trans.
      * intro vηs. induction vηs as [[vη1 vη2] vη3].
        exists (monoidal_precat_associator Mon_V ((pr1 vη1,,pr1 vη2),,pr1 vη3)).
        (* another reasoning in functorial calculus needed *)
        admit.
      * intros vηs vηs' fgs.
        use total2_paths_f.
        cbn. exact (pr21 (monoidal_precat_associator Mon_V) ((pr111 vηs,, pr121 vηs),, pr12 vηs)
                         ((pr111 vηs',, pr121 vηs'),, pr12 vηs') ((pr111 fgs,, pr121 fgs),, pr12 fgs)).
        (* show_id_type. *)
        apply (functor_category_has_homsets _ _ hsA'
                             (functor_compose hsA' hsA' G (FA' (pr111 vηs ⊗ pr121 vηs ⊗ pr12 vηs)))
                             (functor_compose _ _ (FA (pr111 vηs' ⊗ (pr121 vηs' ⊗ pr12 vηs'))) G)).
    + intro vηs.
      use make_is_z_isomorphism.
      * exists (pr1 (pr2 (monoidal_precat_associator Mon_V) ((pr111 vηs,, pr121 vηs),, pr12 vηs))).
        (* another reasoning in functorial calculus needed *)
        admit.
      * split.
        -- use total2_paths_f.
           ++ cbn. apply (pr2 (pr2 (monoidal_precat_associator Mon_V) ((pr111 vηs,, pr121 vηs),, pr12 vηs))).
           ++ (* show_id_type. *)
              apply (functor_category_has_homsets _ _ hsA'
                              (functor_compose hsA' hsA' G (FA' (pr111 vηs ⊗ pr121 vηs ⊗ pr12 vηs)))
                              (functor_compose _ _ (FA (pr111 vηs ⊗ pr121 vηs ⊗ pr12 vηs)) G)).
        --  use total2_paths_f.
           ++ cbn. apply (pr2 (pr2 (monoidal_precat_associator Mon_V) ((pr111 vηs,, pr121 vηs),, pr12 vηs))).
           ++ (* show_id_type. *)
              apply (functor_category_has_homsets _ _ hsA'
                              (functor_compose hsA' hsA' G (FA' (pr111 vηs ⊗ (pr121 vηs ⊗ pr12 vηs))))
                              (functor_compose _ _ (FA (pr111 vηs ⊗ (pr121 vηs ⊗ pr12 vηs))) G)).
  - intros vη wη'.
    use total2_paths_f.
    + cbn. assert (triangleinst := pr1 (monoidal_precat_eq Mon_V) (pr1 vη) (pr1 wη')).
      exact triangleinst.
    + cbn. show_id_type.
      apply (functor_category_has_homsets _ _ hsA' (functor_compose hsA' hsA' G (FA' (pr1 vη ⊗ I ⊗ pr1 wη'))) (functor_compose _ _ (FA (pr1 vη ⊗ pr1 wη')) G)).
  - intros vη1 vη2 vη3 vη4.
    use total2_paths_f.
    + cbn. assert (pentagoninst := pr2 (monoidal_precat_eq Mon_V) (pr1 vη1) (pr1 vη2) (pr1 vη3) (pr1 vη4)).
      exact pentagoninst.
    + cbn. show_id_type.
      apply (functor_category_has_homsets _ _ hsA' (functor_compose hsA' hsA' G (FA' (pr1 vη1 ⊗ pr1 vη2 ⊗ pr1 vη3 ⊗ pr1 vη4))) (functor_compose _ _ (FA (pr1 vη1 ⊗ (pr1 vη2 ⊗ (pr1 vη3 ⊗ pr1 vη4)))) G)).
Admitted.

End Main.
