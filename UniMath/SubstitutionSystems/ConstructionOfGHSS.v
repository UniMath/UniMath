(** construction of monoidal heterogeneous substitution systems from arbitrary final coalgebras
   and from initial algebras arising from iteration in omega-cocontinuous functors

authors: Ralph Matthes, Kobe Wullaert, 2023

Note: the name of the file still refers to GHSS although it would more appropriately be MHSS after the renaming from "generalized" to "monoidal" done in July 2023.

*)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Adamek.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.CompletelyIterativeAlgebras.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Actegories.CoproductsInActegories.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.

Require Import UniMath.SubstitutionSystems.GeneralizedSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.ActionScenarioForGenMendlerIteration_alt.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section FixTheContext.

  Context {V : category} {Mon_V : monoidal V}
          {H : V ⟶ V} (θ : pointedtensorialstrength Mon_V H).

  Let PtdV : category := GeneralizedSubstitutionSystems.PtdV Mon_V.
  Let Mon_PtdV : monoidal PtdV := GeneralizedSubstitutionSystems.Mon_PtdV Mon_V.
  Let Act : actegory Mon_PtdV V:= GeneralizedSubstitutionSystems.Act Mon_V.

  Context  (CP : BinCoproducts V) (δ : actegory_bincoprod_distributor Mon_PtdV CP Act).

  Let Const_plus_H (v : V) : functor V V := GeneralizedSubstitutionSystems.Const_plus_H H CP v.

  Definition I_H : functor V V := Const_plus_H I_{Mon_V}.

Section FinalCoalgebraToMHSS.

  Context (νH : coalgebra_ob I_H)
          (isTerminalνH : isTerminal (CoAlg_category I_H) νH).

  Let t : V := pr1 νH.
  Let out : t --> I_H t := pr2 νH.
  Let out_z_iso : z_iso t (I_H t) := finalcoalgebra_z_iso _ I_H νH isTerminalνH.
  Let out_inv : I_H t --> t := inv_from_z_iso out_z_iso.

  Definition final_coalg_to_mhss_step_term
             {Z : PtdV} (f : pr1 Z --> t)
    : Z ⊗_{Act} t --> I_H (CP (Z ⊗_{Act} t) t).
  Proof.
    refine (Z ⊗^{Act}_{l} out · _).
    refine (δ _ _ _ · _).
    refine (BinCoproductOfArrows _ (CP _ _) (CP _ _) (ru_{Mon_V} _) (pr1 θ Z t) · _).
    refine (# (Const_plus_H (pr1 Z)) (BinCoproductIn1 (CP _ t)) · _).
    exact (BinCoproductArrow (CP _ _) (f · out · #I_H (BinCoproductIn2 (CP _ _))) (BinCoproductIn2 _)).
  Defined.

  (** an alternative route through completely iterative algebras *)
  Definition final_coalg_to_mhss_equation_morphism
             {Z : PtdV} (f : pr1 Z --> t)
    : Z ⊗_{Act} t --> CP (I_H (Z ⊗_{Act} t)) t.
  Proof.
    refine (Z ⊗^{Act}_{l} out · _).
    refine (δ _ _ _ · _).
    refine (BinCoproductOfArrows _ (CP _ _) (CP _ _) (ru_{Mon_V} _) (pr1 θ Z t) · _).
    refine (BinCoproductArrow (CP _ _) _ _).
    - refine (f · _).
      apply BinCoproductIn2.
    - refine (BinCoproductIn2 (CP _ _) · _).
      apply BinCoproductIn1.
  Defined.

  Lemma final_coalg_to_mhss_equation_morphism_is_factor
    {Z : PtdV} (f : pr1 Z --> t)
    :  final_coalg_to_mhss_step_term f =
         CompletelyIterativeAlgebras.ϕ_for_cia CP I_H νH isTerminalνH
           (Z ⊗_{Act} t) (final_coalg_to_mhss_equation_morphism f).
  Proof.
    unfold final_coalg_to_mhss_step_term, CompletelyIterativeAlgebras.ϕ_for_cia, final_coalg_to_mhss_equation_morphism.
    repeat rewrite assoc'.
    do 3 apply maponpaths.
    unfold Const_plus_H, GeneralizedSubstitutionSystems.Const_plus_H. cbn. unfold BinCoproduct_of_functors_mor.
    etrans.
    { apply precompWithBinCoproductArrow. }
    rewrite postcompWithBinCoproductArrow.
    apply maponpaths_12.
    - cbn. rewrite id_left.
      rewrite assoc'.
      apply maponpaths.
      rewrite BinCoproductIn2Commutes.
      apply idpath.
    - etrans.
      2: { repeat rewrite assoc'.
           rewrite BinCoproductIn1Commutes.
           apply pathsinv0, BinCoproductOfArrowsIn2. }
      apply idpath.
  Qed.
  (** This clarifies that in the proof below, primitive corecursion can be replaced by only
      exploiting that [out_inv] is a completely iterative algebra (cia), see the alternative
      proof further below. The lemma itself is not used in the sequel. *)

  Let η : I_{Mon_V} --> t := BinCoproductIn1 (CP I_{Mon_V} (H t)) · out_inv.
  Let τ : H t --> t := BinCoproductIn2 (CP I_{Mon_V} (H t)) · out_inv.

  Lemma ητ_is_out_inv : BinCoproductArrow (CP I_{ Mon_V} (H t)) η τ = out_inv.
  Proof.
    apply pathsinv0, BinCoproductArrowEta.
  Qed.

  Local Definition ϕ {Z : PtdV} (f : pr1 Z --> t)
    := final_coalg_to_mhss_step_term f.
  Local Definition Corec_ϕ {Z : PtdV} (f : pr1 Z --> t)
    := primitive_corecursion CP isTerminalνH (x :=  Z ⊗_{Act} t) (ϕ f).

  (** a hand-crafted auxiliary lemma *)
  Local Lemma changing_the_constant_Const_plus_H (x y v w : V)
    (f : v --> w) (fm : w --> v) (g : x --> Const_plus_H y w) (fmf : fm · f = identity _) :
    # (Const_plus_H x) f · BinCoproductArrow (CP _ _) g (BinCoproductIn2 _) =
      BinCoproductArrow (CP _ _) (g · # (Const_plus_H y) fm) (BinCoproductIn2 _) · # (Const_plus_H y) f.
  Proof.
    use BinCoproductArrowsEq.
    - etrans.
      { rewrite assoc.
        apply cancel_postcomposition.
        apply BinCoproductOfArrowsIn1. }
      etrans.
      { rewrite assoc'.
        apply maponpaths.
        apply BinCoproductIn1Commutes. }
      etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           apply pathsinv0, BinCoproductIn1Commutes. }
      etrans.
      2: { rewrite assoc'.
           apply maponpaths.
           apply functor_comp. }
      rewrite fmf.
      rewrite functor_id.
      rewrite id_right.
      apply id_left.
    - etrans.
      { rewrite assoc.
        apply cancel_postcomposition.
        apply BinCoproductOfArrowsIn2. }
      etrans.
      { rewrite assoc'.
        apply maponpaths.
        apply BinCoproductIn2Commutes. }
      etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           apply pathsinv0, BinCoproductIn2Commutes. }
      etrans.
      2: { apply pathsinv0, BinCoproductOfArrowsIn2. }
      apply idpath.
  Qed.

  Lemma final_coalg_to_mhss_has_equivalent_characteristic_formula
    {Z : PtdV} (f : pr1 Z --> t) (h : Z ⊗_{Act} t --> t) :
    primitive_corecursion_characteristic_formula CP (ϕ f) h ≃
      mbracket_property_parts Mon_V H θ t η τ (pr2 Z) f h.
  Proof.
    apply weqimplimpl.
    - intro Hcorec.
      apply (pr2 (mbracket_property_single_equivalent _ _ _ _ _ _ CP _ _ _)).
      red.
      red in Hcorec.
      fold out t in Hcorec.
      rewrite ητ_is_out_inv.
      apply pathsinv0, (z_iso_inv_on_left _ _ _ _ out_z_iso) in Hcorec.
      etrans.
      { apply maponpaths.
        exact Hcorec. }
      clear Hcorec.
      unfold ϕ, final_coalg_to_mhss_step_term.
      etrans.
      { repeat rewrite assoc.
        do 6 apply cancel_postcomposition.
        rewrite assoc'.
        apply maponpaths.
        etrans.
        { apply pathsinv0, (functor_comp (leftwhiskering_functor Act Z)). }
        etrans.
        { apply maponpaths.
          apply (pr222 out_z_iso). }
        apply (functor_id (leftwhiskering_functor Act Z)).
      }
      rewrite id_right.
      etrans.
      { do 5 apply cancel_postcomposition.
        apply (pr2 δ). }
      rewrite id_left.
      repeat rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply maponpaths.
        rewrite assoc.
        apply cancel_postcomposition.
        rewrite (assoc f out).
        apply pathsinv0.
        use changing_the_constant_Const_plus_H.
        apply BinCoproductIn2Commutes.
      }
      etrans.
      { repeat rewrite assoc.
        do 2 apply cancel_postcomposition.
        etrans.
        { apply pathsinv0, (functor_comp (Const_plus_H (pr1 Z))). }
        apply maponpaths.
        apply BinCoproductIn1Commutes.
      }
      repeat rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply postcompWithBinCoproductArrow. }
      rewrite assoc'.
      apply maponpaths_2.
      etrans.
      { apply maponpaths.
        apply (pr122 out_z_iso). }
      apply id_right.
    - intro Hmhss.
      apply (pr1 (mbracket_property_single_equivalent _ _ _ _ _ _ CP _ _ _)) in Hmhss.
      red.
      red in Hmhss.
      fold out t.
      rewrite ητ_is_out_inv in Hmhss.
      rewrite assoc' in Hmhss.
      apply (z_iso_inv_to_left _ _ _ (_,,bincoprod_functor_lineator_strongly
                                        Mon_PtdV CP Act δ (pr1 Z,, pr2 Z) (I_{ Mon_V},,H t))) in Hmhss.
      apply (z_iso_inv_to_left _ _ _ (functor_on_z_iso (leftwhiskering_functor Act (pr1 Z,, pr2 Z)) out_z_iso)) in Hmhss.
      etrans.
      { apply cancel_postcomposition.
        exact Hmhss. }
      clear Hmhss.
      unfold ϕ, final_coalg_to_mhss_step_term.
      repeat rewrite assoc'.
      do 2 apply maponpaths.
      etrans.
      2: { do 2 apply maponpaths.
           rewrite (assoc f out).
           use changing_the_constant_Const_plus_H.
           apply BinCoproductIn2Commutes. }
      apply maponpaths.
      etrans.
      2: { repeat rewrite assoc.
           apply cancel_postcomposition.
           etrans.
           2: { apply (functor_comp (Const_plus_H (pr1 Z))). }
           apply maponpaths.
           apply pathsinv0, BinCoproductIn1Commutes.
      }
      apply maponpaths.
      etrans.
      { apply postcompWithBinCoproductArrow. }
      apply maponpaths.
      unfold τ.
      etrans.
      { rewrite assoc'.
        apply maponpaths.
        apply (pr222 out_z_iso). }
      apply id_right.
    - apply V.
    - apply isaprop_mbracket_property_parts.
  Qed.

  Definition final_coalg_to_mhss : mhss Mon_V H θ.
  Proof.
    exists t.
    exists η.
    exists τ.
    intros Z f.
    simple refine (iscontrretract _ _ _ (Corec_ϕ f)).
    - intros [h Hyp].
      exists h. apply final_coalg_to_mhss_has_equivalent_characteristic_formula. exact Hyp.
    - intros [h Hyp].
      exists h. apply final_coalg_to_mhss_has_equivalent_characteristic_formula. exact Hyp.
    - intros [h Hyp].
      use total2_paths_f.
      + apply idpath.
      + apply isaprop_mbracket_property_parts.
  Defined.

  (** the alternative proof through cia *)
  Lemma final_coalg_to_mhss_equation_morphism_has_equivalent_characteristic_formula
    {Z : PtdV} (f : pr1 Z --> t) (h : Z ⊗_{Act} t --> t) :
    cia_characteristic_formula CP I_H
      (CompletelyIterativeAlgebras.Xinv _ _ isTerminalνH)
      (final_coalg_to_mhss_equation_morphism f) h ≃
      mbracket_property_parts Mon_V H θ t η τ (pr2 Z) f h.
  Proof.
    apply weqimplimpl.
    - intro Hcia.
      apply (pr2 (mbracket_property_single_equivalent _ _ _ _ _ _ CP _ _ _)).
      red.
      red in Hcia.
      rewrite ητ_is_out_inv.
      etrans.
      { apply maponpaths.
        exact Hcia. }
      clear Hcia.
      unfold final_coalg_to_mhss_equation_morphism.
      etrans.
      { repeat rewrite assoc'.
        apply maponpaths.
        repeat rewrite assoc.
        do 5 apply cancel_postcomposition.
        etrans.
        { apply pathsinv0, (functor_comp (leftwhiskering_functor Act Z)). }
        etrans.
        { apply maponpaths.
          apply (pr222 out_z_iso). }
        apply (functor_id (leftwhiskering_functor Act Z)).
      }
      rewrite id_left.
      etrans.
      { repeat rewrite assoc.
        do 4 apply cancel_postcomposition.
        apply (pr2 δ). }
      rewrite id_left.
      repeat rewrite assoc'.
      apply maponpaths.
      unfold GeneralizedSubstitutionSystems.Const_plus_H. cbn.
      unfold BinCoproduct_of_functors_mor.
      rewrite precompWithBinCoproductArrow.
      etrans.
      2: { apply pathsinv0, precompWithBinCoproductArrow. }
      rewrite postcompWithBinCoproductArrow.
      apply maponpaths_12.
      + rewrite assoc'.
        rewrite BinCoproductIn2Commutes.
        do 2 rewrite id_right.
        apply pathsinv0, id_left.
      + repeat rewrite assoc'.
        etrans.
        { apply maponpaths.
          apply BinCoproductIn1Commutes. }
        rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          apply BinCoproductOfArrowsIn2. }
        rewrite assoc'.
        apply idpath.
    - intro Hmhss.
      apply (pr1 (mbracket_property_single_equivalent _ _ _ _ _ _ CP _ _ _)) in Hmhss.
      red.
      red in Hmhss.
      rewrite ητ_is_out_inv in Hmhss.
      rewrite assoc' in Hmhss.
      apply (z_iso_inv_to_left _ _ _ (_,,bincoprod_functor_lineator_strongly
                                        Mon_PtdV CP Act δ (pr1 Z,, pr2 Z) (I_{ Mon_V},,H t))) in Hmhss.
      apply (z_iso_inv_to_left _ _ _ (functor_on_z_iso (leftwhiskering_functor Act (pr1 Z,, pr2 Z)) out_z_iso)) in Hmhss.
      etrans.
      { exact Hmhss. }
      clear Hmhss.
      unfold final_coalg_to_mhss_equation_morphism.
      repeat rewrite assoc'.
      do 3 apply maponpaths.
      unfold GeneralizedSubstitutionSystems.Const_plus_H. cbn.
      unfold BinCoproduct_of_functors_mor.
      rewrite precompWithBinCoproductArrow.
      etrans.
      { apply precompWithBinCoproductArrow. }
      rewrite postcompWithBinCoproductArrow.
      apply maponpaths_12.
      + rewrite assoc'.
        rewrite BinCoproductIn2Commutes.
        do 2 rewrite id_right.
        apply id_left.
      + repeat rewrite assoc'.
        etrans.
        2: { apply maponpaths.
             apply pathsinv0, BinCoproductIn1Commutes. }
        rewrite assoc.
        etrans.
        2: { apply cancel_postcomposition.
             apply pathsinv0, BinCoproductOfArrowsIn2. }
        rewrite assoc'.
        apply idpath.
    - apply V.
    - apply isaprop_mbracket_property_parts.
  Qed.
  (** this proof is a bit shorter and does not need the hand-crafted auxiliary lemma [changing_the_constant_Const_plus_H] *)

  Definition final_coalg_to_mhss_alt : mhss Mon_V H θ.
  Proof.
    exists t.
    exists η.
    exists τ.
    intros Z f.
    simple refine (iscontrretract _ _ _ (cia_from_final_coalgebra CP I_H
      _ isTerminalνH _ (final_coalg_to_mhss_equation_morphism f))).
    - intros [h Hyp].
      exists h. apply final_coalg_to_mhss_equation_morphism_has_equivalent_characteristic_formula. exact Hyp.
    - intros [h Hyp].
      exists h. apply final_coalg_to_mhss_equation_morphism_has_equivalent_characteristic_formula. exact Hyp.
    - intros [h Hyp].
      use total2_paths_f.
      + apply idpath.
      + apply isaprop_mbracket_property_parts.
  Defined.

End FinalCoalgebraToMHSS.

Section InitialAlgebraToMHSS.

  Context (IV : Initial V) (CV : Colims_of_shape nat_graph V) (HH : is_omega_cocont H).

  Let AF : category := FunctorAlg I_H.
  Let chnF : chain V := initChain IV I_H.

  Let t_Initial : Initial AF := colimAlgInitial IV (ActionScenarioForGenMendlerIteration_alt.HF CP H HH I_{Mon_V})  (CV chnF).
  Let t : V := alg_carrier _ (InitialObject t_Initial).
  Let α : I_H t --> t := alg_map I_H (pr1 t_Initial).

  Let η : constant_functor V V I_{Mon_V} t --> t := BinCoproductIn1 (CP _ _) · α.
  Let τ : H t --> t := BinCoproductIn2 (CP _ _) · α.

  (** a more comfortable presentation of the standard iteration scheme *)


  Lemma Iteration_I_H_aux1 (av : V) (aη : I_{Mon_V} --> av) (aτ : H av --> av)
    (aα := av,, BinCoproductArrow (CP I_{ Mon_V} (H av)) aη aτ)
    (h : t --> pr1 aα) : pr21 t_Initial -->[ h] pr2 aα → τ · h = # H h · aτ × η · h = aη.
  Proof.
    intro Hyp.
    cbn in Hyp.
    split.
    + apply (maponpaths (fun x => BinCoproductIn2 _ · x)) in Hyp.
      rewrite assoc in Hyp.
      etrans.
      { exact Hyp. }
      etrans.
      { apply maponpaths.
        apply precompWithBinCoproductArrow. }
      apply BinCoproductIn2Commutes.
    + apply (maponpaths (fun x => BinCoproductIn1 _ · x)) in Hyp.
      rewrite assoc in Hyp.
      etrans.
      { exact Hyp. }
      etrans.
      { apply maponpaths.
        apply precompWithBinCoproductArrow. }
      cbn.
      rewrite id_left.
      apply BinCoproductIn1Commutes.
  Qed.

  Lemma Iteration_I_H_aux2 (av : V) (aη : I_{Mon_V} --> av) (aτ : H av --> av)
    (aα := av,, BinCoproductArrow (CP I_{ Mon_V} (H av)) aη aτ) (h : t --> av) :
    τ · h = # H h · aτ → η · h = aη → pr21 t_Initial -->[ h] pr2 aα.
  Proof.
    intros Hyp1 Hyp2.
    cbn.
    etrans.
    { apply cancel_postcomposition.
      apply BinCoproductArrowEta. }
    etrans.
    { apply postcompWithBinCoproductArrow. }
    etrans.
    2: { apply pathsinv0, precompWithBinCoproductArrow. }
    apply maponpaths_12.
    + cbn. rewrite id_left. exact Hyp2.
    + cbn. exact Hyp1.
  Qed.

  Definition Iteration_I_H (av : V) (aη : I_{Mon_V} --> av) (aτ : H av --> av) :
    ∃! h : t --> av, τ · h = # H h · aτ × η · h = aη.
  Proof.
    transparent assert (aα : (ob AF)).
    { use tpair.
      - exact av.
      - exact (BinCoproductArrow (CP _ _) aη aτ).
    }
    simple refine (iscontrretract _ _ _ (pr2 t_Initial aα)).
    - intros [h Hyp].
      exists h.
      apply Iteration_I_H_aux1.
      exact Hyp.
    - intros [h [Hyp1 Hyp2]].
      exists h.
      apply Iteration_I_H_aux2.
      + exact Hyp1.
      + exact Hyp2.
    - abstract (intros [h Hyp]; use total2_paths_f; [ apply idpath | apply isapropdirprod; apply V]).
  Defined.

  Context (initial_annihilates : ∏ (v : V), isInitial V (v ⊗_{Mon_V} (InitialObject IV))).
  Context (left_whiskering_omega_cocont : ∏ (v : V), is_omega_cocont (leftwhiskering_functor Mon_V v)).

  Definition initial_alg_to_mhss : mhss Mon_V H θ.
  Proof.
    exists t.
    exists η.
    exists τ.
    intros Z f.
    red.
    unfold mbracket_property_parts.
    set (Mendler_inst := SpecialGenMendlerIterationWithActegoryAndStrength Mon_PtdV IV CV Act
                           Z CP H HH I_{Mon_V} t θ τ (ru^{Mon_V}_{ pr1 Z} · f)
                           (initial_annihilates (pr1 Z)) (left_whiskering_omega_cocont (pr1 Z)) δ).
    simple refine (iscontrretract _ _ _ Mendler_inst).
    - intros [h [Hyp1 Hyp2]].
      exists h.
      split; apply pathsinv0; assumption.
    - intros [h [Hyp1 Hyp2]].
      exists h.
      split; apply pathsinv0; assumption.
    - intros [h Hyp].
      use total2_paths_f.
      + apply idpath.
      + cbn. do 2 rewrite pathsinv0inv0.
        apply idpath.
  Defined.

  Let σ : SigmaMonoid θ := mhss_to_sigma_monoid θ initial_alg_to_mhss.
  Let μ : pr1 σ ⊗_{Mon_V} pr1 σ --> pr1 σ := pr11 (pr212 σ).

  Theorem SigmaMonoidFromInitialAlgebra_is_initial : isInitial _ σ.
  Proof.
    intro asigma.
    induction asigma as [av [[aτ [[aμ aη] Hμη]] Hτ]].
    red in Hτ. cbn in Hτ.
    set (It_inst := Iteration_I_H av aη aτ).
    set (h := pr11 It_inst).
    use tpair.
    - exists h.
      use tpair.
      2: { exact tt. }
      assert (aux := pr21 It_inst).
      hnf in aux.
      split.
      + exact (pr1 aux).
      + red. split.
        2: { red. exact (pr2 aux). }
        red.
        change (h ⊗^{ Mon_V} h · aμ = μ · h).
        destruct aux as [auxτ auxη].
        fold h in auxτ, auxη.
        (** both sides are identical as unique morphism from the Mendler iteration scheme *)
        set (Mendler_inst := SpecialGenMendlerIterationWithActegoryAndStrength Mon_PtdV IV CV Act
                           (t,,η) CP H HH I_{Mon_V} av θ aτ (ru^{Mon_V}_{t} · h)
                           (initial_annihilates t) (left_whiskering_omega_cocont t) δ).
        intermediate_path (pr11 Mendler_inst).
        * apply path_to_ctr.
          red; split.
          -- change (t ⊗^{Mon_V}_{l} η · (h ⊗^{ Mon_V} h · aμ) = ru^{ Mon_V }_{ t} · h).
             etrans.
             2: { apply monoidal_rightunitornat. }
             etrans.
             2: { apply maponpaths.
                  apply (pr12 Hμη). }
             repeat rewrite assoc.
             apply cancel_postcomposition.
             rewrite (bifunctor_equalwhiskers Mon_V).
             unfold functoronmorphisms2.
             rewrite assoc.
             etrans.
             { apply cancel_postcomposition.
               apply pathsinv0, (functor_comp (leftwhiskering_functor Mon_V t)). }
             rewrite auxη.
             apply pathsinv0, (bifunctor_equalwhiskers Mon_V).
          -- change (t ⊗^{Mon_V}_{l} τ · (h ⊗^{ Mon_V} h · aμ) = θ (t,, η) t · # H (h ⊗^{ Mon_V} h · aμ) · aτ).
             etrans.
             2: { apply cancel_postcomposition.
                  rewrite functor_comp.
                  rewrite assoc.
                  apply cancel_postcomposition.
                  transparent assert (h_ptd : (PtdV⟦(t,,η),(av,,aη)⟧)).
                  { exists h.
                    exact auxη.
                  }
                  apply (lineator_is_nattrans_full Mon_PtdV Act Act H
                           (lineator_linnatleft _ _ _ _ θ) (lineator_linnatright _ _ _ _ θ)_ _ _ _ h_ptd h). }
             etrans.
             2: { repeat rewrite assoc'.
                  apply maponpaths.
                  rewrite assoc.
                  apply pathsinv0, Hτ. }
             repeat rewrite assoc.
             apply cancel_postcomposition.
             change (t ⊗^{Mon_V}_{l} τ · h ⊗^{Mon_V} h = h ⊗^{Mon_V} #H h · av ⊗^{Mon_V}_{l} aτ).
             etrans.
             2: { unfold functoronmorphisms1.
                  rewrite assoc'.
                  apply maponpaths.
                  apply (functor_comp (leftwhiskering_functor Mon_V av)). }
             rewrite <- auxτ.
             etrans.
             { rewrite (bifunctor_equalwhiskers Mon_V).
               unfold functoronmorphisms2.
               rewrite assoc.
               apply cancel_postcomposition.
               apply pathsinv0, (functor_comp (leftwhiskering_functor Mon_V t)). }
             apply pathsinv0, (bifunctor_equalwhiskers Mon_V).
        * apply pathsinv0, path_to_ctr.
          red; split.
          -- change (t ⊗^{Mon_V}_{l} η · (μ · h) = ru^{ Mon_V }_{ t} · h).
             rewrite assoc.
             etrans.
             { apply cancel_postcomposition.
               apply (monoid_to_unit_right_law Mon_V (pr212 σ)). }
             apply idpath.
          -- change (t ⊗^{Mon_V}_{l} τ · (μ · h) = θ (t,, η) t · # H (μ · h) · aτ).
             rewrite assoc.
             etrans.
             { apply cancel_postcomposition.
               apply pathsinv0, (pr22 σ). }
             repeat rewrite assoc'.
             apply maponpaths.
             etrans.
             2: { apply cancel_postcomposition.
                  apply pathsinv0, functor_comp. }
             rewrite assoc'.
             apply maponpaths.
             exact auxτ.
    - hnf.
      intros [ah Hyp].
      use total2_paths_f.
      { apply (path_to_ctr _ _ It_inst).
        cbn in Hyp.
        split.
        + exact (pr11 Hyp).
        + exact (pr221 Hyp).
      }
      show_id_type.
      assert (aux: isaprop TYPE).
      { apply isapropdirprod.
        + apply isapropdirprod.
          * apply V.
          * apply isaprop_is_monoid_mor.
        + apply isapropunit.
      }
      apply aux.
  Qed.

  Definition SigmaMonoidFromInitialAlgebraInitial : Initial (SigmaMonoid θ)
    := σ,,SigmaMonoidFromInitialAlgebra_is_initial.

End InitialAlgebraToMHSS.

End FixTheContext.
