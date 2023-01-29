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

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoidsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.CoproductsInActegories.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.

Require Import UniMath.SubstitutionSystems.GeneralizedSubstitutionSystems.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section TerminalCoalgebraToGHSS.

  Context {V : category} {Mon_V : monoidal V}
          {H : V ⟶ V} (θ : pointedtensorialstrength Mon_V H).

  Let PtdV : category := GeneralizedSubstitutionSystems.PtdV Mon_V.
  Let Mon_PtdV : monoidal PtdV := GeneralizedSubstitutionSystems.Mon_PtdV Mon_V.
  Let Act : actegory Mon_PtdV V:= GeneralizedSubstitutionSystems.Act Mon_V.

  Context  (CP : BinCoproducts V) (δ : bincoprod_distributor Mon_PtdV CP Act).

  Let Const_plus_H (v : V) : functor V V := GeneralizedSubstitutionSystems.Const_plus_H H CP v.

  Definition Id_H : functor V V := Const_plus_H I_{Mon_V}.

  Context (νH : coalgebra_ob Id_H)
          (isTerminalνH : isTerminal (CoAlg_category Id_H) νH).

  Let t : V := pr1 νH.
  Let out : t --> Id_H t := pr2 νH.
  Let out_z_iso : z_iso t (Id_H t) := terminalcoalgebra_z_iso _ Id_H νH isTerminalνH.
  Let out_inv : Id_H t --> t := inv_from_z_iso out_z_iso.

  Definition terminal_coalg_to_ghss_step_term
             {Z : PtdV} (f : V ⟦ pr1 Z, t ⟧)
    : V ⟦ Z ⊗_{Act} t, Id_H (CP (Z ⊗_{Act} t) t) ⟧.
  Proof.
    refine (Z ⊗^{Act}_{l} out · _).
    refine (δ _ _ _ · _).
    refine (BinCoproductOfArrows _ (CP _ _) (CP _ _) (ru_{Mon_V} _) (pr1 θ Z t) · _).
    refine (# (Const_plus_H (pr1 Z)) (BinCoproductIn1 (CP _ t)) · _).
    exact (BinCoproductArrow (CP _ _) (f · out · #Id_H (BinCoproductIn2 (CP _ _))) (BinCoproductIn2 _)).
  Defined.

  Let η := BinCoproductIn1 (CP I_{Mon_V} (H t)) · out_inv.
  Let τ := BinCoproductIn2 (CP I_{Mon_V} (H t)) · out_inv.

  Lemma ητ_is_out_inv : BinCoproductArrow (CP I_{ Mon_V} (H t)) η τ = out_inv.
  Proof.
    apply pathsinv0, BinCoproductArrowEta.
  Qed.

  Local Definition ϕ {Z : PtdV} (f : V ⟦ pr1 Z, t ⟧)
    := terminal_coalg_to_ghss_step_term f.
  Local Definition Corec_ϕ {Z : PtdV} (f : V ⟦ pr1 Z, t ⟧)
    := primitive_corecursion CP isTerminalνH (x :=  Z ⊗_{Act} t) (ϕ f).

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

  Lemma terminal_coalg_to_ghss_has_equivalent_characteristic_formula
    {Z : PtdV} (f : V ⟦ pr1 Z, t ⟧) (h : V ⟦ Z ⊗_{ Act} t, t ⟧) :
    primitive_corecursion_characteristic_formula CP (ϕ f) h <->
      gbracket_property_parts Mon_V H θ t η τ (pr2 Z) f h.
  Proof.
    split.
    - intro Hcorec.
      apply (pr2 (gbracket_property_single_equivalent _ _ _ _ _ _ CP _ _ _)).
      red.
      red in Hcorec.
      fold out t in Hcorec.
      rewrite ητ_is_out_inv.
      apply pathsinv0, (z_iso_inv_on_left _ _ _ _ out_z_iso) in Hcorec.
      etrans.
      { apply maponpaths.
        exact Hcorec. }
      unfold ϕ, terminal_coalg_to_ghss_step_term.
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
    - intro Heq.
      apply (pr1 (gbracket_property_single_equivalent _ _ _ _ _ _ CP _ _ _)) in Heq.
      admit.
  Admitted.

(*
  Lemma terminal_coalg_to_ghss_gbracket_property_parts
        {Z : PtdV} (f : V ⟦ pr1 Z, pr1 νH ⟧)
    : gbracket_property_parts Mon_V H θ (pr1 νH) η τ (pr2 Z) f
                              (pr11 (Corec_ϕ f)).
  Proof.
    unfold gbracket_property_parts.
    Check pr21 (Corec_ϕ f).
    split.
    2: {
      unfold τ.
      etrans.
      1: apply assoc.
      apply pathsinv0.
      apply z_iso_inv_on_left.
      etrans.
      2: apply assoc.
      etrans.
      2: {
        apply maponpaths.
        exact (! pr21 (Corec_ϕ f)).
      }

      unfold ϕ.
      unfold terminal_coalg_to_ghss_gbracket_parts_at_data.
      cbn.

      etrans.
      2: apply assoc'.
      etrans.
      2: {
        apply maponpaths_2.
        etrans.
        2: apply assoc'.
        apply maponpaths_2.
        refine (idpath (pr1 Z ⊗^{Mon_V}_{l} (BinCoproductIn2 (CP I_{ Mon_V} (H (pr1 νH))))) @ _).
        etrans.
        2: apply bifunctor_leftcomp.
        apply maponpaths.
        refine (! id_right _ @ _).
        etrans.
        2: apply assoc.
        apply maponpaths.
        unfold  α'.
        unfold FunctorCoalgebras.f.


        (* exact (pr122 (terminalcoalgebra_z_iso _ Id_H νH isTerminalνH)). *)

        admit.
      }


  Admitted.
*)

  Definition terminal_coalg_to_ghss : ghss Mon_V H θ.
  Proof.
    exists t.
    exists η.
    exists τ.
    intros Z f.
    simple refine (iscontrretract _ _ _ (Corec_ϕ f)).
    - intros [h Hyp].
      exists h. apply terminal_coalg_to_ghss_has_equivalent_characteristic_formula. exact Hyp.
    - intros [h Hyp].
      exists h. apply terminal_coalg_to_ghss_has_equivalent_characteristic_formula. exact Hyp.
    - intros [h Hyp].
      use total2_paths_f.
      + apply idpath.
      + apply isaprop_gbracket_property_parts.
  Defined.


End TerminalCoalgebraToGHSS.
