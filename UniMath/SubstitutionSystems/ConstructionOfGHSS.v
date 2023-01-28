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

  Definition Const_plus_H (X : V) : functor V V
  := BinCoproduct_of_functors _ _ CP (constant_functor _ _ X) H.

  Definition Id_H :  functor V V
    := Const_plus_H I_{Mon_V}.

  Context (νH : coalgebra_ob Id_H)
          (isTerminalνH : isTerminal (CoAlg_category Id_H) νH).

  Let νH_inv := inv_from_z_iso (terminalcoalgebra_z_iso _ Id_H νH isTerminalνH).

  Definition terminal_coalg_to_ghss_gbracket_parts_at_data
             {Z : PtdV} (f : V ⟦ pr1 Z, pr1 νH ⟧)
    : V ⟦ Z ⊗_{Act} pr1 νH, Id_H (CP (Z ⊗_{Act} pr1 νH) (pr1 νH)) ⟧.
  Proof.
    refine (Z ⊗^{Act}_{l} (pr2 νH) · _).
    refine (δ _ _ _ · _).
    refine (BinCoproductOfArrows _ (CP _ _) (CP _ _) (ru_{Mon_V} _) (pr1 θ Z (pr1 νH)) · _).
    refine (BinCoproductOfArrows _ (CP _ _) (CP _ _) (identity (pr1 Z)) (#H (BinCoproductIn1 (CP _ (pr1 νH)))) · _).
    use (BinCoproductArrow (CP _ _) _ (BinCoproductIn2 _)).
    refine (f · (pr2 νH) · _).
    use (BinCoproductOfArrows _ _ _ (identity _)).
    exact (#H (BinCoproductIn2 (CP _ _))).
  Defined.

  Let η := BinCoproductIn1 (CP I_{Mon_V} (H (pr1 νH))) · νH_inv.
  Let τ := BinCoproductIn2 (CP I_{Mon_V} (H (pr1 νH))) · νH_inv.

  Local Definition ϕ {Z : PtdV} (f : V ⟦ pr1 Z, pr1 νH ⟧)
    := terminal_coalg_to_ghss_gbracket_parts_at_data f.
  Local Definition Corec_ϕ {Z : PtdV} (f : V ⟦ pr1 Z, pr1 νH ⟧)
    := primitive_corecursion CP isTerminalνH (x :=  Z ⊗_{Act} pr1 νH) (ϕ f).

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

  Definition terminal_coalg_to_ghss : ghss Mon_V H θ.
  Proof.
    exists (pr1 νH).
    exists η.
    exists τ.
    intros Z f.
    exists (pr11 (Corec_ϕ f),, terminal_coalg_to_ghss_gbracket_property_parts f).
  Admitted.


End TerminalCoalgebraToGHSS.
