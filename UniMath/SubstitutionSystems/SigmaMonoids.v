(** a generalization of Σ-monoids to monoidal categories in place of functor categories

author: Kobe Wullaert 2023
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoidsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoidsWhiskered.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.SubstitutionSystems.GeneralizedSubstitutionSystems.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section SigmaMonoid.

  Context {V : category}
          {Mon_V : monoidal V}
          {H : V ⟶ V}
          (θ : pointedtensorialstrength Mon_V H).

  Definition SigmaMonoid_disp_cat_no_compatibility : disp_cat V
    := dirprod_disp_cat (algebra_disp_cat H) (monoid_disp_cat Mon_V).

  Definition SigmaMonoid_compatibility
             (X : total_category SigmaMonoid_disp_cat_no_compatibility) : UU.
  Proof.
    set (x := pr1 X).
    set (η := monoid_data_unit _ (pr22 X : monoid _ _)).
    set (μ := monoid_data_multiplication _ (pr22 X : monoid _ _)).
    set (α := pr12 X).
    set (st := pr1 θ (x ,, η) x).
    exact (st · (#H μ) · α = x ⊗^{Mon_V}_{l} α · μ).
  Defined.

  Definition SigmaMonoid_disp_cat_without_sigma_constr
    : disp_cat (total_category SigmaMonoid_disp_cat_no_compatibility)
    := disp_full_sub
         (total_category SigmaMonoid_disp_cat_no_compatibility)
         SigmaMonoid_compatibility.

  Definition SigmaMonoid_disp_cat
    : disp_cat V
    := sigma_disp_cat SigmaMonoid_disp_cat_without_sigma_constr.

  Definition SigmaMonoid : category
    := total_category SigmaMonoid_disp_cat.

End SigmaMonoid.

Section GHSS_to_SigmaMonoid.

  Context {V : category}
          {Mon_V : monoidal V}
          {H : V ⟶ V}
          (θ : pointedtensorialstrength Mon_V H).

  Definition ghhs_to_sigma_monoid (t : ghss Mon_V H θ)
    : SigmaMonoid θ.
  Proof.
    exists (pr1 t).
    exists (tau_from_alg Mon_V H θ t ,, ghss_monoid Mon_V H θ t).
    exact (gfbracket_τ Mon_V H θ t (Z :=  (pr1 t,, μ_0 Mon_V H θ t)) (identity _)).
  Defined.

End GHSS_to_SigmaMonoid.

Section TerminalCoalgebraToGHSS.

  Context {V : category} {Mon_V : monoidal V}
          {H : V ⟶ V} (θ : pointedtensorialstrength Mon_V H).

  Require Import UniMath.CategoryTheory.limits.terminal.
  Require Import UniMath.CategoryTheory.limits.bincoproducts.
  Require Import UniMath.CategoryTheory.FunctorCoalgebras.


  Context  (CP : BinCoproducts V).

  Definition Const_plus_H (X : V) : functor V V
  := BinCoproduct_of_functors _ _ CP (constant_functor _ _ X) H.

  Definition Id_H :  functor V V
    := Const_plus_H I_{Mon_V}.

  Context (νH : coalgebra_ob Id_H)
          (isTerminalνH : isTerminal (CoAlg_category Id_H) νH).

  Let νH_inv := inv_from_z_iso (terminalcoalgebra_z_iso _ Id_H νH isTerminalνH).

  Let PtdV := GeneralizedSubstitutionSystems.PtdV Mon_V.

  Definition to_change_tensor_distributes_over_coproduct
             (Z : PtdV)
    : V ⟦ pr1 Z ⊗_{ Mon_V} CP I_{ Mon_V} (H (pr1 νH)) ,
          CP ((pr1 Z) ⊗_{Mon_V} I_{Mon_V}) ((pr1 Z) ⊗_{Mon_V} (H (pr1 νH)))⟧.
  Proof.
  Admitted.

  Definition terminal_coalg_to_ghss_gbracket_parts_at_data
             {Z : PtdV} (f : V ⟦ pr1 Z, pr1 νH ⟧)
    : V ⟦ pr1 Z ⊗_{ Mon_V} pr1 νH, Id_H (CP (pr1 Z ⊗_{ Mon_V} pr1 νH) (pr1 νH)) ⟧.
  Proof.

    refine ((pr1 Z) ⊗^{Mon_V}_{l} (pr2 νH) · _).
    refine (to_change_tensor_distributes_over_coproduct Z · _).

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
    := primitive_corecursion CP isTerminalνH (x :=  pr1 Z ⊗_{ Mon_V} pr1 νH) (ϕ f).

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
        admit.
      }

      unfold pointedtensorialstrength in θ.
      unfold liftedstrength in θ.
      unfold lineator_lax in θ.

      set (t := lineator_is_nattrans_full _ _ _ _
            (lineator_linnatleft _ _ _ _ θ)
            (lineator_linnatright _ _ _ _ θ)).
      cbn in t.




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
