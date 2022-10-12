Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.

Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.CurriedMonoidalCategories.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.AssociatorUnitorsLayer.
Require Import UniMath.Bicategories.MonoidalCategories.UnivalenceMonCat.FinalLayer.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section EquivalenceWithCurriedMonStruct.

  Definition ucat (C : bicat_of_univ_cats) : category := (C : univalent_category).

  Definition tensor_unit_unitors_associator_equiv_layer (C : bicat_of_univ_cats)
    : disp_tensor_unit_unitors_associator C ≃ tensor_unit_unitors_associator (ucat C).
  Proof.
    apply weqfibtototal.
    intro tu.
    apply weqdirprodasstor.
  Defined.

  Definition cmon_structure_equiv_layer (C : bicat_of_univ_cats)
    : disp_univmon C ≃ CurriedMonoidalCategories.mon_structure (ucat C).
  Proof.
    use weqtotal2.
    { apply tensor_unit_unitors_associator_equiv_layer. }
    intro tuua.
    simpl.
    apply weqimplimpl.
    - intro tpi.
      repeat split ; apply tpi.
    - intro tpi.
      repeat split ; apply tpi.
    - apply isaprop_P_prop.
    - apply isapropdirprod.
      + apply isaprop_triangle_pentagon.
      + apply isaprop_invertible_data.
  Defined.

  Definition cmon_structure_from_layer
             {C : bicat_of_univ_cats} (M : disp_univmon C)
    : mon_structure (ucat C) := pr1 (cmon_structure_equiv_layer C) M.

  Definition cmon_structure_to_layer
             {C : bicat_of_univ_cats} (M : mon_structure (ucat C))
    : disp_univmon C := invmap (cmon_structure_equiv_layer C) M.

  Definition equivalence_cmon_structure_oblayer
    : ob UMONCAT ≃ ∑ C : bicat_of_univ_cats, mon_structure (ucat C).
  Proof.
    apply weqfibtototal.
    intro ; apply cmon_structure_equiv_layer.
  Defined.

  Definition UMONCAT_to_cmon_category (M : ob UMONCAT)
    : ∑ C : bicat_of_univ_cats, mon_structure (ucat C)
    := (equivalence_cmon_structure_oblayer) M.

  Definition cmon_category_to_UMONCAT
             (M : ∑ C : bicat_of_univ_cats, mon_structure (ucat C))
    : ob UMONCAT := invmap (equivalence_cmon_structure_oblayer) M.

  Lemma sigma_with_unit (A : UU) : (∑ _ : A, unit) ≃ A.
  Proof.
    use weq_iso.
    - intro x ; exact (pr1 x).
    - intro a ; apply (a ,, tt).
    - intro.
      use total2_paths_f.
      { apply idpath. }
      apply isapropunit.
    - intro.
      apply idpath.
  Defined.

  Definition cmonstrongfunctor_structure_equiv_layer (C : bicat_of_univ_cats)
    : disp_univstrongfunctor C ≃ CurriedMonoidalCategories.mon_structure (ucat C).
  Proof.
    refine (sigma_with_unit _ ∘ _)%weq.
    use weqtotal2.
    {
      apply cmon_structure_equiv_layer.
    }
    intro ; apply idweq.
  Defined.

End EquivalenceWithCurriedMonStruct.

Section EquivalenceWithCurriedLaxMonFunctors.

  Definition functor_laxmon_from_layer
             {C D : bicat_of_univ_cats}
             (F : bicat_of_univ_cats⟦C,D⟧)
             (tuuaC : disp_univmon C)
             (tuuaD : disp_univmon D)
    : tuuaC -->[F] tuuaD
            -> functor_lax_monoidal F (cmon_structure_from_layer tuuaC) (cmon_structure_from_layer tuuaD).
  Proof.
    intro ptuua.
    use tpair.
    - apply equality_functor_assunitors_with_layer.
      apply (pr1 ptuua).
    - repeat split.
      + apply (pr121 ptuua).
      + apply (pr2 (pr121 ptuua)).
      + apply (pr221 ptuua).
  Defined.

  Definition functor_laxmon_to_layer
             {C D : bicat_of_univ_cats}
             {F : bicat_of_univ_cats⟦C,D⟧}
             (tuuaC : disp_univmon C)
             (tuuaD : disp_univmon D)
    : functor_lax_monoidal F (cmon_structure_from_layer tuuaC) (cmon_structure_from_layer tuuaD) -> tuuaC -->[F] tuuaD.
  Proof.
    intro ptuua.
    use tpair.
    - apply equality_functor_assunitors_with_layer.
      apply ptuua.
    - exact tt.
  Defined.

  Definition functor_laxmon_equiv_layer
             {C D : bicat_of_univ_cats}
             (F : bicat_of_univ_cats⟦C,D⟧)
             (tuuaC : disp_univmon C)
             (tuuaD : disp_univmon D)
    : functor_lax_monoidal F (cmon_structure_from_layer tuuaC) (cmon_structure_from_layer tuuaD) ≃ tuuaC -->[F] tuuaD.
  Proof.
    use weq_iso.
    - apply functor_laxmon_to_layer.
    - apply functor_laxmon_from_layer.
    - intro ; apply idpath.
    - intro.
      use total2_paths_f.
      + apply idpath.
      + apply isapropunit.
  Defined.

  (* Definition univstrongfunctor_to_univmon_on_ob (C : bicat_of_univ_cats)
    : disp_univstrongfunctor C -> disp_univmon C := pr1. *)

  Definition functor_strongmon_equiv_layer
             {C D : bicat_of_univ_cats}
             (F : bicat_of_univ_cats⟦C,D⟧)
             (tuuaC : disp_univstrongfunctor C)
             (tuuaD : disp_univstrongfunctor D)
    : functor_strong_monoidal F (cmon_structure_from_layer (pr1 tuuaC)) (cmon_structure_from_layer (pr1 tuuaD)) ≃ tuuaC -->[F] tuuaD.
  Proof.
    use weqtotal2.
    { apply functor_laxmon_equiv_layer. }
    intro flm.
    use weqimplimpl.
    - intro flms.
      split ; apply flms.
    - intro flms.
      split ; apply flms.
    - apply isaprop_functor_strong.
    - simpl.
      apply isaprop_P_strong_preserving.
  Defined.

End EquivalenceWithCurriedLaxMonFunctors.

Section EquivalenceWithCurriedNatTrans.

  Import Notations.

  Definition nattrans_laxmon_from_layer
             {C D : bicat_of_univ_cats} {F G : bicat_of_univ_cats⟦C,D⟧} (α : F ==> G)
             {tuuaC : disp_univmon C}
             {tuuaD : disp_univmon D}
             (ptuuaF : tuuaC -->[F] tuuaD) (ptuuaG : tuuaC -->[G] tuuaD)
    : ptuuaF ==>[α] ptuuaG
      -> nattrans_tensor_unit
          (functor_laxmon_from_layer F tuuaC tuuaD ptuuaF)
          (functor_laxmon_from_layer _ _ _ ptuuaG)
          α.
  Proof.
    intro ntu.
    apply ntu.
  Defined.

  Definition nattrans_laxmon_to_layer
             {C D : bicat_of_univ_cats} {F G : bicat_of_univ_cats⟦C,D⟧} (α : F ==> G)
             {tuuaC : disp_univmon C}
             {tuuaD : disp_univmon D}
             (ptuuaF : tuuaC -->[F] tuuaD) (ptuuaG : tuuaC -->[G] tuuaD)
    : nattrans_tensor_unit
          (functor_laxmon_from_layer _ _ _ ptuuaF)
          (functor_laxmon_from_layer _ _ _ ptuuaG)
          α
      -> ptuuaF ==>[α] ptuuaG.
  Proof.
    intro ntu.
    repeat (use tpair) ; try (exact tt) ; try (apply ntu).
  Defined.

  Definition nattrans_laxmon_equiv_layer
             {C D : bicat_of_univ_cats} {F G : bicat_of_univ_cats⟦C,D⟧} (α : F ==> G)
             {tuuaC : disp_univmon C}
             {tuuaD : disp_univmon D}
             (ptuuaF : tuuaC -->[F] tuuaD) (ptuuaG : tuuaC -->[G] tuuaD)
    : nattrans_tensor_unit
          (functor_laxmon_from_layer _ _ _ ptuuaF)
          (functor_laxmon_from_layer _ _ _ ptuuaG)
          α
          ≃ ptuuaF ==>[α] ptuuaG.
  Proof.
    use weq_iso.
    - apply nattrans_laxmon_to_layer.
    - apply nattrans_laxmon_from_layer.
    - intro ; apply idpath.
    - intro.
      repeat (use total2_paths_f) ; try (apply idpath) ; try (apply isapropunit).
  Defined.

  Definition nattrans_strongmon_equiv_layer
             {C D : bicat_of_univ_cats} {F G : bicat_of_univ_cats⟦C,D⟧} (α : F ==> G)
             {tuuaC : disp_univstrongfunctor C}
             {tuuaD : disp_univstrongfunctor D}
             (ptuuaF : tuuaC -->[F] tuuaD) (ptuuaG : tuuaC -->[G] tuuaD)
    : nattrans_tensor_unit
          (functor_laxmon_from_layer _ _ _ (pr1 ptuuaF))
          (functor_laxmon_from_layer _ _ _ (pr1 ptuuaG))
          α
          ≃ ptuuaF ==>[α] ptuuaG.
  Proof.
    use weqimplimpl.
    - intro ptc.
      simpl.
      repeat split ; apply ptc.
    - intro ptc.
      simpl.
      repeat split ; apply ptc.
    - apply isaprop_nattrans_tensor_unit.
    - apply isaproptotal2 ; try (intro ; apply isapropunit).
      do 4 intro.
      use total2_paths_f.
      -- use total2_paths_f.
         {
           use total2_paths_f.
           - apply isaprop_preservestensor_commutes.
           - apply isaprop_preservesunit_commutes.
         }
         simpl.
         repeat (apply isapropdirprod) ; apply isapropunit.
      -- apply isapropunit.
  Defined.

End EquivalenceWithCurriedNatTrans.
