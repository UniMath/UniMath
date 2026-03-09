(**

 Constructions of codes for binary sum types in universes

 We have defined what it means for a universe in a category with finite limits and for a
 universe in a comprehension category to support binary sum types. Our goal is to connect these
 two notions. To do so, we use the biequivalence between categories with finite limits and a
 universe and DFL full comprehension categories with a universe. Specifically, we already showed
 that if `C` is a comprehension category with a universe `u`, then its category of contexts also
 has a universe. We construct an equivalence between the type that expresses that `C` supports
 binary sum types and the type that the universe in the category of contexts supports binary
 sum types. The main technical difficulties in this development come from the stability
 conditions, and there are calculational in nature. There are comments in this file explaining
 these challenges.

 Contents
 1. Construction of binary sum types in the category of contexts
 2. Construction of binary sum types in a comprehension category
 3. The equivalence

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodDomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionEso.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionPreservation.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatExamples.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUnivProps.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Sum.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatTypes.Sum.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUniv.

Local Open Scope cat.
Local Open Scope comp_cat.

Section Sum.
  Context {C : dfl_full_comp_cat_with_univ}
          (sum : fiberwise_cat_property
                   stable_bincoproducts_local_property
                   (dfl_full_comp_cat_with_univ_types C)).

  (** * 1. Construction of binary sum types in the category of contexts *)
  Let el := dfl_full_comp_cat_to_finlim_el_map
              (dfl_full_comp_cat_univ_ob C)
              (dfl_full_comp_cat_el C).

  Definition sums_in_dfl_full_comp_cat_to_finlim_univ_code
             (sc : stable_sum_in_comp_cat_univ C sum)
             {Γ : C}
             (a b : Γ --> [] & dfl_full_comp_cat_univ_ob C)
    : Γ --> [] & dfl_full_comp_cat_univ_ob C.
  Proof.
    use (dfl_full_comp_cat_tm_to_mor_univ
           (C := dfl_full_comp_cat_with_univ_types C)).
    refine (sum_in_comp_cat_univ_code sum sc _ _).
    - exact (dfl_full_comp_cat_mor_to_tm_univ
               (C := dfl_full_comp_cat_with_univ_types C)
               _
               a).
    - exact (dfl_full_comp_cat_mor_to_tm_univ
               (C := dfl_full_comp_cat_with_univ_types C)
               _
               b).
  Defined.

  Arguments sums_in_dfl_full_comp_cat_to_finlim_univ_code /.

  Definition sums_in_dfl_full_comp_cat_to_finlim_univ_z_iso
             (sc : stable_sum_in_comp_cat_univ C sum)
             {Γ : C}
             (a b : Γ --> [] & dfl_full_comp_cat_univ_ob C)
    : z_iso
        (dfl_full_comp_cat_to_finlim_bincoproducts
           sum
           (cat_el_map_el el a)
           (cat_el_map_el el b))
        (cat_el_map_el el (sums_in_dfl_full_comp_cat_to_finlim_univ_code sc a b)).
  Proof.
    refine (z_iso_comp
              (z_iso_comp _ (sum_in_comp_cat_univ_z_iso sum sc _ _)) _).
    - use z_iso_inv.
      exact (preserves_bincoproduct_fiber_comp_cat_comprehension_dom_z_iso sum _ _).
    - use comp_cat_comp_fiber_z_iso.
      use (comp_cat_el_map_on_eq_iso (dfl_full_comp_cat_el C)).
      refine (!_).
      apply (dfl_full_comp_cat_tm_to_mor_to_tm_univ
               (dfl_full_comp_cat_univ_ob C)).
  Defined.

  Proposition sums_in_dfl_full_comp_cat_to_finlim_univ_comm
             (sc : stable_sum_in_comp_cat_univ C sum)
             {Γ : C}
             (a b : Γ --> [] & dfl_full_comp_cat_univ_ob C)
    : BinCoproductArrow
        (dfl_full_comp_cat_to_finlim_bincoproducts
           sum
           (cat_el_map_el el a)
           (cat_el_map_el el b))
        (cat_el_map_mor el a)
        (cat_el_map_mor el b)
      =
      sums_in_dfl_full_comp_cat_to_finlim_univ_z_iso sc a b
      · cat_el_map_mor
          el
          (dfl_full_comp_cat_tm_to_mor_univ
             (dfl_full_comp_cat_univ_ob C)
             (sum_in_comp_cat_univ_code sum sc
                (dfl_full_comp_cat_mor_to_tm_univ (dfl_full_comp_cat_univ_ob C) a)
                (dfl_full_comp_cat_mor_to_tm_univ (dfl_full_comp_cat_univ_ob C) b))).
  Proof.
    unfold sums_in_dfl_full_comp_cat_to_finlim_univ_z_iso.
    refine (!_).
    etrans.
    {
      do 2 refine (assoc' _ _ _ @ _).
      do 2 apply maponpaths.
      apply comprehension_functor_mor_comm.
    }
    etrans.
    {
      apply maponpaths.
      rewrite id_right.
      exact (sum_in_comp_cat_univ_comm sum sc _ _).
    }
    exact (preserves_bincoproduct_fiber_comp_cat_comprehension_dom_z_iso_comm _ _ _).
  Qed.

  Definition sums_in_dfl_full_comp_cat_to_finlim_univ
             (sc : stable_sum_in_comp_cat_univ C sum)
    : cat_univ_codes_sums
        (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
        (dfl_full_comp_cat_to_finlim_bincoproducts sum).
  Proof.
    use make_cat_univ_codes_sums.
    - exact (λ Γ a b, sums_in_dfl_full_comp_cat_to_finlim_univ_code sc a b).
    - exact (λ Γ a b, sums_in_dfl_full_comp_cat_to_finlim_univ_z_iso sc a b).
    - exact (λ Γ a b, sums_in_dfl_full_comp_cat_to_finlim_univ_comm sc a b).
  Defined.

  (**
     Stability expresses two equalities: one for the codes and one for the isomorphism
     relating the code to the type that it is supposed to represent. The first stability
     condition is easy to show, and it is very much in the same way for other type
     constructors in the universe (e.g., truncation and resizing). However, the second
     stability condition is more complicated to show. In essence, the difficulty arises
     from the fact that we need to perform some calculations to simplify the involved
     terms. We need to do this for both the left and the right summand.

     Note that this difficult does not occur for truncations/resizing/identity types. This
     is because those types are propositions, which guarantee that the stability condition
     for the isomorphism is satisfied.
   *)
  Proposition is_stable_sums_in_dfl_full_comp_cat_to_finlim_univ
              (sc : stable_sum_in_comp_cat_univ C sum)
    : is_stable_cat_univ_codes_sums (sums_in_dfl_full_comp_cat_to_finlim_univ sc).
  Proof.
    intros Γ Δ s a b.
    simple refine (_ ,, _).
    - abstract
        (refine (assoc _ _ _ @ _) ;
         refine (stable_sum_in_comp_cat_univ_code_stable_mor C sum sc s _ _ @ _) ;
         refine (maponpaths (λ z, z · _) _) ;
         exact (maponpaths
                  pr1
                  (sum_in_comp_cat_univ_code_eq
                     C sum sc
                     (dfl_full_comp_cat_mor_to_sub_tm (dfl_full_comp_cat_univ_ob C) s a)
                     (dfl_full_comp_cat_mor_to_sub_tm (dfl_full_comp_cat_univ_ob C) s b)))).
    - refine (_ @ assoc _ _ _).
      use BinCoproductArrowsEq.
      + rewrite !assoc.
        rewrite BinCoproductOfArrowsIn1.
        etrans.
        {
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply BinCoproductIn1Commutes.
        }
        etrans.
        {
          apply maponpaths_2.
          refine (comprehension_functor_mor_transportf _ _ _ @ _).
          rewrite assoc_disp_var.
          refine (comprehension_functor_mor_transportf _ _ _ @ _).
          apply comprehension_functor_mor_comp.
        }
        etrans.
        {
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply comprehension_functor_mor_comp.
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            refine (assoc' _ _ _ @ _).
            apply maponpaths.
            exact (!(comprehension_functor_mor_comp _ _ _)).
          }
          refine (stable_sum_in_comp_cat_univ_z_iso_stable_in1 C sum sc s _ _ @ _).
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          exact (!(stable_sum_in_comp_cat_univ_z_iso_stable sum sc s _ _)).
        }
        rewrite !assoc'.
        etrans.
        {
          do 3 apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (!(comprehension_functor_mor_comp _ _ _)).
          }
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply mor_disp_transportf_postwhisker.
          }
          rewrite comprehension_functor_mor_transportf.
          simpl.
          apply idpath.
        }
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(comprehension_functor_mor_comp _ _ _)).
        }
        refine (!_).
        rewrite !assoc'.
        etrans.
        {
          do 3 apply maponpaths.
          exact (comprehension_functor_mor_transportf _ _ _).
        }
        etrans.
        {
          do 2 apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply dfl_full_comp_cat_cat_el_map_el_eq.
          }
          exact (!(comprehension_functor_mor_comp _ _ _)).
        }
        etrans.
        {
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply BinCoproductIn1Commutes.
        }
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          simpl.
          rewrite !assoc_disp.
          unfold transportb.
          rewrite !comprehension_functor_mor_transportf.
          rewrite mor_disp_transportf_postwhisker.
          rewrite comprehension_functor_mor_transportf.
          etrans.
          {
            apply maponpaths.
            do 2 apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
            }
            rewrite mor_disp_transportf_postwhisker.
            apply maponpaths.
            exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
          }
          rewrite transport_f_f.
          rewrite !mor_disp_transportf_postwhisker.
          rewrite comprehension_functor_mor_transportf.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (sum_in_comp_cat_univ_z_iso_eq
                   C sum sc
                   (dfl_full_comp_cat_mor_to_tm_univ_subst (C := C) s a)
                   (dfl_full_comp_cat_mor_to_tm_univ_subst (C := C) s b)).
        }
        rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply comprehension_functor_mor_comp.
          }
          refine (assoc' _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            refine (!(comp_cat_comp_mor_comp _ _) @ _).
            apply maponpaths.
            exact (BinCoproductOfArrowsIn1
                     _
                     (coprod_local_property_bincoproduct sum _ _)
                     _ _ _).
          }
          etrans.
          {
            apply maponpaths.
            apply comp_cat_comp_mor_comp.
          }
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
          }
          rewrite comprehension_functor_mor_transportf.
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C) _).
          }
          exact (comprehension_functor_mor_id _ _).
        }
        rewrite id_left.
        do 2 refine (assoc' _ _ _ @ _).
        refine (_ @ assoc _ _ _).
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (comprehension_functor_mor_comp _ _ _ @ _).
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_subst_natural (dfl_full_comp_cat_el C) _ _).
          }
          rewrite comprehension_functor_mor_transportf.
          apply comprehension_functor_mor_comp.
        }
        do 2 refine (assoc _ _ _ @ _).
        refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
        apply maponpaths_2.
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            exact (comprehension_functor_mor_comp _ _ _).
          }
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_univ_el_stable_natural_inv_disp (dfl_full_comp_cat_el C) _ _).
          }
          rewrite comprehension_functor_mor_transportf.
          exact (comprehension_functor_mor_comp _ _ _).
        }
        do 2 refine (assoc _ _ _ @ _).
        refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
          }
          apply comprehension_functor_mor_transportf.
        }
        refine (!(comprehension_functor_mor_comp _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
        }
        rewrite comprehension_functor_mor_transportf.
        apply maponpaths.
        exact (eq_comp_cat_el_map_on_eq (dfl_full_comp_cat_el C) _ _).
      + rewrite !assoc.
        rewrite BinCoproductOfArrowsIn2.
        etrans.
        {
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply BinCoproductIn2Commutes.
        }
        etrans.
        {
          apply maponpaths_2.
          refine (comprehension_functor_mor_transportf _ _ _ @ _).
          rewrite assoc_disp_var.
          refine (comprehension_functor_mor_transportf _ _ _ @ _).
          apply comprehension_functor_mor_comp.
        }
        etrans.
        {
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply comprehension_functor_mor_comp.
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            refine (assoc' _ _ _ @ _).
            apply maponpaths.
            exact (!(comprehension_functor_mor_comp _ _ _)).
          }
          refine (stable_sum_in_comp_cat_univ_z_iso_stable_in2 C sum sc s _ _ @ _).
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          exact (!(stable_sum_in_comp_cat_univ_z_iso_stable sum sc s _ _)).
        }
        rewrite !assoc'.
        etrans.
        {
          do 3 apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (!(comprehension_functor_mor_comp _ _ _)).
          }
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply mor_disp_transportf_postwhisker.
          }
          rewrite comprehension_functor_mor_transportf.
          simpl.
          apply idpath.
        }
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(comprehension_functor_mor_comp _ _ _)).
        }
        refine (!_).
        rewrite !assoc'.
        etrans.
        {
          do 3 apply maponpaths.
          exact (comprehension_functor_mor_transportf _ _ _).
        }
        etrans.
        {
          do 2 apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply dfl_full_comp_cat_cat_el_map_el_eq.
          }
          exact (!(comprehension_functor_mor_comp _ _ _)).
        }
        etrans.
        {
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply BinCoproductIn2Commutes.
        }
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          simpl.
          rewrite !assoc_disp.
          unfold transportb.
          rewrite !comprehension_functor_mor_transportf.
          rewrite mor_disp_transportf_postwhisker.
          rewrite comprehension_functor_mor_transportf.
          etrans.
          {
            apply maponpaths.
            do 2 apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
            }
            rewrite mor_disp_transportf_postwhisker.
            apply maponpaths.
            exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
          }
          rewrite transport_f_f.
          rewrite !mor_disp_transportf_postwhisker.
          rewrite comprehension_functor_mor_transportf.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (sum_in_comp_cat_univ_z_iso_eq
                   C sum sc
                   (dfl_full_comp_cat_mor_to_tm_univ_subst (C := C) s a)
                   (dfl_full_comp_cat_mor_to_tm_univ_subst (C := C) s b)).
        }
        rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply comprehension_functor_mor_comp.
          }
          refine (assoc' _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            refine (!(comp_cat_comp_mor_comp _ _) @ _).
            apply maponpaths.
            exact (BinCoproductOfArrowsIn2
                     _
                     (coprod_local_property_bincoproduct sum _ _)
                     _ _ _).
          }
          etrans.
          {
            apply maponpaths.
            apply comp_cat_comp_mor_comp.
          }
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
          }
          rewrite comprehension_functor_mor_transportf.
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C) _).
          }
          exact (comprehension_functor_mor_id _ _).
        }
        rewrite id_left.
        do 2 refine (assoc' _ _ _ @ _).
        refine (_ @ assoc _ _ _).
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (comprehension_functor_mor_comp _ _ _ @ _).
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_subst_natural (dfl_full_comp_cat_el C) _ _).
          }
          rewrite comprehension_functor_mor_transportf.
          apply comprehension_functor_mor_comp.
        }
        do 2 refine (assoc _ _ _ @ _).
        refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
        apply maponpaths_2.
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            exact (comprehension_functor_mor_comp _ _ _).
          }
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_univ_el_stable_natural_inv_disp (dfl_full_comp_cat_el C) _ _).
          }
          rewrite comprehension_functor_mor_transportf.
          exact (comprehension_functor_mor_comp _ _ _).
        }
        do 2 refine (assoc _ _ _ @ _).
        refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
          }
          apply comprehension_functor_mor_transportf.
        }
        refine (!(comprehension_functor_mor_comp _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
        }
        rewrite comprehension_functor_mor_transportf.
        apply maponpaths.
        exact (eq_comp_cat_el_map_on_eq (dfl_full_comp_cat_el C) _ _).
  Qed.

  Definition stable_sums_in_dfl_full_comp_cat_to_finlim_univ
             (sc : stable_sum_in_comp_cat_univ C sum)
    : cat_univ_stable_codes_sums
        (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
        (dfl_full_comp_cat_to_finlim_bincoproducts sum).
  Proof.
    use make_cat_univ_stable_codes_sums.
    - exact (sums_in_dfl_full_comp_cat_to_finlim_univ sc).
    - exact (is_stable_sums_in_dfl_full_comp_cat_to_finlim_univ sc).
  Defined.

  (** * 2. Construction of binary sum types in a comprehension category *)
  Definition sums_in_dfl_full_comp_cat_from_finlim_univ_code
             (sc : cat_univ_stable_codes_sums
                     (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                     (dfl_full_comp_cat_to_finlim_bincoproducts sum))
             {Γ : C}
             (a b : tm Γ (dfl_full_comp_cat_univ Γ))
    : tm Γ (dfl_full_comp_cat_univ Γ).
  Proof.
    use (dfl_full_comp_cat_mor_to_tm_univ
           (C := dfl_full_comp_cat_with_univ_types C)).
    use (cat_univ_codes_sums_sum sc).
    - use (dfl_full_comp_cat_tm_to_mor_univ
             (C := dfl_full_comp_cat_with_univ_types C)).
      exact a.
    - use (dfl_full_comp_cat_tm_to_mor_univ
             (C := dfl_full_comp_cat_with_univ_types C)).
      exact b.
  Defined.

  Arguments sums_in_dfl_full_comp_cat_from_finlim_univ_code /.

  Definition sums_in_dfl_full_comp_cat_from_finlim_univ_z_iso
             (sc : cat_univ_stable_codes_sums
                     (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                     (dfl_full_comp_cat_to_finlim_bincoproducts sum))
             {Γ : C}
             (a b : tm Γ (dfl_full_comp_cat_univ Γ))
    : z_iso
        (Γ & coprod_local_property_sum sum
               (comp_cat_univ_el (dfl_full_comp_cat_el C) a)
               (comp_cat_univ_el (dfl_full_comp_cat_el C) b))
        (Γ & comp_cat_univ_el
               (dfl_full_comp_cat_el C)
               (sums_in_dfl_full_comp_cat_from_finlim_univ_code sc a b)).
  Proof.
    refine (z_iso_comp
              _
              (cat_univ_codes_sums_z_iso sc _ _)).
    refine (z_iso_comp
              (preserves_bincoproduct_fiber_comp_cat_comprehension_dom_z_iso
                 sum
                 (coprod_local_property_bincoproduct
                    sum
                    (comp_cat_univ_el (dfl_full_comp_cat_el C) a)
                    (comp_cat_univ_el (dfl_full_comp_cat_el C) b))
                 (dfl_full_comp_cat_to_finlim_bincoproducts
                    sum
                    (Γ & comp_cat_univ_el (dfl_full_comp_cat_el C) a)
                    (Γ & comp_cat_univ_el (dfl_full_comp_cat_el C) b)))
              _).
    use bincoproduct_of_z_iso.
    - use comp_cat_comp_fiber_z_iso.
      use (comp_cat_el_map_on_eq_iso (dfl_full_comp_cat_el C)).
      abstract
        (refine (!_) ;
         apply (dfl_full_comp_cat_tm_to_mor_to_tm_univ
                  (dfl_full_comp_cat_univ_ob C))).
    - use comp_cat_comp_fiber_z_iso.
      use (comp_cat_el_map_on_eq_iso (dfl_full_comp_cat_el C)).
      abstract
        (refine (!_) ;
         apply (dfl_full_comp_cat_tm_to_mor_to_tm_univ
                  (dfl_full_comp_cat_univ_ob C))).
  Defined.

  Proposition sums_in_dfl_full_comp_cat_from_finlim_univ_comm
              (sc : cat_univ_stable_codes_sums
                      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                      (dfl_full_comp_cat_to_finlim_bincoproducts sum))
              {Γ : C}
              (a b : tm Γ (dfl_full_comp_cat_univ Γ))
    : sums_in_dfl_full_comp_cat_from_finlim_univ_z_iso sc a b · π _
      =
      π _.
  Proof.
    do 2 refine (assoc' _ _ _ @ _).
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      exact (cat_univ_codes_sums_sum_comm sc _ _).
    }
    refine (!_).
    use z_iso_inv_to_left.
    etrans.
    {
      exact (preserves_bincoproduct_fiber_comp_cat_comprehension_dom_z_iso_comm sum _ _).
    }
    refine (!_).
    use (precompWithBinCoproductArrow_eq _).
    - refine (!_).
      refine (comprehension_functor_mor_comm _ _ @ _).
      apply id_right.
    - refine (!_).
      refine (comprehension_functor_mor_comm _ _ @ _).
      apply id_right.
  Qed.

  Definition sums_in_dfl_full_comp_cat_from_finlim_univ
             (sc : cat_univ_stable_codes_sums
                     (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                     (dfl_full_comp_cat_to_finlim_bincoproducts sum))
    : sum_in_comp_cat_univ C sum.
  Proof.
    use make_sum_in_comp_cat_univ.
    - exact (λ Γ a b, sums_in_dfl_full_comp_cat_from_finlim_univ_code sc a b).
    - exact (λ Γ a b, sums_in_dfl_full_comp_cat_from_finlim_univ_z_iso sc a b).
    - exact (λ Γ a b, sums_in_dfl_full_comp_cat_from_finlim_univ_comm sc a b).
  Defined.

  Lemma is_stable_sums_in_dfl_full_comp_cat_from_finlim_univ_lem
        (sc : cat_univ_stable_codes_sums
                (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                (dfl_full_comp_cat_to_finlim_bincoproducts sum))
        {Γ Δ : C}
        (s : Γ --> Δ)
        (a b : tm Δ (dfl_full_comp_cat_univ Δ))
    : sum_in_comp_cat_univ_code sum
        (sums_in_dfl_full_comp_cat_from_finlim_univ sc)
        a b [[ s ]]tm
      ↑ sub_dfl_comp_cat_univ s
      =
      sum_in_comp_cat_univ_code sum
        (sums_in_dfl_full_comp_cat_from_finlim_univ sc)
        (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
        (b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s).
  Proof.
    use dfl_full_comp_cat_univ_tm_eq ; simpl.
    etrans.
    {
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (comp_cat_comp_mor_sub_dfl_comp_cat_univ C s).
      }
      simpl.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply PullbackArrow_PullbackPr1.
      }
      rewrite !assoc'.
      apply maponpaths.
      exact (PullbackArrow_PullbackPr1
               (comp_cat_pullback
                  (dfl_full_comp_cat_univ_ob C)
                  _)
               _
               _
               _
               _).
    }
    refine (cat_univ_codes_sums_sum_stable sc s _ _ @ _).
    refine (!_).
    etrans.
    {
      exact (PullbackArrow_PullbackPr1
               (comp_cat_pullback
                  (dfl_full_comp_cat_univ_ob C)
                  _)
               _
               _
               _
               _).
    }
    use cat_univ_codes_sums_sum_eq.
    - exact (dfl_full_comp_cat_tm_to_mor_univ_subst s a).
    - exact (dfl_full_comp_cat_tm_to_mor_univ_subst s b).
  Qed.

  (**
     Here we meet the same difficulty as before: stability expresses an equality for the
     codes and for an isomorphism. While the first is easy to show, the second requires a
     more convoluted calculation.
   *)
  Proposition is_stable_sums_in_dfl_full_comp_cat_from_finlim_univ
              (sc : cat_univ_stable_codes_sums
                      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                      (dfl_full_comp_cat_to_finlim_bincoproducts sum))
    : sum_in_comp_cat_univ_is_stable
        C
        sum
        (sums_in_dfl_full_comp_cat_from_finlim_univ sc).
  Proof.
    intros Γ Δ s a b.
    simple refine (_ ,, _).
    - exact (is_stable_sums_in_dfl_full_comp_cat_from_finlim_univ_lem sc s a b).
    - use (BinCoproductArrowsEq
               _ _ _
               (preserves_bincoproduct_to_bincoproduct
                  _
                  (preserves_bincoproduct_fiber_comp_cat_comprehension_dom sum Γ)
                  _)).
      + etrans.
        {
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply BinCoproductIn1Commutes.
        }
        etrans.
        {
          do 3 apply maponpaths_2.
          apply BinCoproductIn1Commutes.
        }
        refine (!_).
        etrans.
        {
          do 2 refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          do 2 apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            refine (comprehension_functor_mor_transportf _ _ _ @ _).
            apply comprehension_functor_mor_comp.
          }
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!(comp_cat_comp_mor_comp _ _) @ _).
          apply maponpaths.
          exact (BinCoproductIn1Commutes
                   _ _ _
                   (coprod_local_property_bincoproduct sum _ _)
                   _ _ _).
        }
        etrans.
        {
          do 5 apply maponpaths_2.
          apply comp_cat_comp_mor_comp.
        }
        do 5 refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          do 4 refine (assoc _ _ _ @ _).
          do 4 apply maponpaths_2.
          refine (!(comp_cat_comp_mor_comp _ _) @ _).
          apply maponpaths.
          exact (BinCoproductIn1Commutes
                   _ _ _
                   (coprod_local_property_bincoproduct sum _ _)
                   _ _ _).
        }
        etrans.
        {
          apply maponpaths.
          do 3 apply maponpaths_2.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply cartesian_factorisation_commutes.
          }
          rewrite comprehension_functor_mor_transportf.
          apply comprehension_functor_mor_comp.
        }
        etrans.
        {
          apply maponpaths.
          do 3 refine (assoc' _ _ _ @ _).
          apply maponpaths.
          do 2 refine (assoc _ _ _ @ _).
          do 2 apply maponpaths_2.
          exact (BinCoproductIn1Commutes
                   _ _ _
                   (preserves_bincoproduct_to_bincoproduct
                      _
                      (preserves_bincoproduct_fiber_comp_cat_comprehension_dom sum Δ)
                      _)
                   _ _ _).
        }
        etrans.
        {
          do 2 apply maponpaths.
          apply maponpaths_2.
          apply BinCoproductIn1Commutes.
        }
        etrans.
        {
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          apply maponpaths.
          exact (comp_cat_subst_natural (dfl_full_comp_cat_el C) s _).
        }
        rewrite comprehension_functor_mor_transportf.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply comprehension_functor_mor_comp.
          }
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          apply maponpaths.
          exact (comp_cat_univ_el_stable_natural_inv_disp (dfl_full_comp_cat_el C) s _).
        }
        rewrite comprehension_functor_mor_transportf.
        etrans.
        {
          pose (cat_univ_codes_sums_z_iso_stable_in1
                  sc
                  s
                  (dfl_full_comp_cat_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) a)
                  (dfl_full_comp_cat_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) b))
            as p.
          refine (_ @ maponpaths
                        (λ z, comprehension_functor_mor
                                (comp_cat_comprehension
                                   (dfl_full_comp_cat_with_univ_types C))
                                (comp_cat_el_map_on_eq
                                   (dfl_full_comp_cat_el C)
                                   (dfl_full_comp_cat_tm_to_mor_univ_subst' s a))
                              · z)
                        p).
          rewrite !assoc.
          do 2 apply maponpaths_2.
          refine (_ @ comprehension_functor_mor_comp _ _ _).
          rewrite mor_disp_transportf_prewhisker.
          rewrite comprehension_functor_mor_transportf.
          rewrite assoc_disp.
          unfold transportb.
          rewrite comprehension_functor_mor_transportf.
          refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
          apply maponpaths_2.
          rewrite assoc_disp.
          unfold transportb.
          rewrite comprehension_functor_mor_transportf.
          refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
          refine (comprehension_functor_mor_comp _ _ _ @ _).
          apply maponpaths_2.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            apply (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C)).
          }
          rewrite comprehension_functor_mor_transportf.
          apply maponpaths.
          exact (eq_comp_cat_el_map_on_eq (dfl_full_comp_cat_el C) _ _).
        }
        etrans.
        {
          apply maponpaths.
          do 2 apply maponpaths_2.
          apply maponpaths.
          exact (cat_univ_codes_sums_z_iso_eq
                   sc
                   (!(dfl_full_comp_cat_tm_to_mor_univ_subst s a))
                   (!(dfl_full_comp_cat_tm_to_mor_univ_subst s b))).
        }
        etrans.
        {
          apply maponpaths.
          do 2 apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply BinCoproductIn1Commutes.
        }
        rewrite !assoc.
        etrans.
        {
          do 5 apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply dfl_full_comp_cat_cat_el_map_el_eq.
          }
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          apply maponpaths.
          apply (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C)).
        }
        rewrite comprehension_functor_mor_transportf.
        rewrite !assoc'.
        use maponpaths_compose.
        {
          refine (maponpaths
                    (comprehension_functor_mor
                       (comp_cat_comprehension
                          (dfl_full_comp_cat_with_univ_types C)))
                    _).
          apply (eq_comp_cat_el_map_on_eq (dfl_full_comp_cat_el C)).
        }
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply dfl_full_comp_cat_cat_el_map_el_eq.
        }
        unfold comp_cat_extend_over.
        etrans.
        {
          do 2 apply maponpaths.
          refine (comprehension_functor_mor_transportf _ _ _ @ _).
          apply comprehension_functor_mor_comp.
        }
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply comprehension_functor_mor_comp.
        }
        rewrite !assoc.
        refine (_ @ !(comp_cat_comp_mor_comp _ _)).
        apply maponpaths_2.
        etrans.
        {
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply dfl_full_comp_cat_cat_el_map_el_eq.
          }
          etrans.
          {
            apply maponpaths_2.
            exact (!(comprehension_functor_mor_comp _ _ _)).
          }
          exact (!(comprehension_functor_mor_comp _ _ _)).
        }
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C)).
        }
        rewrite mor_disp_transportf_postwhisker.
        rewrite comprehension_functor_mor_transportf.
        etrans.
        {
          apply maponpaths.
          apply (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C)).
        }
        rewrite comprehension_functor_mor_transportf.
        apply maponpaths.
        apply (eq_comp_cat_el_map_on_eq (dfl_full_comp_cat_el C)).
      + etrans.
        {
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply BinCoproductIn2Commutes.
        }
        etrans.
        {
          do 3 apply maponpaths_2.
          apply BinCoproductIn2Commutes.
        }
        refine (!_).
        etrans.
        {
          do 2 refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          do 2 apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            refine (comprehension_functor_mor_transportf _ _ _ @ _).
            apply comprehension_functor_mor_comp.
          }
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!(comp_cat_comp_mor_comp _ _) @ _).
          apply maponpaths.
          exact (BinCoproductIn2Commutes
                   _ _ _
                   (coprod_local_property_bincoproduct sum _ _)
                   _ _ _).
        }
        etrans.
        {
          do 5 apply maponpaths_2.
          apply comp_cat_comp_mor_comp.
        }
        do 5 refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          do 4 refine (assoc _ _ _ @ _).
          do 4 apply maponpaths_2.
          refine (!(comp_cat_comp_mor_comp _ _) @ _).
          apply maponpaths.
          exact (BinCoproductIn2Commutes
                   _ _ _
                   (coprod_local_property_bincoproduct sum _ _)
                   _ _ _).
        }
        etrans.
        {
          apply maponpaths.
          do 3 apply maponpaths_2.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply cartesian_factorisation_commutes.
          }
          rewrite comprehension_functor_mor_transportf.
          apply comprehension_functor_mor_comp.
        }
        etrans.
        {
          apply maponpaths.
          do 3 refine (assoc' _ _ _ @ _).
          apply maponpaths.
          do 2 refine (assoc _ _ _ @ _).
          do 2 apply maponpaths_2.
          exact (BinCoproductIn2Commutes
                   _ _ _
                   (preserves_bincoproduct_to_bincoproduct
                      _
                      (preserves_bincoproduct_fiber_comp_cat_comprehension_dom sum Δ)
                      _)
                   _ _ _).
        }
        etrans.
        {
          do 2 apply maponpaths.
          apply maponpaths_2.
          apply BinCoproductIn2Commutes.
        }
        etrans.
        {
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          apply maponpaths.
          exact (comp_cat_subst_natural (dfl_full_comp_cat_el C) s _).
        }
        rewrite comprehension_functor_mor_transportf.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply comprehension_functor_mor_comp.
          }
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          apply maponpaths.
          exact (comp_cat_univ_el_stable_natural_inv_disp (dfl_full_comp_cat_el C) s _).
        }
        rewrite comprehension_functor_mor_transportf.
        etrans.
        {
          pose (cat_univ_codes_sums_z_iso_stable_in2
                  sc
                  s
                  (dfl_full_comp_cat_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) a)
                  (dfl_full_comp_cat_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) b))
            as p.
          refine (_ @ maponpaths
                        (λ z, comprehension_functor_mor
                                (comp_cat_comprehension
                                   (dfl_full_comp_cat_with_univ_types C))
                                (comp_cat_el_map_on_eq
                                   (dfl_full_comp_cat_el C)
                                   (dfl_full_comp_cat_tm_to_mor_univ_subst' s b))
                              · z)
                        p).
          rewrite !assoc.
          do 2 apply maponpaths_2.
          refine (_ @ comprehension_functor_mor_comp _ _ _).
          rewrite mor_disp_transportf_prewhisker.
          rewrite comprehension_functor_mor_transportf.
          rewrite assoc_disp.
          unfold transportb.
          rewrite comprehension_functor_mor_transportf.
          refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
          apply maponpaths_2.
          rewrite assoc_disp.
          unfold transportb.
          rewrite comprehension_functor_mor_transportf.
          refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
          refine (comprehension_functor_mor_comp _ _ _ @ _).
          apply maponpaths_2.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            apply (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C)).
          }
          rewrite comprehension_functor_mor_transportf.
          apply maponpaths.
          exact (eq_comp_cat_el_map_on_eq (dfl_full_comp_cat_el C) _ _).
        }
        etrans.
        {
          apply maponpaths.
          do 2 apply maponpaths_2.
          apply maponpaths.
          exact (cat_univ_codes_sums_z_iso_eq
                   sc
                   (!(dfl_full_comp_cat_tm_to_mor_univ_subst s a))
                   (!(dfl_full_comp_cat_tm_to_mor_univ_subst s b))).
        }
        etrans.
        {
          apply maponpaths.
          do 2 apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply BinCoproductIn2Commutes.
        }
        rewrite !assoc.
        etrans.
        {
          do 5 apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply dfl_full_comp_cat_cat_el_map_el_eq.
          }
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          apply maponpaths.
          apply (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C)).
        }
        rewrite comprehension_functor_mor_transportf.
        rewrite !assoc'.
        use maponpaths_compose.
        {
          refine (maponpaths
                    (comprehension_functor_mor
                       (comp_cat_comprehension
                          (dfl_full_comp_cat_with_univ_types C)))
                    _).
          apply (eq_comp_cat_el_map_on_eq (dfl_full_comp_cat_el C)).
        }
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply dfl_full_comp_cat_cat_el_map_el_eq.
        }
        unfold comp_cat_extend_over.
        etrans.
        {
          do 2 apply maponpaths.
          refine (comprehension_functor_mor_transportf _ _ _ @ _).
          apply comprehension_functor_mor_comp.
        }
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply comprehension_functor_mor_comp.
        }
        rewrite !assoc.
        refine (_ @ !(comp_cat_comp_mor_comp _ _)).
        apply maponpaths_2.
        etrans.
        {
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply dfl_full_comp_cat_cat_el_map_el_eq.
          }
          etrans.
          {
            apply maponpaths_2.
            exact (!(comprehension_functor_mor_comp _ _ _)).
          }
          exact (!(comprehension_functor_mor_comp _ _ _)).
        }
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C)).
        }
        rewrite mor_disp_transportf_postwhisker.
        rewrite comprehension_functor_mor_transportf.
        etrans.
        {
          apply maponpaths.
          apply (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C)).
        }
        rewrite comprehension_functor_mor_transportf.
        apply maponpaths.
        apply (eq_comp_cat_el_map_on_eq (dfl_full_comp_cat_el C)).
  Qed.

  Definition stable_sums_in_dfl_full_comp_cat_from_finlim_univ
             (sc : cat_univ_stable_codes_sums
                     (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                     (dfl_full_comp_cat_to_finlim_bincoproducts sum))
    : stable_sum_in_comp_cat_univ C sum.
  Proof.
    use make_stable_sum_in_comp_cat_univ.
    - exact (sums_in_dfl_full_comp_cat_from_finlim_univ sc).
    - exact (is_stable_sums_in_dfl_full_comp_cat_from_finlim_univ sc).
  Defined.

  (** * 3. The equivalence *)
  Proposition stable_sums_in_dfl_full_comp_cat_weq_finlim_univ_left
              (sc : stable_sum_in_comp_cat_univ C sum)
    : stable_sums_in_dfl_full_comp_cat_from_finlim_univ
        (stable_sums_in_dfl_full_comp_cat_to_finlim_univ sc)
      =
      sc.
  Proof.
    use stable_sum_in_comp_cat_univ_eq.
    - intros Γ a b ; cbn.
      refine (dfl_full_comp_cat_tm_to_mor_to_tm_univ (dfl_full_comp_cat_univ_ob C) _
              @ _).
      use sum_in_comp_cat_univ_code_eq.
      + exact (dfl_full_comp_cat_tm_to_mor_to_tm_univ (dfl_full_comp_cat_univ_ob C) _).
      + exact (dfl_full_comp_cat_tm_to_mor_to_tm_univ (dfl_full_comp_cat_univ_ob C) _).
    - intros Γ a b.
      do 2 refine (assoc' _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        do 2 refine (assoc' _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          exact (sum_in_comp_cat_univ_z_iso_eq
                   C sum _
                   (dfl_full_comp_cat_tm_to_mor_to_tm_univ
                      (dfl_full_comp_cat_univ_ob C)
                      _)
                   (dfl_full_comp_cat_tm_to_mor_to_tm_univ
                      (dfl_full_comp_cat_univ_ob C)
                      _)).
        }
        do 2 refine (assoc' _ _ _ @ _).
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply comprehension_functor_mor_comp.
        }
        refine (!(comprehension_functor_mor_comp _ _ _) @ _).
        simpl.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
          }
          rewrite mor_disp_transportf_prewhisker.
          apply maponpaths.
          exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
        }
        rewrite !comprehension_functor_mor_transportf.
        etrans.
        {
          apply maponpaths.
          exact (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C) _).
        }
        apply comprehension_functor_mor_id.
      }
      rewrite id_right.
      rewrite !assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      use (BinCoproductArrowsEq
               _ _ _
               (preserves_bincoproduct_to_bincoproduct
                  _
                  (preserves_bincoproduct_fiber_comp_cat_comprehension_dom sum Γ)
                  _)).
      + rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          exact (BinCoproductIn1Commutes
                   _ _ _
                   (preserves_bincoproduct_to_bincoproduct
                      _
                      (preserves_bincoproduct_fiber_comp_cat_comprehension_dom sum Γ)
                      _)
                   _ _ _).
        }
        etrans.
        {
          do 2 apply maponpaths_2.
          apply BinCoproductOfArrowsIn1.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          apply BinCoproductIn1Commutes.
        }
        etrans.
        {
          apply maponpaths.
          refine (!(comp_cat_comp_mor_comp _ _) @ _).
          apply maponpaths.
          apply (BinCoproductOfArrowsIn1
                   _
                   (coprod_local_property_bincoproduct sum _ _)).
        }
        rewrite id_right.
        refine (_ @ id_left _).
        etrans.
        {
          apply maponpaths.
          apply comp_cat_comp_mor_comp.
        }
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (!(comp_cat_comp_mor_comp _ _) @ _).
        refine (_ @ comp_cat_comp_mor_id _).
        apply maponpaths.
        refine (!(comp_cat_el_map_on_concat (dfl_full_comp_cat_el C) _ _) @ _).
        apply (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C)).
      + rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          exact (BinCoproductIn2Commutes
                   _ _ _
                   (preserves_bincoproduct_to_bincoproduct
                      _
                      (preserves_bincoproduct_fiber_comp_cat_comprehension_dom sum Γ)
                      _)
                   _ _ _).
        }
        etrans.
        {
          do 2 apply maponpaths_2.
          apply BinCoproductOfArrowsIn2.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          apply BinCoproductIn2Commutes.
        }
        etrans.
        {
          apply maponpaths.
          refine (!(comp_cat_comp_mor_comp _ _) @ _).
          apply maponpaths.
          apply (BinCoproductOfArrowsIn2
                   _
                   (coprod_local_property_bincoproduct sum _ _)).
        }
        rewrite id_right.
        refine (_ @ id_left _).
        etrans.
        {
          apply maponpaths.
          apply comp_cat_comp_mor_comp.
        }
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (!(comp_cat_comp_mor_comp _ _) @ _).
        refine (_ @ comp_cat_comp_mor_id _).
        apply maponpaths.
        refine (!(comp_cat_el_map_on_concat (dfl_full_comp_cat_el C) _ _) @ _).
        apply (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C)).
  Qed.

  Proposition stable_sums_in_dfl_full_comp_cat_weq_finlim_univ_right
              (sc : cat_univ_stable_codes_sums
                      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                      (dfl_full_comp_cat_to_finlim_bincoproducts sum))
    : stable_sums_in_dfl_full_comp_cat_to_finlim_univ
        (stable_sums_in_dfl_full_comp_cat_from_finlim_univ sc)
      =
      sc.
  Proof.
    use cat_univ_stable_codes_sums_eq.
    - intros Γ a b ; cbn.
      refine (dfl_full_comp_cat_mor_to_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) _
              @ _).
      use (cat_univ_codes_sums_sum_eq sc).
      + exact (dfl_full_comp_cat_mor_to_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) _).
      + exact (dfl_full_comp_cat_mor_to_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) _).
    - intros Γ a b.
      do 2 refine (assoc' _ _ _ @ _).
      use z_iso_inv_on_right.
      do 2 refine (assoc' _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          exact (cat_univ_codes_sums_z_iso_eq
                   sc
                   (dfl_full_comp_cat_mor_to_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) _)
                   (dfl_full_comp_cat_mor_to_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) _)).
        }
        do 2 refine (assoc' _ _ _ @ _).
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          exact (dfl_full_comp_cat_cat_el_map_el_eq _ _ _).
        }
        etrans.
        {
          do 2 apply maponpaths.
          exact (dfl_full_comp_cat_cat_el_map_el_eq _ _ _).
        }
        etrans.
        {
          apply maponpaths.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
          }
          apply comprehension_functor_mor_transportf.
        }
        refine (!(comprehension_functor_mor_comp _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
        }
        refine (comprehension_functor_mor_transportf _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          exact (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C) _).
        }
        apply comprehension_functor_mor_id.
      }
      rewrite id_right.
      refine (_ @ id_left _).
      rewrite !assoc.
      apply maponpaths_2.
      refine (BinCoproductOfArrows_comp _ _ _ _ _ _ _ _ _ _ _ _ @ _).
      refine (_ @ BinCoproduct_of_identities _ _).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (dfl_full_comp_cat_cat_el_map_el_eq _ _ _).
        }
        refine (!(comprehension_functor_mor_comp _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
        }
        refine (comprehension_functor_mor_transportf _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          exact (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C) _).
        }
        apply comprehension_functor_mor_id.
      }
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        exact (dfl_full_comp_cat_cat_el_map_el_eq _ _ _).
      }
      refine (!(comprehension_functor_mor_comp _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
      }
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        exact (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C) _).
      }
      apply comprehension_functor_mor_id.
  Qed.

  Definition stable_sums_in_dfl_full_comp_cat_weq_finlim_univ
    : stable_sum_in_comp_cat_univ C sum
      ≃
      cat_univ_stable_codes_sums
        (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
        (dfl_full_comp_cat_to_finlim_bincoproducts sum).
  Proof.
    use weq_iso.
    - exact stable_sums_in_dfl_full_comp_cat_to_finlim_univ.
    - exact stable_sums_in_dfl_full_comp_cat_from_finlim_univ.
    - exact stable_sums_in_dfl_full_comp_cat_weq_finlim_univ_left.
    - exact stable_sums_in_dfl_full_comp_cat_weq_finlim_univ_right.
  Defined.
End Sum.
