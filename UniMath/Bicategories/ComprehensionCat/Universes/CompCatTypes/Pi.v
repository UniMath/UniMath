(**

 ∏-types in comprehension categories

 In other files, we defined universe types for comprehension categories and we defined when
 a full comprehension category supports ∏-types. In this file, we define when a universe is
 closed under ∏-types. To do so, we follow the same ideas as for other types formers.
 Specifically, we first define when a universe contains codes for ∏-types. We formulate that
 by saying that whenever we have types `a` and `b` in the universe where `b` depends on `a`,
 then their dependent product also lies in the universe, meaning that we have another term
 in the universe whose associated type is isomorphic to the dependent product of `a` and `b`.
 We also formulate when such codes are stable, which requires us to give stability conditions
 for both the code (i.e., term of the universe) and the isomorphism.

 Contents
 1. Codes for ∏-types
 2. Accessors and builders
 3. Stability

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.
Require Import UniMath.Bicategories.ComprehensionCat.PiTypeNotations.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUnivProps.

Local Open Scope cat.
Local Open Scope comp_cat.

Section TypesInCompCatUniv.
  Context (C : dfl_full_comp_cat_with_univ)
          (P : comp_cat_dependent_prod C).

  Let el : comp_cat_univ_type (dfl_full_comp_cat_ob C)
    := dfl_full_comp_cat_el C.

  (** * 1. Codes for ∏-types *)
  Definition pi_in_comp_cat_univ
    : UU
    := ∏ (Γ : C)
         (a : tm Γ (dfl_full_comp_cat_univ Γ))
         (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
       ∑ (pi : tm Γ (dfl_full_comp_cat_univ Γ))
         (f : z_iso
                (Γ & comp_cat_univ_el el pi)
                (Γ & dep_prod_cc P (comp_cat_univ_el el a) (comp_cat_univ_el el b))),
       f · π _ = π _.

  Proposition isaset_pi_in_comp_cat_univ
      : isaset pi_in_comp_cat_univ.
  Proof.
    do 3 (use impred_isaset ; intro).
    use isaset_total2.
    - apply isaset_comp_cat_tm.
    - intro.
      use isaset_total2.
      + apply isaset_z_iso.
      + intro.
        apply isasetaprop.
        apply homset_property.
  Qed.

  (** * 2. Accessors and builders *)
  Definition make_pi_in_comp_cat_univ
             (pi : ∏ (Γ : C)
                     (a : tm Γ (dfl_full_comp_cat_univ Γ))
                     (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
                    tm Γ (dfl_full_comp_cat_univ Γ))
             (f : ∏ (Γ : C)
                    (a : tm Γ (dfl_full_comp_cat_univ Γ))
                    (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
                  z_iso
                    (Γ & comp_cat_univ_el el (pi Γ a b))
                    (Γ & dep_prod_cc P (comp_cat_univ_el el a) (comp_cat_univ_el el b)))
             (p : ∏ (Γ : C)
                    (a : tm Γ (dfl_full_comp_cat_univ Γ))
                    (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
                  f Γ a b · π _ = π _)
    : pi_in_comp_cat_univ
    := λ Γ a b, pi Γ a b ,, f Γ a b ,, p Γ a b.

  Definition pi_in_comp_cat_univ_code
             (pi : pi_in_comp_cat_univ)
             {Γ : C}
             (a : tm Γ (dfl_full_comp_cat_univ Γ))
             (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : tm Γ (dfl_full_comp_cat_univ Γ)
    := pr1 (pi Γ a b).

  Definition pi_in_comp_cat_univ_z_iso
             (pi : pi_in_comp_cat_univ)
             {Γ : C}
             (a : tm Γ (dfl_full_comp_cat_univ Γ))
             (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : z_iso
        (Γ & comp_cat_univ_el el (pi_in_comp_cat_univ_code pi a b))
        (Γ & dep_prod_cc P (comp_cat_univ_el el a) (comp_cat_univ_el el b))
    := pr12 (pi Γ a b).

  Proposition pi_in_comp_cat_univ_comm
              (pi : pi_in_comp_cat_univ)
              {Γ : C}
              (a : tm Γ (dfl_full_comp_cat_univ Γ))
              (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : pi_in_comp_cat_univ_z_iso pi a b · π _ = π _.
  Proof.
    exact (pr22 (pi Γ a b)).
  Defined.

  Definition pi_in_comp_cat_univ_z_iso_fiber
             (pi : pi_in_comp_cat_univ)
             {Γ : C}
             (a : tm Γ (dfl_full_comp_cat_univ Γ))
             (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : z_iso
        (C := fiber_category _ _)
        (comp_cat_univ_el el (pi_in_comp_cat_univ_code pi a b))
        (dep_prod_cc P (comp_cat_univ_el el a) (comp_cat_univ_el el b)).
  Proof.
    use cod_iso_to_type_iso.
    - exact (pi_in_comp_cat_univ_z_iso pi a b).
    - exact (pi_in_comp_cat_univ_comm pi a b).
  Defined.

  (** * 3. Stability *)
  Proposition pi_in_comp_cat_univ_is_stable_path
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : tm Δ (dfl_full_comp_cat_univ Δ))
              (b : tm (Δ & comp_cat_univ_el el a)
                      (dfl_full_comp_cat_univ (Δ & comp_cat_univ_el el a)))
    : (b [[extend_sub_univ el s a ]]tm
       ↑ sub_dfl_comp_cat_univ (C := C) (extend_sub_univ el s a))
       [[comp_cat_comp_mor (comp_cat_univ_el_stable_mor el s a) ]]tm
       ↑ sub_dfl_comp_cat_univ (C := C) (comp_cat_comp_mor (comp_cat_univ_el_stable_mor el s a))
      =
      b [[comp_cat_extend_over (comp_cat_univ_el el a) s ]]tm
      ↑ sub_dfl_comp_cat_univ (C := C) (comp_cat_extend_over (comp_cat_univ_el el a) s).
  Proof.
    rewrite subst_coerce_comp_cat_tm.
    rewrite comp_coerce_comp_cat_tm.
    rewrite comp_sub_comp_cat_tm_alt.
    rewrite comp_coerce_comp_cat_tm.
    assert (comp_cat_comp_mor (comp_cat_univ_el_stable_mor el s a) · extend_sub_univ el s a
            =
            comp_cat_extend_over (comp_cat_univ_el el a) s)
      as p.
    {
      refine (assoc _ _ _ @ _).
      rewrite <- comp_cat_comp_mor_comp.
      etrans.
      {
        apply maponpaths_2.
        refine (maponpaths comp_cat_comp_mor _).
        exact (z_iso_inv_after_z_iso (comp_cat_univ_el_stable el s a)).
      }
      etrans.
      {
        apply maponpaths_2.
        apply comp_cat_comp_mor_id.
      }
      apply id_left.
    }
    etrans.
    {
      apply maponpaths.
      exact (subst_comp_cat_tm_eq _ p).
    }
    rewrite comp_coerce_comp_cat_tm.
    refine (maponpaths (λ z, _ ↑ z) _).
    refine (!_).
    etrans.
    {
      exact (sub_comp_cat_univ_on_eq (C := dfl_full_comp_cat_ob C) (!p)).
    }
    apply maponpaths.
    refine (sub_comp_cat_univ_comp (C := dfl_full_comp_cat_ob C) _ _ @ _).
    rewrite assoc.
    apply idpath.
  Qed.

  Definition pi_in_comp_cat_univ_is_stable
             (pi : pi_in_comp_cat_univ)
    : UU
    := ∏ (Γ Δ : C)
         (s : Γ --> Δ)
         (a : tm Δ (dfl_full_comp_cat_univ _))
         (b : tm (Δ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
       ∑ (p : pi_in_comp_cat_univ_code pi a b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
              =
              pi_in_comp_cat_univ_code pi
                (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
                (b [[ extend_sub_univ el s a ]]tm ↑ sub_dfl_comp_cat_univ _)),
       comp_cat_comp_mor_over
         _
         (comp_cat_el_map_on_eq el (!p)
          · comp_cat_univ_el_stable_inv el s _)
       · pi_in_comp_cat_univ_z_iso pi a b
       =
       pi_in_comp_cat_univ_z_iso
         pi
         (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
         (b [[ extend_sub_univ el s a ]]tm ↑ sub_dfl_comp_cat_univ _)
       · comp_cat_comp_mor
           (comp_cat_pi_coerce
              P
              (comp_cat_univ_el_stable_mor el s _)
              (comp_cat_univ_el_stable_mor el _ _
               · comp_cat_el_map_on_eq el (pi_in_comp_cat_univ_is_stable_path s a b)
               · comp_cat_univ_el_stable_inv el _ _))
       · comp_cat_comp_mor
           (comp_cat_pi_subst_coerce_inv P (comp_cat_univ_el el a) (comp_cat_univ_el el b) s)
       · comp_cat_extend_over _ s.

  Proposition isaprop_pi_in_comp_cat_univ_is_stable
              (pi : pi_in_comp_cat_univ)
    : isaprop (pi_in_comp_cat_univ_is_stable pi).
  Proof.
    do 5 (use impred ; intro).
    use isaproptotal2.
    - intro.
      apply homset_property.
    - intros.
      apply isaset_comp_cat_tm.
  Qed.

  Definition stable_pi_in_comp_cat_univ
    : UU
    := ∑ (pi : pi_in_comp_cat_univ),
       pi_in_comp_cat_univ_is_stable pi.

  Definition make_stable_pi_in_comp_cat_univ
             (pi : pi_in_comp_cat_univ)
             (H : pi_in_comp_cat_univ_is_stable pi)
    : stable_pi_in_comp_cat_univ
    := pi ,, H.

  Proposition isaset_stable_pi_in_comp_cat_univ
    : isaset stable_pi_in_comp_cat_univ.
  Proof.
    use isaset_total2.
    - exact isaset_pi_in_comp_cat_univ.
    - intro x.
      apply isasetaprop.
      apply isaprop_pi_in_comp_cat_univ_is_stable.
  Qed.

  Coercion stable_pi_in_comp_cat_univ_to_codes
           (pi : stable_pi_in_comp_cat_univ)
    : pi_in_comp_cat_univ
    := pr1 pi.

  Proposition stable_pi_in_comp_cat_univ_code_stable
              (pi : stable_pi_in_comp_cat_univ)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : tm Δ (dfl_full_comp_cat_univ _))
              (b : tm (Δ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : pi_in_comp_cat_univ_code pi a b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
      =
      pi_in_comp_cat_univ_code pi
        (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
        (b [[ extend_sub_univ el s a ]]tm ↑ sub_dfl_comp_cat_univ _).
  Proof.
    exact (pr1 (pr2 pi Γ Δ s a b)).
  Defined.

  Proposition stable_pi_in_comp_cat_univ_z_iso_stable
              (pi : stable_pi_in_comp_cat_univ)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : tm Δ (dfl_full_comp_cat_univ _))
              (b : tm (Δ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : comp_cat_comp_mor_over
         _
         (comp_cat_el_map_on_eq el (!(stable_pi_in_comp_cat_univ_code_stable pi s a b))
          · comp_cat_univ_el_stable_inv el s _)
       · pi_in_comp_cat_univ_z_iso pi a b
       =
       pi_in_comp_cat_univ_z_iso
         pi
         (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
         (b [[ extend_sub_univ el s a ]]tm ↑ sub_dfl_comp_cat_univ _)
       · comp_cat_comp_mor
           (comp_cat_pi_coerce
              P
              (comp_cat_univ_el_stable_mor el s _)
              (comp_cat_univ_el_stable_mor el _ _
               · comp_cat_el_map_on_eq el (pi_in_comp_cat_univ_is_stable_path s a b)
               · comp_cat_univ_el_stable_inv el _ _))
       · comp_cat_comp_mor
           (comp_cat_pi_subst_coerce_inv P (comp_cat_univ_el el a) (comp_cat_univ_el el b) s)
       · comp_cat_extend_over _ s.
  Proof.
    exact (pr2 (pr2 pi Γ Δ s a b)).
  Defined.
End TypesInCompCatUniv.

Arguments pi_in_comp_cat_univ_code {C P} pi {Γ} a b.
Arguments pi_in_comp_cat_univ_z_iso {C P} pi {Γ} a b.
Arguments pi_in_comp_cat_univ_comm {C P} pi {Γ} a b.
Arguments pi_in_comp_cat_univ_z_iso_fiber {C P} pi {Γ} a b.
Arguments stable_pi_in_comp_cat_univ_code_stable {C P} pi {Γ Δ} s a b.
Arguments stable_pi_in_comp_cat_univ_z_iso_stable {C P} pi {Γ Δ} s a b.
