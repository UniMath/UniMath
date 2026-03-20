(**

 Sum types in comprehension categories

 We defined when a comprehension category is equipped with a universe type, and we constructed
 a biequivalence between the bicategory of univalent DFL full comprehension categories with a
 universe type and the bicategory of univalent categories with finite limits and a universe
 type. Our next goal is to extended this biequivalence to cover universes that are closed under
 certain type formers as well. We consider various type formers, and these are given in various
 files. In this file, we consider codes for sum types. We use the same ideas for each type
 former, and these are explained in the file `Constant.v`

 Contents
 1. Codes for sum types
 2. Accessors and builders
 3. Stability

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionPreservation.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUnivProps.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatExamples.

Local Open Scope cat.
Local Open Scope comp_cat.

Section TypesInCompCatUniv.
  Context (C : dfl_full_comp_cat_with_univ).

  Let el : comp_cat_univ_type (dfl_full_comp_cat_ob C)
    := dfl_full_comp_cat_el C.

  Section SumCode.
    Context (HC : fiberwise_cat_property
                    stable_bincoproducts_local_property
                    (dfl_full_comp_cat_with_univ_types C)).

    (** * 1. Codes for sum types *)
    Definition sum_in_comp_cat_univ
      : UU
      := ∏ (Γ : C)
           (a b : tm Γ (dfl_full_comp_cat_univ Γ))
           (A := comp_cat_univ_el el a)
           (B := comp_cat_univ_el el b),
         ∑ (sum : tm Γ (dfl_full_comp_cat_univ Γ))
           (f : z_iso
                  (Γ & coprod_local_property_sum HC A B)
                  (Γ & comp_cat_univ_el el sum)),
         f · π _ = π _.

    Proposition isaset_sum_in_comp_cat_univ
      : isaset sum_in_comp_cat_univ.
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
    Definition make_sum_in_comp_cat_univ
               (sum : ∏ (Γ : C)
                        (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                      tm Γ (dfl_full_comp_cat_univ Γ))
               (f : ∏ (Γ : C)
                      (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                    z_iso
                      (Γ & coprod_local_property_sum
                             HC
                             (comp_cat_univ_el el a)
                             (comp_cat_univ_el el b))
                      (Γ & comp_cat_univ_el el (sum Γ a b)))
               (p : ∏ (Γ : C)
                      (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                    f Γ a b · π _ = π _)
    : sum_in_comp_cat_univ
    := λ Γ a b, sum Γ a b ,, f Γ a b ,, p Γ a b.

    Definition sum_in_comp_cat_univ_code
               (sum : sum_in_comp_cat_univ)
               {Γ : C}
               (a b : tm Γ (dfl_full_comp_cat_univ Γ))
      : tm Γ (dfl_full_comp_cat_univ Γ)
      := pr1 (sum Γ a b).

    Definition sum_in_comp_cat_univ_z_iso
               (sum : sum_in_comp_cat_univ)
               {Γ : C}
               (a b : tm Γ (dfl_full_comp_cat_univ Γ))
      : z_iso
          (Γ & coprod_local_property_sum
                 HC
                 (comp_cat_univ_el el a)
                 (comp_cat_univ_el el b))
          (Γ & comp_cat_univ_el el (sum_in_comp_cat_univ_code sum a b))
      := pr12 (sum Γ a b).

    Proposition sum_in_comp_cat_univ_comm
                (sum : sum_in_comp_cat_univ)
                {Γ : C}
                (a b : tm Γ (dfl_full_comp_cat_univ Γ))
      : sum_in_comp_cat_univ_z_iso sum a b · π _ = π _.
    Proof.
      exact (pr22 (sum Γ a b)).
    Defined.

    Definition sum_in_comp_cat_univ_z_iso_fiber
               (sum : sum_in_comp_cat_univ)
               {Γ : C}
               (a b : tm Γ (dfl_full_comp_cat_univ Γ))
      : z_iso
          (C := fiber_category _ _)
          (coprod_local_property_sum
             HC
             (comp_cat_univ_el el a)
             (comp_cat_univ_el el b))
          (comp_cat_univ_el el (sum_in_comp_cat_univ_code sum a b)).
    Proof.
      use cod_iso_to_type_iso.
      - exact (sum_in_comp_cat_univ_z_iso sum a b).
      - exact (sum_in_comp_cat_univ_comm sum a b).
    Defined.

    Proposition sum_in_comp_cat_univ_code_eq
                (sum : sum_in_comp_cat_univ)
                {Γ : C}
                {a a' b b' : tm Γ (dfl_full_comp_cat_univ Γ)}
                (p : a = a')
                (q : b = b')
      : sum_in_comp_cat_univ_code sum a b
        =
        sum_in_comp_cat_univ_code sum a' b'.
    Proof.
      induction p, q.
      apply idpath.
    Qed.

    Proposition sum_in_comp_cat_univ_z_iso_eq
                (sum : sum_in_comp_cat_univ)
                {Γ : C}
                {a a' b b' : tm Γ (dfl_full_comp_cat_univ Γ)}
                (p : a = a')
                (q : b = b')
      : (sum_in_comp_cat_univ_z_iso sum a b : _ --> _)
        =
        comp_cat_comp_mor
          (BinCoproductOfArrows
             _
             (coprod_local_property_bincoproduct
                HC
                (comp_cat_univ_el el a)
                (comp_cat_univ_el el b))
             _
             (comp_cat_el_map_on_eq el p)
             (comp_cat_el_map_on_eq el q))
        · sum_in_comp_cat_univ_z_iso sum a' b'
        · comp_cat_comp_mor
            (comp_cat_el_map_on_eq
               el
               (!(sum_in_comp_cat_univ_code_eq sum p q))).
    Proof.
      induction p, q ; simpl.
      rewrite BinCoproduct_of_identities.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        apply comp_cat_comp_mor_id.
      }
      rewrite id_left.
      refine (_ @ id_right _).
      apply maponpaths.
      refine (_ @ comp_cat_comp_mor_id _).
      apply maponpaths.
      exact (comp_cat_el_map_on_idpath el _).
    Qed.

    Proposition sum_in_comp_cat_univ_eq
                {sum₁ sum₂ : sum_in_comp_cat_univ}
                (p : ∏ (Γ : C)
                       (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                     sum_in_comp_cat_univ_code sum₁ a b
                     =
                     sum_in_comp_cat_univ_code sum₂ a b)
                (q : ∏ (Γ : C)
                       (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                     sum_in_comp_cat_univ_z_iso sum₁ a b
                     · comp_cat_comp_mor (comp_cat_el_map_on_eq el (p Γ a b))
                     =
                     sum_in_comp_cat_univ_z_iso sum₂ a b)
      : sum₁ = sum₂.
    Proof.
      use funextsec ; intro Γ.
      use funextsec ; intro a.
      use funextsec ; intro b.
      use total2_paths_f.
      - exact (p Γ a b).
      - use subtypePath.
        {
          intro.
          apply homset_property.
        }
        rewrite pr1_transportf.
        use z_iso_eq.
        etrans.
        {
          apply (pr1_transportf
                   (P := λ (x : tm Γ (dfl_full_comp_cat_univ Γ))
                           (f : Γ & coprod_local_property_sum HC _ _
                                -->
                                Γ & comp_cat_univ_el el x),
                      is_z_isomorphism _)).
        }
        etrans.
        {
          exact (transportf_comp_cat_univ_el' el (p Γ a b) _).
        }
        exact (q Γ a b).
    Qed.

    (** * 3. Stability *)
    Definition sum_in_comp_cat_univ_is_stable
               (sum : sum_in_comp_cat_univ)
      : UU
      := ∏ (Γ Δ : C)
           (s : Γ --> Δ)
           (a b : tm Δ (dfl_full_comp_cat_univ Δ)),
         ∑ (p : sum_in_comp_cat_univ_code sum a b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
                =
                sum_in_comp_cat_univ_code sum
                  (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
                  (b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)),
         sum_in_comp_cat_univ_z_iso
           sum
           (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
           (b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
         · comp_cat_comp_mor
             (comp_cat_el_map_on_eq el (!p)
              · inv_from_z_iso (comp_cat_univ_el_stable el s _))
         · comp_cat_extend_over _ s
         =
         comp_cat_comp_mor_over
           _
           (coprod_local_property_sum_functor
              HC
              (inv_from_z_iso (comp_cat_univ_el_stable el s a))
              (inv_from_z_iso (comp_cat_univ_el_stable el s b))
            · inv_from_z_iso (coprod_local_property_subst_z_iso HC s _ _))
         · sum_in_comp_cat_univ_z_iso sum a b.

    Proposition isaprop_sum_in_comp_cat_univ_is_stable
                (sum : sum_in_comp_cat_univ)
      : isaprop (sum_in_comp_cat_univ_is_stable sum).
    Proof.
      do 5 (use impred ; intro).
      use isaproptotal2.
      - intro.
        apply homset_property.
      - intros.
        apply isaset_comp_cat_tm.
    Qed.

    Definition stable_sum_in_comp_cat_univ
      : UU
      := ∑ (sum : sum_in_comp_cat_univ),
         sum_in_comp_cat_univ_is_stable sum.

    Definition make_stable_sum_in_comp_cat_univ
               (sum : sum_in_comp_cat_univ)
               (H : sum_in_comp_cat_univ_is_stable sum)
      : stable_sum_in_comp_cat_univ
      := sum ,, H.

    Proposition isaset_stable_sum_in_comp_cat_univ
      : isaset stable_sum_in_comp_cat_univ.
    Proof.
      use isaset_total2.
      - exact isaset_sum_in_comp_cat_univ.
      - intro x.
        apply isasetaprop.
        apply isaprop_sum_in_comp_cat_univ_is_stable.
    Qed.

    Coercion stable_sum_in_comp_cat_univ_to_codes
             (sum : stable_sum_in_comp_cat_univ)
      : sum_in_comp_cat_univ
      := pr1 sum.

    Proposition stable_sum_in_comp_cat_univ_code_stable
                (sum : stable_sum_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a b : tm Δ (dfl_full_comp_cat_univ Δ))
      : sum_in_comp_cat_univ_code sum a b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
        =
        sum_in_comp_cat_univ_code sum
          (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
          (b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s).
    Proof.
      exact (pr1 (pr2 sum Γ Δ s a b)).
    Defined.

    Proposition stable_sum_in_comp_cat_univ_code_stable_mor
                (sum : stable_sum_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a b : tm Δ (dfl_full_comp_cat_univ Δ))
      : s
        · sum_in_comp_cat_univ_code sum a b
        · comprehension_functor_mor
            (comp_cat_comprehension C)
            (cleaving_of_types _ _ _ _ _)
        =
        sum_in_comp_cat_univ_code
          sum
          (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
          (b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
        · PullbackPr1 (comp_cat_pullback _ _).
    Proof.
      pose (maponpaths pr1 (stable_sum_in_comp_cat_univ_code_stable sum s a b)) as p.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (!p).
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        exact (comp_cat_comp_mor_sub_dfl_comp_cat_univ C s).
      }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply subst_comp_cat_tm_pr1.
    Qed.

    Proposition stable_sum_in_comp_cat_univ_z_iso_stable
                (sum : stable_sum_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a b : tm Δ (dfl_full_comp_cat_univ Δ))
      : sum_in_comp_cat_univ_z_iso
           sum
           (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
           (b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
        · comp_cat_comp_mor
            (comp_cat_el_map_on_eq el (!(stable_sum_in_comp_cat_univ_code_stable sum s a b))
             · inv_from_z_iso (comp_cat_univ_el_stable el s _))
        · comp_cat_extend_over _ s
        =
        comp_cat_comp_mor_over
          _
          (coprod_local_property_sum_functor
             HC
             (inv_from_z_iso (comp_cat_univ_el_stable el s a))
             (inv_from_z_iso (comp_cat_univ_el_stable el s b))
           · inv_from_z_iso (coprod_local_property_subst_z_iso HC s _ _))
        · sum_in_comp_cat_univ_z_iso sum a b.
    Proof.
      exact (pr2 (pr2 sum Γ Δ s a b)).
    Defined.

    Proposition stable_sum_in_comp_cat_univ_z_iso_stable_in1
                (sum : stable_sum_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a b : tm Δ (dfl_full_comp_cat_univ Δ))
      : comp_cat_comp_mor (inv_from_z_iso (comp_cat_univ_el_stable el s a))
        · comprehension_functor_mor
            (comp_cat_comprehension
               (dfl_full_comp_cat_with_univ_types C))
            (comp_cat_subst (comp_cat_univ_el el a) s
             ;; BinCoproductIn1
                  (coprod_local_property_bincoproduct
                     HC
                     (comp_cat_univ_el el a)
                     (comp_cat_univ_el el b)))
        · sum_in_comp_cat_univ_z_iso sum a b
        =
        comp_cat_comp_mor (BinCoproductIn1 (coprod_local_property_bincoproduct HC _ _))
        · comp_cat_comp_mor_over
            _
            (coprod_local_property_sum_functor
               HC
               (inv_from_z_iso (comp_cat_univ_el_stable el s a))
               (inv_from_z_iso (comp_cat_univ_el_stable el s b))
             · inv_from_z_iso (coprod_local_property_subst_z_iso HC s _ _))
        · sum_in_comp_cat_univ_z_iso sum a b.
    Proof.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (!(comp_cat_comp_mor_comp _ _) @ _).
        apply maponpaths.
        etrans.
        {
          refine (assoc (C := fiber_category _ _) _ _ _ @ _).
          apply maponpaths_2.
          apply BinCoproductIn1Commutes.
        }
        refine (assoc' (C := fiber_category _ _) _ _ _ @ _).
        apply maponpaths.
        apply BinCoproductIn1Commutes.
      }
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply comp_cat_comp_mor_comp.
        }
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          exact (!(comprehension_functor_mor_comp _ _ _)).
        }
        etrans.
        {
          apply maponpaths.
          apply cartesian_factorisation_commutes.
        }
        apply comprehension_functor_mor_transportf.
      }
      apply idpath.
    Qed.

    Proposition stable_sum_in_comp_cat_univ_z_iso_stable_in2
                (sum : stable_sum_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a b : tm Δ (dfl_full_comp_cat_univ Δ))
      : comp_cat_comp_mor (inv_from_z_iso (comp_cat_univ_el_stable el s b))
        · comprehension_functor_mor
            (comp_cat_comprehension
               (dfl_full_comp_cat_with_univ_types C))
            (comp_cat_subst (comp_cat_univ_el el b) s
             ;; BinCoproductIn2
                  (coprod_local_property_bincoproduct
                     HC
                     (comp_cat_univ_el el a)
                     (comp_cat_univ_el el b)))
        · sum_in_comp_cat_univ_z_iso sum a b
        =
        comp_cat_comp_mor (BinCoproductIn2 (coprod_local_property_bincoproduct HC _ _))
        · comp_cat_comp_mor_over
            _
            (coprod_local_property_sum_functor
               HC
               (inv_from_z_iso (comp_cat_univ_el_stable el s a))
               (inv_from_z_iso (comp_cat_univ_el_stable el s b))
             · inv_from_z_iso (coprod_local_property_subst_z_iso HC s _ _))
        · sum_in_comp_cat_univ_z_iso sum a b.
    Proof.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (!(comp_cat_comp_mor_comp _ _) @ _).
        apply maponpaths.
        etrans.
        {
          refine (assoc (C := fiber_category _ _) _ _ _ @ _).
          apply maponpaths_2.
          apply BinCoproductIn2Commutes.
        }
        refine (assoc' (C := fiber_category _ _) _ _ _ @ _).
        apply maponpaths.
        apply BinCoproductIn2Commutes.
      }
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply comp_cat_comp_mor_comp.
        }
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          exact (!(comprehension_functor_mor_comp _ _ _)).
        }
        etrans.
        {
          apply maponpaths.
          apply cartesian_factorisation_commutes.
        }
        apply comprehension_functor_mor_transportf.
      }
      apply idpath.
    Qed.

    Proposition stable_sum_in_comp_cat_univ_eq
                {sum₁ sum₂ : stable_sum_in_comp_cat_univ}
                (p : ∏ (Γ : C)
                       (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                     sum_in_comp_cat_univ_code sum₁ a b
                     =
                     sum_in_comp_cat_univ_code sum₂ a b)
                (q : ∏ (Γ : C)
                       (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                     sum_in_comp_cat_univ_z_iso sum₁ a b
                     · comp_cat_comp_mor (comp_cat_el_map_on_eq el (p Γ a b))
                     =
                     sum_in_comp_cat_univ_z_iso sum₂ a b)
      : sum₁ = sum₂.
    Proof.
      use subtypePath.
      {
        intro.
        apply isaprop_sum_in_comp_cat_univ_is_stable.
      }
      use sum_in_comp_cat_univ_eq.
      - exact p.
      - exact q.
    Qed.
  End SumCode.
End TypesInCompCatUniv.

Arguments sum_in_comp_cat_univ_code {C} HC sum {Γ} a b.
Arguments sum_in_comp_cat_univ_z_iso {C} HC sum {Γ} a b.
Arguments sum_in_comp_cat_univ_comm {C} HC sum {Γ} a b.
Arguments sum_in_comp_cat_univ_z_iso_fiber {C} HC sum {Γ} a b.
Arguments stable_sum_in_comp_cat_univ_code_stable {C} HC sum {Γ Δ} s a b.
Arguments stable_sum_in_comp_cat_univ_z_iso_stable {C} HC sum {Γ Δ} s a b.
