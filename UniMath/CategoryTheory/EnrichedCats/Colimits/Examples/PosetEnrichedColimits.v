(*****************************************************************

 Colimits in categories enriched over posets

 If we have a category enriched over posets, then we can
 characterize colimits using elementary terms. The
 characterization is similar for products: the initial object is
 inherited from the underlying category, while for coproducts and
 coequalizer, we need to demand that the arrow coming
 from the universal property is monotone.

 To construct copowers in a category `C` enriched over posets, we
 assume that we have a poset `P` and an object `x` of `C`. To
 construct the copower, we take a coproduct of `x` indexed by the
 underlying set of `P`. As such, `C` must have 'large enough'
 coproducts, because otherwise, this product cannot be constructed.

 Contents
 1. Initial object
 2. Binary coroducts
 3. Coqualizers
 4. Copowers
 5. Type indexed coproducts

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.CategoryOfPosets.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.PosetEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedInitial.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedBinaryCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCoequalizers.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCopowers.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Examples.PosetsMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.coequalizers.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Proposition isaprop_Coequalizer
            {C : category}
            (HC : is_univalent C)
            {x y : C}
            (f g : x --> y)
  : isaprop (Coequalizer f g).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use subtypePath.
  {
    intro.
    use (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
    - apply homset_property.
    - simpl.
      repeat (use impred ; intro).
      apply isapropiscontr.
  }
  use total2_paths_f.
  - use (isotoid _ HC).
    exact (z_iso_between_Coequalizer φ₁ φ₂).
  - rewrite transportf_isotoid' ; cbn.
    apply CoequalizerCommutes.
Qed.

Section PosetEnrichmentColimits.
  Context {C : category}
          (E : poset_enrichment C).

  Let E' : enrichment C poset_sym_mon_closed_cat
    := make_enrichment_over_poset C E.

  (**
   1. Initial object
   *)
  Section PosetEnrichedInitial.
    Context {x : C}
            (Hx : isInitial C x).

    Let I : Initial C := make_Initial x Hx.

    Definition poset_enrichment_is_initial
      : is_initial_enriched E' x.
    Proof.
      use make_is_initial_enriched.
      - intros P y.
        simple refine (_ ,, _).
        + exact (λ _, InitialArrow I y).
        + abstract
            (intros x₁ x₂ p ;
             apply refl_PartialOrder).
      - abstract
          (intros P y f g ;
           use eq_monotone_function ;
           intros z ;
           apply (@InitialArrowEq _ I)).
    Defined.
  End PosetEnrichedInitial.

  Definition make_poset_enrichment_initial
             (HC : Initial C)
    : initial_enriched E'
    := pr1 HC ,, poset_enrichment_is_initial (pr2 HC).

  Definition poset_terminal_enriched_weq_Initial
             (HC : is_univalent C)
    : initial_enriched E' ≃ Initial C.
  Proof.
    use weqimplimpl.
    - exact (λ T, initial_underlying E' T).
    - exact make_poset_enrichment_initial.
    - apply (isaprop_initial_enriched _ HC).
    - apply (isaprop_Initial _ HC).
  Defined.

  (**
   2. Binary coproducts
   *)
  Definition poset_enrichment_binary_coprod
    : UU
    := ∑ (BC : BinCoproducts C),
       ∏ (x₁ x₂ y : C)
         (f f' : x₁ --> y)
         (qf : E _ _ f f')
         (g g' : x₂ --> y)
         (qg : E _ _ g g'),
       E _ _ (BinCoproductArrow (BC x₁ x₂) f g)
             (BinCoproductArrow (BC x₁ x₂) f' g').

  Proposition isaprop_poset_enrichment_binary_coprod
              (HC : is_univalent C)
    : isaprop poset_enrichment_binary_coprod.
  Proof.
    simple refine (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
    - do 2 (use impred ; intro).
      apply (isaprop_BinCoproduct _ HC).
    - repeat (use impred ; intro).
      apply propproperty.
  Qed.

  Section PosetEnrichedCoprodAccessors.
    Context (EBC : poset_enrichment_binary_coprod).

    Definition poset_enrichment_obj_binary_coprod
               (x y : C)
      : C
      := pr1 EBC x y.

    Definition poset_enrichment_obj_in1
               (x y : C)
      : x --> poset_enrichment_obj_binary_coprod x y
      := BinCoproductIn1 (pr1 EBC x y).

    Definition poset_enrichment_obj_in2
               (x y : C)
      : y --> poset_enrichment_obj_binary_coprod x y
      := BinCoproductIn2 (pr1 EBC x y).

    Definition poset_enrichment_obj_sum
               {z x y : C}
               (f : x --> z)
               (g : y --> z)
      : poset_enrichment_obj_binary_coprod x y --> z
      := BinCoproductArrow (pr1 EBC x y) f g.

    Proposition poset_enrichment_obj_in1_sum
                {z x y : C}
                (f : x --> z)
                (g : y --> z)
      : poset_enrichment_obj_in1 x y · poset_enrichment_obj_sum f g
        =
        f.
    Proof.
      apply BinCoproductIn1Commutes.
    Qed.

    Proposition poset_enrichment_obj_in2_sum
                {z x y : C}
                (f : x --> z)
                (g : y --> z)
      : poset_enrichment_obj_in2 x y · poset_enrichment_obj_sum f g
        =
        g.
    Proof.
      apply BinCoproductIn2Commutes.
    Qed.

    Proposition poset_enrichment_binary_coprod_arr_eq
                {w x y : C}
                {f g : poset_enrichment_obj_binary_coprod x y --> w}
                (p : poset_enrichment_obj_in1 x y · f
                     =
                     poset_enrichment_obj_in1 x y · g)
                (q : poset_enrichment_obj_in2 x y · f
                     =
                     poset_enrichment_obj_in2 x y · g)
      : f = g.
    Proof.
      use (BinCoproductArrowsEq _ _ _ (pr1 EBC x y)).
      - exact p.
      - exact q.
    Qed.

    Definition poset_enrichment_binary_coprod_pair
               (x y z : C)
      : E' ⦃ x , z ⦄ ⊗ (E' ⦃ y , z ⦄) --> E' ⦃ poset_enrichment_obj_binary_coprod x y , z ⦄.
    Proof.
      simple refine (_ ,, _).
      - exact (λ fg, poset_enrichment_obj_sum (pr1 fg) (pr2 fg)).
      - intros fg₁ fg₂ p.
        apply (pr2 EBC).
        + exact (pr1 p).
        + exact (pr2 p).
    Defined.
  End PosetEnrichedCoprodAccessors.

  Section PosetCoprod.
    Context (EBC : poset_enrichment_binary_coprod)
            (x y : C).

    Definition make_poset_enriched_binary_coprod_cocone
      : enriched_binary_coprod_cocone E' x y.
    Proof.
      use make_enriched_binary_coprod_cocone.
      - exact (poset_enrichment_obj_binary_coprod EBC x y).
      - exact (enriched_from_arr E' (poset_enrichment_obj_in1 EBC x y)).
      - exact (enriched_from_arr E' (poset_enrichment_obj_in2 EBC x y)).
    Defined.

    Definition poset_enrichment_binary_coprod_is_coprod
      : is_binary_coprod_enriched E' x y make_poset_enriched_binary_coprod_cocone.
    Proof.
      use make_is_binary_coprod_enriched.
      - intros z P f g.
        refine (_ · poset_enrichment_binary_coprod_pair _ _ _ _).
        simple refine (_ ,, _).
        + exact (prodtofuntoprod (pr1 f ,, pr1 g)).
        + apply prodtofun_is_monotone.
          * exact (pr2 f).
          * exact (pr2 g).
      - abstract
          (intros z P f g ;
           use eq_monotone_function ;
           intros w ; cbn ;
           apply poset_enrichment_obj_in1_sum).
      - abstract
          (intros z P f g ;
           use eq_monotone_function ;
           intros w ; cbn ;
           apply poset_enrichment_obj_in2_sum).
      - abstract
          (intros z P φ₁ φ₂ q₁ q₂ ;
           use eq_monotone_function ;
           intro w ;
           use poset_enrichment_binary_coprod_arr_eq ;
           [ exact (eqtohomot (maponpaths (λ f, pr1 f) q₁) w)
           | exact (eqtohomot (maponpaths (λ f, pr1 f) q₂) w) ]).
    Defined.
  End PosetCoprod.

  Definition make_poset_enrichment_binary_coprod
             (EBC : poset_enrichment_binary_coprod)
    : enrichment_binary_coprod E'
    := λ x y,
       make_poset_enriched_binary_coprod_cocone EBC x y
       ,,
       poset_enrichment_binary_coprod_is_coprod EBC x y.

  Section ToPosetCoproduct.
    Context (EP : enrichment_binary_coprod E')
            {x₁ x₂ y : C}.

    Let prod : poset_sym_mon_closed_cat
      := (E' ⦃ x₁ , y ⦄) ⊗ (E' ⦃ x₂ , y ⦄).

    Let prod_pr1 : prod --> E' ⦃ x₁ , y ⦄
      := _ ,, dirprod_pr1_is_monotone _ _.

    Let prod_pr2 : prod --> E' ⦃ x₂ , y ⦄
      := _ ,, dirprod_pr2_is_monotone _ _.

    Definition poset_to_underlying_binary_coprod_map
               (f : x₁ --> y)
               (g : x₂ --> y)
      : underlying_BinCoproduct E' x₁ x₂ (pr2 (EP x₁ x₂)) --> y
      := pr1 (BinProductArrow
                category_of_posets
                (is_binary_coprod_enriched_to_BinProduct E' _ _ (pr2 (EP x₁ x₂)) y)
                prod_pr1
                prod_pr2)
             (f ,, g).

    Proposition poset_to_underlying_binary_coprod_map_in1
                (f : x₁ --> y)
                (g : x₂ --> y)
      : enriched_coprod_cocone_in1 E' x₁ x₂ (pr1 (EP x₁ x₂))
        · poset_to_underlying_binary_coprod_map f g
        =
        f.
    Proof.
      exact (eqtohomot
               (maponpaths
                  pr1
                  (BinProductPr1Commutes
                     category_of_posets
                     _ _
                     (is_binary_coprod_enriched_to_BinProduct E' _ _ (pr2 (EP x₁ x₂)) y)
                     _
                     prod_pr1
                     prod_pr2))
               (f ,, g)).
    Qed.

    Proposition poset_to_underlying_binary_coprod_map_in2
                (f : x₁ --> y)
                (g : x₂ --> y)
      : enriched_coprod_cocone_in2 E' x₁ x₂ (pr1 (EP x₁ x₂))
        · poset_to_underlying_binary_coprod_map f g
        =
        g.
    Proof.
      exact (eqtohomot
               (maponpaths
                  pr1
                  (BinProductPr2Commutes
                     category_of_posets
                     _ _
                     (is_binary_coprod_enriched_to_BinProduct E' _ _ (pr2 (EP x₁ x₂)) y)
                     _
                     prod_pr1
                     prod_pr2))
               (f ,, g)).
    Qed.

    Proposition poset_to_underlying_binary_coprod_map_monotone
                {φ₁ φ₂ : x₁ --> y}
                {ψ₁ ψ₂ : x₂ --> y}
                (p : E x₁ y φ₁ φ₂)
                (q : E x₂ y ψ₁ ψ₂)
      : E _ _ (poset_to_underlying_binary_coprod_map φ₁ ψ₁)
              (poset_to_underlying_binary_coprod_map φ₂ ψ₂).
    Proof.
      exact (pr2 (@BinProductArrow
                    _ _ _
                    (is_binary_coprod_enriched_to_BinProduct E' _ _ (pr2 (EP x₁ x₂)) y)
                    prod
                    prod_pr1
                    prod_pr2)
                 (φ₁ ,, ψ₁)
                 (φ₂ ,, ψ₂)
                 (p ,, q)).
    Qed.

    Proposition poset_to_underlying_binary_coprod_map_eq
                (f : x₁ --> y)
                (g : x₂ --> y)
      : BinCoproductArrow (underlying_BinCoproduct E' x₁ x₂ (pr2 (EP x₁ x₂))) f g
        =
        poset_to_underlying_binary_coprod_map f g.
    Proof.
      use is_binary_coprod_enriched_arrow_eq.
      - exact (pr2 (EP x₁ x₂)).
      - refine (_ @ !(poset_to_underlying_binary_coprod_map_in1 f g)).
        apply (BinCoproductIn1Commutes
                 C
                 _ _
                 (underlying_BinCoproduct E' x₁ x₂ (pr2 (EP x₁ x₂)))
                 _
                 f g).
      - refine (_ @ !(poset_to_underlying_binary_coprod_map_in2 f g)).
        apply (BinCoproductIn2Commutes
                 C
                 _ _
                 (underlying_BinCoproduct E' x₁ x₂ (pr2 (EP x₁ x₂)))
                 _
                 f g).
    Qed.
  End ToPosetCoproduct.

  Definition to_poset_enrichment_binary_coprod
             (EP : enrichment_binary_coprod E')
    : poset_enrichment_binary_coprod.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, underlying_BinCoproduct E' x y (pr2 (EP x y))).
    - abstract
        (intros x y₁ y₂ f f' p g g' q ;
         rewrite !poset_to_underlying_binary_coprod_map_eq ;
         apply (poset_to_underlying_binary_coprod_map_monotone EP p q)).
  Defined.

  Definition poset_enrichment_coprod_weq
             (HC : is_univalent C)
    : enrichment_binary_coprod E' ≃ poset_enrichment_binary_coprod.
  Proof.
    use weqimplimpl.
    - apply to_poset_enrichment_binary_coprod.
    - apply make_poset_enrichment_binary_coprod.
    - apply (isaprop_enrichment_binary_coprod HC).
    - apply (isaprop_poset_enrichment_binary_coprod HC).
  Defined.

  (**
   3. Coequalizers
   *)
  Definition poset_enrichment_coequalizers
    : UU
    := ∑ (EC : Coequalizers C),
       ∏ (x y z : C)
         (f g : x --> y)
         (h₁ h₂ : y --> z)
         (p₁ : f · h₁ = g · h₁)
         (p₂ : f · h₂ = g · h₂)
         (qh : E _ _ h₁ h₂),
       E _ _ (CoequalizerOut (EC x y f g) z h₁ p₁)
             (CoequalizerOut (EC x y f g) z h₂ p₂).

  Proposition isaprop_poset_enrichment_coequalizers
              (HC : is_univalent C)
    : isaprop poset_enrichment_coequalizers.
  Proof.
    simple refine (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
    - repeat (use impred ; intro).
      apply isaprop_Coequalizer.
      exact HC.
    - repeat (use impred ; intro).
      apply propproperty.
  Qed.

  Section PosetEnrichedCoequalizerAccessors.
    Context (EEC : poset_enrichment_coequalizers).

    Definition poset_enrichment_obj_coequalizer
               {x y : C}
               (f g : x --> y)
      : C
      := pr1 EEC x y f g.

    Definition poset_enrichment_obj_coeq_in
               {x y : C}
               (f g : x --> y)
      : y --> poset_enrichment_obj_coequalizer f g
      := CoequalizerArrow (pr1 EEC x y f g).

    Proposition poset_enrichment_obj_coeq_in_eq
                {x y : C}
                (f g : x --> y)
      : f · poset_enrichment_obj_coeq_in f g
        =
        g · poset_enrichment_obj_coeq_in f g.
    Proof.
      apply CoequalizerEqAr.
    Qed.

    Definition poset_enrichment_obj_from_coequalizer
               {x y z : C}
               {f g : x --> y}
               (h : y --> z)
               (q : f · h = g · h)
      : poset_enrichment_obj_coequalizer f g --> z
      := CoequalizerOut (pr1 EEC x y f g) z h q.

    Proposition poset_enrichment_obj_from_coequalizer_in
                {x y z : C}
                {f g : x --> y}
                (h : y --> z)
                (q : f · h = g · h)
      : poset_enrichment_obj_coeq_in f g · poset_enrichment_obj_from_coequalizer h q
        =
        h.
    Proof.
      apply CoequalizerCommutes.
    Qed.

    Proposition poset_enrichment_coequalizer_arr_eq
                {x y z : C}
                {f g : x --> y}
                {h₁ h₂ : poset_enrichment_obj_coequalizer f g --> z}
                (q : poset_enrichment_obj_coeq_in f g · h₁
                     =
                     poset_enrichment_obj_coeq_in f g · h₂)
      : h₁ = h₂.
    Proof.
      use CoequalizerOutsEq.
      exact q.
    Qed.

    Definition poset_enrichment_coequalizer_to_equalizer
               {x y z : C}
               (f g : x --> y)
      : Equalizers_category_of_posets
          _
          _
          (precomp_arr E' z f)
          (precomp_arr E' z g)
        -->
        E' ⦃ poset_enrichment_obj_coequalizer f g , z ⦄.
    Proof.
      simple refine (_ ,, _).
      - cbn.
        exact (λ hp, poset_enrichment_obj_from_coequalizer (pr1 hp) (pr2 hp)).
      - intros h₁ h₂ q.
        exact (pr2 EEC x y z f g (pr1 h₁) (pr1 h₂) (pr2 h₁) (pr2 h₂) q).
    Defined.
  End PosetEnrichedCoequalizerAccessors.

  Section PosetCoequalizer.
    Context (EEC : poset_enrichment_coequalizers)
            {x y : C}
            (f g : x --> y).

    Definition make_poset_enrichment_coequalizer_cocone
      : enriched_coequalizer_cocone E' f g.
    Proof.
      use make_enriched_coequalizer_cocone.
      - exact (poset_enrichment_obj_coequalizer EEC f g).
      - exact (enriched_from_arr E' (poset_enrichment_obj_coeq_in EEC f g)).
      - exact (poset_enrichment_obj_coeq_in_eq EEC f g).
    Defined.

    Definition make_poset_enrichment_coequalizer_is_coequalizer
      : is_coequalizer_enriched
          E'
          f g
          make_poset_enrichment_coequalizer_cocone.
    Proof.
      use make_is_coequalizer_enriched.
      - abstract
          (intros w P φ₁ φ₂ q ;
           use eq_monotone_function ;
           intro z ;
           use poset_enrichment_coequalizer_arr_eq ;
           exact (eqtohomot (maponpaths pr1 q) z)).
      - intros w P h q.
        refine (_ · poset_enrichment_coequalizer_to_equalizer EEC f g).
        simple refine (_ ,, _).
        + refine (λ z, pr1 h z ,, _).
          exact (eqtohomot (maponpaths pr1 q) z).
        + abstract
            (apply Equalizer_map_monotone ;
             apply (pr2 h)).
      - abstract
          (intros w P h q ;
           use eq_monotone_function ;
           intros z ;
           apply poset_enrichment_obj_from_coequalizer_in).
    Defined.
  End PosetCoequalizer.

  Definition make_poset_enrichment_coequalizers
             (EEC : poset_enrichment_coequalizers)
    : enrichment_coequalizers E'.
  Proof.
    intros x y f g.
    simple refine (_ ,, _).
    - exact (make_poset_enrichment_coequalizer_cocone EEC f g).
    - exact (make_poset_enrichment_coequalizer_is_coequalizer EEC f g).
  Defined.

  Section ToPosetCoequalizer.
    Context (EEC : enrichment_coequalizers E')
            {x y z : C}
            (f g : x --> y).

    Let Eq : Equalizer _ _
      := Equalizers_category_of_posets
           _
           _
           (precomp_arr E' z f)
           (precomp_arr E' z g).

    Let Eq_pr : Eq --> E' ⦃ y , z ⦄
      := EqualizerArrow _.

    Let Eq_path : Eq_pr · precomp_arr E' z f
                  =
                  Eq_pr · precomp_arr E' z g
      := EqualizerEqAr _.

    Definition poset_to_underlying_coequalizer_map
               (h : y --> z)
               (q : f · h = g · h)
      : underlying_Coequalizer E' f g (pr2 (EEC x y f g)) --> z
      := pr1 (EqualizerIn
                (is_coequalizer_enriched_to_Equalizer E' f g (pr2 (EEC x y f g)) z)
                Eq
                Eq_pr
                Eq_path)
              (h ,, q).

    Proposition poset_to_underlying_coequalizer_map_in
                (h : y --> z)
                (q : f · h = g · h)
      : enriched_coequalizer_cocone_in E' f g (pr1 (EEC x y f g))
        · poset_to_underlying_coequalizer_map h q
        =
        h.
    Proof.
      exact (eqtohomot
               (maponpaths
                  pr1
                  (EqualizerCommutes
                     (is_coequalizer_enriched_to_Equalizer E' f g (pr2 (EEC x y f g)) z)
                     Eq
                     Eq_pr
                     Eq_path))
               (h ,, q)).
    Qed.

    Proposition poset_to_underlying_coequalizer_map_monotone
                (h₁ h₂ : y --> z)
                (q₁ : f · h₁ = g · h₁)
                (q₂ : f · h₂ = g · h₂)
                (ph : E y z h₁ h₂)
      : E _ _ (poset_to_underlying_coequalizer_map h₁ q₁)
              (poset_to_underlying_coequalizer_map h₂ q₂).
    Proof.
      apply (pr2 (EqualizerIn
                    (is_coequalizer_enriched_to_Equalizer E' f g (pr2 (EEC x y f g)) z)
                    Eq
                    Eq_pr
                    Eq_path)
               (h₁ ,, q₁)
               (h₂ ,, q₂)
               ph).
    Qed.

    Proposition poset_to_underlying_coequalizer_map_eq
                (h : y --> z)
                (q : f · h = g · h)
      : CoequalizerOut (underlying_Coequalizer E' f g (pr2 (EEC x y f g))) z h q
        =
        poset_to_underlying_coequalizer_map h q.
    Proof.
      use underlying_Coequalizer_arr_eq.
      {
        exact (pr2 (EEC x y f g)).
      }
      etrans.
      {
        apply (CoequalizerCommutes (underlying_Coequalizer E' f g (pr2 (EEC x y f g)))).
      }
      refine (!_).
      apply poset_to_underlying_coequalizer_map_in.
    Qed.
  End ToPosetCoequalizer.

  Definition to_poset_enrichment_coequalizer
             (EEC : enrichment_coequalizers E')
    : poset_enrichment_coequalizers.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y f g, underlying_Coequalizer E' f g (pr2 (EEC x y f g))).
    - abstract
        (intros w x y f g h₁ h₂ p₁ p₂ qh ;
         rewrite !poset_to_underlying_coequalizer_map_eq ;
         apply poset_to_underlying_coequalizer_map_monotone ;
         exact qh).
  Defined.

  Definition poset_enrichment_coequalizer_weq
             (HC : is_univalent C)
    : enrichment_coequalizers E' ≃ poset_enrichment_coequalizers.
  Proof.
    use weqimplimpl.
    - apply to_poset_enrichment_coequalizer.
    - apply make_poset_enrichment_coequalizers.
    - apply (isaprop_enrichment_coequalizers HC).
    - apply (isaprop_poset_enrichment_coequalizers HC).
  Defined.

  (**
   4. Copowers
   *)
  Definition poset_enrichment_copows
    : UU
    := ∑ (coprods : ∏ (P : poset_sym_mon_closed_cat), Coproducts (pr11 P) C),
       ∏ (P : poset_sym_mon_closed_cat)
         (x : C),
       is_monotone
         (pr2 P)
         (E x (coprods P (λ _, x)))
         (CoproductIn _ _ (coprods P (λ _, x)))
       ×
       (∏ (y : C),
        is_monotone
          (monotone_function_PartialOrder
             (pr2 P)
             (E x y))
          (E (coprods P (λ _, x)) y)
          (λ f, CoproductArrow _ _ (coprods P (λ _, x)) (pr1 f))).

  Section PosetEnrichmentCopowersAccessors.
    Context (HE : poset_enrichment_copows).

    Definition poset_copows_coprod
               (P : poset_sym_mon_closed_cat)
               (x : C)
      : Coproduct (pr11 P) C (λ _, x)
      := pr1 HE P (λ _, x).

    Definition poset_copows_in
               {P : poset_sym_mon_closed_cat}
               {x : C}
               (i : pr11 P)
      : x --> poset_copows_coprod P x
      := CoproductIn _ _ (poset_copows_coprod P x) i.

    Proposition poset_copows_monotone_in
                (P : poset_sym_mon_closed_cat)
                (x : C)
      : is_monotone
          (pr2 P)
          (E x (poset_copows_coprod P x))
          poset_copows_in.
    Proof.
      exact (pr1 (pr2 HE P x)).
    Qed.

    Proposition poset_copows_monotone_coproduct_arr
                (P : poset_sym_mon_closed_cat)
                (x y : C)
      : is_monotone
          (monotone_function_PartialOrder
             (pr2 P)
             (E x y))
          (E (poset_copows_coprod P x) y)
          (λ f, CoproductArrow _ _ (poset_copows_coprod P x) (pr1 f)).
    Proof.
      exact (pr2 (pr2 HE P x) y).
    Qed.
  End PosetEnrichmentCopowersAccessors.

  Section PosetEnrichmentCopowers.
    Context (HE : poset_enrichment_copows)
            (P : poset_sym_mon_closed_cat)
            (x : C).

    Let copow : Coproduct _ C (λ _, x) := poset_copows_coprod HE P x.
    Let copow_in : ∏ (_ : pr11 P), x --> copow := λ i, poset_copows_in HE i.

    Definition poset_copower_cocone
      : copower_cocone E' P x.
    Proof.
      simple refine (_ ,, _).
      - exact copow.
      - simple refine (_ ,, _).
        + exact copow_in.
        + exact (poset_copows_monotone_in HE P x).
    Defined.

    Definition poset_copower_map
               (y : C)
      : P ⊸ (E' ⦃ x , y ⦄) --> E' ⦃ poset_copower_cocone , y ⦄.
    Proof.
      simple refine (_ ,, _).
      - intro f.
        exact (CoproductArrow _ _ copow (pr1 f)).
      - exact (poset_copows_monotone_coproduct_arr HE P x y).
    Defined.

    Definition poset_copower_is_copower
      : is_copower_enriched E' P x poset_copower_cocone.
    Proof.
      use make_is_copower_enriched.
      - exact poset_copower_map.
      - abstract
          (intro y ;
           use eq_monotone_function ;
           intro f ;
           cbn in f ;
           use CoproductArrow_eq ;
           intro i ;
           apply (CoproductInCommutes _ _ _ copow)).
      - abstract
          (intro y ;
           use eq_monotone_function ;
           intro f ;
           use eq_monotone_function ;
           intro i ;
           cbn ;
           apply (CoproductInCommutes _ _ _ copow)).
    Defined.
  End PosetEnrichmentCopowers.

  Definition poset_enrichment_copowers_from_coproducts
             (HE : poset_enrichment_copows)
    : enrichment_copower E'.
  Proof.
    intros P x.
    simple refine (_ ,, _).
    - exact (poset_copower_cocone HE P x).
    - apply poset_copower_is_copower.
  Defined.

  (**
   5. Type indexed coproducts
   *)
  Section TypeIndexedCoproducts.
    Context (J : UU).

    Definition poset_enrichment_coprod
      : UU
      := ∑ (PC : Coproducts J C),
         ∏ (x : C)
           (ys : J → C)
           (fs₁ : ∏ (j : J), ys j --> x)
           (fs₂ : ∏ (j : J), ys j --> x)
           (q : ∏ (j : J), E _ _ (fs₁ j) (fs₂ j)),
         E _ _ (CoproductArrow _ _ (PC ys) fs₁)
               (CoproductArrow _ _ (PC ys) fs₂).

    Proposition isaprop_poset_enrichment_coprod
                (HC : is_univalent C)
      : isaprop poset_enrichment_coprod.
    Proof.
      simple refine (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
      - repeat (use impred ; intro).
        apply isaprop_Coproduct.
        exact HC.
      - repeat (use impred ; intro).
        apply propproperty.
    Qed.

    Section PosetEnrichedCoprodAccessors.
      Context (EC : poset_enrichment_coprod).

      Definition poset_enrichment_obj_coprod
                 (ys : J → C)
        : C
        := pr1 EC ys.

      Definition poset_enrichment_obj_coprod_in
                 (ys : J → C)
                 (j : J)
        : ys j --> poset_enrichment_obj_coprod ys
        := CoproductIn _ _ (pr1 EC ys) j.

      Definition poset_enrichment_obj_coprod_sum
                 {x : C}
                 {ys : J → C}
                 (fs : ∏ (j : J), ys j --> x)
        : poset_enrichment_obj_coprod ys --> x
        := CoproductArrow _ _ (pr1 EC ys) fs.

      Proposition poset_enrichment_obj_coprod_in_sum
                  {x : C}
                  {ys : J → C}
                  (fs : ∏ (j : J), ys j --> x)
                  (j : J)
        : poset_enrichment_obj_coprod_in ys j · poset_enrichment_obj_coprod_sum fs
          =
          fs j.
      Proof.
        apply CoproductInCommutes.
      Qed.

      Proposition poset_enrichment_coprod_arr_eq
                  {x : C}
                  {ys : J → C}
                  {f g : poset_enrichment_obj_coprod ys --> x}
                  (p : ∏ (j : J),
                       poset_enrichment_obj_coprod_in ys j · f
                       =
                       poset_enrichment_obj_coprod_in ys j · g)
        : f = g.
      Proof.
        use (CoproductArrow_eq _ _ _ (pr1 EC ys)).
        exact p.
      Qed.

      Definition poset_enrichment_coprod_pair
                 (x : C)
                 (ys : J → C)
        : Products_category_of_posets J (λ j, E' ⦃ ys j , x ⦄)
          -->
          E' ⦃ poset_enrichment_obj_coprod ys , x ⦄.
      Proof.
        simple refine (_ ,, _).
        - exact (λ fs, poset_enrichment_obj_coprod_sum (λ j, fs j)).
        - intros fs₁ fs₂ p.
          apply (pr2 EC).
          exact p.
      Defined.
    End PosetEnrichedCoprodAccessors.

    Section PosetCoprod.
      Context (EC : poset_enrichment_coprod)
              (ys : J → C).

      Definition make_poset_enriched_coprod_cocone
        : enriched_coprod_cocone E' ys.
      Proof.
        use make_enriched_coprod_cocone.
        - exact (poset_enrichment_obj_coprod EC ys).
        - exact (λ j, enriched_from_arr E' (poset_enrichment_obj_coprod_in EC ys j)).
      Defined.

      Definition poset_enrichment_coprod_is_coprod
        : is_coprod_enriched E' ys make_poset_enriched_coprod_cocone.
      Proof.
        use make_is_coprod_enriched.
        - intros z P fs.
          refine (_ · poset_enrichment_coprod_pair _ _ _).
          simple refine (_ ,, _).
          + exact (λ x j, pr1 (fs j) x).
          + abstract
              (use is_monotone_depfunction_poset_pair ;
               intro j ;
               exact (pr2 (fs j))).
        - abstract
            (intros z P f g ;
             use eq_monotone_function ;
             intros w ; cbn ;
             apply poset_enrichment_obj_coprod_in_sum).
        - abstract
            (intros z P φ₁ φ₂ q ;
             use eq_monotone_function ;
             intro w ;
             use poset_enrichment_coprod_arr_eq ;
             intro j ;
             exact (eqtohomot (maponpaths (λ f, pr1 f) (q j)) w)).
      Defined.
    End PosetCoprod.

    Definition make_poset_enrichment_coprod
               (EC : poset_enrichment_coprod)
      : enrichment_coprod E' J
      := λ ys,
         make_poset_enriched_coprod_cocone EC ys
         ,,
         poset_enrichment_coprod_is_coprod EC ys.

    Section ToPosetCoproduct.
      Context (EP : enrichment_coprod E' J)
              {x : C}
              (ys : J → C).

      Let prod : poset_sym_mon_closed_cat
        := Products_category_of_posets J (λ j, E' ⦃ ys j , x ⦄).

      Let prod_pr : ∏ (j : J), prod --> E' ⦃ ys j , x ⦄
          := λ j, _ ,, is_monotone_depfunction_poset_pr _ _ _.

      Definition poset_to_underlying_coprod_map
                 (fs : ∏ (j : J), ys j --> x)
        : underlying_Coproduct E' ys (pr2 (EP ys)) --> x
        := pr1 (ProductArrow
                  J
                  category_of_posets
                  (is_coprod_enriched_to_Product E' _ (pr2 (EP ys)) x)
                  prod_pr)
             fs.

      Proposition poset_to_underlying_coprod_map_pr
                  (fs : ∏ (j : J), ys j --> x)
                  (j : J)
        : enriched_coprod_cocone_in E' ys (pr1 (EP ys)) j
          · poset_to_underlying_coprod_map fs
          =
          fs j.
      Proof.
        exact (eqtohomot
                 (maponpaths
                    pr1
                    (ProductPrCommutes
                       J category_of_posets _
                       (is_coprod_enriched_to_Product E' _ (pr2 (EP ys)) x)
                       _
                       prod_pr
                       j))
                 fs).
      Qed.

      Proposition poset_to_underlying_coprod_map_monotone
                  {φ ψ : ∏ (j : J), ys j --> x}
                  (p : ∏ (j : J), E (ys j) x (φ j) (ψ j))
        : E _ _ (poset_to_underlying_coprod_map φ)
                (poset_to_underlying_coprod_map ψ).
      Proof.
        exact (pr2 (@ProductArrow
                      _ _ _
                      (is_coprod_enriched_to_Product E' _ (pr2 (EP ys)) x)
                      prod
                      prod_pr)
                 φ
                 ψ
                 p).
      Qed.

      Proposition poset_to_underlying_coprod_map_eq
                  (fs : ∏ (j : J), ys j --> x)
        : CoproductArrow _ C (underlying_Coproduct E' ys (pr2 (EP ys))) fs
          =
          poset_to_underlying_coprod_map fs.
      Proof.
        use is_coprod_enriched_arrow_eq.
        - exact (pr2 (EP ys)).
        - intro j.
          refine (_ @ !(poset_to_underlying_coprod_map_pr fs j)).
          apply (CoproductInCommutes
                   _ C
                   _
                   (underlying_Coproduct E' ys (pr2 (EP ys)))
                   _
                   fs).
      Qed.
    End ToPosetCoproduct.

    Definition to_poset_enrichment_coprod
               (EP : enrichment_coprod E' J)
      : poset_enrichment_coprod.
    Proof.
      simple refine (_ ,, _).
      - exact (λ ys, underlying_Coproduct E' ys (pr2 (EP ys))).
      - abstract
          (intros x ys fs₁ fs₂ p ;
           rewrite !poset_to_underlying_coprod_map_eq ;
           apply (poset_to_underlying_coprod_map_monotone EP _ p)).
    Defined.

    Definition poset_enrichment_prod_weq
               (HC : is_univalent C)
      : enrichment_coprod E' J ≃ poset_enrichment_coprod.
    Proof.
      use weqimplimpl.
      - apply to_poset_enrichment_coprod.
      - apply make_poset_enrichment_coprod.
      - apply (isaprop_enrichment_coprod HC).
      - apply (isaprop_poset_enrichment_coprod HC).
    Defined.
  End TypeIndexedCoproducts.
End PosetEnrichmentColimits.
