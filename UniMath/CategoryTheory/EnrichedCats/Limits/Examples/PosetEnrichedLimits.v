(*****************************************************************

 Limits in categories enriched over posets

 If we have a category enriched over posets, then we can
 characterize terminal objects, products, and equalizers using
 elementary terms. Such a category has a terminal object if and
 only if the underlying category has a terminal object. For
 products and equalizers, we also demand that the arrow coming
 from the universal property is monotone.

 Contents
 1. Terminal object
 2. Products
 3. Equalizers

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Posets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.CategoryOfPosets.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.PosetEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedTerminal.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedBinaryProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedEqualizers.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedPowers.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Examples.PosetsMonoidal.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section PosetEnrichmentLimits.
  Context {C : category}
          (E : poset_enrichment C).

  Let E' : enrichment C poset_sym_mon_closed_cat
    := make_enrichment_over_poset C E.

  (**
   1. Terminal object
   *)
  Section PosetEnrichedTerminal.
    Context {x : C}
            (Hx : isTerminal C x).

    Let T : Terminal C := make_Terminal x Hx.

    Definition poset_enrichment_is_terminal
      : is_terminal_enriched E' x.
    Proof.
      use make_is_terminal_enriched.
      - intros P y.
        simple refine (_ ,, _).
        + exact (λ _, TerminalArrow T y).
        + abstract
            (intros x₁ x₂ p ;
             apply refl_PartialOrder).
      - abstract
          (intros P y f g ;
           use eq_monotone_function ;
           intros z ;
           apply (@TerminalArrowEq _ T)).
    Defined.
  End PosetEnrichedTerminal.

  Definition make_poset_enrichment_terminal
             (HC : Terminal C)
    : terminal_enriched E'
    := pr1 HC ,, poset_enrichment_is_terminal (pr2 HC).

  Definition poset_terminal_enriched_weq_Terminal
             (HC : is_univalent C)
    : terminal_enriched E' ≃ Terminal C.
  Proof.
    use weqimplimpl.
    - exact (λ T, terminal_underlying E' T).
    - exact make_poset_enrichment_terminal.
    - apply (isaprop_terminal_enriched _ HC).
    - apply (isaprop_Terminal _ HC).
  Defined.

  (**
   2. Products
   *)
  Definition poset_enrichment_binary_prod
    : UU
    := ∑ (BC : BinProducts C),
       ∏ (x y₁ y₂ : C)
         (f f' : x --> y₁)
         (qf : E _ _ f f')
         (g g' : x --> y₂)
         (qg : E _ _ g g'),
       E _ _ (BinProductArrow _ (BC y₁ y₂) f g)
             (BinProductArrow _ (BC y₁ y₂) f' g').

  Proposition isaprop_poset_enrichment_prod
              (HC : is_univalent C)
    : isaprop poset_enrichment_binary_prod.
  Proof.
    simple refine (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
    - do 2 (use impred ; intro).
      apply (isaprop_BinProduct HC).
    - repeat (use impred ; intro).
      apply propproperty.
  Qed.

  Section PosetEnrichedProdAccessors.
    Context (EBC : poset_enrichment_binary_prod).

    Definition poset_enrichment_obj_prod
               (x y : C)
      : C
      := pr1 EBC x y.

    Definition poset_enrichment_obj_pr1
               (x y : C)
      : poset_enrichment_obj_prod x y --> x
      := BinProductPr1 _ (pr1 EBC x y).

    Definition poset_enrichment_obj_pr2
               (x y : C)
      : poset_enrichment_obj_prod x y --> y
      := BinProductPr2 _ (pr1 EBC x y).

    Definition poset_enrichment_obj_pair
               {z x y : C}
               (f : z --> x)
               (g : z --> y)
      : z --> poset_enrichment_obj_prod x y
      := BinProductArrow _ (pr1 EBC x y) f g.

    Proposition poset_enrichment_obj_pair_pr1
                {z x y : C}
                (f : z --> x)
                (g : z --> y)
      : poset_enrichment_obj_pair f g · poset_enrichment_obj_pr1 x y
        =
        f.
    Proof.
      apply BinProductPr1Commutes.
    Qed.

    Proposition poset_enrichment_obj_pair_pr2
                {z x y : C}
                (f : z --> x)
                (g : z --> y)
      : poset_enrichment_obj_pair f g · poset_enrichment_obj_pr2 x y
        =
        g.
    Proof.
      apply BinProductPr2Commutes.
    Qed.

    Proposition poset_enrichment_arr_eq
                {w x y : C}
                {f g : w --> poset_enrichment_obj_prod x y}
                (p : f · poset_enrichment_obj_pr1 x y
                     =
                     g · poset_enrichment_obj_pr1 x y)
                (q : f · poset_enrichment_obj_pr2 x y
                     =
                     g · poset_enrichment_obj_pr2 x y)
      : f = g.
    Proof.
      use (BinProductArrowsEq _ _ _ (pr1 EBC x y)).
      - exact p.
      - exact q.
    Qed.

    Definition poset_enrichment_prod_pair
               (x y z : C)
      : E' ⦃ z, x ⦄ ⊗ (E' ⦃ z , y ⦄) --> E' ⦃ z , poset_enrichment_obj_prod x y ⦄.
    Proof.
      simple refine (_ ,, _).
      - exact (λ fg, poset_enrichment_obj_pair (pr1 fg) (pr2 fg)).
      - intros fg₁ fg₂ p.
        apply (pr2 EBC).
        + exact (pr1 p).
        + exact (pr2 p).
    Defined.
  End PosetEnrichedProdAccessors.

  Section PosetProd.
    Context (EBC : poset_enrichment_binary_prod)
            (x y : C).

    Definition make_poset_enriched_binary_prod_cone
      : enriched_binary_prod_cone E' x y.
    Proof.
      use make_enriched_binary_prod_cone.
      - exact (poset_enrichment_obj_prod EBC x y).
      - exact (enriched_from_arr E' (poset_enrichment_obj_pr1 EBC x y)).
      - exact (enriched_from_arr E' (poset_enrichment_obj_pr2 EBC x y)).
    Defined.

    Definition poset_enrichment_binary_prod_is_prod
      : is_binary_prod_enriched E' x y make_poset_enriched_binary_prod_cone.
    Proof.
      use make_is_binary_prod_enriched.
      - intros z P f g.
        refine (_ · poset_enrichment_prod_pair _ _ _ _).
        simple refine (_ ,, _).
        + exact (prodtofuntoprod (pr1 f ,, pr1 g)).
        + apply prodtofun_is_monotone.
          * exact (pr2 f).
          * exact (pr2 g).
      - abstract
          (intros z P f g ;
           use eq_monotone_function ;
           intros w ; cbn ;
           apply poset_enrichment_obj_pair_pr1).
      - abstract
          (intros z P f g ;
           use eq_monotone_function ;
           intros w ; cbn ;
           apply poset_enrichment_obj_pair_pr2).
      - abstract
          (intros z P φ₁ φ₂ q₁ q₂ ;
           use eq_monotone_function ;
           intro w ;
           use poset_enrichment_arr_eq ;
           [ exact (eqtohomot (maponpaths (λ f, pr1 f) q₁) w)
           | exact (eqtohomot (maponpaths (λ f, pr1 f) q₂) w) ]).
    Defined.
  End PosetProd.

  Definition make_poset_enrichment_binary_prod
             (EBC : poset_enrichment_binary_prod)
    : enrichment_binary_prod E'
    := λ x y,
       make_poset_enriched_binary_prod_cone EBC x y
       ,,
       poset_enrichment_binary_prod_is_prod EBC x y.

  Section ToPosetProduct.
    Context (EP : enrichment_binary_prod E')
            {x y₁ y₂ : C}.

    Let prod : poset_sym_mon_closed_cat
      := (E' ⦃ x , y₁ ⦄) ⊗ (E' ⦃ x , y₂ ⦄).

    Let prod_pr1 : prod --> E' ⦃ x, y₁ ⦄
      := _ ,, dirprod_pr1_is_monotone _ _.

    Let prod_pr2 : prod --> E' ⦃ x, y₂ ⦄
      := _ ,, dirprod_pr2_is_monotone _ _.

    Definition poset_to_underlying_binary_prod_map
               (f : x --> y₁)
               (g : x --> y₂)
      : x --> underlying_BinProduct E' y₁ y₂ (pr2 (EP y₁ y₂))
      := pr1 (BinProductArrow
                category_of_posets
                (is_binary_prod_enriched_to_BinProduct E' _ _ (pr2 (EP y₁ y₂)) x)
                prod_pr1
                prod_pr2)
             (f ,, g).

    Proposition poset_to_underlying_binary_prod_map_pr1
                (f : x --> y₁)
                (g : x --> y₂)
      : poset_to_underlying_binary_prod_map f g
        · enriched_prod_cone_pr1 E' y₁ y₂ (pr1 (EP y₁ y₂))
        =
        f.
    Proof.
      exact (eqtohomot
               (maponpaths
                  pr1
                  (BinProductPr1Commutes
                     category_of_posets
                     _ _
                     (is_binary_prod_enriched_to_BinProduct E' _ _ (pr2 (EP y₁ y₂)) x)
                     _
                     prod_pr1
                     prod_pr2))
               (f ,, g)).
    Qed.

    Proposition poset_to_underlying_binary_prod_map_pr2
                (f : x --> y₁)
                (g : x --> y₂)
      : poset_to_underlying_binary_prod_map f g
        · enriched_prod_cone_pr2 E' y₁ y₂ (pr1 (EP y₁ y₂))
        =
        g.
    Proof.
      exact (eqtohomot
               (maponpaths
                  pr1
                  (BinProductPr2Commutes
                     category_of_posets
                     _ _
                     (is_binary_prod_enriched_to_BinProduct E' _ _ (pr2 (EP y₁ y₂)) x)
                     _
                     prod_pr1
                     prod_pr2))
               (f ,, g)).
    Qed.

    Proposition poset_to_underlying_binary_prod_map_monotone
                {φ₁ φ₂ : x --> y₁}
                {ψ₁ ψ₂ : x --> y₂}
                (p : E x y₁ φ₁ φ₂)
                (q : E x y₂ ψ₁ ψ₂)
      : E _ _ (poset_to_underlying_binary_prod_map φ₁ ψ₁)
              (poset_to_underlying_binary_prod_map φ₂ ψ₂).
    Proof.
      exact (pr2 (@BinProductArrow
                    _ _ _
                    (is_binary_prod_enriched_to_BinProduct E' _ _ (pr2 (EP y₁ y₂)) x)
                    prod
                    prod_pr1
                    prod_pr2)
                 (φ₁ ,, ψ₁)
                 (φ₂ ,, ψ₂)
                 (p ,, q)).
    Qed.

    Proposition poset_to_underlying_binary_prod_map_eq
                (f : x --> y₁)
                (g : x --> y₂)
      : BinProductArrow C (underlying_BinProduct E' y₁ y₂ (pr2 (EP y₁ y₂))) f g
        =
        poset_to_underlying_binary_prod_map f g.
    Proof.
      use is_binary_prod_enriched_arrow_eq.
      - exact (pr2 (EP y₁ y₂)).
      - refine (_ @ !(poset_to_underlying_binary_prod_map_pr1 f g)).
        apply (BinProductPr1Commutes
                 C
                 _ _
                 (underlying_BinProduct E' y₁ y₂ (pr2 (EP y₁ y₂)))
                 _
                 f g).
      - refine (_ @ !(poset_to_underlying_binary_prod_map_pr2 f g)).
        apply (BinProductPr2Commutes
                 C
                 _ _
                 (underlying_BinProduct E' y₁ y₂ (pr2 (EP y₁ y₂)))
                 _
                 f g).
    Qed.
  End ToPosetProduct.

  Definition to_poset_enrichment_prod
             (EP : enrichment_binary_prod E')
    : poset_enrichment_binary_prod.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, underlying_BinProduct E' x y (pr2 (EP x y))).
    - abstract
        (intros x y₁ y₂ f f' p g g' q ;
         rewrite !poset_to_underlying_binary_prod_map_eq ;
         apply (poset_to_underlying_binary_prod_map_monotone EP p q)).
  Defined.

  Definition poset_enrichment_prod_weq
             (HC : is_univalent C)
    : enrichment_binary_prod E' ≃ poset_enrichment_binary_prod.
  Proof.
    use weqimplimpl.
    - apply to_poset_enrichment_prod.
    - apply make_poset_enrichment_binary_prod.
    - apply (isaprop_enrichment_binary_prod HC).
    - apply (isaprop_poset_enrichment_prod HC).
  Defined.

  (**
   3. Equalizers
   *)
  Definition poset_enrichment_equalizers
    : UU
    := ∑ (EC : Equalizers C),
       ∏ (w x y : C)
         (f g : x --> y)
         (h₁ h₂ : w --> x)
         (p₁ : h₁ · f = h₁ · g)
         (p₂ : h₂ · f = h₂ · g)
         (qh : E _ _ h₁ h₂),
       E _ _ (EqualizerIn (EC x y f g) w h₁ p₁)
             (EqualizerIn (EC x y f g) w h₂ p₂).

  Proposition isaprop_poset_enrichment_equalizers
              (HC : is_univalent C)
    : isaprop poset_enrichment_equalizers.
  Proof.
    simple refine (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
    - repeat (use impred ; intro).
      apply isaprop_Equalizer.
      exact HC.
    - repeat (use impred ; intro).
      apply propproperty.
  Qed.

  Section PosetEnrichedEqualizerAccessors.
    Context (EEC : poset_enrichment_equalizers).

    Definition poset_enrichment_obj_equalizer
               {x y : C}
               (f g : x --> y)
      : C
      := pr1 EEC x y f g.

    Definition poset_enrichment_obj_pr
               {x y : C}
               (f g : x --> y)
      : poset_enrichment_obj_equalizer f g --> x
      := EqualizerArrow (pr1 EEC x y f g).

    Proposition poset_enrichment_obj_pr_eq
                {x y : C}
                (f g : x --> y)
      : poset_enrichment_obj_pr f g · f
        =
        poset_enrichment_obj_pr f g · g.
    Proof.
      apply EqualizerEqAr.
    Qed.

    Definition poset_enrichment_obj_to_equalizer
               {w x y : C}
               {f g : x --> y}
               (h : w --> x)
               (q : h · f = h · g)
      : w --> poset_enrichment_obj_equalizer f g
      := EqualizerIn (pr1 EEC x y f g) w h q.

    Proposition poset_enrichment_obj_to_equalizer_pr
                {w x y : C}
                {f g : x --> y}
                (h : w --> x)
                (q : h · f = h · g)
      : poset_enrichment_obj_to_equalizer h q · poset_enrichment_obj_pr f g
        =
        h.
    Proof.
      apply EqualizerCommutes.
    Qed.

    Proposition poset_enrichment_equalizer_arr_eq
                {w x y : C}
                {f g : x --> y}
                {h₁ h₂ : w --> poset_enrichment_obj_equalizer f g}
                (q : h₁ · poset_enrichment_obj_pr f g
                     =
                     h₂ · poset_enrichment_obj_pr f g)
      : h₁ = h₂.
    Proof.
      use EqualizerInsEq.
      exact q.
    Qed.

    Definition poset_enrichment_to_equalizer
               {w x y : C}
               (f g : x --> y)
      : Equalizers_category_of_posets
          _
          _
          (postcomp_arr E' w f)
          (postcomp_arr E' w g)
        -->
        E' ⦃ w , poset_enrichment_obj_equalizer f g ⦄.
    Proof.
      simple refine (_ ,, _).
      - exact (λ hp, poset_enrichment_obj_to_equalizer (pr1 hp) (pr2 hp)).
      - intros h₁ h₂ q.
        apply EEC.
        exact q.
    Defined.
  End PosetEnrichedEqualizerAccessors.

  Section PosetEqualizer.
    Context (EEC : poset_enrichment_equalizers)
            {x y : C}
            (f g : x --> y).

    Definition make_poset_enrichment_equalizer_cone
      : enriched_equalizer_cone E' f g.
    Proof.
      use make_enriched_equalizer_cone.
      - exact (poset_enrichment_obj_equalizer EEC f g).
      - exact (enriched_from_arr E' (poset_enrichment_obj_pr EEC f g)).
      - exact (poset_enrichment_obj_pr_eq EEC f g).
    Defined.

    Definition make_poset_enrichment_equalizer_is_equalizer
      : is_equalizer_enriched
          E'
          f g
          make_poset_enrichment_equalizer_cone.
    Proof.
      use make_is_equalizer_enriched.
      - abstract
          (intros w P φ₁ φ₂ q ;
           use eq_monotone_function ;
           intro z ;
           use poset_enrichment_equalizer_arr_eq ;
           exact (eqtohomot (maponpaths pr1 q) z)).
      - intros w P h q.
        refine (_ · poset_enrichment_to_equalizer EEC f g).
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
           apply poset_enrichment_obj_to_equalizer_pr).
    Defined.
  End PosetEqualizer.

  Definition make_poset_enrichment_equalizers
             (EEC : poset_enrichment_equalizers)
    : enrichment_equalizers E'.
  Proof.
    intros x y f g.
    simple refine (_ ,, _).
    - exact (make_poset_enrichment_equalizer_cone EEC f g).
    - exact (make_poset_enrichment_equalizer_is_equalizer EEC f g).
  Defined.

  Section ToPosetEqualizer.
    Context (EEC : enrichment_equalizers E')
            {w x y : C}
            (f g : x --> y).

    Let Eq : Equalizer _ _
      := Equalizers_category_of_posets
           _
           _
           (postcomp_arr E' w f)
           (postcomp_arr E' w g).

    Let Eq_pr : Eq --> E' ⦃ w , x ⦄
      := EqualizerArrow _.

    Let Eq_path : Eq_pr · postcomp_arr E' w f
                  =
                  Eq_pr · postcomp_arr E' w g
      := EqualizerEqAr _.

    Definition poset_to_underlying_equalizer_map
               (h : w --> x)
               (q : h · f = h · g)
      : w --> underlying_Equalizer E' f g (pr2 (EEC x y f g))
      := pr1 (EqualizerIn
                (is_equalizer_enriched_to_Equalizer E' f g (pr2 (EEC x y f g)) w)
                Eq
                Eq_pr
                Eq_path)
              (h ,, q).

    Proposition poset_to_underlying_equalizer_map_pr
                (h : w --> x)
                (q : h · f = h · g)
      : poset_to_underlying_equalizer_map h q
        · enriched_equalizer_cone_pr E' f g (pr1 (EEC x y f g))
        =
        h.
    Proof.
      exact (eqtohomot
               (maponpaths
                  pr1
                  (EqualizerCommutes
                     (is_equalizer_enriched_to_Equalizer E' f g (pr2 (EEC x y f g)) w)
                     Eq
                     Eq_pr
                     Eq_path))
               (h ,, q)).
    Qed.

    Proposition poset_to_underlying_equalizer_map_monotone
                (h₁ h₂ : w --> x)
                (q₁ : h₁ · f = h₁ · g)
                (q₂ : h₂ · f = h₂ · g)
                (ph : E w x h₁ h₂)
      : E _ _ (poset_to_underlying_equalizer_map h₁ q₁)
              (poset_to_underlying_equalizer_map h₂ q₂).
    Proof.
      apply (pr2 (EqualizerIn
                    (is_equalizer_enriched_to_Equalizer E' f g (pr2 (EEC x y f g)) w)
                    Eq
                    Eq_pr
                    Eq_path)
               (h₁ ,, q₁)
               (h₂ ,, q₂)
               ph).
    Qed.

    Proposition poset_to_underlying_equalizer_map_eq
                (h : w --> x)
                (q : h · f = h · g)
      : EqualizerIn (underlying_Equalizer E' f g (pr2 (EEC x y f g))) w h q
        =
        poset_to_underlying_equalizer_map h q.
    Proof.
      use underlying_Equalizer_arr_eq.
      {
        exact (pr2 (EEC x y f g)).
      }
      etrans.
      {
        apply (EqualizerCommutes (underlying_Equalizer E' f g (pr2 (EEC x y f g)))).
      }
      refine (!_).
      apply poset_to_underlying_equalizer_map_pr.
    Qed.
  End ToPosetEqualizer.

  Definition to_poset_enrichment_equalizer
             (EEC : enrichment_equalizers E')
    : poset_enrichment_equalizers.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y f g, underlying_Equalizer E' f g (pr2 (EEC x y f g))).
    - abstract
        (intros w x y f g h₁ h₂ p₁ p₂ qh ;
         rewrite !poset_to_underlying_equalizer_map_eq ;
         apply poset_to_underlying_equalizer_map_monotone ;
         exact qh).
  Defined.

  Definition poset_enrichment_equalizer_weq
             (HC : is_univalent C)
    : enrichment_equalizers E' ≃ poset_enrichment_equalizers.
  Proof.
    use weqimplimpl.
    - apply to_poset_enrichment_equalizer.
    - apply make_poset_enrichment_equalizers.
    - apply (isaprop_enrichment_equalizers HC).
    - apply (isaprop_poset_enrichment_equalizers HC).
  Defined.
End PosetEnrichmentLimits.
