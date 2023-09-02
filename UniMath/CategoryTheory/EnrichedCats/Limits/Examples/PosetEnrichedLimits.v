(*****************************************************************

 Limits in categories enriched over posets

 If we have a category enriched over posets, then we can
 characterize terminal objects, products, and equalizers using
 elementary terms. Such a category has a terminal object if and
 only if the underlying category has a terminal object. For
 products and equalizers, we also demand that the arrow coming
 from the universal property is monotone.

 To construct powers in a category `C` enriched over posets, we
 assume that we have a poset `P` and an object `x` of `C`. To
 construct the power, we take a product of `x` indexed by the
 underlying set of `P`. As such, `C` must have 'large enough'
 products, because otherwise, this product cannot be constructed.
 Note that for powers, we do not construct an equivalence between
 the elementary version and the enriched version. The reason for
 that, is that for the elementary version, we assume that `C` has
 products of all diagrams indexed by the underlying set of a poset
 `P`. However, for powers, we only need such products for constant
 diagrams. As such, our elementary version is actually stronger.

 Contents
 1. Terminal object
 2. Binary products
 3. Equalizers
 4. Powers
 5. Type indexed products

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
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedTerminal.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedBinaryProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedEqualizers.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedPowers.
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
   2. Binary products
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

  Proposition isaprop_poset_enrichment_binary_prod
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

    Definition poset_enrichment_obj_binary_prod
               (x y : C)
      : C
      := pr1 EBC x y.

    Definition poset_enrichment_obj_pr1
               (x y : C)
      : poset_enrichment_obj_binary_prod x y --> x
      := BinProductPr1 _ (pr1 EBC x y).

    Definition poset_enrichment_obj_pr2
               (x y : C)
      : poset_enrichment_obj_binary_prod x y --> y
      := BinProductPr2 _ (pr1 EBC x y).

    Definition poset_enrichment_obj_pair
               {z x y : C}
               (f : z --> x)
               (g : z --> y)
      : z --> poset_enrichment_obj_binary_prod x y
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

    Proposition poset_enrichment_binary_prod_arr_eq
                {w x y : C}
                {f g : w --> poset_enrichment_obj_binary_prod x y}
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

    Definition poset_enrichment_binary_prod_pair
               (x y z : C)
      : E' ⦃ z, x ⦄ ⊗ (E' ⦃ z , y ⦄) --> E' ⦃ z , poset_enrichment_obj_binary_prod x y ⦄.
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
      - exact (poset_enrichment_obj_binary_prod EBC x y).
      - exact (enriched_from_arr E' (poset_enrichment_obj_pr1 EBC x y)).
      - exact (enriched_from_arr E' (poset_enrichment_obj_pr2 EBC x y)).
    Defined.

    Definition poset_enrichment_binary_prod_is_prod
      : is_binary_prod_enriched E' x y make_poset_enriched_binary_prod_cone.
    Proof.
      use make_is_binary_prod_enriched.
      - intros z P f g.
        refine (_ · poset_enrichment_binary_prod_pair _ _ _ _).
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
           use poset_enrichment_binary_prod_arr_eq ;
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

  Definition to_poset_enrichment_binary_prod
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

  Definition poset_enrichment_binary_prod_weq
             (HC : is_univalent C)
    : enrichment_binary_prod E' ≃ poset_enrichment_binary_prod.
  Proof.
    use weqimplimpl.
    - apply to_poset_enrichment_binary_prod.
    - apply make_poset_enrichment_binary_prod.
    - apply (isaprop_enrichment_binary_prod HC).
    - apply (isaprop_poset_enrichment_binary_prod HC).
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

    Definition poset_enrichment_obj_equalizer_pr
               {x y : C}
               (f g : x --> y)
      : poset_enrichment_obj_equalizer f g --> x
      := EqualizerArrow (pr1 EEC x y f g).

    Proposition poset_enrichment_obj_pr_eq
                {x y : C}
                (f g : x --> y)
      : poset_enrichment_obj_equalizer_pr f g · f
        =
        poset_enrichment_obj_equalizer_pr f g · g.
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
      : poset_enrichment_obj_to_equalizer h q · poset_enrichment_obj_equalizer_pr f g
        =
        h.
    Proof.
      apply EqualizerCommutes.
    Qed.

    Proposition poset_enrichment_equalizer_arr_eq
                {w x y : C}
                {f g : x --> y}
                {h₁ h₂ : w --> poset_enrichment_obj_equalizer f g}
                (q : h₁ · poset_enrichment_obj_equalizer_pr f g
                     =
                     h₂ · poset_enrichment_obj_equalizer_pr f g)
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
      - exact (enriched_from_arr E' (poset_enrichment_obj_equalizer_pr EEC f g)).
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

  (**
   4. Powers
   *)
  Definition poset_enrichment_pows
    : UU
    := ∑ (prods : ∏ (P : poset_sym_mon_closed_cat), Products (pr11 P) C),
       ∏ (P : poset_sym_mon_closed_cat)
         (x : C),
       is_monotone (pr2 P) (E (prods P (λ _, x)) x) (ProductPr _ _ (prods P (λ _, x)))
       ×
       (∏ (y : C),
        is_monotone
          (monotone_function_PartialOrder
             (pr2 P)
             (E y x))
          (E y (prods P (λ _, x)))
          (λ f, ProductArrow _ _ (prods P (λ _, x)) (pr1 f))).

  Section PosetEnrichmentPowersAccessors.
    Context (HE : poset_enrichment_pows).

    Definition poset_pows_prod
               (P : poset_sym_mon_closed_cat)
               (x : C)
      : Product (pr11 P) C (λ _, x)
      := pr1 HE P (λ _, x).

    Definition poset_pows_pr
               {P : poset_sym_mon_closed_cat}
               {x : C}
               (i : pr11 P)
      : poset_pows_prod P x --> x
      := ProductPr _ _ (poset_pows_prod P x) i.

    Proposition poset_pows_monotone_pr
                (P : poset_sym_mon_closed_cat)
                (x : C)
      : is_monotone
          (pr2 P)
          (E (poset_pows_prod P x) x)
          poset_pows_pr.
    Proof.
      exact (pr1 (pr2 HE P x)).
    Qed.

    Proposition poset_pows_monotone_product_arr
                (P : poset_sym_mon_closed_cat)
                (x y : C)
      : is_monotone
          (monotone_function_PartialOrder
             (pr2 P)
             (E y x))
          (E y (poset_pows_prod P x))
          (λ f, ProductArrow _ _ (poset_pows_prod P x) (pr1 f)).
    Proof.
      exact (pr2 (pr2 HE P x) y).
    Qed.
  End PosetEnrichmentPowersAccessors.

  Section PosetEnrichmentPowers.
    Context (HE : poset_enrichment_pows)
            (P : poset_sym_mon_closed_cat)
            (x : C).

    Let pow : Product _ C (λ _, x) := poset_pows_prod HE P x.
    Let pow_pr : ∏ (_ : pr11 P), pow --> x := λ i, poset_pows_pr HE i.

    Definition poset_power_cone
      : power_cone E' P x.
    Proof.
      simple refine (_ ,, _).
      - exact pow.
      - simple refine (_ ,, _).
        + exact pow_pr.
        + exact (poset_pows_monotone_pr HE P x).
    Defined.

    Definition poset_power_map
               (y : C)
      : P ⊸ (E' ⦃ y, x ⦄) --> E' ⦃ y, poset_power_cone ⦄.
    Proof.
      simple refine (_ ,, _).
      - intro f.
        exact (ProductArrow _ _ pow (pr1 f)).
      - exact (poset_pows_monotone_product_arr HE P x y).
    Defined.

    Definition poset_power_is_power
      : is_power_enriched E' P x poset_power_cone.
    Proof.
      use make_is_power_enriched.
      - exact poset_power_map.
      - abstract
          (intro y ;
           use eq_monotone_function ;
           intro f ;
           cbn in f ;
           use ProductArrow_eq ;
           intro i ;
           apply (ProductPrCommutes _ _ _ pow)).
      - abstract
          (intro y ;
           use eq_monotone_function ;
           intro f ;
           use eq_monotone_function ;
           intro i ;
           cbn ;
           apply (ProductPrCommutes _ _ _ pow)).
    Defined.
  End PosetEnrichmentPowers.

  Definition poset_enrichment_powers_from_products
             (HE : poset_enrichment_pows)
    : enrichment_power E'.
  Proof.
    intros P x.
    simple refine (_ ,, _).
    - exact (poset_power_cone HE P x).
    - apply poset_power_is_power.
  Defined.

  (**
   5. Type indexed products
   *)
  Section TypeIndexedProducts.
    Context (J : UU).

    Definition poset_enrichment_prod
      : UU
      := ∑ (PC : Products J C),
         ∏ (x : C)
           (ys : J → C)
           (fs₁ : ∏ (j : J), x --> ys j)
           (fs₂ : ∏ (j : J), x --> ys j)
           (q : ∏ (j : J), E _ _ (fs₁ j) (fs₂ j)),
         E _ _ (ProductArrow _ _ (PC ys) fs₁)
               (ProductArrow _ _ (PC ys) fs₂).

    Proposition isaprop_poset_enrichment_prod
                (HC : is_univalent C)
      : isaprop poset_enrichment_prod.
    Proof.
      simple refine (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
      - repeat (use impred ; intro).
        apply isaprop_Product.
        exact HC.
      - repeat (use impred ; intro).
        apply propproperty.
    Qed.

    Section PosetEnrichedProdAccessors.
      Context (EC : poset_enrichment_prod).

      Definition poset_enrichment_obj_prod
                 (ys : J → C)
        : C
        := pr1 EC ys.

      Definition poset_enrichment_obj_prod_pr
                 (ys : J → C)
                 (j : J)
        : poset_enrichment_obj_prod ys --> ys j
        := ProductPr _ _ (pr1 EC ys) j.

      Definition poset_enrichment_obj_prod_pair
                 {x : C}
                 {ys : J → C}
                 (fs : ∏ (j : J), x --> ys j)
        : x --> poset_enrichment_obj_prod ys
        := ProductArrow _ _ (pr1 EC ys) fs.

      Proposition poset_enrichment_obj_prod_pair_pr
                  {x : C}
                  {ys : J → C}
                  (fs : ∏ (j : J), x --> ys j)
                  (j : J)
        : poset_enrichment_obj_prod_pair fs · poset_enrichment_obj_prod_pr ys j
          =
          fs j.
      Proof.
        apply ProductPrCommutes.
      Qed.

      Proposition poset_enrichment_prod_arr_eq
                  {x : C}
                  {ys : J → C}
                  {f g : x --> poset_enrichment_obj_prod ys}
                  (p : ∏ (j : J),
                       f · poset_enrichment_obj_prod_pr ys j
                       =
                       g · poset_enrichment_obj_prod_pr ys j)
        : f = g.
      Proof.
        use (ProductArrow_eq _ _ _ (pr1 EC ys)).
        exact p.
      Qed.

      Definition poset_enrichment_prod_pair
                 (x : C)
                 (ys : J → C)
        : Products_category_of_posets J (λ j, E' ⦃ x , ys j ⦄)
          -->
          E' ⦃ x , poset_enrichment_obj_prod ys ⦄.
      Proof.
        simple refine (_ ,, _).
        - exact (λ fs, poset_enrichment_obj_prod_pair (λ j, fs j)).
        - intros fs₁ fs₂ p.
          apply (pr2 EC).
          exact p.
      Defined.
    End PosetEnrichedProdAccessors.

    Section PosetProd.
      Context (EBC : poset_enrichment_prod)
              (ys : J → C).

      Definition make_poset_enriched_prod_cone
        : enriched_prod_cone E' ys.
      Proof.
        use make_enriched_prod_cone.
        - exact (poset_enrichment_obj_prod EBC ys).
        - exact (λ j, enriched_from_arr E' (poset_enrichment_obj_prod_pr EBC ys j)).
      Defined.

      Definition poset_enrichment_prod_is_prod
        : is_prod_enriched E' ys make_poset_enriched_prod_cone.
      Proof.
        use make_is_prod_enriched.
        - intros z P fs.
          refine (_ · poset_enrichment_prod_pair _ _ _).
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
             apply poset_enrichment_obj_prod_pair_pr).
        - abstract
            (intros z P φ₁ φ₂ q ;
             use eq_monotone_function ;
             intro w ;
             use poset_enrichment_prod_arr_eq ;
             intro j ;
             exact (eqtohomot (maponpaths (λ f, pr1 f) (q j)) w)).
      Defined.
    End PosetProd.

    Definition make_poset_enrichment_prod
               (EBC : poset_enrichment_prod)
      : enrichment_prod E' J
      := λ ys,
         make_poset_enriched_prod_cone EBC ys
         ,,
         poset_enrichment_prod_is_prod EBC ys.

    Section ToPosetProduct.
      Context (EP : enrichment_prod E' J)
              {x : C}
              (ys : J → C).

      Let prod : poset_sym_mon_closed_cat
        := Products_category_of_posets J (λ j, E' ⦃ x , ys j ⦄).

      Let prod_pr : ∏ (j : J), prod --> E' ⦃ x , ys j ⦄
          := λ j, _ ,, is_monotone_depfunction_poset_pr _ _ _.

      Definition poset_to_underlying_prod_map
                 (fs : ∏ (j : J), x --> ys j)
        : x --> underlying_Product E' ys (pr2 (EP ys))
        := pr1 (ProductArrow
                  J
                  category_of_posets
                  (is_prod_enriched_to_Product E' _ (pr2 (EP ys)) x)
                  prod_pr)
             fs.

      Proposition poset_to_underlying_prod_map_pr
                  (fs : ∏ (j : J), x --> ys j)
                  (j : J)
        : poset_to_underlying_prod_map fs
          · enriched_prod_cone_pr E' ys (pr1 (EP ys)) j
          =
          fs j.
      Proof.
        exact (eqtohomot
                 (maponpaths
                    pr1
                    (ProductPrCommutes
                       J category_of_posets _
                       (is_prod_enriched_to_Product E' _ (pr2 (EP ys)) x)
                       _
                       prod_pr
                       j))
                 fs).
      Qed.

      Proposition poset_to_underlying_prod_map_monotone
                  {φ ψ : ∏ (j : J), x --> ys j}
                  (p : ∏ (j : J), E x (ys j) (φ j) (ψ j))
        : E _ _ (poset_to_underlying_prod_map φ)
                (poset_to_underlying_prod_map ψ).
      Proof.
        exact (pr2 (@ProductArrow
                      _ _ _
                      (is_prod_enriched_to_Product E' _ (pr2 (EP ys)) x)
                      prod
                      prod_pr)
                 φ
                 ψ
                 p).
      Qed.

      Proposition poset_to_underlying_prod_map_eq
                  (fs : ∏ (j : J), x --> ys j)
        : ProductArrow _ C (underlying_Product E' ys (pr2 (EP ys))) fs
          =
          poset_to_underlying_prod_map fs.
      Proof.
        use is_prod_enriched_arrow_eq.
        - exact (pr2 (EP ys)).
        - intro j.
          refine (_ @ !(poset_to_underlying_prod_map_pr fs j)).
          apply (ProductPrCommutes
                   _ C
                   _
                   (underlying_Product E' ys (pr2 (EP ys)))
                   _
                   fs).
      Qed.
    End ToPosetProduct.

    Definition to_poset_enrichment_prod
               (EP : enrichment_prod E' J)
      : poset_enrichment_prod.
    Proof.
      simple refine (_ ,, _).
      - exact (λ ys, underlying_Product E' ys (pr2 (EP ys))).
      - abstract
          (intros x ys fs₁ fs₂ p ;
           rewrite !poset_to_underlying_prod_map_eq ;
           apply (poset_to_underlying_prod_map_monotone EP _ p)).
    Defined.

    Definition poset_enrichment_prod_weq
               (HC : is_univalent C)
      : enrichment_prod E' J ≃ poset_enrichment_prod.
    Proof.
      use weqimplimpl.
      - apply to_poset_enrichment_prod.
      - apply make_poset_enrichment_prod.
      - apply (isaprop_enrichment_prod HC).
      - apply (isaprop_poset_enrichment_prod HC).
    Defined.
  End TypeIndexedProducts.
End PosetEnrichmentLimits.
