From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac Batch Debug.
(*****************************************************************

 Limits in categories enriched over structures

 In this file we characterize limits in categories enriched over
 structures. The proofs and characterizations are in essence the
 same as for posets. A category enriched over structures inherits
 its limits from the underlying category if projections and the
 maps arising from the universal property are structure
 preserving.

 Contents
 1. Terminal object
 2. Binary products
 3. Equalizers
 4. Type indexed products
 5. Powers

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.StructureEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedTerminal.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedBinaryProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedEqualizers.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedPowers.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Examples.StructuresMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.equalizers.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section StructureEnrichmentLimits.
  Context {P : hset_cartesian_closed_struct}
          {C : category}
          (E : struct_enrichment P C).

  Let E' : enrichment C (sym_mon_closed_cat_of_hset_struct P)
    := make_enrichment_over_struct P C E.

  (**
   1. Terminal object
   *)
  Section StructureEnrichedTerminal.
    Context {x : C}
            (Hx : isTerminal C x).

    Let T : Terminal C := make_Terminal x Hx.

    Definition structure_enrichment_is_terminal
      : is_terminal_enriched E' x.
    Proof.
      use make_is_terminal_enriched.
      - intros X y.
        simple refine (_ ,, _).
        + exact (λ _, TerminalArrow T y).
        + abstract
            (cbn ;
             apply hset_struct_const).
      - abstract
          (intros X y f g ;
           use eq_mor_hset_struct ;
           intros z ;
           apply (@TerminalArrowEq _ T)).
    Defined.
  End StructureEnrichedTerminal.

  Definition make_structure_enrichment_terminal
             (HC : Terminal C)
    : terminal_enriched E'
    := pr1 HC ,, structure_enrichment_is_terminal (pr2 HC).

  Definition structure_terminal_enriched_weq_Terminal
             (HC : is_univalent C)
    : terminal_enriched E' ≃ Terminal C.
  Proof.
    use weqimplimpl.
    - exact (λ T, terminal_underlying E' T).
    - exact make_structure_enrichment_terminal.
    - apply (isaprop_terminal_enriched _ HC).
    - apply (isaprop_Terminal _ HC).
  Defined.

  (**
   2. Binary products
   *)
  Definition structure_enrichment_binary_prod
    : UU
    := ∑ (BC : BinProducts C),
       ∏ (x y z : C),
       mor_hset_struct
         P
         (hset_struct_prod P (E z x) (E z y))
         (E z (BC x y))
         (λ fg, BinProductArrow _ (BC x y) (pr1 fg) (pr2 fg)).

  Proposition isaprop_structure_enrichment_binary_prod
              (HC : is_univalent C)
    : isaprop structure_enrichment_binary_prod.
  Proof.
    simple refine (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
    - do 2 (use impred ; intro).
      apply (isaprop_BinProduct HC).
    - repeat (use impred ; intro).
      apply isaprop_hset_struct_on_mor.
  Qed.

  Section StructureEnrichedProdAccessors.
    Context (EBC : structure_enrichment_binary_prod).

    Definition structure_enrichment_obj_binary_prod
               (x y : C)
      : C
      := pr1 EBC x y.

    Definition structure_enrichment_obj_pr1
               (x y : C)
      : structure_enrichment_obj_binary_prod x y --> x
      := BinProductPr1 _ (pr1 EBC x y).

    Definition structure_enrichment_obj_pr2
               (x y : C)
      : structure_enrichment_obj_binary_prod x y --> y
      := BinProductPr2 _ (pr1 EBC x y).

    Definition structure_enrichment_obj_pair
               {z x y : C}
               (f : z --> x)
               (g : z --> y)
      : z --> structure_enrichment_obj_binary_prod x y
      := BinProductArrow _ (pr1 EBC x y) f g.

    Proposition structure_enrichment_obj_pair_pr1
                {z x y : C}
                (f : z --> x)
                (g : z --> y)
      : structure_enrichment_obj_pair f g · structure_enrichment_obj_pr1 x y
        =
        f.
    Proof.
      apply BinProductPr1Commutes.
    Qed.

    Proposition structure_enrichment_obj_pair_pr2
                {z x y : C}
                (f : z --> x)
                (g : z --> y)
      : structure_enrichment_obj_pair f g · structure_enrichment_obj_pr2 x y
        =
        g.
    Proof.
      apply BinProductPr2Commutes.
    Qed.

    Proposition structure_enrichment_binary_prod_arr_eq
                {w x y : C}
                {f g : w --> structure_enrichment_obj_binary_prod x y}
                (p : f · structure_enrichment_obj_pr1 x y
                     =
                     g · structure_enrichment_obj_pr1 x y)
                (q : f · structure_enrichment_obj_pr2 x y
                     =
                     g · structure_enrichment_obj_pr2 x y)
      : f = g.
    Proof.
      use (BinProductArrowsEq _ _ _ (pr1 EBC x y)).
      - exact p.
      - exact q.
    Qed.

    Definition structure_enrichment_binary_prod_pair
               (x y z : C)
      : E' ⦃ z , x ⦄ ⊗ (E' ⦃ z , y ⦄)
        -->
        E' ⦃ z , structure_enrichment_obj_binary_prod x y ⦄
      := _ ,, pr2 EBC x y z.
  End StructureEnrichedProdAccessors.

  Section StructureProd.
    Context (EBC : structure_enrichment_binary_prod)
            (x y : C).

    Definition make_structure_enriched_binary_prod_cone
      : enriched_binary_prod_cone E' x y.
    Proof.
      use make_enriched_binary_prod_cone.
      - exact (structure_enrichment_obj_binary_prod EBC x y).
      - exact (enriched_from_arr E' (structure_enrichment_obj_pr1 EBC x y)).
      - exact (enriched_from_arr E' (structure_enrichment_obj_pr2 EBC x y)).
    Defined.

    Definition structure_enrichment_binary_prod_is_prod
      : is_binary_prod_enriched E' x y make_structure_enriched_binary_prod_cone.
    Proof.
      use make_is_binary_prod_enriched.
      - intros z X f g.
        refine (_ · structure_enrichment_binary_prod_pair _ _ _ _).
        simple refine (_ ,, _).
        + exact (prodtofuntoprod (pr1 f ,, pr1 g)).
        + apply hset_struct_pair.
          * exact (pr2 f).
          * exact (pr2 g).
      - abstract
          (intros z X f g ;
           use eq_mor_hset_struct ;
           intros w ; cbn ;
           apply structure_enrichment_obj_pair_pr1).
      - abstract
          (intros z X f g ;
           use eq_mor_hset_struct ;
           intros w ; cbn ;
           apply structure_enrichment_obj_pair_pr2).
      - abstract
          (intros z X φ₁ φ₂ q₁ q₂ ;
           use eq_mor_hset_struct ;
           intro w ;
           use structure_enrichment_binary_prod_arr_eq ;
           [ exact (eqtohomot (maponpaths (λ f, pr1 f) q₁) w)
           | exact (eqtohomot (maponpaths (λ f, pr1 f) q₂) w) ]).
    Defined.
  End StructureProd.

  Definition make_structure_enrichment_binary_prod
             (EBC : structure_enrichment_binary_prod)
    : enrichment_binary_prod E'
    := λ x y,
       make_structure_enriched_binary_prod_cone EBC x y
       ,,
       structure_enrichment_binary_prod_is_prod EBC x y.

  Section ToStructureProduct.
    Context (EP : enrichment_binary_prod E')
            {x y z : C}.

    Let prod : sym_monoidal_cat_of_hset_struct P
      := (E' ⦃ x , y ⦄) ⊗ (E' ⦃ x , z ⦄).

    Let prod_pr1 : prod --> E' ⦃ x , y ⦄
      := _ ,, hset_struct_pr1 _ _ _.

    Let prod_pr2 : prod --> E' ⦃ x , z ⦄
      := _ ,, hset_struct_pr2 _ _ _.

    Definition structure_to_underlying_binary_prod_map
               (f : x --> y)
               (g : x --> z)
      : x --> underlying_BinProduct E' y z (pr2 (EP y z))
      := pr1 (BinProductArrow
                (sym_monoidal_cat_of_hset_struct P)
                (is_binary_prod_enriched_to_BinProduct E' _ _ (pr2 (EP y z)) x)
                prod_pr1
                prod_pr2)
             (f ,, g).

    Proposition structure_to_underlying_binary_prod_map_pr1
                (f : x --> y)
                (g : x --> z)
      : structure_to_underlying_binary_prod_map f g
        · enriched_prod_cone_pr1 E' y z (pr1 (EP y z))
        =
        f.
    Proof.
      pose (eqtohomot
              (maponpaths
                 pr1
                 (BinProductPr1Commutes
                    _
                    _ _
                    (is_binary_prod_enriched_to_BinProduct E' _ _ (pr2 (EP y z)) x)
                    _
                    prod_pr1
                    prod_pr2))
              (f ,, g))
        as p.
      cbn in p.
      exact p.
    Qed.

    Proposition structure_to_underlying_binary_prod_map_pr2
                (f : x --> y)
                (g : x --> z)
      : structure_to_underlying_binary_prod_map f g
        · enriched_prod_cone_pr2 E' y z (pr1 (EP y z))
        =
        g.
    Proof.
      pose (eqtohomot
              (maponpaths
                 pr1
                 (BinProductPr2Commutes
                    _
                    _ _
                    (is_binary_prod_enriched_to_BinProduct E' _ _ (pr2 (EP y z)) x)
                    _
                    prod_pr1
                    prod_pr2))
              (f ,, g))
        as p.
      cbn in p.
      exact p.
    Qed.

    Proposition structure_to_underlying_binary_prod_map_eq
      : (λ fg, BinProductArrow
                 C
                 (underlying_BinProduct E' y z (pr2 (EP y z)))
                 (pr1 fg)
                 (pr2 fg))
        =
        (λ fg, structure_to_underlying_binary_prod_map
                 (pr1 fg)
                 (dirprod_pr2 fg)).
    Proof.
      use funextsec.
      intros fg.
      use is_binary_prod_enriched_arrow_eq.
      - exact (pr2 (EP y z)).
      - refine (_ @ !(structure_to_underlying_binary_prod_map_pr1 _ _)).
        apply (BinProductPr1Commutes
                 C
                 _ _
                 (underlying_BinProduct E' y z (pr2 (EP y z)))
                 _
                 _ _).
      - refine (_ @ !(structure_to_underlying_binary_prod_map_pr2 _ _)).
        apply (BinProductPr2Commutes
                 C
                 _ _
                 (underlying_BinProduct E' y z (pr2 (EP y z)))
                 _
                 _ _).
    Qed.

    Proposition structure_to_underlying_binary_prod_map_structure_preserving
      : mor_hset_struct
          P
          (hset_struct_prod P (E x y) (E x z))
          (E x (underlying_BinProduct E' y z (pr2 (EP y z))))
          (λ fg,
            BinProductArrow
              C
              (underlying_BinProduct E' y z (pr2 (EP y z)))
              (pr1 fg)
              (pr2 fg)).
    Proof.
      exact (transportb
                _
                structure_to_underlying_binary_prod_map_eq
                (pr2 (@BinProductArrow
                         _ _ _
                         (is_binary_prod_enriched_to_BinProduct E' _ _ (pr2 (EP y z)) x)
                         prod
                         prod_pr1
                         prod_pr2))).
    Qed.
  End ToStructureProduct.

  Definition to_structure_enrichment_binary_prod
             (EP : enrichment_binary_prod E')
    : structure_enrichment_binary_prod.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, underlying_BinProduct E' x y (pr2 (EP x y))).
    - abstract
        (intros x y z ;
         apply structure_to_underlying_binary_prod_map_structure_preserving).
  Defined.

  Definition structure_enrichment_binary_prod_weq
             (HC : is_univalent C)
    : enrichment_binary_prod E' ≃ structure_enrichment_binary_prod.
  Proof.
    use weqimplimpl.
    - apply to_structure_enrichment_binary_prod.
    - apply make_structure_enrichment_binary_prod.
    - apply (isaprop_enrichment_binary_prod HC).
    - apply (isaprop_structure_enrichment_binary_prod HC).
  Defined.

  (**
   3. Equalizers
   *)
  Section EqualizerStructures.
    Context (HP : hset_equalizer_struct P).

    Definition structure_enrichment_equalizers
      : UU
      := ∑ (EC : Equalizers C),
         ∏ (w x y : C)
           (f g : x --> y),
         mor_hset_struct
           P
           (hset_struct_equalizer
              HP
              (pr2 (postcomp_arr E' w f))
              (pr2 (postcomp_arr E' w g)))
           (E w (EC x y f g))
           (λ h, EqualizerIn (EC x y f g) w (pr1 h) (pr2 h)).

    Proposition isaprop_structure_enrichment_equalizers
                (HC : is_univalent C)
      : isaprop structure_enrichment_equalizers.
    Proof.
      simple refine (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
      - repeat (use impred ; intro).
        apply isaprop_Equalizer.
        exact HC.
      - repeat (use impred ; intro).
        apply isaprop_hset_struct_on_mor.
    Qed.

    Section StructureEnrichedEqualizerAccessors.
      Context (EEC : structure_enrichment_equalizers).

      Definition structure_enrichment_obj_equalizer
                 {x y : C}
                 (f g : x --> y)
        : C
        := pr1 EEC x y f g.

      Definition structure_enrichment_obj_equalizer_pr
                 {x y : C}
                 (f g : x --> y)
        : structure_enrichment_obj_equalizer f g --> x
        := EqualizerArrow (pr1 EEC x y f g).

      Proposition structure_enrichment_obj_pr_eq
                  {x y : C}
                  (f g : x --> y)
        : structure_enrichment_obj_equalizer_pr f g · f
          =
          structure_enrichment_obj_equalizer_pr f g · g.
      Proof.
        apply EqualizerEqAr.
      Qed.

      Definition structure_enrichment_obj_to_equalizer
                 {w x y : C}
                 {f g : x --> y}
                 (h : w --> x)
                 (q : h · f = h · g)
        : w --> structure_enrichment_obj_equalizer f g
        := EqualizerIn (pr1 EEC x y f g) w h q.

      Proposition structure_enrichment_obj_to_equalizer_pr
                  {w x y : C}
                  {f g : x --> y}
                  (h : w --> x)
                  (q : h · f = h · g)
        : structure_enrichment_obj_to_equalizer h q
          · structure_enrichment_obj_equalizer_pr f g
          =
          h.
      Proof.
        apply EqualizerCommutes.
      Qed.

      Proposition structure_enrichment_equalizer_arr_eq
                  {w x y : C}
                  {f g : x --> y}
                  {h₁ h₂ : w --> structure_enrichment_obj_equalizer f g}
                  (q : h₁ · structure_enrichment_obj_equalizer_pr f g
                       =
                       h₂ · structure_enrichment_obj_equalizer_pr f g)
        : h₁ = h₂.
      Proof.
        use EqualizerInsEq.
        exact q.
      Qed.

      Definition structure_enrichment_to_equalizer
                 {w x y : C}
                 (f g : x --> y)
        : hset_struct_equalizer_ob
            HP
            (pr2 (postcomp_arr E' w f))
            (pr2 (postcomp_arr E' w g))
           -->
           E' ⦃ w , structure_enrichment_obj_equalizer f g ⦄
        := _ ,, pr2 EEC w x y f g.
    End StructureEnrichedEqualizerAccessors.

    Section StructureEqualizer.
      Context (EEC : structure_enrichment_equalizers)
              {x y : C}
              (f g : x --> y).

      Definition make_structure_enrichment_equalizer_cone
        : enriched_equalizer_cone E' f g.
      Proof.
        use make_enriched_equalizer_cone.
        - exact (structure_enrichment_obj_equalizer EEC f g).
        - exact (enriched_from_arr E' (structure_enrichment_obj_equalizer_pr EEC f g)).
        - exact (structure_enrichment_obj_pr_eq EEC f g).
      Defined.

      Definition make_structure_enrichment_equalizer_is_equalizer
        : is_equalizer_enriched
            E'
            f g
            make_structure_enrichment_equalizer_cone.
      Proof.
        use make_is_equalizer_enriched.
        - abstract
            (intros w X φ₁ φ₂ q ;
             use eq_mor_hset_struct ;
             intro z ;
             use structure_enrichment_equalizer_arr_eq ;
             exact (eqtohomot (maponpaths pr1 q) z)).
        - intros w X h q.
          refine (_ · structure_enrichment_to_equalizer EEC f g).
          simple refine (_ ,, _).
          + refine (λ z, pr1 h z ,, _).
            exact (eqtohomot (maponpaths pr1 q) z).
          + abstract
              (apply hset_equalizer_arrow_struct ;
               exact (pr2 h)).
        - abstract
            (intros w X h q ;
             use eq_mor_hset_struct ;
             intros z ;
             apply structure_enrichment_obj_to_equalizer_pr).
      Defined.
    End StructureEqualizer.

    Definition make_structure_enrichment_equalizers
               (EEC : structure_enrichment_equalizers)
      : enrichment_equalizers E'.
    Proof.
      intros x y f g.
      simple refine (_ ,, _).
      - exact (make_structure_enrichment_equalizer_cone EEC f g).
      - exact (make_structure_enrichment_equalizer_is_equalizer EEC f g).
    Defined.

    Section ToStructureEqualizer.
      Context (EEC : enrichment_equalizers E')
              {w x y : C}
              (f g : x --> y).

      Let Eq : Equalizer _ _
        := Equalizers_category_of_hset_struct
             HP
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

      Definition structure_to_underlying_equalizer_map
                 (h : w --> x)
                 (q : h · f = h · g)
        : w --> underlying_Equalizer E' f g (pr2 (EEC x y f g))
        := pr1 (EqualizerIn
                  (is_equalizer_enriched_to_Equalizer E' f g (pr2 (EEC x y f g)) w)
                  Eq
                  Eq_pr
                  Eq_path)
             (h ,, q).

      Proposition structure_to_underlying_equalizer_map_pr
                  (h : w --> x)
                  (q : h · f = h · g)
        : structure_to_underlying_equalizer_map h q
            · enriched_equalizer_cone_pr E' f g (pr1 (EEC x y f g))
          =
          h.
      Proof.
        pose (eqtohomot
                (maponpaths
                   pr1
                   (EqualizerCommutes
                      (is_equalizer_enriched_to_Equalizer E' f g (pr2 (EEC x y f g)) w)
                      Eq
                      Eq_pr
                      Eq_path))
                (h ,, q))
          as p.
        cbn in p.
        exact p.
      Qed.

      Definition to_structure_enrichment_equalizer_structure_preserving
        : mor_hset_struct
            P
            (hset_struct_equalizer
               HP
               (pr2 (postcomp_arr E' w f))
               (pr2 (postcomp_arr E' w g)))
            (E w (underlying_Equalizer E' f g (pr2 (EEC x y f g))))
            (λ h, EqualizerIn
                    (underlying_Equalizer E' f g (pr2 (EEC x y f g)))
                    w
                    (pr1 h)
                    (pr2 h)).
      Proof.
        refine (transportb
                  _
                  _
                  (pr2 (EqualizerIn
                          (is_equalizer_enriched_to_Equalizer E' _ _ (pr2 (EEC x y f g)) w)
                          Eq
                          Eq_pr
                          Eq_path))).
        use funextsec.
        intros fg.
        use underlying_Equalizer_arr_eq.
        - exact (pr2 (EEC x y f g)).
        - refine (_ @ !(structure_to_underlying_equalizer_map_pr (pr1 fg) (pr2 fg))).
          apply (EqualizerCommutes
                   (underlying_Equalizer E' f g (pr2 (EEC x y f g)))).
      Qed.
    End ToStructureEqualizer.

    Definition to_structure_enrichment_equalizer
               (EEC : enrichment_equalizers E')
      : structure_enrichment_equalizers.
    Proof.
      simple refine (_ ,, _).
      - exact (λ x y f g, underlying_Equalizer E' f g (pr2 (EEC x y f g))).
      - abstract
          (intros w x y f g ;
           apply to_structure_enrichment_equalizer_structure_preserving).
    Defined.

    Definition structure_enrichment_equalizer_weq
               (HC : is_univalent C)
      : enrichment_equalizers E' ≃ structure_enrichment_equalizers.
    Proof.
      use weqimplimpl.
      - apply to_structure_enrichment_equalizer.
      - apply make_structure_enrichment_equalizers.
      - apply (isaprop_enrichment_equalizers HC).
      - apply (isaprop_structure_enrichment_equalizers HC).
    Defined.
  End EqualizerStructures.

  (**
   4. Type indexed products
   *)
  Section StructureTypeIndexedProducts.
    Context {J : UU}
            (HP : hset_struct_type_prod P J).

    Definition structure_enrichment_prod
      : UU
      := ∑ (PC : Products J C),
         ∏ (x : C)
           (ys : J → C),
         mor_hset_struct
           P
           (HP _ (λ j, pr2 (E' ⦃ x , ys j ⦄)))
           (E x (PC ys))
           (λ h, ProductArrow _ _ (PC ys) (λ i, h i)).

    Proposition isaprop_structure_enrichment_prod
                (HC : is_univalent C)
      : isaprop structure_enrichment_prod.
    Proof.
      simple refine (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
      - repeat (use impred ; intro).
        apply isaprop_Product.
        exact HC.
      - repeat (use impred ; intro).
        apply isaprop_hset_struct_on_mor.
    Qed.

    Section StructureEnrichedProdAccessors.
      Context (EC : structure_enrichment_prod).

      Definition structure_enrichment_obj_prod
                 (ys : J → C)
        : C
        := pr1 EC ys.

      Definition structure_enrichment_obj_prod_pr
                 (ys : J → C)
                 (j : J)
        : structure_enrichment_obj_prod ys --> ys j
        := ProductPr _ _ (pr1 EC ys) j.

      Definition structure_enrichment_obj_prod_pair
                 {x : C}
                 {ys : J → C}
                 (fs : ∏ (j : J), x --> ys j)
        : x --> structure_enrichment_obj_prod ys
        := ProductArrow _ _ (pr1 EC ys) fs.

      Proposition structure_enrichment_obj_prod_pair_pr
                  {x : C}
                  {ys : J → C}
                  (fs : ∏ (j : J), x --> ys j)
                  (j : J)
        : structure_enrichment_obj_prod_pair fs · structure_enrichment_obj_prod_pr ys j
          =
          fs j.
      Proof.
        apply ProductPrCommutes.
      Qed.

      Proposition structure_enrichment_prod_arr_eq
                  {x : C}
                  {ys : J → C}
                  {f g : x --> structure_enrichment_obj_prod ys}
                  (p : ∏ (j : J),
                       f · structure_enrichment_obj_prod_pr ys j
                       =
                       g · structure_enrichment_obj_prod_pr ys j)
        : f = g.
      Proof.
        use (ProductArrow_eq _ _ _ (pr1 EC ys)).
        exact p.
      Qed.

      Definition structure_enrichment_prod_pair
                 (x : C)
                 (ys : J → C)
        : hset_struct_type_prod_ob HP _ (λ j, pr2 (E' ⦃ x , ys j ⦄))
          -->
          E' ⦃ x , pr1 EC ys ⦄
        := _ ,, pr2 EC x ys.
    End StructureEnrichedProdAccessors.

    Section StructureProd.
      Context (EBC : structure_enrichment_prod)
              (ys : J → C).

      Definition make_structure_enriched_prod_cone
        : enriched_prod_cone E' ys.
      Proof.
        use make_enriched_prod_cone.
        - exact (structure_enrichment_obj_prod EBC ys).
        - exact (λ j, enriched_from_arr E' (structure_enrichment_obj_prod_pr EBC ys j)).
      Defined.

      Definition structure_enrichment_prod_is_prod
        : is_prod_enriched E' ys make_structure_enriched_prod_cone.
      Proof.
        use make_is_prod_enriched.
        - intros z X fs.
          refine (_ · structure_enrichment_prod_pair _ _ _).
          simple refine (_ ,, _).
          + exact (λ x j, pr1 (fs j) x).
          + abstract
              (use hset_struct_type_prod_pair ;
               intro j ;
               exact (pr2 (fs j))).
        - abstract
            (intros z X f g ;
             use eq_mor_hset_struct ;
             intros w ; cbn ;
             apply structure_enrichment_obj_prod_pair_pr).
        - abstract
            (intros z X φ₁ φ₂ q ;
             use eq_mor_hset_struct ;
             intro w ;
             use structure_enrichment_prod_arr_eq ;
             intro j ;
             exact (eqtohomot (maponpaths (λ f, pr1 f) (q j)) w)).
      Defined.
    End StructureProd.

    Definition make_structure_enrichment_prod
               (EBC : structure_enrichment_prod)
      : enrichment_prod E' J
      := λ ys,
         make_structure_enriched_prod_cone EBC ys
         ,,
         structure_enrichment_prod_is_prod EBC ys.

    Section ToStructureProduct.
      Context (EP : enrichment_prod E' J)
              {x : C}
              (ys : J → C).

      Let prod : Product _ _ _
        := Products_category_of_hset_struct_type_prod HP (λ j, E' ⦃ x , ys j ⦄).

      Let prod_pr : ∏ (j : J), prod --> E' ⦃ x , ys j ⦄
        := λ j, _ ,, hset_struct_type_prod_pr HP (λ j, pr2 (E' ⦃ x , ys j ⦄)) j.

      Definition structure_to_underlying_prod_map
                 (fs : ∏ (j : J), x --> ys j)
        : x --> underlying_Product E' ys (pr2 (EP ys))
        := pr1 (ProductArrow
                  _ _
                  (is_prod_enriched_to_Product E' _ (pr2 (EP ys)) x)
                  prod_pr)
             fs.

      Proposition structure_to_underlying_prod_map_pr
                  (fs : ∏ (j : J), x --> ys j)
                  (j : J)
        : structure_to_underlying_prod_map fs
          · enriched_prod_cone_pr E' ys (pr1 (EP ys)) j
          =
          fs j.
      Proof.
        pose (eqtohomot
                (maponpaths
                   pr1
                   (ProductPrCommutes
                      J _ _
                      (is_prod_enriched_to_Product E' _ (pr2 (EP ys)) x)
                      _
                      prod_pr
                      j))
                fs)
          as p.
        cbn in p.
        exact p.
      Qed.

      Definition to_structure_enrichment_prod_structure_preserving
        : mor_hset_struct
            P
            (HP (λ j, pr1 (E' ⦃ x, ys j ⦄)) (λ j : J, pr2 (E' ⦃ x, ys j ⦄)))
            (E x (underlying_Product E' ys (pr2 (EP ys))))
            (λ h, ProductArrow
                    J C
                    (underlying_Product E' ys (pr2 (EP ys)))
                    (λ i, h i)).
      Proof.
        refine (transportb
                  _
                  _
                  (pr2 (@ProductArrow
                      _ _ _
                      (is_prod_enriched_to_Product E' _ (pr2 (EP ys)) x)
                      prod
                      prod_pr))).
        use funextsec.
        intros fg.
        use is_prod_enriched_arrow_eq.
        - exact (pr2 (EP ys)).
        - intro j.
          refine (_ @ !(structure_to_underlying_prod_map_pr _ j)).
          apply (ProductPrCommutes _ _ _ (underlying_Product E' ys (pr2 (EP ys)))).
      Qed.
    End ToStructureProduct.

    Definition to_structure_enrichment_prod
               (EP : enrichment_prod E' J)
      : structure_enrichment_prod.
    Proof.
      simple refine (_ ,, _).
      - exact (λ ys, underlying_Product E' ys (pr2 (EP ys))).
      - intros x ys.
        apply to_structure_enrichment_prod_structure_preserving.
    Defined.

    Definition structure_enrichment_prod_weq
               (HC : is_univalent C)
      : enrichment_prod E' J ≃ structure_enrichment_prod.
    Proof.
      use weqimplimpl.
      - apply to_structure_enrichment_prod.
      - apply make_structure_enrichment_prod.
      - apply (isaprop_enrichment_prod HC).
      - apply (isaprop_structure_enrichment_prod HC).
    Defined.
  End StructureTypeIndexedProducts.

  (**
   5. Powers
   *)
  Definition structure_enrichment_pows
    : UU
    := ∑ (prods : ∏ (X : category_of_hset_struct P), Products (pr11 X) C),
       ∏ (X : category_of_hset_struct P)
         (x : C),
       mor_hset_struct
         P
         (pr2 X)
         (E (prods X (λ _, x)) x)
         (ProductPr _ _ (prods X (λ _, x)))
       ×
       (∏ (y : C),
        mor_hset_struct
          P
          (hset_struct_fun P (pr2 X) (E y x))
          (E y (prods X (λ _, x)))
          (λ f, ProductArrow _ _ (prods X (λ _, x)) (pr1 f))).

  Section StructureEnrichmentPowersAccessors.
    Context (HE : structure_enrichment_pows).

    Definition structure_pows_prod
               (X : category_of_hset_struct P)
               (x : C)
      : Product (pr11 X) C (λ _, x)
      := pr1 HE X (λ _, x).

    Definition structure_pows_pr
               {X : category_of_hset_struct P}
               {x : C}
               (i : pr11 X)
      : structure_pows_prod X x --> x
      := ProductPr _ _ (structure_pows_prod X x) i.

    Proposition structure_pows_mor_pr
                (X : category_of_hset_struct P)
                (x : C)
      : mor_hset_struct
          P
          (pr2 X)
          (E (structure_pows_prod X x) x)
          structure_pows_pr.
    Proof.
      exact (pr1 (pr2 HE X x)).
    Qed.

    Proposition structure_pows_mor_product_arr
                (X : category_of_hset_struct P)
                (x y : C)
      : mor_hset_struct
          P
          (hset_struct_fun P (pr2 X) (E y x))
          (E y (structure_pows_prod X x))
          (λ f, ProductArrow _ _ (structure_pows_prod X x) (pr1 f)).
    Proof.
      exact (pr2 (pr2 HE X x) y).
    Qed.
  End StructureEnrichmentPowersAccessors.

  Section StructureEnrichmentPowers.
    Context (HE : structure_enrichment_pows)
            (X : sym_mon_closed_cat_of_hset_struct P)
            (x : C).

    Let pow : Product _ C (λ _, x) := structure_pows_prod HE X x.
    Let pow_pr : ∏ (_ : pr11 X), pow --> x := λ i, structure_pows_pr HE i.

    Definition structure_power_cone
      : power_cone E' X x.
    Proof.
      simple refine (_ ,, _).
      - exact pow.
      - simple refine (_ ,, _).
        + exact pow_pr.
        + exact (structure_pows_mor_pr HE X x).
    Defined.

    Definition structure_power_map
               (y : C)
      : X ⊸ (E' ⦃ y , x ⦄) --> E' ⦃ y , structure_power_cone ⦄.
    Proof.
      simple refine (_ ,, _).
      - intro f.
        exact (ProductArrow _ _ pow (pr1 f)).
      - exact (structure_pows_mor_product_arr HE X x y).
    Defined.

    Definition structure_power_is_power
      : is_power_enriched E' X x structure_power_cone.
    Proof.
      use make_is_power_enriched.
      - exact structure_power_map.
      - abstract
          (intro y ;
           use eq_mor_hset_struct ;
           intro f ;
           cbn in f ;
           use ProductArrow_eq ;
           intro i ;
           apply (ProductPrCommutes _ _ _ pow)).
      - abstract
          (intro y ;
           use eq_mor_hset_struct ;
           intro f ;
           use eq_mor_hset_struct ;
           intro i ;
           cbn ;
           apply (ProductPrCommutes _ _ _ pow)).
    Defined.
  End StructureEnrichmentPowers.

  Definition structure_enrichment_powers_from_products
             (HE : structure_enrichment_pows)
    : enrichment_power E'.
  Proof.
    intros X x.
    simple refine (_ ,, _).
    - exact (structure_power_cone HE X x).
    - apply structure_power_is_power.
  Defined.
End StructureEnrichmentLimits.
