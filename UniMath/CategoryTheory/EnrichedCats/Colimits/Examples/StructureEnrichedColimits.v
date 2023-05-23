#[local] Unset Universe Checking.
(*****************************************************************

 Colimits in categories enriched over structures

 In this file we characterize colimits in categories enriched over
 structures. The proofs and characterizations are in essence the
 same as for posets. A category enriched over structures inherits
 its colimits from the underlying category if inclsuons and the
 maps arising from the universal property are structure
 preserving.

 Contents
 1. Initial object
 2. Binary coproducts
 3. Coequalizers
 4. Type indexed coproducts
 5. Copowers

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
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedInitial.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedBinaryCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCoequalizers.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCopowers.
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
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.coequalizers.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section StructureEnrichmentColimits.
  Context {P : hset_cartesian_closed_struct}
          {C : category}
          (E : struct_enrichment P C).

  Let E' : enrichment C (sym_mon_closed_cat_of_hset_struct P)
    := make_enrichment_over_struct P C E.

  (**
   1. Initial object
   *)
  Section StructureEnrichedInitial.
    Context {x : C}
            (Hx : isInitial C x).

    Let T : Initial C := make_Initial x Hx.

    Definition structure_enrichment_is_initial
      : is_initial_enriched E' x.
    Proof.
      use make_is_initial_enriched.
      - intros X y.
        simple refine (_ ,, _).
        + exact (λ _, InitialArrow T y).
        + abstract
            (cbn ;
             apply hset_struct_const).
      - abstract
          (intros X y f g ;
           use eq_mor_hset_struct ;
           intros z ;
           apply (@InitialArrowEq _ T)).
    Defined.
  End StructureEnrichedInitial.

  Definition make_structure_enrichment_initial
             (HC : Initial C)
    : initial_enriched E'
    := pr1 HC ,, structure_enrichment_is_initial (pr2 HC).

  Definition structure_terminal_enriched_weq_Initial
             (HC : is_univalent C)
    : initial_enriched E' ≃ Initial C.
  Proof.
    use weqimplimpl.
    - exact (λ T, initial_underlying E' T).
    - exact make_structure_enrichment_initial.
    - apply (isaprop_initial_enriched _ HC).
    - apply (isaprop_Initial _ HC).
  Defined.

  (**
   2. Binary coproducts
   *)
  Definition structure_enrichment_binary_coprod
    : UU
    := ∑ (BC : BinCoproducts C),
       ∏ (x y z : C),
       mor_hset_struct
         P
         (hset_struct_prod P (E x z) (E y z))
         (E (BC x y) z)
         (λ fg, BinCoproductArrow (BC x y) (pr1 fg) (pr2 fg)).

  Proposition isaprop_structure_enrichment_binary_coprod
              (HC : is_univalent C)
    : isaprop structure_enrichment_binary_coprod.
  Proof.
    simple refine (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
    - do 2 (use impred ; intro).
      apply (isaprop_BinCoproduct _ HC).
    - repeat (use impred ; intro).
      apply isaprop_hset_struct_on_mor.
  Qed.

  Section StructureEnrichedCoprodAccessors.
    Context (EBC : structure_enrichment_binary_coprod).

    Definition structure_enrichment_obj_binary_coprod
               (x y : C)
      : C
      := pr1 EBC x y.

    Definition structure_enrichment_obj_in1
               (x y : C)
      : x --> structure_enrichment_obj_binary_coprod x y
      := BinCoproductIn1 (pr1 EBC x y).

    Definition structure_enrichment_obj_in2
               (x y : C)
      : y --> structure_enrichment_obj_binary_coprod x y
      := BinCoproductIn2 (pr1 EBC x y).

    Definition structure_enrichment_obj_sum
               {z x y : C}
               (f : x --> z)
               (g : y --> z)
      : structure_enrichment_obj_binary_coprod x y --> z
      := BinCoproductArrow (pr1 EBC x y) f g.

    Proposition structure_enrichment_obj_in1_sum
                {z x y : C}
                (f : x --> z)
                (g : y --> z)
      : structure_enrichment_obj_in1 x y · structure_enrichment_obj_sum f g
        =
        f.
    Proof.
      apply BinCoproductIn1Commutes.
    Qed.

    Proposition structure_enrichment_obj_in2_sum
                {z x y : C}
                (f : x --> z)
                (g : y --> z)
      : structure_enrichment_obj_in2 x y · structure_enrichment_obj_sum f g
        =
        g.
    Proof.
      apply BinCoproductIn2Commutes.
    Qed.

    Proposition structure_enrichment_binary_coprod_arr_eq
                {w x y : C}
                {f g : structure_enrichment_obj_binary_coprod x y --> w}
                (p : structure_enrichment_obj_in1 x y · f
                     =
                     structure_enrichment_obj_in1 x y · g)
                (q : structure_enrichment_obj_in2 x y · f
                     =
                     structure_enrichment_obj_in2 x y · g)
      : f = g.
    Proof.
      use (BinCoproductArrowsEq _ _ _ (pr1 EBC x y)).
      - exact p.
      - exact q.
    Qed.

    Definition structure_enrichment_binary_coprod_pair
               (x y z : C)
      : E' ⦃ x , z ⦄ ⊗ (E' ⦃ y , z ⦄)
        -->
        E' ⦃ structure_enrichment_obj_binary_coprod x y , z ⦄
      := _ ,, pr2 EBC x y z.
  End StructureEnrichedCoprodAccessors.

  Section StructureCoprod.
    Context (EBC : structure_enrichment_binary_coprod)
            (x y : C).

    Definition make_structure_enriched_binary_coprod_cocone
      : enriched_binary_coprod_cocone E' x y.
    Proof.
      use make_enriched_binary_coprod_cocone.
      - exact (structure_enrichment_obj_binary_coprod EBC x y).
      - exact (enriched_from_arr E' (structure_enrichment_obj_in1 EBC x y)).
      - exact (enriched_from_arr E' (structure_enrichment_obj_in2 EBC x y)).
    Defined.

    Definition structure_enrichment_binary_coprod_is_coprod
      : is_binary_coprod_enriched E' x y make_structure_enriched_binary_coprod_cocone.
    Proof.
      use make_is_binary_coprod_enriched.
      - intros z X f g.
        refine (_ · structure_enrichment_binary_coprod_pair _ _ _ _).
        simple refine (_ ,, _).
        + exact (prodtofuntoprod (pr1 f ,, pr1 g)).
        + apply hset_struct_pair.
          * exact (pr2 f).
          * exact (pr2 g).
      - abstract
          (intros z X f g ;
           use eq_mor_hset_struct ;
           intros w ; cbn ;
           apply structure_enrichment_obj_in1_sum).
      - abstract
          (intros z X f g ;
           use eq_mor_hset_struct ;
           intros w ; cbn ;
           apply structure_enrichment_obj_in2_sum).
      - abstract
          (intros z X φ₁ φ₂ q₁ q₂ ;
           use eq_mor_hset_struct ;
           intro w ;
           use structure_enrichment_binary_coprod_arr_eq ;
           [ exact (eqtohomot (maponpaths (λ f, pr1 f) q₁) w)
           | exact (eqtohomot (maponpaths (λ f, pr1 f) q₂) w) ]).
    Defined.
  End StructureCoprod.

  Definition make_structure_enrichment_binary_coprod
             (EBC : structure_enrichment_binary_coprod)
    : enrichment_binary_coprod E'
    := λ x y,
       make_structure_enriched_binary_coprod_cocone EBC x y
       ,,
       structure_enrichment_binary_coprod_is_coprod EBC x y.

  Section ToStructureCoproduct.
    Context (EP : enrichment_binary_coprod E')
            {x y z : C}.

    Let prod : sym_monoidal_cat_of_hset_struct P
      := (E' ⦃ y , x ⦄) ⊗ (E' ⦃ z , x ⦄).

    Let prod_pr1 : prod --> E' ⦃ y , x ⦄
      := _ ,, hset_struct_pr1 _ _ _.

    Let prod_pr2 : prod --> E' ⦃ z , x ⦄
      := _ ,, hset_struct_pr2 _ _ _.

    Definition structure_to_underlying_binary_coprod_map
               (f : y --> x)
               (g : z --> x)
      : underlying_BinCoproduct E' y z (pr2 (EP y z)) --> x
      := pr1 (BinProductArrow
                (sym_monoidal_cat_of_hset_struct P)
                (is_binary_coprod_enriched_to_BinProduct E' _ _ (pr2 (EP y z)) x)
                prod_pr1
                prod_pr2)
             (f ,, g).

    Proposition structure_to_underlying_binary_coprod_map_in1
                (f : y --> x)
                (g : z --> x)
      : enriched_coprod_cocone_in1 E' y z (pr1 (EP y z))
        · structure_to_underlying_binary_coprod_map f g
        =
        f.
    Proof.
      pose (eqtohomot
              (maponpaths
                 pr1
                 (BinProductPr1Commutes
                    _
                    _ _
                    (is_binary_coprod_enriched_to_BinProduct E' _ _ (pr2 (EP y z)) x)
                    _
                    prod_pr1
                    prod_pr2))
              (f ,, g))
        as p.
      cbn in p.
      exact p.
    Qed.

    Proposition structure_to_underlying_binary_coprod_map_in2
                (f : y --> x)
                (g : z --> x)
      : enriched_coprod_cocone_in2 E' y z (pr1 (EP y z))
        · structure_to_underlying_binary_coprod_map f g
        =
        g.
    Proof.
      pose (eqtohomot
              (maponpaths
                 pr1
                 (BinProductPr2Commutes
                    _
                    _ _
                    (is_binary_coprod_enriched_to_BinProduct E' _ _ (pr2 (EP y z)) x)
                    _
                    prod_pr1
                    prod_pr2))
              (f ,, g))
        as p.
      cbn in p.
      exact p.
    Qed.

    Proposition structure_to_underlying_binary_coprod_map_eq
      : (λ fg, BinCoproductArrow
                 (underlying_BinCoproduct E' y z (pr2 (EP y z)))
                 (pr1 fg)
                 (pr2 fg))
        =
        (λ fg, structure_to_underlying_binary_coprod_map
                 (pr1 fg)
                 (dirprod_pr2 fg)).
    Proof.
      use funextsec.
      intros fg.
      use is_binary_coprod_enriched_arrow_eq.
      - exact (pr2 (EP y z)).
      - refine (_ @ !(structure_to_underlying_binary_coprod_map_in1 _ _)).
        apply (BinCoproductIn1Commutes
                 C
                 _ _
                 (underlying_BinCoproduct E' y z (pr2 (EP y z)))
                 _
                 _ _).
      - refine (_ @ !(structure_to_underlying_binary_coprod_map_in2 _ _)).
        apply (BinCoproductIn2Commutes
                 C
                 _ _
                 (underlying_BinCoproduct E' y z (pr2 (EP y z)))
                 _
                 _ _).
    Qed.

    Proposition structure_to_underlying_binary_coprod_map_structure_preserving
      : mor_hset_struct
          P
          (hset_struct_prod P (E y x) (E z x))
          (E (underlying_BinCoproduct E' y z (pr2 (EP y z))) x)
          (λ fg,
            BinCoproductArrow
              (underlying_BinCoproduct E' y z (pr2 (EP y z)))
              (pr1 fg)
              (pr2 fg)).
    Proof.
      exact (transportb
                _
                structure_to_underlying_binary_coprod_map_eq
                (pr2 (@BinProductArrow
                         _ _ _
                         (is_binary_coprod_enriched_to_BinProduct E' _ _ (pr2 (EP y z)) x)
                         prod
                         prod_pr1
                         prod_pr2))).
    Qed.
  End ToStructureCoproduct.

  Definition to_structure_enrichment_binary_coprod
             (EP : enrichment_binary_coprod E')
    : structure_enrichment_binary_coprod.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, underlying_BinCoproduct E' x y (pr2 (EP x y))).
    - abstract
        (intros x y z ;
         apply structure_to_underlying_binary_coprod_map_structure_preserving).
  Defined.

  Definition structure_enrichment_binary_coprod_weq
             (HC : is_univalent C)
    : enrichment_binary_coprod E' ≃ structure_enrichment_binary_coprod.
  Proof.
    use weqimplimpl.
    - apply to_structure_enrichment_binary_coprod.
    - apply make_structure_enrichment_binary_coprod.
    - apply (isaprop_enrichment_binary_coprod HC).
    - apply (isaprop_structure_enrichment_binary_coprod HC).
  Defined.

  (**
   3. Coequalizers
   *)
  Section CoequalizerStructures.
    Context (HP : hset_equalizer_struct P).

    Definition structure_enrichment_coequalizers
      : UU
      := ∑ (EC : Coequalizers C),
         ∏ (w x y : C)
           (f g : x --> y),
         mor_hset_struct
           P
           (hset_struct_equalizer
              HP
              (pr2 (precomp_arr E' w f))
              (pr2 (precomp_arr E' w g)))
           (E (EC x y f g) w)
           (λ h, CoequalizerOut (EC x y f g) w (pr1 h) (pr2 h)).

    Proposition isaprop_structure_enrichment_coequalizers
                (HC : is_univalent C)
      : isaprop structure_enrichment_coequalizers.
    Proof.
      simple refine (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
      - repeat (use impred ; intro).
        apply isaprop_Coequalizer.
        exact HC.
      - repeat (use impred ; intro).
        apply isaprop_hset_struct_on_mor.
    Qed.

    Section StructureEnrichedCoequalizerAccessors.
      Context (EEC : structure_enrichment_coequalizers).

      Definition structure_enrichment_obj_coequalizer
                 {x y : C}
                 (f g : x --> y)
        : C
        := pr1 EEC x y f g.

      Definition structure_enrichment_obj_coequalizer_in
                 {x y : C}
                 (f g : x --> y)
        : y --> structure_enrichment_obj_coequalizer f g
        := CoequalizerArrow (pr1 EEC x y f g).

      Proposition structure_enrichment_obj_in_eq
                  {x y : C}
                  (f g : x --> y)
        : f · structure_enrichment_obj_coequalizer_in f g
          =
          g · structure_enrichment_obj_coequalizer_in f g.
      Proof.
        apply CoequalizerEqAr.
      Qed.

      Definition structure_enrichment_obj_from_coequalizer
                 {w x y : C}
                 {f g : x --> y}
                 (h : y --> w)
                 (q : f · h = g · h)
        : structure_enrichment_obj_coequalizer f g --> w
        := CoequalizerOut (pr1 EEC x y f g) w h q.

      Proposition structure_enrichment_obj_from_coequalizer_in
                  {w x y : C}
                  {f g : x --> y}
                  (h : y --> w)
                  (q : f · h = g · h)
        : structure_enrichment_obj_coequalizer_in f g
          · structure_enrichment_obj_from_coequalizer h q
          =
          h.
      Proof.
        apply CoequalizerCommutes.
      Qed.

      Proposition structure_enrichment_coequalizer_arr_eq
                  {w x y : C}
                  {f g : x --> y}
                  {h₁ h₂ : structure_enrichment_obj_coequalizer f g --> w}
                  (q : structure_enrichment_obj_coequalizer_in f g · h₁
                       =
                       structure_enrichment_obj_coequalizer_in f g · h₂)
        : h₁ = h₂.
      Proof.
        use CoequalizerOutsEq.
        exact q.
      Qed.

      Definition structure_enrichment_to_coequalizer
                 {w x y : C}
                 (f g : x --> y)
        : hset_struct_equalizer_ob
            HP
            (pr2 (precomp_arr E' w f))
            (pr2 (precomp_arr E' w g))
           -->
           E' ⦃ structure_enrichment_obj_coequalizer f g , w⦄
        := _ ,, pr2 EEC w x y f g.
    End StructureEnrichedCoequalizerAccessors.

    Section StructureCoequalizer.
      Context (EEC : structure_enrichment_coequalizers)
              {x y : C}
              (f g : x --> y).

      Definition make_structure_enrichment_coequalizer_cocone
        : enriched_coequalizer_cocone E' f g.
      Proof.
        use make_enriched_coequalizer_cocone.
        - exact (structure_enrichment_obj_coequalizer EEC f g).
        - exact (enriched_from_arr E' (structure_enrichment_obj_coequalizer_in EEC f g)).
        - exact (structure_enrichment_obj_in_eq EEC f g).
      Defined.

      Definition make_structure_enrichment_coequalizer_is_coequalizer
        : is_coequalizer_enriched
            E'
            f g
            make_structure_enrichment_coequalizer_cocone.
      Proof.
        use make_is_coequalizer_enriched.
        - abstract
            (intros w X φ₁ φ₂ q ;
             use eq_mor_hset_struct ;
             intro z ;
             use structure_enrichment_coequalizer_arr_eq ;
             exact (eqtohomot (maponpaths pr1 q) z)).
        - intros w X h q.
          refine (_ · structure_enrichment_to_coequalizer EEC f g).
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
             apply structure_enrichment_obj_from_coequalizer_in).
      Defined.
    End StructureCoequalizer.

    Definition make_structure_enrichment_coequalizers
               (EEC : structure_enrichment_coequalizers)
      : enrichment_coequalizers E'.
    Proof.
      intros x y f g.
      simple refine (_ ,, _).
      - exact (make_structure_enrichment_coequalizer_cocone EEC f g).
      - exact (make_structure_enrichment_coequalizer_is_coequalizer EEC f g).
    Defined.

    Section ToStructureCoequalizer.
      Context (EEC : enrichment_coequalizers E')
              {w x y : C}
              (f g : x --> y).

      Let Eq : Equalizer _ _
        := Equalizers_category_of_hset_struct
             HP
             _
             _
             (precomp_arr E' w f)
             (precomp_arr E' w g).

      Let Eq_pr : Eq --> E' ⦃ y , w ⦄
        := EqualizerArrow _.

      Let Eq_path : Eq_pr · precomp_arr E' w f
                    =
                    Eq_pr · precomp_arr E' w g
        := EqualizerEqAr _.

      Definition structure_to_underlying_coequalizer_map
                 (h : y --> w)
                 (q : f · h = g · h)
        : underlying_Coequalizer E' f g (pr2 (EEC x y f g)) --> w
        := pr1 (EqualizerIn
                  (is_coequalizer_enriched_to_Equalizer E' f g (pr2 (EEC x y f g)) w)
                  Eq
                  Eq_pr
                  Eq_path)
             (h ,, q).

      Proposition structure_to_underlying_coequalizer_map_in
                  (h : y --> w)
                  (q : f · h = g · h)
        : enriched_coequalizer_cocone_in E' f g (pr1 (EEC x y f g))
          · structure_to_underlying_coequalizer_map h q
          =
          h.
      Proof.
        pose (eqtohomot
                (maponpaths
                   pr1
                   (EqualizerCommutes
                      (is_coequalizer_enriched_to_Equalizer E' f g (pr2 (EEC x y f g)) w)
                      Eq
                      Eq_pr
                      Eq_path))
                (h ,, q))
          as p.
        cbn in p.
        exact p.
      Qed.

      Definition to_structure_enrichment_coequalizer_structure_preserving
        : mor_hset_struct
            P
            (hset_struct_equalizer
               HP
               (pr2 (precomp_arr E' w f))
               (pr2 (precomp_arr E' w g)))
            (E (underlying_Coequalizer E' f g (pr2 (EEC x y f g))) w)
            (λ h, CoequalizerOut
                    (underlying_Coequalizer E' f g (pr2 (EEC x y f g)))
                    w
                    (pr1 h)
                    (pr2 h)).
      Proof.
        refine (transportb
                  _
                  _
                  (pr2 (EqualizerIn
                          (is_coequalizer_enriched_to_Equalizer E' _ _ (pr2 (EEC x y f g)) w)
                          Eq
                          Eq_pr
                          Eq_path))).
        use funextsec.
        intros fg.
        use underlying_Coequalizer_arr_eq.
        - exact (pr2 (EEC x y f g)).
        - refine (_ @ !(structure_to_underlying_coequalizer_map_in (pr1 fg) (pr2 fg))).
          apply (CoequalizerCommutes
                   (underlying_Coequalizer E' f g (pr2 (EEC x y f g)))).
      Qed.
    End ToStructureCoequalizer.

    Definition to_structure_enrichment_coequalizer
               (EEC : enrichment_coequalizers E')
      : structure_enrichment_coequalizers.
    Proof.
      simple refine (_ ,, _).
      - exact (λ x y f g, underlying_Coequalizer E' f g (pr2 (EEC x y f g))).
      - abstract
          (intros w x y f g ;
           apply to_structure_enrichment_coequalizer_structure_preserving).
    Defined.

    Definition structure_enrichment_coequalizer_weq
               (HC : is_univalent C)
      : enrichment_coequalizers E' ≃ structure_enrichment_coequalizers.
    Proof.
      use weqimplimpl.
      - apply to_structure_enrichment_coequalizer.
      - apply make_structure_enrichment_coequalizers.
      - apply (isaprop_enrichment_coequalizers HC).
      - apply (isaprop_structure_enrichment_coequalizers HC).
    Defined.
  End CoequalizerStructures.

  (**
   4. Type indexed coproducts
   *)
  Section StructureTypeIndexedCoproducts.
    Context {J : UU}
            (HP : hset_struct_type_prod P J).

    Definition structure_enrichment_coprod
      : UU
      := ∑ (PC : Coproducts J C),
         ∏ (x : C)
           (ys : J → C),
         mor_hset_struct
           P
           (HP _ (λ j, pr2 (E' ⦃ ys j , x ⦄)))
           (E (PC ys) x)
           (λ h, CoproductArrow _ _ (PC ys) (λ i, h i)).

    Proposition isaprop_structure_enrichment_coprod
                (HC : is_univalent C)
      : isaprop structure_enrichment_coprod.
    Proof.
      simple refine (isaprop_total2 (_ ,, _) (λ _, (_ ,, _))).
      - repeat (use impred ; intro).
        apply isaprop_Coproduct.
        exact HC.
      - repeat (use impred ; intro).
        apply isaprop_hset_struct_on_mor.
    Qed.

    Section StructureEnrichedCoprodAccessors.
      Context (EC : structure_enrichment_coprod).

      Definition structure_enrichment_obj_coprod
                 (ys : J → C)
        : C
        := pr1 EC ys.

      Definition structure_enrichment_obj_coprod_in
                 (ys : J → C)
                 (j : J)
        : ys j --> structure_enrichment_obj_coprod ys
        := CoproductIn _ _ (pr1 EC ys) j.

      Definition structure_enrichment_obj_coprod_sum
                 {x : C}
                 {ys : J → C}
                 (fs : ∏ (j : J), ys j --> x)
        : structure_enrichment_obj_coprod ys --> x
        := CoproductArrow _ _ (pr1 EC ys) fs.

      Proposition structure_enrichment_obj_coprod_sum_in
                  {x : C}
                  {ys : J → C}
                  (fs : ∏ (j : J), ys j --> x)
                  (j : J)
        : structure_enrichment_obj_coprod_in ys j · structure_enrichment_obj_coprod_sum fs
          =
          fs j.
      Proof.
        apply CoproductInCommutes.
      Qed.

      Proposition structure_enrichment_coprod_arr_eq
                  {x : C}
                  {ys : J → C}
                  {f g : structure_enrichment_obj_coprod ys --> x}
                  (p : ∏ (j : J),
                       structure_enrichment_obj_coprod_in ys j · f
                       =
                       structure_enrichment_obj_coprod_in ys j · g)
        : f = g.
      Proof.
        use (CoproductArrow_eq _ _ _ (pr1 EC ys)).
        exact p.
      Qed.

      Definition structure_enrichment_coprod_pair
                 (x : C)
                 (ys : J → C)
        : hset_struct_type_prod_ob HP _ (λ j, pr2 (E' ⦃ ys j , x ⦄))
          -->
          E' ⦃ pr1 EC ys , x ⦄
        := _ ,, pr2 EC x ys.
    End StructureEnrichedCoprodAccessors.

    Section StructureCoprod.
      Context (EBC : structure_enrichment_coprod)
              (ys : J → C).

      Definition make_structure_enriched_coprod_cocone
        : enriched_coprod_cocone E' ys.
      Proof.
        use make_enriched_coprod_cocone.
        - exact (structure_enrichment_obj_coprod EBC ys).
        - exact (λ j, enriched_from_arr E' (structure_enrichment_obj_coprod_in EBC ys j)).
      Defined.

      Definition structure_enrichment_coprod_is_coprod
        : is_coprod_enriched E' ys make_structure_enriched_coprod_cocone.
      Proof.
        use make_is_coprod_enriched.
        - intros z X fs.
          refine (_ · structure_enrichment_coprod_pair _ _ _).
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
             apply structure_enrichment_obj_coprod_sum_in).
        - abstract
            (intros z X φ₁ φ₂ q ;
             use eq_mor_hset_struct ;
             intro w ;
             use structure_enrichment_coprod_arr_eq ;
             intro j ;
             exact (eqtohomot (maponpaths (λ f, pr1 f) (q j)) w)).
      Defined.
    End StructureCoprod.

    Definition make_structure_enrichment_coprod
               (EBC : structure_enrichment_coprod)
      : enrichment_coprod E' J
      := λ ys,
         make_structure_enriched_coprod_cocone EBC ys
         ,,
         structure_enrichment_coprod_is_coprod EBC ys.

    Section ToStructureCoproduct.
      Context (EP : enrichment_coprod E' J)
              {x : C}
              (ys : J → C).

      Let prod : Product _ _ _
        := Products_category_of_hset_struct_type_prod HP (λ j, E' ⦃ ys j , x ⦄).

      Let prod_pr : ∏ (j : J), prod --> E' ⦃ ys j , x ⦄
        := λ j, _ ,, hset_struct_type_prod_pr HP (λ j, pr2 (E' ⦃ ys j , x ⦄)) j.

      Definition structure_to_underlying_coprod_map
                 (fs : ∏ (j : J), ys j --> x)
        : underlying_Coproduct E' ys (pr2 (EP ys)) --> x
        := pr1 (ProductArrow
                  _ _
                  (is_coprod_enriched_to_Product E' _ (pr2 (EP ys)) x)
                  prod_pr)
             fs.

      Proposition structure_to_underlying_coprod_map_in
                  (fs : ∏ (j : J), ys j --> x)
                  (j : J)
        : enriched_coprod_cocone_in E' ys (pr1 (EP ys)) j
          · structure_to_underlying_coprod_map fs
          =
          fs j.
      Proof.
        pose (eqtohomot
                (maponpaths
                   pr1
                   (ProductPrCommutes
                      J _ _
                      (is_coprod_enriched_to_Product E' _ (pr2 (EP ys)) x)
                      _
                      prod_pr
                      j))
                fs)
          as p.
        cbn in p.
        exact p.
      Qed.

      Definition to_structure_enrichment_coprod_structure_preserving
        : mor_hset_struct
            P
            (HP (λ j, pr1 (E' ⦃ ys j , x ⦄)) (λ j : J, pr2 (E' ⦃ ys j , x ⦄)))
            (E (underlying_Coproduct E' ys (pr2 (EP ys))) x)
            (λ h, CoproductArrow
                    J C
                    (underlying_Coproduct E' ys (pr2 (EP ys)))
                    (λ i, h i)).
      Proof.
        refine (transportb
                  _
                  _
                  (pr2 (@ProductArrow
                      _ _ _
                      (is_coprod_enriched_to_Product E' _ (pr2 (EP ys)) x)
                      prod
                      prod_pr))).
        use funextsec.
        intros fg.
        use is_coprod_enriched_arrow_eq.
        - exact (pr2 (EP ys)).
        - intro j.
          refine (_ @ !(structure_to_underlying_coprod_map_in _ j)).
          apply (CoproductInCommutes _ _ _ (underlying_Coproduct E' ys (pr2 (EP ys)))).
      Qed.
    End ToStructureCoproduct.

    Definition to_structure_enrichment_coprod
               (EP : enrichment_coprod E' J)
      : structure_enrichment_coprod.
    Proof.
      simple refine (_ ,, _).
      - exact (λ ys, underlying_Coproduct E' ys (pr2 (EP ys))).
      - intros x ys.
        apply to_structure_enrichment_coprod_structure_preserving.
    Defined.

    Definition structure_enrichment_coprod_weq
               (HC : is_univalent C)
      : enrichment_coprod E' J ≃ structure_enrichment_coprod.
    Proof.
      use weqimplimpl.
      - apply to_structure_enrichment_coprod.
      - apply make_structure_enrichment_coprod.
      - apply (isaprop_enrichment_coprod HC).
      - apply (isaprop_structure_enrichment_coprod HC).
    Defined.
  End StructureTypeIndexedCoproducts.

  (**
   5. Copowers
   *)
  Definition structure_enrichment_copows
    : UU
    := ∑ (prods : ∏ (X : category_of_hset_struct P), Coproducts (pr11 X) C),
       ∏ (X : category_of_hset_struct P)
         (x : C),
       mor_hset_struct
         P
         (pr2 X)
         (E x (prods X (λ _, x)))
         (CoproductIn _ _ (prods X (λ _, x)))
       ×
       (∏ (y : C),
        mor_hset_struct
          P
          (hset_struct_fun P (pr2 X) (E x y))
          (E (prods X (λ _, x)) y)
          (λ f, CoproductArrow _ _ (prods X (λ _, x)) (pr1 f))).

  Section StructureEnrichmentCopowersAccessors.
    Context (HE : structure_enrichment_copows).

    Definition structure_copows_coprod
               (X : category_of_hset_struct P)
               (x : C)
      : Coproduct (pr11 X) C (λ _, x)
      := pr1 HE X (λ _, x).

    Definition structure_copows_in
               {X : category_of_hset_struct P}
               {x : C}
               (i : pr11 X)
      : x --> structure_copows_coprod X x
      := CoproductIn _ _ (structure_copows_coprod X x) i.

    Proposition structure_copows_mor_in
                (X : category_of_hset_struct P)
                (x : C)
      : mor_hset_struct
          P
          (pr2 X)
          (E x (structure_copows_coprod X x))
          structure_copows_in.
    Proof.
      exact (pr1 (pr2 HE X x)).
    Qed.

    Proposition structure_copows_mor_coproduct_arr
                (X : category_of_hset_struct P)
                (x y : C)
      : mor_hset_struct
          P
          (hset_struct_fun P (pr2 X) (E x y))
          (E (structure_copows_coprod X x) y)
          (λ f, CoproductArrow _ _ (structure_copows_coprod X x) (pr1 f)).
    Proof.
      exact (pr2 (pr2 HE X x) y).
    Qed.
  End StructureEnrichmentCopowersAccessors.

  Section StructureEnrichmentCopowers.
    Context (HE : structure_enrichment_copows)
            (X : sym_mon_closed_cat_of_hset_struct P)
            (x : C).

    Let copow : Coproduct _ C (λ _, x) := structure_copows_coprod HE X x.
    Let copow_in : ∏ (_ : pr11 X), x --> copow := λ i, structure_copows_in HE i.

    Definition structure_copower_cocone
      : copower_cocone E' X x.
    Proof.
      simple refine (_ ,, _).
      - exact copow.
      - simple refine (_ ,, _).
        + exact copow_in.
        + exact (structure_copows_mor_in HE X x).
    Defined.

    Definition structure_copower_map
               (y : C)
      : X ⊸ (E' ⦃ x , y ⦄) --> E' ⦃ structure_copower_cocone , y ⦄.
    Proof.
      simple refine (_ ,, _).
      - intro f.
        exact (CoproductArrow _ _ copow (pr1 f)).
      - exact (structure_copows_mor_coproduct_arr HE X x y).
    Defined.

    Definition structure_copower_is_copower
      : is_copower_enriched E' X x structure_copower_cocone.
    Proof.
      use make_is_copower_enriched.
      - exact structure_copower_map.
      - abstract
          (intro y ;
           use eq_mor_hset_struct ;
           intro f ;
           cbn in f ;
           use CoproductArrow_eq ;
           intro i ;
           apply (CoproductInCommutes _ _ _ copow)).
      - abstract
          (intro y ;
           use eq_mor_hset_struct ;
           intro f ;
           use eq_mor_hset_struct ;
           intro i ;
           cbn ;
           apply (CoproductInCommutes _ _ _ copow)).
    Defined.
  End StructureEnrichmentCopowers.

  Definition structure_enrichment_copowers_from_coproducts
             (HE : structure_enrichment_copows)
    : enrichment_copower E'.
  Proof.
    intros X x.
    simple refine (_ ,, _).
    - exact (structure_copower_cocone HE X x).
    - apply structure_copower_is_copower.
  Defined.
End StructureEnrichmentColimits.
