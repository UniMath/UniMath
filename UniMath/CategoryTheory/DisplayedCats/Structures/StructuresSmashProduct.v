(*****************************************************************

 Structures with smash products

 In this file, we define a general notion of structure that
 supports a smash product. If we have a pointed structure (if a
 set can be equipped with a structure, then we have a point, and
 structure preserving maps preserve the point), then we can define
 an equivalence relation on the product that identifies all points
 for which at least 1 coordinate is the point arising from the
 structure.

 For a structure to support smash products, the first requirement
 is that the quotient with the aforementioned equivalence relation
 can be equipped with a structure. In addition, we must be able to
 equip the booleans with the structure, because these will
 ultimately form the unit of the desired monoidal structure. This
 leads to the definition `hset_struct_with_smash`, and from that,
 we construct the smash product and the unit.

 However, this is not sufficient in general to construct the
 desired monoidal structure (a counterexample would be topological
 spaces with a base point), and thus we look at more conditions.
 The first additional requirement is that we must have function
 spaces (`hset_struct_with_smash_closed_pointed`). This condition
 says that we can equip the hom-sets with the structure. In
 addition, we also require that the currying and uncurrying are
 structure preserving maps. These conditions are necessary to prove
 that the anticipated monoidal structure is closed.

 This is actually still not enough to construct the desired
 monoidal structure. Our solution is inspired by Construction 4.19
 and Lemma 4.20 in https://arxiv.org/pdf/0710.0082.pdf.

 The idea is to strengthen the requirement further: informally, we
 could say that aforementioned adjunction must be properly
 enriched (note that formally stating this, would be circular,
 because such an enrichment would presuppose that we already
 constructed the desired monoidal category). The extra requirements
 state that the maps that witness the isomorphisms between the
 homsets of the aforementioned adjunction, are themselves structure
 preserving maps as well.

 Contents
 1. Equivalence relation of smash product
 2. Structures with smash products
 3. Accessors for structures with smash products
 4. Structures with pointed homs
 5. Accessors of structures with pointed homs
 6. Structures with an pointed hom-adjunction
 7. Accessores for structures with an pointed hom-adjunction
 8. Closed smash product structures

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.

Local Open Scope cat.

Section SmashProduct.
  Context (P : hset_cartesian_struct)
          (Pt : pointed_hset_struct P)
          {X Y : hSet}
          (PX : P X)
          (PY : P Y).

  Let Px : X := hset_struct_point Pt PX.
  Let Py : Y := hset_struct_point Pt PY.

  (**
   1. Equivalence relation of smash product
   *)
  Definition product_point_coordinate
             (xy : X × Y)
    : UU
    := (pr1 xy = Px) ⨿ (pr2 xy = Py).

  Definition smash_hrel
    : hrel (X × Y)
    := λ xy₁ xy₂,
       xy₁ = xy₂
       ∨
       (product_point_coordinate xy₁
        ×
        product_point_coordinate xy₂).

  Proposition iseqrel_smash_hrel
    : iseqrel smash_hrel.
  Proof.
    refine ((_ ,, _) ,, _).
    - intros x₁ x₂ x₃.
      use factor_through_squash.
      {
        use impred ; intro.
        apply propproperty.
      }
      intros p₁.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros p₂.
      apply hinhpr.
      induction p₁ as [ p₁ | p₁ ] ; induction p₂ as [ p₂ | p₂ ] ; cbn in *.
      + exact (inl (p₁ @ p₂)).
      + induction p₁.
        exact (inr p₂).
      + induction p₂.
        exact (inr p₁).
      + exact (inr (pr1 p₁ ,, pr2 p₂)).
    - intros xy.
      exact (hinhpr (inl (idpath _))).
    - intros xy₁ xy₂.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros p.
      apply hinhpr.
      induction p as [ p | p ] ; cbn in *.
      + exact (inl (!p)).
      + exact (inr (pr2 p ,, pr1 p)).
  Qed.

  Definition smash_eqrel
    : eqrel (X × Y).
  Proof.
    use make_eqrel.
    - exact smash_hrel.
    - exact iseqrel_smash_hrel.
  Defined.

  Definition map_from_smash
             {Z : hSet}
             (h : X → Y → Z)
             (hp₁ : ∏ (y₁ y₂ : Y), h Px y₁ = h Px y₂)
             (hp₂ : ∏ (x : X) (y : Y), h x Py = h Px y)
             (hp₃ : ∏ (x₁ x₂ : X), h x₁ Py = h x₂ Py)
    : setquot smash_eqrel → Z.
  Proof.
    use setquotuniv.
    - exact (λ xy, h (pr1 xy) (pr2 xy)).
    - abstract
        (intros xy₁ xy₂ ;
         use factor_through_squash ; [ apply setproperty | ] ;
         intro p ;
         induction p as [ p | p ] ; [ induction p ; apply idpath | ] ;
         induction p as [ p₁ p₂ ] ;
         induction xy₁ as [ x₁ y₁ ] ;
         induction xy₂ as [ x₂ y₂ ] ;
         induction p₁ as [ p₁ | p₁ ] ;
         induction p₂ as [ p₂ | p₂ ] ;
         cbn in * ;
         rewrite p₁, p₂ ;
         [ apply hp₁
         | refine (!_) ;
           apply hp₂
         | apply hp₂
         | apply hp₃ ]).
  Defined.

  Definition map_from_smash'
             {Z : UU}
             (HZ : isaset Z)
             (h : X → Y → Z)
             (hp₁ : ∏ (y₁ y₂ : Y), h Px y₁ = h Px y₂)
             (hp₂ : ∏ (x : X) (y : Y), h x Py = h Px y)
             (hp₃ : ∏ (x₁ x₂ : X), h x₁ Py = h x₂ Py)
    : setquot smash_eqrel → Z
    := @map_from_smash (make_hSet Z HZ) h hp₁ hp₂ hp₃.

  Definition map_from_smash_pt
             {Z : hSet}
             (PZ : P Z)
             (Pz := hset_struct_point Pt PZ)
             (h : X → Y → Z)
             (hp₁ : ∏ (y : Y), h Px y = Pz)
             (hp₂ : ∏ (x : X), h x Py = Pz)
    : setquot smash_eqrel → Z.
  Proof.
    use map_from_smash.
    - exact h.
    - abstract
        (intros y₁ y₂ ;
         rewrite !hp₁ ;
         apply idpath).
    - abstract
        (intros x y ;
         rewrite hp₁, hp₂ ;
         apply idpath).
    - abstract
        (intros x₁ x₂ ;
         rewrite !hp₂ ;
         apply idpath).
  Defined.
End SmashProduct.

(**
 2. Structures with smash products
 *)
Definition pointed_hset_struct_map_from_unit
           {P : hset_struct}
           (Pt : pointed_hset_struct P)
           {Y : hSet}
           (PY : P Y)
           (y : Y)
           (b : bool)
  : Y
  := if b then y else hset_struct_point Pt PY.

Definition pointed_hset_struct_unit_map
           {P : hset_struct}
           (Pt : pointed_hset_struct P)
           {X Y : hSet}
           (PY : P Y)
           (f : X → bool)
           (g : X → Y)
           (x : X)
  : Y
  := if f x then g x else hset_struct_point Pt PY.

Definition hset_struct_with_smash_data
           (P : hset_cartesian_struct)
           (Pt : pointed_hset_struct P)
  : UU
  := P boolset
     ×
     (∏ (X Y : hSet)
        (PX : P X)
        (PY : P Y),
       P (setquotinset (smash_eqrel P Pt PX PY))).

Definition hset_struct_with_smash_laws
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           (SP : hset_struct_with_smash_data P Pt)
  : UU
  := (hset_struct_point Pt (pr1 SP) = false)
     ×
     (∏ (X Y : hSet)
        (PX : P X)
        (PY : P Y),
      hset_struct_point Pt (pr2 SP X Y PX PY)
      =
      setquotpr _ (hset_struct_point Pt PX ,, hset_struct_point Pt PY))
     ×
     (∏ (Y : hSet)
        (PY : P Y)
        (y : Y),
      mor_hset_struct
        P
        (pr1 SP)
        PY
        (pointed_hset_struct_map_from_unit Pt PY y))
     ×
     (∏ (X Y : hSet)
        (PX : P X)
        (PY : P Y)
        (f : X → bool)
        (Pf : mor_hset_struct P PX (pr1 SP) f)
        (g : X → Y)
        (Pg : mor_hset_struct P PX PY g),
      mor_hset_struct
        P
        PX
        PY
        (pointed_hset_struct_unit_map Pt PY f g))
     ×
     ∏ (X Y : hSet)
       (PX : P X)
       (PY : P Y),
     (∏ (y : Y),
      mor_hset_struct
        P
        PX
        (pr2 SP X Y PX PY)
        (λ x, setquotpr (smash_eqrel P Pt PX PY) (x ,, y)))
     ×
     (∏ (x : X),
      mor_hset_struct
        P
        PY
        (pr2 SP X Y PX PY)
        (λ y, setquotpr (smash_eqrel P Pt PX PY) (x ,, y)))
      ×
      (mor_hset_struct
        P
        (hset_struct_prod P PX PY)
        (pr2 SP X Y PX PY)
        (setquotpr (smash_eqrel P Pt PX PY)))
      ×
      (∏ (Z : hSet)
         (PZ : P Z)
         (h : X → Y → Z)
         (Ph : mor_hset_struct
                 P
                 (hset_struct_prod P PX PY)
                 PZ
                 (λ xy, h (pr1 xy) (pr2 xy)))
         (hp₁ : ∏ (y₁ y₂ : Y),
                h (hset_struct_point Pt PX) y₁
                =
                h (hset_struct_point Pt PX) y₂)
         (hp₂ : ∏ (x : X) (y : Y),
                h x (hset_struct_point Pt PY)
                =
                h (hset_struct_point Pt PX) y)
         (hp₃ : ∏ (x₁ x₂ : X),
                h x₁ (hset_struct_point Pt PY)
                =
                h x₂ (hset_struct_point Pt PY)),
        mor_hset_struct
          P
          (pr2 SP X Y PX PY)
          PZ
          (map_from_smash P Pt PX PY h hp₁ hp₂ hp₃)).

Definition hset_struct_with_smash
           (P : hset_cartesian_struct)
           (Pt : pointed_hset_struct P)
  : UU
  := ∑ (SP : hset_struct_with_smash_data P Pt), hset_struct_with_smash_laws SP.

(**
 3. Accessors for structures with smash products
 *)
Definition make_hset_struct_with_smash
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           (SP : hset_struct_with_smash_data P Pt)
           (SPL : hset_struct_with_smash_laws SP)
  : hset_struct_with_smash P Pt
  := SP ,, SPL.

Definition hset_struct_with_smash_unit
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           (SP : hset_struct_with_smash P Pt)
  : P boolset
  := pr11 SP.

Definition hset_struct_with_smash_unit_ob
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           (SP : hset_struct_with_smash P Pt)
  : category_of_hset_struct P
  := _ ,, hset_struct_with_smash_unit SP.

Definition hset_struct_with_smash_setquot
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           (SP : hset_struct_with_smash P Pt)
           {X Y : hSet}
           (PX : P X)
           (PY : P Y)
  : P (setquotinset (smash_eqrel P Pt PX PY))
  := pr21 SP X Y PX PY.

Coercion hset_struct_with_smash_setquot : hset_struct_with_smash >-> Funclass.

Definition hset_struct_with_smash_setquot_ob
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           (SP : hset_struct_with_smash P Pt)
           (PX PY : category_of_hset_struct P)
  : category_of_hset_struct P
  := _ ,, SP _ _ (pr2 PX) (pr2 PY).

Proposition hset_struct_with_smash_point_unit
            {P : hset_cartesian_struct}
            {Pt : pointed_hset_struct P}
            (SP : hset_struct_with_smash P Pt)
  : hset_struct_point Pt (hset_struct_with_smash_unit SP) = false.
Proof.
  exact (pr12 SP).
Qed.

Proposition hset_struct_with_smash_point_smash
            {P : hset_cartesian_struct}
            {Pt : pointed_hset_struct P}
            (SP : hset_struct_with_smash P Pt)
            {X Y : hSet}
            (PX : P X)
            (PY : P Y)
  : hset_struct_point Pt (SP X Y PX PY)
    =
    setquotpr _ (hset_struct_point Pt PX ,, hset_struct_point Pt PY).
Proof.
  exact (pr122 SP X Y PX PY).
Qed.

Proposition hset_struct_with_smash_map_from_unit
            {P : hset_cartesian_struct}
            {Pt : pointed_hset_struct P}
            (SP : hset_struct_with_smash P Pt)
            {Y : hSet}
            (PY : P Y)
            (y : Y)
  : mor_hset_struct
      P
      (hset_struct_with_smash_unit SP)
      PY
      (pointed_hset_struct_map_from_unit Pt PY y).
Proof.
  exact (pr1 (pr222 SP) Y PY y).
Qed.

Proposition hset_struct_with_smash_map_bool
            {P : hset_cartesian_struct}
            {Pt : pointed_hset_struct P}
            (SP : hset_struct_with_smash P Pt)
            {X Y : hSet}
            {PX : P X}
            {PY : P Y}
            {f : X → bool}
            (Pf : mor_hset_struct
                    P
                    PX
                    (hset_struct_with_smash_unit SP)
                    f)
            {g : X → Y}
            (Pg : mor_hset_struct P PX PY g)
  : mor_hset_struct
      P
      PX
      PY
      (pointed_hset_struct_unit_map Pt PY f g).
Proof.
  exact (pr12 (pr222 SP) X Y PX PY f Pf g Pg).
Qed.

Proposition hset_struct_with_smash_setquotpr_l
            {P : hset_cartesian_struct}
            {Pt : pointed_hset_struct P}
            (SP : hset_struct_with_smash P Pt)
            {X Y : hSet}
            (PX : P X)
            (PY : P Y)
            (y : Y)
  : mor_hset_struct
      P
      PX
      (SP X Y PX PY)
      (λ x, setquotpr (smash_eqrel P Pt PX PY) (x ,, y)).
Proof.
  exact (pr1 (pr22 (pr222 SP) X Y PX PY) y).
Qed.

Proposition hset_struct_with_smash_setquotpr_r
            {P : hset_cartesian_struct}
            {Pt : pointed_hset_struct P}
            (SP : hset_struct_with_smash P Pt)
            {X Y : hSet}
            (PX : P X)
            (PY : P Y)
            (x : X)
  : mor_hset_struct
      P
      PY
      (SP X Y PX PY)
      (λ y, setquotpr (smash_eqrel P Pt PX PY) (x ,, y)).
Proof.
  exact (pr12 (pr22 (pr222 SP) X Y PX PY) x).
Qed.

Proposition hset_struct_with_smash_setquotpr
            {P : hset_cartesian_struct}
            {Pt : pointed_hset_struct P}
            (SP : hset_struct_with_smash P Pt)
            {X Y : hSet}
            (PX : P X)
            (PY : P Y)
  : mor_hset_struct
      P
      (hset_struct_prod P PX PY)
      (SP X Y PX PY)
      (setquotpr (smash_eqrel P Pt PX PY)).
Proof.
  exact (pr122 (pr22 (pr222 SP) X Y PX PY)).
Qed.

Proposition hset_struct_with_smash_map_from_smash
            {P : hset_cartesian_struct}
            {Pt : pointed_hset_struct P}
            (SP : hset_struct_with_smash P Pt)
            {X Y : hSet}
            (PX : P X)
            (PY : P Y)
            {Z : hSet}
            (PZ : P Z)
            (Pz := hset_struct_point Pt PZ)
            (h : X → Y → Z)
            (Ph : mor_hset_struct
                    P
                    (hset_struct_prod P PX PY)
                    PZ
                    (λ xy, h (pr1 xy) (pr2 xy)))
            (hp₁ : ∏ (y₁ y₂ : Y),
                   h (hset_struct_point Pt PX) y₁
                   =
                   h (hset_struct_point Pt PX) y₂)
            (hp₂ : ∏ (x : X) (y : Y),
                   h x (hset_struct_point Pt PY)
                   =
                   h (hset_struct_point Pt PX) y)
            (hp₃ : ∏ (x₁ x₂ : X),
                   h x₁ (hset_struct_point Pt PY)
                   =
                   h x₂ (hset_struct_point Pt PY))
  : mor_hset_struct
      P
      (SP X Y PX PY)
      PZ
      (map_from_smash P Pt PX PY h hp₁ hp₂ hp₃).
Proof.
  exact (pr222 (pr22 (pr222 SP) X Y PX PY) Z PZ h Ph hp₁ hp₂ hp₃).
Qed.

Proposition hset_struct_with_smash_map_from_smash'
            {P : hset_cartesian_struct}
            {Pt : pointed_hset_struct P}
            (SP : hset_struct_with_smash P Pt)
            {X Y : hSet}
            (PX : P X)
            (PY : P Y)
            {Z : UU}
            (HZ : isaset Z)
            (PZ : P (Z ,, HZ))
            (Pz := hset_struct_point Pt PZ)
            (h : X → Y → Z)
            (Ph : mor_hset_struct
                    P
                    (hset_struct_prod P PX PY)
                    PZ
                    (λ xy, h (pr1 xy) (pr2 xy)))
            (hp₁ : ∏ (y₁ y₂ : Y),
                   h (hset_struct_point Pt PX) y₁
                   =
                   h (hset_struct_point Pt PX) y₂)
            (hp₂ : ∏ (x : X) (y : Y),
                   h x (hset_struct_point Pt PY)
                   =
                   h (hset_struct_point Pt PX) y)
            (hp₃ : ∏ (x₁ x₂ : X),
                   h x₁ (hset_struct_point Pt PY)
                   =
                   h x₂ (hset_struct_point Pt PY))
  : mor_hset_struct
      P
      (SP X Y PX PY)
      PZ
      (map_from_smash' P Pt PX PY HZ h hp₁ hp₂ hp₃).
Proof.
  exact (pr222 (pr22 (pr222 SP) X Y PX PY) _ PZ h Ph hp₁ hp₂ hp₃).
Qed.

(**
 4. Structures with pointed homs
 *)
Definition hset_struct_with_smash_closed_data
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           (SP : hset_struct_with_smash P Pt)
  : UU
  := ∏ (X Y : hSet)
       (PX : P X)
       (PY : P Y),
    P (@homset (category_of_hset_struct P) (X ,, PX) (Y ,, PY)).

Definition hset_struct_with_smash_closed_pointed_laws
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           {SP : hset_struct_with_smash P Pt}
           (PC : hset_struct_with_smash_closed_data SP)
  : UU
  := ∏ (X Y : hSet)
       (PX : P X)
       (PY : P Y)
       (x : X),
     pr1 (hset_struct_point Pt (PC X Y PX PY)) x
     =
     hset_struct_point Pt PY.

Definition hset_struct_with_smash_closed_pointed
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           (SP : hset_struct_with_smash P Pt)
  : UU
  := ∑ (PC : hset_struct_with_smash_closed_data SP),
     hset_struct_with_smash_closed_pointed_laws PC.

(**
 5. Accessors of structures with pointed homs
 *)
Definition hset_struct_with_smash_closed_to_funspace
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           {SP : hset_struct_with_smash P Pt}
           (PC : hset_struct_with_smash_closed_pointed SP)
           (X Y : category_of_hset_struct P)
  : category_of_hset_struct P
  := _ ,, pr1 PC (pr1 X) (pr1 Y) (pr2 X) (pr2 Y).

Proposition hset_struct_with_smash_closed_funspace_point
            {P : hset_cartesian_struct}
            {Pt : pointed_hset_struct P}
            {SP : hset_struct_with_smash P Pt}
            (PC : hset_struct_with_smash_closed_pointed SP)
            {X Y : hSet}
            (PX : P X)
            (PY : P Y)
            (x : X)
  : pr1 (hset_struct_point Pt (pr1 PC X Y PX PY)) x
    =
    hset_struct_point Pt PY.
Proof.
  exact (pr2 PC X Y PX PY x).
Qed.

(**
 6. Structures with an pointed hom-adjunction
 *)
Definition hset_struct_smash_curry_fun
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           {SP : hset_struct_with_smash P Pt}
           (PC : hset_struct_with_smash_closed_pointed SP)
           {PX PY PZ : category_of_hset_struct P}
           (f : PX --> hset_struct_with_smash_closed_to_funspace PC PY PZ)
  : setquot (smash_hrel P Pt (pr2 PX) (pr2 PY)) → pr11 PZ.
Proof.
  use map_from_smash.
  - exact (λ x y, pr1 (pr1 f x) y).
  - abstract
      (intros y₁ y₂ ; cbn ;
       rewrite !(pointed_hset_struct_preserve_point Pt (pr2 f)) ;
       refine (pr2 PC _ _ _ _ _ @ !_) ;
       exact (pr2 PC _ _ _ _ _)).
  - abstract
      (intros x y ; cbn ;
       rewrite !(pointed_hset_struct_preserve_point Pt (pr2 f)) ;
       refine (_ @ !(pr2 PC _ _ _ _ _)) ;
       exact (pointed_hset_struct_preserve_point Pt (pr2 (pr1 f x)))).
  - abstract
      (intros x₁ x₂ ; cbn ;
       refine (pointed_hset_struct_preserve_point Pt (pr2 (pr1 f x₁)) @ !_) ;
       refine (pointed_hset_struct_preserve_point Pt (pr2 (pr1 f x₂)))).
Defined.

Definition hset_struct_smash_uncurry_fun
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           (SP : hset_struct_with_smash P Pt)
           {PX PY PZ : category_of_hset_struct P}
           (g : hset_struct_with_smash_setquot_ob SP PX PY --> PZ)
           (x : pr11 PX)
  : PY --> PZ.
Proof.
  simple refine (_ ,, _).
  - exact (λ y, pr1 g (setquotpr _ (x ,, y))).
  - abstract
      (use (hset_struct_comp P _ (pr2 g)) ;
       apply hset_struct_with_smash_setquotpr_r).
Defined.

Definition hset_struct_smash_eval_fun
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           {SP : hset_struct_with_smash P Pt}
           (PC : hset_struct_with_smash_closed_pointed SP)
           {X Y : hSet}
           (PX : P X)
           (PY : P Y)
  : setquot (smash_eqrel P Pt (pr1 PC X Y PX PY) PX) → Y.
Proof.
  exact (hset_struct_smash_curry_fun PC (identity _)).
Defined.

Definition hset_struct_with_smash_closed_adj_laws
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           {SP : hset_struct_with_smash P Pt}
           (PC : hset_struct_with_smash_closed_pointed SP)
  : UU
  := (∏ (PX PY PZ : category_of_hset_struct P)
        (f : PX --> hset_struct_with_smash_closed_to_funspace PC PY PZ),
      mor_hset_struct
        P
        (pr2 (hset_struct_with_smash_setquot_ob SP PX PY))
        (pr2 PZ)
        (hset_struct_smash_curry_fun PC f))
     ×
     (∏ (PX PY PZ : category_of_hset_struct P)
        (f : hset_struct_with_smash_setquot_ob SP PX PY --> PZ),
      mor_hset_struct
        P
        (pr2 PX)
        (pr1 PC _ _ (pr2 PY) (pr2 PZ))
        (hset_struct_smash_uncurry_fun SP f)).

Definition hset_struct_with_smash_closed_adj
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           (SP : hset_struct_with_smash P Pt)
  : UU
  := ∑ (PC : hset_struct_with_smash_closed_pointed SP),
     hset_struct_with_smash_closed_adj_laws PC.

(**
 7. Accessores for structures with an pointed hom-adjunction
 *)
#[reversible=no] Coercion hset_struct_with_smash_closed_to_point
         {P : hset_cartesian_struct}
         {Pt : pointed_hset_struct P}
         {SP : hset_struct_with_smash P Pt}
         (PC : hset_struct_with_smash_closed_adj SP)
  : hset_struct_with_smash_closed_pointed SP
  := pr1 PC.

Definition hset_struct_with_smash_closed_adj_to_hom
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           {SP : hset_struct_with_smash P Pt}
           (PC : hset_struct_with_smash_closed_adj SP)
           (X Y : hSet)
           (PX : P X)
           (PY : P Y)
  : P (@homset (category_of_hset_struct P) (X ,, PX) (Y ,, PY))
  := pr11 PC X Y PX PY.

Coercion hset_struct_with_smash_closed_adj_to_hom
  : hset_struct_with_smash_closed_adj >-> Funclass.

Definition hset_struct_smash_curry
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           {SP : hset_struct_with_smash P Pt}
           (PC : hset_struct_with_smash_closed_adj SP)
           {PX PY PZ : category_of_hset_struct P}
           (f : PX --> hset_struct_with_smash_closed_to_funspace PC PY PZ)
  : hset_struct_with_smash_setquot_ob SP PX PY --> PZ
  := hset_struct_smash_curry_fun (pr1 PC) f ,, pr12 PC PX PY PZ f.

Definition hset_struct_smash_uncurry
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           {SP : hset_struct_with_smash P Pt}
           (PC : hset_struct_with_smash_closed_adj SP)
           {PX PY PZ : category_of_hset_struct P}
           (g : hset_struct_with_smash_setquot_ob SP PX PY --> PZ)
  : PX --> hset_struct_with_smash_closed_to_funspace PC PY PZ
  := hset_struct_smash_uncurry_fun SP g ,, pr22 PC PX PY PZ g.

Definition hset_struct_with_smash_closed_smash_eval
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           {SP : hset_struct_with_smash P Pt}
           (PC : hset_struct_with_smash_closed_adj SP)
           (X Y : category_of_hset_struct P)
  : hset_struct_with_smash_setquot_ob
      SP
      (hset_struct_with_smash_closed_to_funspace PC X Y)
      X
    -->
    Y
  := hset_struct_smash_curry PC (identity _).

(**
 8. Closed smash product structures
 *)
Definition hset_struct_with_smash_closed_laws_enrich
           {P : hset_cartesian_struct}
           {Pt : pointed_hset_struct P}
           {SP : hset_struct_with_smash P Pt}
           (PC : hset_struct_with_smash_closed_adj SP)
  : UU
  := (∏ (PX PY PZ : category_of_hset_struct P),
      mor_hset_struct
        P
        (pr2 (hset_struct_with_smash_closed_to_funspace
                PC
                PX
                (hset_struct_with_smash_closed_to_funspace PC PZ PY)))
        (pr2 (hset_struct_with_smash_closed_to_funspace
                PC
                (hset_struct_with_smash_setquot_ob SP PX PZ)
                PY))
        (hset_struct_smash_curry PC))
     ×
     (∏ (PX PY PZ : category_of_hset_struct P),
      mor_hset_struct
        P
        (pr2 (hset_struct_with_smash_closed_to_funspace
                PC
                (hset_struct_with_smash_setquot_ob SP PX PZ)
                PY))
        (pr2 (hset_struct_with_smash_closed_to_funspace
                PC
                PX
                (hset_struct_with_smash_closed_to_funspace PC PZ PY)))
        (hset_struct_smash_uncurry PC)).

Definition hset_struct_with_smash_closed
  : UU
  := ∑ (P : hset_cartesian_struct)
       (Pt : pointed_hset_struct P)
       (SP : hset_struct_with_smash P Pt)
       (PC : hset_struct_with_smash_closed_adj SP),
     hset_struct_with_smash_closed_laws_enrich PC.

#[reversible=no] Coercion hset_struct_with_smash_closed_to_struct
         (PC : hset_struct_with_smash_closed)
  : hset_cartesian_struct
  := pr1 PC.

#[reversible=no] Coercion hset_struct_with_smash_closed_point
         (PC : hset_struct_with_smash_closed)
  : pointed_hset_struct PC
  := pr12 PC.

Definition hset_struct_with_smash_closed_unit
           (PC : hset_struct_with_smash_closed)
  : category_of_hset_struct PC
  := hset_struct_with_smash_unit_ob (pr122 PC).

Definition hset_struct_with_smash_closed_smash
           {PC : hset_struct_with_smash_closed}
           (PX PY : category_of_hset_struct PC)
  : category_of_hset_struct PC
  := hset_struct_with_smash_setquot_ob (pr122 PC) PX PY.

Notation "PX ∧* PY" := (hset_struct_with_smash_closed_smash PX PY)
                         (at level 30, right associativity) : cat.

Proposition hset_struct_with_smash_closed_point_unit
            (PC : hset_struct_with_smash_closed)
  : hset_struct_point PC (pr2 (hset_struct_with_smash_closed_unit PC)) = false.
Proof.
  exact (hset_struct_with_smash_point_unit (pr122 PC)).
Qed.

Proposition hset_struct_with_smash_closed_point_smash
            {PC : hset_struct_with_smash_closed}
            (PX PY : category_of_hset_struct PC)
  : hset_struct_point PC (pr2 (PX ∧* PY))
    =
    setquotpr _ (hset_struct_point PC (pr2 PX) ,, hset_struct_point PC (pr2 PY)).
Proof.
  exact (hset_struct_with_smash_point_smash (pr122 PC) (pr2 PX) (pr2 PY)).
Qed.

Definition hset_struct_with_smash_closed_map_bool
           {PC : hset_struct_with_smash_closed}
           {PX PY : category_of_hset_struct PC}
           (f : PX --> hset_struct_with_smash_closed_unit PC)
           (g : PX --> PY)
  : PX --> PY
  := _ ,, hset_struct_with_smash_map_bool (pr122 PC) (pr2 f) (pr2 g).

Definition hset_struct_with_smash_closed_setquotpr_l
           {PC : hset_struct_with_smash_closed}
           {PX PY : category_of_hset_struct PC}
           (y : pr11 PY)
  : PX --> PX ∧* PY
  := _ ,, hset_struct_with_smash_setquotpr_l (pr122 PC) _ _ y.

Definition hset_struct_with_smash_closed_setquotpr_r
           {PC : hset_struct_with_smash_closed}
           {PX PY : category_of_hset_struct PC}
           (x : pr11 PX)
  : PY --> PX ∧* PY
  := _ ,, hset_struct_with_smash_setquotpr_r (pr122 PC) _ _ x.

Definition hset_struct_with_smash_closed_setquotpr
           {PC : hset_struct_with_smash_closed}
           (PX PY : category_of_hset_struct PC)
  : hset_struct_prod_ob PX PY --> PX ∧* PY
  := _ ,, hset_struct_with_smash_setquotpr (pr122 PC) (pr2 PX) (pr2 PY).

Definition hset_struct_with_smash_closed_to_funspace_ob
           {PC : hset_struct_with_smash_closed}
           (PX PY : category_of_hset_struct PC)
  : category_of_hset_struct PC
  := hset_struct_with_smash_closed_to_funspace (pr1 (pr222 PC)) PX PY.

Notation "PX -->* PY" := (hset_struct_with_smash_closed_to_funspace_ob PX PY)
                           (at level 20, right associativity) : cat.

Proposition hset_struct_with_smash_closed_fun_point
            {PC : hset_struct_with_smash_closed}
            (PX PY : category_of_hset_struct PC)
            (x : pr11 PX)
  : pr1 (hset_struct_point PC (pr2 (PX -->* PY))) x
    =
    hset_struct_point PC (pr2 PY).
Proof.
  apply hset_struct_with_smash_closed_funspace_point.
Qed.

Definition hset_struct_smash_closed_curry
           {PC : hset_struct_with_smash_closed}
           {PX PY PZ : category_of_hset_struct PC}
           (f : PX --> PY -->* PZ)
  : (PX ∧* PY) --> PZ
  := hset_struct_smash_curry (pr1 (pr222 PC)) f.

Definition hset_struct_smash_closed_uncurry
           {PC : hset_struct_with_smash_closed}
           {PX PY PZ : category_of_hset_struct PC}
           (g : (PX ∧* PY) --> PZ)
  : PX --> PY -->* PZ
  := hset_struct_smash_uncurry (pr1 (pr222 PC)) g.

Definition hset_struct_with_smash_closed_eval
           {PC : hset_struct_with_smash_closed}
           (PX PY : category_of_hset_struct PC)
  : (PX -->* PY) ∧* PX --> PY
  := hset_struct_with_smash_closed_smash_eval (pr1 (pr222 PC)) PX PY.

Definition hset_struct_smash_enriched_curry
           {PC : hset_struct_with_smash_closed}
           (PX PY PZ : category_of_hset_struct PC)
  : (PX -->* PY -->* PZ) --> ((PX ∧* PY) -->* PZ)
  := _ ,, pr12 (pr222 PC) PX PZ PY.

Definition hset_struct_smash_enriched_uncurry
           {PC : hset_struct_with_smash_closed}
           (PX PY PZ : category_of_hset_struct PC)
  : ((PX ∧* PY) -->* PZ) --> (PX -->* PY -->* PZ)
  := _ ,, pr22 (pr222 PC) PX PZ PY.
