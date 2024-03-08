(*****************************************************************

 Limits and colimits of structures

 The category of structures might have additional structure. For
 example, it could be cartesian closed or it could have all
 limits. In this file, we give conditions that guarantee the
 existence of certain limits/colimits in the category of
 structures. We also provide conditions from which we can conclude
 that this category is cartesian closed (where the internal hom
 would be given by the set of morphisms). Besides that, we define
 pointed structures: structures together with a chosen point.

 Note that a in a pointed structures, the point does not have to
 be an arbitrary point. For example, groups would form a pointed
 structure, where we can select the identity element to be the
 point for each structure.

 Contents
 1. Cartesian closed structures
 2. Equalizers of structures
 3. Coequalizers
 4. Type indexed products
 5. Pointed structures
 6. Binary coproducts
 7. Set-indexed coproducts

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Binproducts.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.

Local Open Scope cat.

(**
 1. Cartesian closed structures
 *)
Definition struct_fun
           {P : hset_struct}
           {X Y : hSet}
           (PX : P X)
           (PY : P Y)
  : UU
  := ∑ (f : X → Y), mor_hset_struct P PX PY f.

Definition struct_fun_to_fun
           {P : hset_struct}
           {X Y : hSet}
           {PX : P X}
           {PY : P Y}
           (f : struct_fun PX PY)
  : X → Y
  := pr1 f.

Coercion struct_fun_to_fun : struct_fun >-> Funclass.

Definition struct_fun_hSet
           {P : hset_struct}
           {X Y : hSet}
           (PX : P X)
           (PY : P Y)
  : hSet.
Proof.
  use (make_hSet (struct_fun PX PY)).
  use isaset_total2.
  - apply funspace_isaset.
    apply setproperty.
  - intro.
    apply isasetaprop.
    apply isaprop_hset_struct_on_mor.
Defined.

Definition closed_under_fun_data
           (P : hset_struct)
  : UU
  := ∏ (X Y : hSet)
       (PX : P X)
       (PY : P Y),
    P (struct_fun_hSet PX PY).

Definition struct_contains_constant
           (P : hset_struct)
  : UU
  := ∏ (X Y : hSet)
       (PX : P X)
       (PY : P Y)
       (y : Y),
     mor_hset_struct P PX PY (λ x, y).

Definition hset_cartesian_closed_struct_data
  : UU
  := ∑ (P : hset_cartesian_struct)
       (constP : struct_contains_constant P),
     closed_under_fun_data P.

#[reversible=no] Coercion hset_cartesian_closed_struct_data_to_struct
         (P : hset_cartesian_closed_struct_data)
  : hset_cartesian_struct
  := pr1 P.

Proposition hset_struct_const
            (P : hset_cartesian_closed_struct_data)
            {X Y : hSet}
            (PX : P X)
            (PY : P Y)
            (y : Y)
  : mor_hset_struct P PX PY (λ x, y).
Proof.
  exact (pr12 P X Y PX PY y).
Qed.

Proposition hset_struct_pointwise
            (P : hset_cartesian_closed_struct_data)
            {X Y Z : hSet}
            {PX : P X}
            {PY : P Y}
            {PZ : P Z}
            (f : X × Z → Y)
            (Pf : mor_hset_struct P (hset_struct_prod P PX PZ) PY f)
            (z : Z)
  : mor_hset_struct P PX PY (λ x : X, f (x ,, z)).
Proof.
  exact (hset_struct_comp
           P
           (hset_struct_pair
              P
              (hset_struct_id P PX)
              (hset_struct_const P PX PZ z))
           Pf).
Qed.

Definition hset_struct_fun
           (P : hset_cartesian_closed_struct_data)
           {X Y : hSet}
           (PX : P X)
           (PY : P Y)
  : P (struct_fun_hSet PX PY)
  := pr22 P X Y PX PY.

Definition closed_under_fun_laws
           (P : hset_cartesian_closed_struct_data)
  : UU
  := (∏ (X Y : hSet)
        (PX : P X)
        (PY : P Y),
      mor_hset_struct
        P
        (hset_struct_prod P PX (hset_struct_fun P PX PY))
        PY
        (λ xf, pr12 xf (pr1 xf)))
     ×
     (∏ (X Y Z : hSet)
        (PX : P X)
        (PY : P Y)
        (PZ : P Z)
        (f : X × Z → Y)
        (Pf : mor_hset_struct P (hset_struct_prod P PX PZ) PY f),
      mor_hset_struct
        P
        PZ (hset_struct_fun P PX PY)
        (λ z, _ ,, hset_struct_pointwise P f Pf z)).

Definition hset_cartesian_closed_struct
  : UU
  := ∑ (P : hset_cartesian_closed_struct_data), closed_under_fun_laws P.

#[reversible=no] Coercion hset_cartesian_closed_struct_to_data
         (P : hset_cartesian_closed_struct)
  : hset_cartesian_closed_struct_data
  := pr1 P.

Section ClosedUnderFunLaws.
  Context (P : hset_cartesian_closed_struct).

  Proposition closed_under_fun_eval
              {X Y : hSet}
              (PX : P X)
              (PY : P Y)
    : mor_hset_struct
        P
        (hset_struct_prod P PX (hset_struct_fun P PX PY))
        PY
        (λ xf, pr12 xf (pr1 xf)).
  Proof.
    exact (pr12 P X Y PX PY).
  Qed.

  Proposition closed_under_fun_lam
              {X Y Z : hSet}
              {PX : P X}
              {PY : P Y}
              {PZ : P Z}
              (f : X × Z → Y)
              (Pf : mor_hset_struct P (hset_struct_prod P PX PZ) PY f)
    : mor_hset_struct
        P
        PZ (hset_struct_fun P PX PY)
        (λ z, _ ,, hset_struct_pointwise P f Pf z).
  Proof.
    exact (pr22 P X Y Z PX PY PZ f Pf).
  Qed.
End ClosedUnderFunLaws.

Definition Exponentials_struct
           (P : hset_cartesian_closed_struct)
  : Exponentials (BinProducts_category_of_hset_struct P).
Proof.
  intros PX.
  use left_adjoint_from_partial.
  - exact (λ PY, _ ,, hset_struct_fun P (pr2 PX) (pr2 PY)).
  - exact (λ PY, _ ,, closed_under_fun_eval P _ _).
  - refine (λ Y Z f, _).
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros g₁ g₂ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use eq_mor_hset_struct ; intro z ;
         use eq_mor_hset_struct ; intro x ;
         refine (!(eqtohomot (maponpaths pr1 (pr2 g₁)) (x ,, z)) @ _) ;
         exact (eqtohomot (maponpaths pr1 (pr2 g₂)) (x ,, z))).
    + simple refine (_ ,, _).
      * exact (_ ,, closed_under_fun_lam P (pr1 f) (pr2 f)).
      * abstract
          (use eq_mor_hset_struct ;
           intro x ; cbn ;
           apply idpath).
Defined.

(**
 2. Equalizers of structures
 *)
Definition hset_equalizer_struct_data
           (P : hset_struct)
  : UU
  := ∏ (X Y : hSet)
       (f g : X → Y)
       (PX : P X)
       (PY : P Y)
       (Pf : mor_hset_struct P PX PY f)
       (Pg : mor_hset_struct P PX PY g),
     P (∑ (x : X), hProp_to_hSet (eqset (f x) (g x)))%set.

Definition hset_struct_equalizer
           {P : hset_struct}
           (EP : hset_equalizer_struct_data P)
           {X Y : hSet}
           {f g : X → Y}
           {PX : P X}
           {PY : P Y}
           (Pf : mor_hset_struct P PX PY f)
           (Pg : mor_hset_struct P PX PY g)
  : P (∑ (x : X), hProp_to_hSet (eqset (f x) (g x)))%set
  := EP X Y f g PX PY Pf Pg.

Definition hset_struct_equalizer_ob
           {P : hset_struct}
           (EP : hset_equalizer_struct_data P)
           {X Y : hSet}
           {f g : X → Y}
           {PX : P X}
           {PY : P Y}
           (Pf : mor_hset_struct P PX PY f)
           (Pg : mor_hset_struct P PX PY g)
  : category_of_hset_struct P
  := _ ,, hset_struct_equalizer EP Pf Pg.

Definition hset_equalizer_struct_laws
           {P : hset_struct}
           (EP : hset_equalizer_struct_data P)
  : UU
  := (∏ (X Y : hSet)
        (f g : X → Y)
        (PX : P X)
        (PY : P Y)
        (Pf : mor_hset_struct P PX PY f)
        (Pg : mor_hset_struct P PX PY g),
      mor_hset_struct P (hset_struct_equalizer EP Pf Pg) PX pr1)
     ×
     (∏ (X Y : hSet)
        (f g : X → Y)
        (PX : P X)
        (PY : P Y)
        (Pf : mor_hset_struct P PX PY f)
        (Pg : mor_hset_struct P PX PY g)
        (W : hSet)
        (PW : P W)
        (h : W → X)
        (Ph : mor_hset_struct P PW PX h)
        (q : (λ w, f(h w)) = (λ w, g(h w))),
      mor_hset_struct
        P
        PW
        (hset_struct_equalizer EP Pf Pg)
        (λ w, h w ,, eqtohomot q w)).

Definition hset_equalizer_struct
           (P : hset_struct)
  : UU
  := ∑ (EP : hset_equalizer_struct_data P), hset_equalizer_struct_laws EP.

#[reversible=no] Coercion hset_equalizer_struct_to_data
         {P : hset_struct}
         (EP : hset_equalizer_struct P)
  : hset_equalizer_struct_data P
  := pr1 EP.

Section EqualizerLaws.
  Context {P : hset_struct}
          (EP : hset_equalizer_struct P).

  Proposition hset_equalizer_pr_struct
              {X Y : hSet}
              {f g : X → Y}
              {PX : P X}
              {PY : P Y}
              (Pf : mor_hset_struct P PX PY f)
              (Pg : mor_hset_struct P PX PY g)
    : mor_hset_struct P (hset_struct_equalizer EP Pf Pg) PX pr1.
  Proof.
    exact (pr12 EP X Y f g PX PY Pf Pg).
  Qed.

  Proposition hset_equalizer_arrow_struct
              {X Y : hSet}
              {f g : X → Y}
              {PX : P X}
              {PY : P Y}
              (Pf : mor_hset_struct P PX PY f)
              (Pg : mor_hset_struct P PX PY g)
              {W : hSet}
              (PW : P W)
              (h : W → X)
              (Ph : mor_hset_struct P PW PX h)
              (q : (λ w, f(h w)) = (λ w, g(h w)))
    : mor_hset_struct
        P
        PW
        (hset_struct_equalizer EP Pf Pg)
        (λ w, h w ,, eqtohomot q w).
  Proof.
    exact (pr22 EP X Y f g PX PY Pf Pg W PW h Ph q).
  Qed.
End EqualizerLaws.

Definition disp_Equalizers_hset_disp_struct
           {P : hset_struct}
           (EP : hset_equalizer_struct P)
  : disp_Equalizers
      (hset_struct_disp_cat P)
      Equalizers_in_HSET.
Proof.
  intros X Y f g PX PY Pf Pg.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (hset_struct_equalizer EP Pf Pg).
  - exact (hset_equalizer_pr_struct EP Pf Pg).
  - apply isaprop_hset_struct_on_mor.
  - intros W PW h Ph q qq.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply isasetaprop ; apply isaprop_hset_struct_on_mor | ] ;
         apply isaprop_hset_struct_on_mor).
    + simple refine (_ ,, _).
      * exact (hset_equalizer_arrow_struct EP Pf Pg PW h Ph q).
      * apply isaprop_hset_struct_on_mor.
Defined.

Definition Equalizers_category_of_hset_struct
           {P : hset_struct}
           (EP : hset_equalizer_struct P)
  : Equalizers (category_of_hset_struct P).
Proof.
  use total_Equalizers.
  - exact Equalizers_in_HSET.
  - exact (disp_Equalizers_hset_disp_struct EP).
Defined.

(**
 3. Coequalizers of structures
 *)
Definition hset_coequalizer_struct_data
           (P : hset_struct)
  : UU
  := ∏ (X Y : hSet)
       (f g : X → Y)
       (PX : P X)
       (PY : P Y)
       (Pf : mor_hset_struct P PX PY f)
       (Pg : mor_hset_struct P PX PY g),
     P (coequalizer_hSet f g).

Definition hset_struct_coequalizer
           {P : hset_struct}
           (EP : hset_coequalizer_struct_data P)
           {X Y : hSet}
           {f g : X → Y}
           {PX : P X}
           {PY : P Y}
           (Pf : mor_hset_struct P PX PY f)
           (Pg : mor_hset_struct P PX PY g)
  : P (coequalizer_hSet f g)
  := EP X Y f g PX PY Pf Pg.

Definition hset_coequalizer_struct_laws
           {P : hset_struct}
           (EP : hset_coequalizer_struct_data P)
  : UU
  := (∏ (X Y : hSet)
        (f g : X → Y)
        (PX : P X)
        (PY : P Y)
        (Pf : mor_hset_struct P PX PY f)
        (Pg : mor_hset_struct P PX PY g),
      mor_hset_struct P PY (hset_struct_coequalizer EP Pf Pg) (coequalizer_map_hSet f g))
     ×
     (∏ (X Y : hSet)
        (f g : X → Y)
        (PX : P X)
        (PY : P Y)
        (Pf : mor_hset_struct P PX PY f)
        (Pg : mor_hset_struct P PX PY g)
        (Z : hSet)
        (PZ : P Z)
        (h : Y → Z)
        (Ph : mor_hset_struct P PY PZ h)
        (q : (λ w, h(f w)) = (λ w, h(g w))),
      mor_hset_struct
        P
        (hset_struct_coequalizer EP Pf Pg)
        PZ
        (coequalizer_out_hSet f g h (eqtohomot q))).

Definition hset_coequalizer_struct
           (P : hset_struct)
  : UU
  := ∑ (EP : hset_coequalizer_struct_data P), hset_coequalizer_struct_laws EP.

#[reversible=no] Coercion hset_coequalizer_struct_to_data
         {P : hset_struct}
         (EP : hset_coequalizer_struct P)
  : hset_coequalizer_struct_data P
  := pr1 EP.

Section CoequalizerLaws.
  Context {P : hset_struct}
          (EP : hset_coequalizer_struct P).

  Proposition hset_coequalizer_map_struct
              {X Y : hSet}
              {f g : X → Y}
              {PX : P X}
              {PY : P Y}
              (Pf : mor_hset_struct P PX PY f)
              (Pg : mor_hset_struct P PX PY g)
    : mor_hset_struct
        P
        PY
        (hset_struct_coequalizer EP Pf Pg)
        (coequalizer_map_hSet f g).
  Proof.
    exact (pr12 EP X Y f g PX PY Pf Pg).
  Qed.

  Proposition hset_equalizer_out_struct
              {X Y : hSet}
              {f g : X → Y}
              {PX : P X}
              {PY : P Y}
              (Pf : mor_hset_struct P PX PY f)
              (Pg : mor_hset_struct P PX PY g)
              {Z : hSet}
              (PZ : P Z)
              (h : Y → Z)
              (Ph : mor_hset_struct P PY PZ h)
              (q : (λ w, h(f w)) = (λ w, h(g w)))
    : mor_hset_struct
        P
        (hset_struct_coequalizer EP Pf Pg)
        PZ
        (coequalizer_out_hSet f g h (eqtohomot q)).
  Proof.
    exact (pr22 EP X Y f g PX PY Pf Pg Z PZ h Ph q).
  Qed.
End CoequalizerLaws.

Definition disp_Coequalizers_hset_disp_struct
           {P : hset_struct}
           (EP : hset_coequalizer_struct P)
  : disp_Coequalizers
      (hset_struct_disp_cat P)
      Coequalizers_HSET.
Proof.
  intros X Y f g PX PY Pf Pg.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (hset_struct_coequalizer EP Pf Pg).
  - exact (hset_coequalizer_map_struct EP Pf Pg).
  - apply isaprop_hset_struct_on_mor.
  - intros W PW h Ph q qq.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply isasetaprop ; apply isaprop_hset_struct_on_mor | ] ;
         apply isaprop_hset_struct_on_mor).
    + simple refine (_ ,, _).
      * exact (hset_equalizer_out_struct EP Pf Pg PW h Ph q).
      * apply isaprop_hset_struct_on_mor.
Defined.

Definition Coequalizers_category_of_hset_struct
           {P : hset_struct}
           (EP : hset_coequalizer_struct P)
  : Coequalizers (category_of_hset_struct P).
Proof.
  use total_Coequalizers.
  - exact Coequalizers_HSET.
  - exact (disp_Coequalizers_hset_disp_struct EP).
Defined.

(**
 4. Type indexed products
 *)
Definition hset_struct_type_prod_data
           (P : hset_struct)
           (I : UU)
  : UU
  := ∏ (D : I → hSet)
       (PD : ∏ (i : I), P (D i)),
     P (forall_hSet D).

Definition hset_struct_type_prod_laws
           {P : hset_struct}
           {I : UU}
           (HP : hset_struct_type_prod_data P I)
  : UU
  := (∏ (D : I → hSet)
        (PD : ∏ (i : I), P (D i))
        (i : I),
      mor_hset_struct P (HP D PD) (PD i) (λ f, f i))
     ×
     (∏ (D : I → hSet)
        (PD : ∏ (i : I), P (D i))
        (W : hSet)
        (PW : P W)
        (fs : ∏ (i : I), W → D i)
        (Pfs : ∏ (i : I), mor_hset_struct P PW (PD i) (fs i)),
       mor_hset_struct P PW (HP D PD) (λ w i, fs i w)).

Definition hset_struct_type_prod
           (P : hset_struct)
           (I : UU)
  : UU
  := ∑ (P : hset_struct_type_prod_data P I), hset_struct_type_prod_laws P.

Definition hset_struct_type_prod_to_data
           {P : hset_struct}
           {I : UU}
           (HP : hset_struct_type_prod P I)
           {D : I → hSet}
           (PD : ∏ (i : I), P (D i))
  : P (forall_hSet D)
  := pr1 HP D PD.

Coercion hset_struct_type_prod_to_data : hset_struct_type_prod >-> Funclass.

Definition hset_struct_type_prod_ob
           {P : hset_struct}
           {I : UU}
           (EP : hset_struct_type_prod P I)
           (D : I → hSet)
           (PD : ∏ (i : I), P (D i))
  : category_of_hset_struct P
  := _ ,, EP D PD.

Section Projections.
  Context {P : hset_struct}
          {I : UU}
          (HP : hset_struct_type_prod P I).

  Proposition hset_struct_type_prod_pr
              {D : I → hSet}
              (PD : ∏ (i : I), P (D i))
              (i : I)
    : mor_hset_struct P (HP D PD) (PD i) (λ f, f i).
  Proof.
    exact (pr12 HP D PD i).
  Qed.

  Proposition hset_struct_type_prod_pair
              {D : I → hSet}
              (PD : ∏ (i : I), P (D i))
              (W : hSet)
              (PW : P W)
              (fs : ∏ (i : I), W → D i)
              (Pfs : ∏ (i : I), mor_hset_struct P PW (PD i) (fs i))
    : mor_hset_struct P PW (HP D PD) (λ w i, fs i w).
  Proof.
    exact (pr22 HP D PD W PW fs Pfs).
  Qed.
End Projections.

Definition dispProducts_hset_struct
           {P : hset_struct}
           {I : UU}
           (HP : hset_struct_type_prod P I)
  : disp_Products (hset_struct_disp_cat P) I (ProductsHSET I).
Proof.
  intros D DD.
  simple refine (_ ,, (_ ,, _)).
  - exact (HP D DD).
  - exact (hset_struct_type_prod_pr HP DD).
  - intros W PW fs Hf.
    use iscontraprop1.
    + abstract
        (use isaproptotal2 ;
         [ intro ;
           use impred ; intro ;
           apply hset_struct_disp_cat
         | ] ;
         intros ;
         apply isaprop_hset_struct_on_mor).
    + simple refine (_ ,, _).
      * exact (hset_struct_type_prod_pair HP _ _ _ _ Hf).
      * intro i.
        apply isaprop_hset_struct_on_mor.
Defined.

Definition Products_category_of_hset_struct_type_prod
           {P : hset_struct}
           {I : UU}
           (HP : hset_struct_type_prod P I)
  : Products I (category_of_hset_struct P).
Proof.
  use total_Products.
  - exact (ProductsHSET I).
  - exact (dispProducts_hset_struct HP).
Defined.

(**
 5. Pointed structures
 *)
Definition pointed_hset_struct_data
           (P : hset_struct)
  : UU
  := ∏ (X : hSet), P X → X.

Definition hset_struct_point
           {P : hset_struct}
           (Px : pointed_hset_struct_data P)
           {X : hSet}
           (PX : P X)
  : X
  := Px X PX.

Definition pointed_hset_struct_laws
           {P : hset_struct}
           (Pt : pointed_hset_struct_data P)
  : UU
  := (∏ (X Y : hSet)
        (PX : P X)
        (PY : P Y),
      mor_hset_struct P PX PY (λ _, hset_struct_point Pt PY))
     ×
     (∏ (X Y : hSet)
        (f : X → Y)
        (PX : P X)
        (PY : P Y)
        (Pf : mor_hset_struct P PX PY f),
      f (hset_struct_point Pt PX) = hset_struct_point Pt PY).

Definition pointed_hset_struct
           (P : hset_struct)
  : UU
  := ∑ (Pt : pointed_hset_struct_data P), pointed_hset_struct_laws Pt.

#[reversible=no] Coercion pointed_hset_struct_to_data
         {P : hset_struct}
         (Pt : pointed_hset_struct P)
  : pointed_hset_struct_data P
  := pr1 Pt.

Proposition pointed_hset_struct_const
            {P : hset_struct}
            (Pt : pointed_hset_struct P)
            {X Y : hSet}
            (PX : P X)
            (PY : P Y)
  : mor_hset_struct P PX PY (λ _, hset_struct_point Pt PY).
Proof.
  exact (pr12 Pt X Y PX PY).
Qed.

Proposition pointed_hset_struct_preserve_point
            {P : hset_struct}
            (Pt : pointed_hset_struct P)
            {X Y : hSet}
            {f : X → Y}
            {PX : P X}
            {PY : P Y}
            (Pf : mor_hset_struct P PX PY f)
  : f (hset_struct_point Pt PX) = hset_struct_point Pt PY.
Proof.
  exact (pr22 Pt X Y f PX PY Pf).
Qed.

Proposition transportf_hset_struct_point
            {P : hset_cartesian_struct}
            (Pt : pointed_hset_struct P)
            {X Y : hSet}
            (p : X ≃ Y)
            (PX : P X)
  : hset_struct_point
      Pt
      (transportf
         P
         (univalence_hSet p)
         PX)
    =
      p (hset_struct_point Pt PX).
Proof.
  exact (!(pointed_hset_struct_preserve_point
             Pt
             (transportf_struct_weq_on_weq P p PX))).
Qed.

(**
 6. Binary coproducts
 *)
Definition hset_binary_coprod_struct_data
           (P : hset_struct)
  : UU
  := ∏ (X Y : hSet)
       (PX : P X)
       (PY : P Y),
     P (BinCoproductObject (BinCoproductsHSET X Y)).

Definition hset_struct_binary_coprod
           {P : hset_struct}
           (EP : hset_binary_coprod_struct_data P)
           {X Y : hSet}
           (PX : P X)
           (PY : P Y)
  : P (BinCoproductObject (BinCoproductsHSET X Y))
  := EP X Y PX PY.

Definition hset_binary_coprod_struct_laws
           {P : hset_struct}
           (EP : hset_binary_coprod_struct_data P)
  : UU
  := (∏ (X Y : hSet)
        (PX : P X)
        (PY : P Y),
      mor_hset_struct P PX (hset_struct_binary_coprod EP PX PY) inl)
     ×
     (∏ (X Y : hSet)
        (PX : P X)
        (PY : P Y),
      mor_hset_struct P PY (hset_struct_binary_coprod EP PX PY) inr)
     ×
     (∏ (X Y Z : hSet)
        (PX : P X)
        (PY : P Y)
        (PZ : P Z)
        (f : X → Z)
        (g : Y → Z)
        (Pf : mor_hset_struct P PX PZ f)
        (Pg : mor_hset_struct P PY PZ g),
      mor_hset_struct P (hset_struct_binary_coprod EP PX PY) PZ (sumofmaps f g)).

Definition hset_binary_coprod_struct
           (P : hset_struct)
  : UU
  := ∑ (EP : hset_binary_coprod_struct_data P), hset_binary_coprod_struct_laws EP.

#[reversible=no] Coercion hset_binary_coprod_struct_to_data
         {P : hset_struct}
         (EP : hset_binary_coprod_struct P)
  : hset_binary_coprod_struct_data P
  := pr1 EP.

Section BinaryCoprodLaws.
  Context {P : hset_struct}
          (EP : hset_binary_coprod_struct P).

  Proposition hset_binary_coprod_struct_inl
              {X Y : hSet}
              (PX : P X)
              (PY : P Y)
    : mor_hset_struct P PX (hset_struct_binary_coprod EP PX PY) inl.
  Proof.
    exact (pr12 EP X Y PX PY).
  Qed.

  Proposition hset_binary_coprod_struct_inr
              {X Y : hSet}
              (PX : P X)
              (PY : P Y)
    : mor_hset_struct P PY (hset_struct_binary_coprod EP PX PY) inr.
  Proof.
    exact (pr122 EP X Y PX PY).
  Qed.

  Proposition hset_binary_coprod_struct_sumofmaps
              {X Y Z : hSet}
              {PX : P X}
              {PY : P Y}
              {PZ : P Z}
              {f : X → Z}
              {g : Y → Z}
              (Pf : mor_hset_struct P PX PZ f)
              (Pg : mor_hset_struct P PY PZ g)
    : mor_hset_struct P (hset_struct_binary_coprod EP PX PY) PZ (sumofmaps f g).
  Proof.
    exact (pr222 EP X Y Z PX PY PZ f g Pf Pg).
  Qed.
End BinaryCoprodLaws.

Definition disp_BinCoproducts_hset_disp_struct
           {P : hset_struct}
           (EP : hset_binary_coprod_struct P)
  : disp_BinCoproducts
      (hset_struct_disp_cat P)
      BinCoproductsHSET.
Proof.
  intros X Y PX PY.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (hset_struct_binary_coprod EP PX PY).
  - exact (hset_binary_coprod_struct_inl EP PX PY).
  - exact (hset_binary_coprod_struct_inr EP PX PY).
  - intros W PW f Pf g Pg.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ;
         [ intro ;
           apply isapropdirprod ;
           apply isasetaprop ;
           apply isaprop_hset_struct_on_mor
         | ] ;
         apply isaprop_hset_struct_on_mor).
    + simple refine (_ ,, _ ,, _).
      * exact (hset_binary_coprod_struct_sumofmaps EP Pf Pg).
      * apply isaprop_hset_struct_on_mor.
      * apply isaprop_hset_struct_on_mor.
Defined.

Definition BinCoproducts_category_of_hset_struct
           {P : hset_struct}
           (EP : hset_binary_coprod_struct P)
  : BinCoproducts (category_of_hset_struct P).
Proof.
  use total_BinCoproducts.
  - exact BinCoproductsHSET.
  - exact (disp_BinCoproducts_hset_disp_struct EP).
Defined.

(**
 7. Set-indexed coproducts
 *)
Definition hset_struct_set_coprod_data
           (P : hset_struct)
           (I : hSet)
  : UU
  := ∏ (D : I → hSet)
       (PD : ∏ (i : I), P (D i)),
     P (∑ (i : I), D i)%set.

Definition hset_struct_set_coprod_laws
           {P : hset_struct}
           {I : hSet}
           (HP : hset_struct_set_coprod_data P I)
  : UU
  := (∏ (D : I → hSet)
        (PD : ∏ (i : I), P (D i))
        (i : I),
      mor_hset_struct P (PD i) (HP D PD) (λ d, i ,, d))
     ×
     (∏ (D : I → hSet)
        (PD : ∏ (i : I), P (D i))
        (W : hSet)
        (PW : P W)
        (fs : ∏ (i : I), D i → W)
        (Pfs : ∏ (i : I), mor_hset_struct P (PD i) PW (fs i)),
      mor_hset_struct P (HP D PD) PW (λ id, fs (pr1 id) (pr2 id))).

Definition hset_struct_set_coprod
           (P : hset_struct)
           (I : hSet)
  : UU
  := ∑ (P : hset_struct_set_coprod_data P I), hset_struct_set_coprod_laws P.

Definition hset_struct_set_coprod_to_data
           {P : hset_struct}
           {I : hSet}
           (HP : hset_struct_set_coprod P I)
           {D : I → hSet}
           (PD : ∏ (i : I), P (D i))
  : P (∑ (i : I), D i)%set
  := pr1 HP D PD.

Coercion hset_struct_set_coprod_to_data : hset_struct_set_coprod >-> Funclass.

Definition hset_struct_set_coprod_ob
           {P : hset_struct}
           {I : hSet}
           (EP : hset_struct_set_coprod P I)
           (D : I → hSet)
           (PD : ∏ (i : I), P (D i))
  : category_of_hset_struct P
  := _ ,, EP D PD.

Section Projections.
  Context {P : hset_struct}
          {I : hSet}
          (HP : hset_struct_set_coprod P I).

  Proposition hset_struct_set_coprod_in
              {D : I → hSet}
              (PD : ∏ (i : I), P (D i))
              (i : I)
    : mor_hset_struct P (PD i) (HP D PD) (λ d, i ,, d).
  Proof.
    exact (pr12 HP D PD i).
  Qed.

  Proposition hset_struct_set_coprod_sum
              {D : I → hSet}
              (PD : ∏ (i : I), P (D i))
              {W : hSet}
              (PW : P W)
              {fs : ∏ (i : I), D i → W}
              (Pfs : ∏ (i : I), mor_hset_struct P (PD i) PW (fs i))
    : mor_hset_struct P (HP D PD) PW (λ id, fs (pr1 id) (pr2 id)).
  Proof.
    exact (pr22 HP D PD W PW fs Pfs).
  Qed.
End Projections.

Definition dispCoproducts_hset_struct
           {P : hset_struct}
           {I : hSet}
           (HP : hset_struct_set_coprod P I)
  : disp_Coproducts (hset_struct_disp_cat P) I (CoproductsHSET I (pr2 I)).
Proof.
  intros D DD.
  simple refine (_ ,, (_ ,, _)).
  - exact (HP D DD).
  - exact (hset_struct_set_coprod_in HP DD).
  - intros W PW fs Hf.
    use iscontraprop1.
    + abstract
        (use isaproptotal2 ;
         [ intro ;
           use impred ; intro ;
           apply hset_struct_disp_cat
         | ] ;
         intros ;
         apply isaprop_hset_struct_on_mor).
    + simple refine (_ ,, _).
      * exact (hset_struct_set_coprod_sum HP _ _ Hf).
      * intro i.
        apply isaprop_hset_struct_on_mor.
Defined.

Definition Coproducts_category_of_hset_struct_set_coprod
           {P : hset_struct}
           {I : hSet}
           (HP : hset_struct_set_coprod P I)
  : Coproducts I (category_of_hset_struct P).
Proof.
  use total_Coproducts.
  - exact (CoproductsHSET I (pr2 I)).
  - exact (dispCoproducts_hset_struct HP).
Defined.
