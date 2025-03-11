
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Limits.Zero.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinBiproducts.

Local Open Scope cat.




(**

1. Superposition rules

*)



Definition operation_data 
           {C : category}
           (A B : C) 
           : UU 
:= C⟦A, B⟧ -> C⟦A, B⟧ -> C⟦A, B⟧.

Definition super_commutes
           {C : category}
           {A B : C}
           (op : operation_data A B)
           : UU 
:= ∏ (f g : C⟦A, B⟧), op f g = op g f.

Definition super_is_assoc
           {C : category}
           {A B: C}
           (op : operation_data A B)
           : UU 
:= ∏ (f g h: C⟦A, B⟧), op (op f g) h = op f (op g h).

Definition super_unit
           {C : category}
           {A B: C}
           (op : operation_data A B)
           : UU 
:= ∑ (un : C⟦A, B⟧), ∏ (f : C⟦A, B⟧), op f un = f.

Definition pre_superpos_oper (C: category) : UU := 
  ∏ (A B : C), ∑ (op : operation_data A B),
  (super_commutes op)×(super_is_assoc op)×(super_unit op).

Definition addition_notation
           {C : category}
           {A B : C}
           (op : pre_superpos_oper C)
           (f g : C⟦A, B⟧)
           : C⟦A, B⟧
:= (pr1 (op A B)) f g.

Notation "f +^{ op } g" := (addition_notation op f g) (at level 31).

Definition superpos_unit
           {C : category}
           (op : pre_superpos_oper C)
           (A B : C)
           : C⟦A, B⟧
:= pr1 (pr222 (op A B)).

Notation "u^{ op }_{ A , B }" := (superpos_unit op A B ).

Definition compatible_with_comp_1
           {C : category}
           (op : pre_superpos_oper C)
           : UU 
:= ∏ (A B D : C), ∏ (g g' : C⟦B, D⟧), ∏ (f : C⟦A, B⟧),
f·(g +^{op} g') = (f·g) +^{op} (f·g').


Definition compatible_with_comp_2
           {C : category}
           (op : pre_superpos_oper C)
           : UU 

:= ∏ (A B D : C),∏ (f f' : C⟦A, B⟧),∏ (g : C⟦B, D⟧),
( f +^{op} f')·g = (f·g) +^{op} (f'·g).

Definition units_compat_with_comp_1
           {C : category}
           (op : pre_superpos_oper C)
           : UU 
:= ∏ (A B D : C), ∏ (f : A --> B), u^{op}_{D,B}
= (u^{op}_{D,A}) · f.


Definition units_compat_with_comp_2
           {C : category}
           (op : pre_superpos_oper C)
           : UU 
:= ∏ (A B D : C), ∏ (f : A --> B), u^{op}_{A,D} 
= f · (u^{op}_{B,D}).


Definition superpos_oper (C : category): UU :=
  ∑ (oper : pre_superpos_oper C), 
  (compatible_with_comp_1 oper)×(compatible_with_comp_2 oper)
  ×(units_compat_with_comp_1 oper)×(units_compat_with_comp_2 oper).

Coercion superpos_to_pre_superpos {C : category} (op : superpos_oper C) : pre_superpos_oper C := pr1 op.

(* Accessors for Axioms *)

Definition superpos_commutes
           {C : category}
           (op: superpos_oper C)
           (A B : C)
           (f  : C⟦A, B⟧)
           (g : C⟦A, B⟧)
           : f +^{op} g = g +^{op} f
        := (pr12 ((pr1 op) A B)) f g.

Definition superpos_unit_zero
           {C : category}
           (op: superpos_oper C)
           (A B : C)
           (f  : C⟦A, B⟧)
           : f +^{op} u^{op}_{A,B} = f
           := (pr2 (pr222 ((pr1 op) A B))) f.

Definition superpos_assoc
           {C : category}
           (op: superpos_oper C)
           (A B : C)
           (f g h : C⟦A, B⟧)
           : (f +^{op} g) +^{op} h = f +^{op} (g +^{op} h)
           := (pr122 ((pr1 op) A B)) f g h.


Definition superpos_compat_with_comp_1
           {C : category}
           (oper: superpos_oper C)
           (A B D : C)
           (g g' : C⟦B, D⟧)
           (f : C⟦A, B⟧)
           : f·(g +^{oper} g') = (f·g) +^{oper} (f·g')
      := ((pr12 oper)) A B D g g' f.

Definition superpos_compat_with_comp_2
           {C : category}
           (oper: superpos_oper C)
           (A B D : C)
           (f f' : C⟦A, B⟧)
           (g : C⟦B, D⟧)
           : ( f +^{oper} f')·g = (f·g) +^{oper} (f'·g)
      := ((pr122 oper)) A B D f f' g.

Definition superpos_units_compat_1
           {C : category}
           (oper: superpos_oper C)
           (A B D : C)
           (f : A --> B)
           : u^{oper}_{D , B} = u^{oper}_{D , A} · f
      := (pr1 (pr222 oper)) A B D f.

Definition superpos_units_compat_2
           {C : category}
           (oper: superpos_oper C)
           (A B D : C)
           (f : A --> B)
           : u^{oper}_{A , D} = f · u^{oper}_{B , D}
      := (pr2 (pr222 oper)) A B D f.


(* Lemma 2.15 *)

Lemma zero_super_unit_eq
      {C : category}
      (Z : Zero C)
      (op : superpos_oper C)
      (A B : C)
      : (ZeroArrow Z A B) = u^{op}_{A,B}.
Proof.
  set (q := u^{op}_{Z,B}).
  set (h := u^{op}_{A,Z}).
  assert (X : (u^{ op }_{ A, B} = h · q)).
  exact (superpos_units_compat_2 op A Z B h).
  symmetry.
  assert (X0 : (h · q = ZeroArrow Z A B)).
  exact (ZeroArrowEq C Z A B h q).
  rewrite X.
  exact X0.
Qed.


(* Definition 2.17 *)

Definition is_linear_func 
           {M : category}
           {N : category}
           {opC : superpos_oper M}
           {opN : superpos_oper N}
           (F : functor M N)
           : UU 
:= ∏ (A B: M), ∏ (f g : A --> B), #F((f +^{opC} g)) 
=  (#F(f)) +^{opN} (#F(g)).


(* Axiom 3 from Definition 2.18 in Heunen and Vicary *)

Lemma id_biproduct_superpos
  (C : category)
  (A B : C)
  (Z : Zero C)
  (P : bin_biproduct A B Z)
  (op : superpos_oper C)
  : identity (bin_biproduct_object P) = (((bin_biproduct_pr1 (pr1 P)) · (bin_biproduct_i1 (pr1 P))) 
  +^{op} ((bin_biproduct_pr2 (pr1 P)) · (bin_biproduct_i2 (pr1 P)))).

Proof.

  set (binprod := bin_biproduct_to_bin_product P).
  set (pro1 := bin_biproduct_pr1 (pr1 P)).
  set (pro2 := bin_biproduct_pr2 (pr1 P)).
  set (in1 := bin_biproduct_i1 (pr1 P)).
  set (in2 := bin_biproduct_i2 (pr1 P)).
  set (obP := (bin_biproduct_object P)).
  set (p1p2 := (BinProductArrow C binprod (BinProductPr1 C binprod) (BinProductPr2 C binprod))).

  assert (X0 : ((identity obP)  = (BinProductArrow C binprod ((identity obP) · (BinProductPr1 C binprod))
  ((identity obP) · (BinProductPr2 C binprod))))).
  exact (BinProductArrowEta C A B binprod obP (identity P)).
  rewrite id_left in X0.
  rewrite id_left in X0.
  assert (X1 : identity obP = p1p2).
  exact X0.

  set (sum := (pro1 · in1) +^{op} (pro2 · in2)).
  assert (H0 : (sum · (identity obP)) = sum).
  exact (id_right sum).
  rewrite X1 in H0.
  assert (H1 : (sum · p1p2 = BinProductArrow C binprod (sum ·(BinProductPr1 C binprod)) 
  (sum ·(BinProductPr2 C binprod)))).
  exact (precompWithBinProductArrow C binprod (BinProductPr1 C binprod) (BinProductPr2 C binprod) sum).
  set (c1 := (sum · BinProductPr1 C binprod)).
  assert (H2: c1 = (BinProductPr1 C binprod)).
  - set (Y0 := superpos_compat_with_comp_2 op obP obP A (pro1 · in1) (pro2 · in2) (BinProductPr1 C binprod)).
    assert (Y1 : (BinProductPr1 C binprod) = pro1).
    {
      unfold BinProductPr1. 
      unfold binprod.
      unfold bin_biproduct_pr1.
      reflexivity.
    }
    rewrite Y1 in Y0.
    unfold sum in c1.
    unfold c1.
    rewrite Y1.
    rewrite superpos_compat_with_comp_2.

    assert (A0 : pro1 · in1 · pro1 = pro1).
    assert (bb : in1 · pro1 = identity A).
    exact (bin_biproduct_i1_pr1 P). 
    rewrite assoc'.
    rewrite bb.
    exact (id_right (pro1)).

    assert (A1 : pro2 · in2 · pro1 = ZeroArrow Z P A).
    assert (bb1 : in2 · pro1 = ZeroArrow Z B A).
    exact (bin_biproduct_i2_pr1 P).
    rewrite assoc'.
    rewrite bb1.
    exact (ZeroArrow_comp_right C Z P B A pro2).

    assert (A2 : (pro1 +^{op} (ZeroArrow Z P A) = pro1 )).
    set (im1 := zero_super_unit_eq Z op P A).
    rewrite im1.
    exact (superpos_unit_zero op P A pro1). 

    rewrite A0.
    rewrite A1.
    exact A2.

  - set (c2 := (sum · BinProductPr2 C binprod)).
    assert (H3: c2 = (BinProductPr2 C binprod)).
    set (Y2 := superpos_compat_with_comp_2 op obP obP B (pro1 · in1) (pro2 · in2) (BinProductPr2 C binprod)).

    assert (Y3 : (BinProductPr2 C binprod) = pro2).
    {
      unfold BinProductPr2. 
      unfold binprod.
      unfold bin_biproduct_pr2.
      reflexivity.
    }
    rewrite Y3 in Y2.
    unfold sum in c2.
    unfold c2.
    rewrite Y3.
    rewrite superpos_compat_with_comp_2.

    assert (A3 : pro1 · in1 · pro2 = ZeroArrow Z P B).
    assert (bb2 : in1 · pro2 = ZeroArrow Z A B).
    exact (bin_biproduct_i1_pr2 P).
    rewrite assoc'.
    rewrite bb2.
    exact (ZeroArrow_comp_right C Z P A B pro1).

    assert (A4 : pro2 · in2 · pro2 = pro2).
    assert (bb3 : in2 · pro2 = identity B).
    exact (bin_biproduct_i2_pr2 P). 
    rewrite assoc'.
    rewrite bb3.
    exact (id_right pro2).

    assert (A5 : (ZeroArrow Z P B) +^{op} pro2 = pro2).
    set (im := zero_super_unit_eq Z op P B).
    rewrite im.
    assert (bb4 : u^{ op }_{ P, B} +^{ op} pro2 = pro2 +^{ op} u^{ op }_{ P, B}).
    exact (superpos_commutes op P B u^{ op }_{ P, B} pro2).
    rewrite bb4.
    exact (superpos_unit_zero op P B pro2).

    rewrite A3.
    rewrite A4.
    exact A5.

  unfold c2 in H3.
  rewrite H3 in H1.
  unfold c1 in H2.
  rewrite H2 in H1.

  assert (X4 : sum · p1p2 = p1p2).
  exact H1.
  rewrite <- X1 in X4.
  rewrite <- ( id_right sum).
  symmetry.
  exact X4.

Qed.

(* Proving that the structure given in 2.18 of Heunen and Vicary
indeed gives a biproduct *)

Lemma axiom3_converse
  (C : category)
  (A B P : C)
  (Z : Zero C)
  (op : superpos_oper C)
  (p1 : P --> A)
  (p2 : P --> B)
  (i1 : A --> P)
  (i2 : B --> P)
  (H1 : i1 · p1 = (identity A))
  (H2 : i2 · p2 = (identity B))
  (Z1 : i1 · p2 = (ZeroArrow Z A B))
  (Z2 : i2 · p1 = (ZeroArrow Z B A))
  (A3 : (identity P) = (p1 · i1) +^{op} (p2 · i2))
  : bin_biproduct A B Z.
Proof.

  assert (X0 : isBinProduct C A B P p1 p2).
  {
    unfold isBinProduct.
    intros a f g. 
    set (mor := (f · i1) +^{op} (g·i2)).
    assert (H0 : mor · p1 = f). 
    { 
      unfold mor.
      rewrite superpos_compat_with_comp_2.
      assert (T : f · i1 · p1 = f).
      rewrite assoc'. rewrite H1. exact (id_right f).
      assert (T1 : g · i2 · p1 = u^{op}_{a,A}).
      rewrite assoc'.
      rewrite Z2.
      rewrite (zero_super_unit_eq Z op B A).
      symmetry.
      rewrite (superpos_units_compat_2 op a B A g).
      reflexivity.
      rewrite T. rewrite T1. rewrite superpos_unit_zero.
      reflexivity.
    }
    assert (Y1 : mor · p2 = g).
    {
      unfold mor.
      rewrite superpos_compat_with_comp_2.
      assert (T : g · i2 · p2 = g).
      rewrite assoc'.
      rewrite H2.
      exact (id_right g).
      assert (T1 : f · i1 · p2 = u^{op}_{a,B}).
      rewrite assoc'.
      rewrite Z1.
      rewrite (zero_super_unit_eq Z op A B).
      symmetry.
      rewrite (superpos_units_compat_2 op a A B f).
      reflexivity.
      rewrite T. rewrite T1. rewrite superpos_commutes. rewrite superpos_unit_zero.
      reflexivity.
    }
    use tpair. 
    exact (mor ,, H0 ,, Y1).
    intro cntr.
    apply subtypePath.
    intros x. 
    apply isapropdirprod; apply C. 

    set (q_mor := pr1 cntr). 
    assert (X4 : q_mor · (p1 · i1) +^{op} (p2 · i2) = (f · i1) +^{op} (g · i2)).
    rewrite superpos_compat_with_comp_1.
    assert (X5 : q_mor · (p1 · i1) = f · i1).
    rewrite assoc.
    unfold q_mor.
    rewrite (pr12 cntr).
    reflexivity.
    assert (X6 : q_mor · (p2 · i2) = g · i2).
    rewrite assoc.
    unfold q_mor.
    rewrite (pr22 cntr).
    reflexivity.
    rewrite X5. rewrite X6.
    reflexivity.
    rewrite <- A3 in X4. rewrite id_right in X4.
    simpl. exact X4.
  }
  assert (X1 : isBinCoproduct C A B P i1 i2).
  {
    unfold isBinCoproduct.
    intros c f g.
    set (mor := (p1 · f) +^{op} (p2 · g)).
    assert (H0 : i1 · mor = f).
    {
      unfold mor.
      rewrite superpos_compat_with_comp_1.
      assert (Y0 : (i1 · (p1 · f)) = f).
      rewrite assoc. rewrite H1.
      exact (id_left f).
      assert (Y1 : (i1 · (p2 · g)) = u^{op}_{A,c}).
      rewrite assoc. rewrite Z1.
      assert (Y11 : ZeroArrow Z A B = u^{op}_{A,B}).
      exact (zero_super_unit_eq Z op A B).
      rewrite Y11.
      symmetry.
      exact (superpos_units_compat_1 op B c A g).
      rewrite Y0. rewrite Y1.
      exact (superpos_unit_zero op A c f).
    }
    assert (K1 : i2 · mor = g).
    {
      unfold mor.
      rewrite superpos_compat_with_comp_1.
      assert (Y0 : (i2 · (p2 · g)) = g).
      rewrite assoc.
      rewrite H2.
      exact (id_left g).
      assert (Y1 : (i2 · (p1 · f)) = u^{op}_{B,c}).
      rewrite assoc.
      rewrite Z2.
      assert (Y11 : ZeroArrow Z B A = u^{op}_{B,A}).
      exact (zero_super_unit_eq Z op B A).
      rewrite Y11.
      symmetry.
      exact (superpos_units_compat_1 op A c B f).
      rewrite Y0. 
      rewrite Y1.
      rewrite superpos_commutes.
      exact (superpos_unit_zero op B c g).
    }
    use tpair.
    exact (mor ,, H0 ,, K1).
    intro cntr.
    apply subtypePath.
    intros x. 
    apply isapropdirprod; apply C. 


    set (h := pr1 cntr).
    assert (Y2 : ((p1 · i1) +^{ op} (p2 · i2)) · h = h).
    rewrite <- A3.
    exact (id_left h).
    rewrite superpos_compat_with_comp_2 in Y2.

    assert (B1 : (p1 · i1 · h) = p1 · f).
    unfold h. rewrite assoc'. rewrite (pr12 cntr).
    reflexivity.
    assert (B2 : (p2 · i2 · h) = p2 · g).
    unfold h. rewrite assoc'. rewrite (pr22 cntr).
    reflexivity.
    rewrite B1 in Y2. rewrite B2 in Y2.
    symmetry. exact Y2.
  }
  set (is_bipr := make_is_bin_biproduct (P ,, (p1 ,, p2 ,, i1 ,, i2)) X0 X1 H1 Z1 Z2 H2).
  exact (make_bin_biproduct (P,, p1,, p2,, i1,, i2) is_bipr).

Qed.










