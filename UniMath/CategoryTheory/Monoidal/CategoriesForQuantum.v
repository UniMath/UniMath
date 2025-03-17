
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Limits.Zero.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
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
  : identity (bin_biproduct_object P)
    = (bin_biproduct_pr1 P · bin_biproduct_i1 P) +^{op} (bin_biproduct_pr2 P · bin_biproduct_i2 P).
Proof. 
  apply (BinProductArrowsEq _ _ _ P).
  - change (BinProductPr1 C P) with (bin_biproduct_pr1 P). 
    rewrite id_left.
    rewrite superpos_compat_with_comp_2.
    do 2 rewrite assoc'.
    rewrite (bin_biproduct_i1_pr1 P).
    rewrite id_right.
    rewrite bin_biproduct_i2_pr1.
    rewrite ZeroArrow_comp_right.
    rewrite (zero_super_unit_eq _ op).
    rewrite superpos_unit_zero.
    reflexivity.
  - change (BinProductPr2 C P) with (bin_biproduct_pr2 P).
    rewrite id_left.
    rewrite superpos_compat_with_comp_2.
    do 2 rewrite assoc'.
    rewrite bin_biproduct_i1_pr2.
    rewrite bin_biproduct_i2_pr2.
    rewrite ZeroArrow_comp_right.
    rewrite (zero_super_unit_eq _ op).
    rewrite superpos_commutes. 
    rewrite superpos_unit_zero.
    rewrite (id_right _).
    reflexivity.
Qed.
  
Section IsBinBiproduct'.

  Context {C : category}.
  Context {A B : C}.
  Context {P : bin_biproduct_data A B}.
  Context {Z : Zero C}.
  Context {op : superpos_oper C}.

  Context (H1 : bin_biproduct_i1 P · bin_biproduct_pr1 P = identity A).
  Context (H2 : bin_biproduct_i2 P · bin_biproduct_pr2 P = identity B).
  Context (Z1 : bin_biproduct_i1 P · bin_biproduct_pr2 P = ZeroArrow Z A B).
  Context (Z2 : bin_biproduct_i2 P · bin_biproduct_pr1 P = ZeroArrow Z B A).
  Context (A3 : identity P
                = (bin_biproduct_pr1 P · bin_biproduct_i1 P)
                  +^{op} (bin_biproduct_pr2 P · bin_biproduct_i2 P)).

  Section ProductUniversalProperty.

    Context (Q : C).
    Context (f : C ⟦ Q, A ⟧).
    Context (g : C ⟦ Q, B ⟧).

    Definition make_is_bin_biproduct'_product_arrow
      : C⟦Q, P⟧.
    Proof.
      exact ((f · (bin_biproduct_i1 P)) +^{op} (g · bin_biproduct_i2 P)).
    Defined.

    Lemma make_is_bin_biproduct'_product_arrow_commutes1
      : make_is_bin_biproduct'_product_arrow · bin_biproduct_pr1 P = f.
    Proof.
      unfold make_is_bin_biproduct'_product_arrow.
      rewrite superpos_compat_with_comp_2.
      do 2 rewrite assoc'.
      rewrite H1. 
      rewrite Z2.
      rewrite id_right.
      rewrite ZeroArrow_comp_right.
      rewrite (zero_super_unit_eq _ op).
      rewrite superpos_unit_zero. 
      reflexivity.
    Qed.

    Lemma make_is_bin_biproduct'_product_arrow_commutes2
      : make_is_bin_biproduct'_product_arrow · bin_biproduct_pr2 P = g.
    Proof.
      unfold make_is_bin_biproduct'_product_arrow.
      rewrite superpos_compat_with_comp_2.
      do 2 rewrite assoc'.
      rewrite H2. 
      rewrite Z1.
      rewrite id_right.
      rewrite ZeroArrow_comp_right.
      rewrite (zero_super_unit_eq _ op).
      rewrite superpos_commutes.
      rewrite superpos_unit_zero. 
      reflexivity.
    Qed.

    Lemma make_is_bin_biproduct'_product_arrow_commutes'
      (h': C⟦Q, P⟧)
      (H : h' · bin_biproduct_pr1 P = f × h' · bin_biproduct_pr2 P = g)
      : h' = make_is_bin_biproduct'_product_arrow.
    Proof.
      rewrite <- (id_right h').
      rewrite A3.
      rewrite superpos_compat_with_comp_1.
      do 2 rewrite assoc.
      unfold make_is_bin_biproduct'_product_arrow.
      rewrite <- (pr1 H).
      rewrite <- (pr2 H).
      reflexivity.
    Qed.

(* isn't this lemma below the same as the above?

    Lemma make_is_bin_biproduct'_product_arrow_unique
      (h': C⟦Q, P⟧)
      (H : h' · bin_biproduct_pr1 P = f × h' · bin_biproduct_pr2 P = g)
      : h' = make_is_bin_biproduct'_product_arrow.
    Proof.
      
    Qed.

*)

    Definition make_is_bin_biproduct'_product_property
      : ∃! (h: C⟦Q, P⟧), h · bin_biproduct_pr1 P = f × h · bin_biproduct_pr2 P = g.
    Proof.
      use unique_exists.
      - exact make_is_bin_biproduct'_product_arrow.
      - split.
        + exact make_is_bin_biproduct'_product_arrow_commutes1.
        + exact make_is_bin_biproduct'_product_arrow_commutes2.
      - abstract (
          intro y;
          apply isapropdirprod;
          apply homset_property
        ).
      - exact make_is_bin_biproduct'_product_arrow_commutes'.
    Defined.

  End ProductUniversalProperty.

  Section CoproductUniversalProperty.

    Context (Q : C).
    Context (f : C ⟦ A, Q ⟧).
    Context (g : C ⟦ B, Q ⟧).

    Definition make_is_bin_biproduct'_coproduct_arrow
      : C⟦P, Q⟧.
    Proof.
      exact ((bin_biproduct_pr1 P · f) +^{op} (bin_biproduct_pr2 P · g)).
    Defined.

    Lemma make_is_bin_biproduct'_coproduct_arrow_commutes1
      : bin_biproduct_i1 P · make_is_bin_biproduct'_coproduct_arrow = f.
    Proof.
      unfold make_is_bin_biproduct'_coproduct_arrow.
      rewrite superpos_compat_with_comp_1.
      do 2 rewrite assoc.
      rewrite H1. 
      rewrite Z1.
      rewrite id_left.
      rewrite ZeroArrow_comp_left.
      rewrite (zero_super_unit_eq _ op).
      rewrite superpos_unit_zero. 
      reflexivity.
    Qed.

    Lemma make_is_bin_biproduct'_coproduct_arrow_commutes2
      : bin_biproduct_i2 P · make_is_bin_biproduct'_coproduct_arrow = g.
    Proof.
      unfold make_is_bin_biproduct'_coproduct_arrow.
      rewrite superpos_compat_with_comp_1.
      do 2 rewrite assoc.
      rewrite H2. 
      rewrite Z2.
      rewrite id_left.
      rewrite ZeroArrow_comp_left.
      rewrite (zero_super_unit_eq _ op).
      rewrite superpos_commutes.
      rewrite superpos_unit_zero. 
      reflexivity.
    Qed.

    Lemma make_is_bin_biproduct'_coproduct_arrow_commutes'
      (h': C⟦P, Q⟧)
      (H : bin_biproduct_i1 P · h' = f × bin_biproduct_i2 P · h' = g)
      : h' = make_is_bin_biproduct'_coproduct_arrow.
    Proof.
      rewrite <- (id_left h').
      rewrite A3.
      rewrite superpos_compat_with_comp_2.
      do 2 rewrite assoc'.
      rewrite (pr1 H).
      rewrite (pr2 H).
      reflexivity.
    Qed.

    Definition make_is_bin_biproduct'_coproduct_property
      : ∃! (h: C⟦P, Q⟧), bin_biproduct_i1 P · h = f × bin_biproduct_i2 P · h = g.
    Proof.
      use unique_exists.
      - exact make_is_bin_biproduct'_coproduct_arrow.
      - split.
        + exact make_is_bin_biproduct'_coproduct_arrow_commutes1.
        + exact make_is_bin_biproduct'_coproduct_arrow_commutes2.
      - abstract (
          intro y;
          apply isapropdirprod;
          apply homset_property
        ).
      - exact make_is_bin_biproduct'_coproduct_arrow_commutes'.
    Defined.

  End CoproductUniversalProperty.

  Definition make_is_bin_biproduct'
    : is_bin_biproduct (Z := Z) P.
  Proof.
    use make_is_bin_biproduct.
    - exact make_is_bin_biproduct'_product_property.
    - exact make_is_bin_biproduct'_coproduct_property.
    - exact H1.
    - exact Z1.
    - exact Z2.
    - exact H2.
  Defined.

End IsBinBiproduct'.










