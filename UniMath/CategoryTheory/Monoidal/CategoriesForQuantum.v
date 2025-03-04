(***************************************************************************

 Monoidal categories for Quantum Theory

 This file is a sample of an attempt to formalize the book 
 Categories for Quantum Theory: An Introduction, by Chris Heunen 
 and James Vicary 2019. 

 Using the existing framework of Coq Unimath monoidal categories, we
 build upon it by introducing the definition of a superposition rule,
 linear functors, and biproducts, as seen in Heunen and Vicary from
 sections 2.2.2 and 2.2.3. 

 Contents
 1. Superposition Rules
 2. Biproducts


 ***************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Limits.Zero.

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



Definition pre_superpos_unit
           {C : category}
           (op : pre_superpos_oper C)
           (A B : C)
           : C⟦A, B⟧
:= pr1 (pr222 (op A B)).

Definition addition_notation
           {C : category}
           (op : pre_superpos_oper C)
           {A B : C}
           (f g : C⟦A, B⟧)
           : C⟦A, B⟧
:= (pr1 (op A B)) f g.


Notation "f +^{ op } g" := (addition_notation op f g) (at level 31).


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
:= ∏ (A B D : C), ∏ (f : A --> B), pre_superpos_unit op D B
= (pre_superpos_unit op D A) · f.


Definition units_compat_with_comp_2
           {C : category}
           (op : pre_superpos_oper C)
           : UU 
:= ∏ (A B D : C), ∏ (f : A --> B), pre_superpos_unit op A D 
= f · (pre_superpos_unit op B D).


Definition superpos_oper (C : category): UU :=
  ∑ (oper : pre_superpos_oper C), 
  (compatible_with_comp_1 oper)×(compatible_with_comp_2 oper)
  ×(units_compat_with_comp_1 oper)×(units_compat_with_comp_2 oper).


Definition oper_notation
           {C : category}
           (oper : superpos_oper C)
           (A B : C)
           : (C⟦A, B⟧ -> C⟦A, B⟧ -> C⟦A, B⟧)
:= pr1((pr1 oper) A B).

Notation "op^{ oper }_{ A , B }" := (oper_notation oper A B ).

Definition superpos_unit 
           {C : category}
           (oper : superpos_oper C)
           (A B : C)
           : A --> B 
:= pre_superpos_unit (pr1 oper) A B.

Notation "u^{ op }_{ A , B }" := (superpos_unit op A B ).


Definition superpos_compat_with_comp_1
           {C : category}
           (oper: superpos_oper C)
           (A B D : C)
           (g g' : C⟦B, D⟧)
           (f : C⟦A, B⟧)
           : f·(g +^{pr1 oper} g') = (f·g) +^{pr1 oper} (f·g')
      := ((pr12 oper)) A B D g g' f.


Definition superpos_compat_with_comp_2
           {C : category}
           (oper: superpos_oper C)
           (A B D : C)
           (f f' : C⟦A, B⟧)
           (g : C⟦B, D⟧)
           : ( f +^{pr1 oper} f')·g = (f·g) +^{pr1 oper} (f'·g)
      := ((pr122 oper)) A B D f f' g.


Definition super_units_compat_1
           {C : category}
           (oper: superpos_oper C)
           (A B D : C)
           (f : A --> B)
           : u^{oper}_{D , B} = u^{oper}_{D , A} · f
      := (pr1 (pr222 oper)) A B D f.


Definition super_units_compat_2
           {C : category}
           (oper: superpos_oper C)
           (A B D : C)
           (f : A --> B)
           : u^{oper}_{A , D} = f · u^{oper}_{B , D}
      := (pr2 (pr222 oper)) A B D f.


(* Lemma 2.15 *)

Lemma zero_super_unit_eq
      {C : category}
      {Z : Zero C}
      {op : superpos_oper C}
      (A B : C)
      : (ZeroArrow Z A B) = u^{op}_{A,B}.
Proof.
  set (q := u^{op}_{Z,B}).
  set (h := u^{op}_{A,Z}).
  assert (X : (u^{ op }_{ A, B} = h · q)).
  exact (super_units_compat_2 op A Z B h).
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
:= ∏ (A B: M), ∏ (f g : A --> B), #F((op^{opC}_{A,B} f g)) 
= (op^{opN}_{F(A),F(B)} (#F(f)) (#F(g))).

      



(**

2. Biproducts

*)




Definition biproduct_data
           (M : monoidal_cat)
           : UU 
:= ∏ ( A B : pr1 M), (pr1 M).


Definition injec_mor_1
           {M : monoidal_cat}
           (bipr : biproduct_data M)
           : UU 
:= ∏ (A B : pr1 M), (A --> (bipr A B)).

Definition injec_mor_2
           {M : monoidal_cat}
           (bipr : biproduct_data M)
           : UU 
:= ∏ (A B : pr1 M), (B --> (bipr A B)).

Definition proj_mor_1
           {M : monoidal_cat}
           (bipr : biproduct_data M)
           : UU 
:= ∏ (A B : pr1 M), ((bipr A B)--> A).

Definition proj_mor_2
           {M : monoidal_cat}
           (bipr : biproduct_data M)
           : UU 
:= ∏ (A B : pr1 M), ((bipr A B)--> B).

Definition satisfy_bipr_1 
           {M : monoidal_cat}
           (bipr : biproduct_data M)
           (inj : injec_mor_1 bipr)
           (proj : proj_mor_1 bipr)
           : UU 
:= ∏ ( A B : pr1 M), (inj A B)· (proj A B) = identity A.

Definition satisfy_bipr_2 
           {M : monoidal_cat}
           (bipr : biproduct_data M)
           (inj : injec_mor_2 bipr)
           (proj : proj_mor_2 bipr)
           : UU 
:= ∏ ( A B : pr1 M), (inj A B)· (proj A B) = identity B.


Definition satisfy_zero_12 
           {M : monoidal_cat}
           (Z : Zero (pr1 M))
           (bipr : biproduct_data M) 
           (inj : injec_mor_1 bipr)
           (proj : proj_mor_2 bipr)
           : UU 
:= ∏ ( A B : pr1 M), (inj A B)· (proj A B) = (ZeroArrow Z A B).

Definition satisfy_zero_21 
           {M : monoidal_cat}
           (Z : Zero (pr1 M))
           (bipr : biproduct_data M) 
           (inj : injec_mor_2 bipr)
           (proj : proj_mor_1 bipr)
           : UU 
:= ∏ ( A B : pr1 M), (inj A B)· (proj A B) = (ZeroArrow Z B A).

Definition satisfy_bipr_3
           {M : monoidal_cat}
           (Z : Zero (pr1 M))
           (opM : superpos_oper M)
           (bipr : biproduct_data M) 
           (inj1 : injec_mor_1 bipr)
           (proj1 : proj_mor_1 bipr)
           (inj2 : injec_mor_2 bipr)
           (proj2 : proj_mor_2 bipr)
           : UU 
:= ∏ ( A B : pr1 M), identity (bipr A B) = op^{opM}_{(bipr A B) , 
 (bipr A B)} ((proj1 A B) · (inj1 A B)) ((proj2 A B) · (inj2 A B)).


Definition bipr_rule 
           (M : monoidal_cat)
           (Z : Zero (pr1 M))
           (op : superpos_oper M)
           : UU 
:= ∑ (bipr : biproduct_data M) 
    (inj1 : injec_mor_1 bipr)
    (proj1 : proj_mor_1 bipr)
    (inj2 : injec_mor_2 bipr)
    (proj2 : proj_mor_2 bipr),
(satisfy_bipr_1 bipr inj1 proj1) × (satisfy_bipr_2 bipr inj2 proj2)×
(satisfy_zero_12 Z bipr inj1 proj2)×(satisfy_zero_21 Z bipr inj2 proj1)×
(satisfy_bipr_3 Z op bipr inj1 proj1 inj2 proj2).











