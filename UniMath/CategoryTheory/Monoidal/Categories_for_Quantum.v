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
Require Import UniMath.CategoryTheory.All.

Local Open Scope cat.




(**

1. Superposition rules

*)



Definition operation_data 
           {C : monoidal_cat}
           (A B : pr1 C) 
: UU 
:= C⟦A, B⟧ -> C⟦A, B⟧ -> C⟦A, B⟧.



Definition super_commutes
           {C : monoidal_cat}
           {A B : pr1 C}
           (op : operation_data A B)
: UU 
:= ∏ (f g : C⟦A, B⟧), op f g = op g f.



Definition super_is_assoc
           {C : monoidal_cat}
           {A B: pr1 C}
           (op : operation_data A B)
: UU 
:= ∏ (f g h: C⟦A, B⟧), op (op f g) h = op f (op g h).


Definition super_unit
           {C : monoidal_cat}
           {A B: pr1 C}
           (op : operation_data A B)
: UU 
:= ∑ (un : C⟦A, B⟧), ∏ (f : C⟦A, B⟧), op f un = f.



Definition pre_superpos_oper (M: monoidal_cat) : UU := 
  ∏ (A B : pr1 M), ∑ (op : operation_data A B),
  (super_commutes op)×(super_is_assoc op)×(super_unit op).


Definition compatible_with_comp_1
           {M : monoidal_cat}
           (op : pre_superpos_oper M)
: UU 
:= ∏ (A B D : pr1 M), ∏ (g g' : M⟦B, D⟧), ∏ (f : M⟦A, B⟧),

f·((pr1 (op B D)) g g') = (pr1 (op A D)) (f·g) (f·g').


Definition compatible_with_comp_2
           {M : monoidal_cat}
           (op : pre_superpos_oper M)
: UU 

:= ∏ (A B D : pr1 M),∏ (f f' : M⟦A, B⟧),∏ (g : M⟦B, D⟧),

((pr1 (op A B)) f f')·g = (pr1 (op A D)) (f·g) (f'·g).

Definition units_compat_with_comp_1
           {M : monoidal_cat}
           (op : pre_superpos_oper M)
: UU 
:= ∏ (A B C : pr1 M), ∏ (f : A --> B), pr1 (pr2 (pr2 (pr2 (op C B)))) 
= (pr1 (pr2 (pr2 (pr2 (op C A))))) · f.


Definition units_compat_with_comp_2
           {M : monoidal_cat}
           (op : pre_superpos_oper M)
: UU 
:= ∏ (A B D : pr1 M), ∏ (f : A --> B), pr1 (pr2 (pr2 (pr2 (op A D)))) 
= f · (pr1 (pr2 (pr2 (pr2 (op B D))))).




Definition superpos_rule (M : monoidal_cat): UU :=
  ∑ (oper : pre_superpos_oper M), 
  (compatible_with_comp_1 oper)×(compatible_with_comp_2 oper)
  ×(units_compat_with_comp_1 oper)×(units_compat_with_comp_2 oper).

Definition oper_notation
           {M : monoidal_cat}
           (oper : superpos_rule M)
           (A B : pr1 M)
: (M⟦A, B⟧ -> M⟦A, B⟧ -> M⟦A, B⟧)
:= pr1((pr1 oper) A B).

Notation "op^{ oper }_{ A , B }" := (oper_notation oper A B ).

Definition super_pos_unit 
           {M : monoidal_cat}
           (op : superpos_rule M)
           (A B : pr1 M)
: A --> B 
:= pr1 (pr2 (pr2 (pr2((pr1 op) A B)))).

Notation "u^{ op }_{ A , B }" := (super_pos_unit op A B ).


(* Lemma 2.15 *)

Lemma zero_super_unit_eq
      {M : monoidal_cat}
      {Z : Zero (pr1 M)}
      {op : superpos_rule M}
      (A B : pr1 M)
: (ZeroArrow Z A B) = u^{op}_{A,B}.
Proof.
  set (q := u^{op}_{Z,B}).
  set (h := u^{op}_{A,Z}).
  assert (X : (u^{ op }_{ A, B} = h · q)).
  exact (((pr2 (pr2 (pr2 (pr2 op)))) A Z B) h).
  symmetry.
  assert (X0 : (h · q = ZeroArrow Z A B)).
  exact (ZeroArrowEq (pr1 M) Z A B h q).
  rewrite X.
  exact X0.
Defined.


(* Definition 2.17 *)

Definition is_linear_func 
           {M : monoidal_cat}
           {N : monoidal_cat}
           {opC : superpos_rule M}
           {opN : superpos_rule N}
           (F : functor (pr1 M) (pr1 N))
: UU 
:= ∏ (A B: pr1 M), ∏ (f g : A --> B), #F((op^{opC}_{A,B} f g)) 
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

Definition satisf_bipr_1 
           {M : monoidal_cat}
           (bipr : biproduct_data M)
           (inj : injec_mor_1 bipr)
           (proj : proj_mor_1 bipr)
: UU 
:= ∏ ( A B : pr1 M), (inj A B)· (proj A B) = id A.

Definition satisf_bipr_2 
           {M : monoidal_cat}
           (bipr : biproduct_data M)
           (inj : injec_mor_2 bipr)
           (proj : proj_mor_2 bipr)
: UU 
:= ∏ ( A B : pr1 M), (inj A B)· (proj A B) = id B.


Definition satisf_zero_12 
           {M : monoidal_cat}
           (Z : Zero (pr1 M))
           (bipr : biproduct_data M) 
           (inj : injec_mor_1 bipr)
           (proj : proj_mor_2 bipr)
: UU 
:= ∏ ( A B : pr1 M), (inj A B)· (proj A B) = (ZeroArrow Z A B).

Definition satisf_zero_21 
           {M : monoidal_cat}
           (Z : Zero (pr1 M))
           (bipr : biproduct_data M) 
           (inj : injec_mor_2 bipr)
           (proj : proj_mor_1 bipr)
: UU 
:= ∏ ( A B : pr1 M), (inj A B)· (proj A B) = (ZeroArrow Z B A).

Definition satisf_bipr_3
           {M : monoidal_cat}
           (Z : Zero (pr1 M))
           (opM : superpos_rule M)
           (bipr : biproduct_data M) 
           (inj1 : injec_mor_1 bipr)
           (proj1 : proj_mor_1 bipr)
           (inj2 : injec_mor_2 bipr)
           (proj2 : proj_mor_2 bipr)
: UU 
:= ∏ ( A B : pr1 M), id (bipr A B) = op^{opM}_{(bipr A B) , 
 (bipr A B)} ((proj1 A B) · (inj1 A B)) ((proj2 A B) · (inj2 A B)).


Definition bipr_rule 
           (M : monoidal_cat)
           (Z : Zero (pr1 M))
           (op : superpos_rule M)
: UU 
:= ∑ (bipr : biproduct_data M) 
    (inj1 : injec_mor_1 bipr)
    (proj1 : proj_mor_1 bipr)
    (inj2 : injec_mor_2 bipr)
    (proj2 : proj_mor_2 bipr),

(satisf_bipr_1 bipr inj1 proj1) × (satisf_bipr_2 bipr inj2 proj2)×
(satisf_zero_12 Z bipr inj1 proj2)×(satisf_zero_21 Z bipr inj2 proj1)×
(satisf_bipr_3 Z op bipr inj1 proj1 inj2 proj2).
















