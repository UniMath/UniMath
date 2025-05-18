(***************************************************************************

 Dagger Monoidal Categories

 In this file we introduce the dagger structure to monoidal categories. Then,
 we delve into its interaction with biproducts, we define kernels, and finally
 define part of the quantum computing notation from Heunen and Vicary. 
 This file is part of a larger project to formalize parts of the book 
 Categories for Quantum Theory: An Introduction (Heunen and Vicary 2019).

 Note that in the section Quantum Notation a different definition is used for 
 Born rule than that provided in Heunen and Vicary.

 Contents
 
 1. Dagger Monoidal Categories
 2. Dagger Biproducts
 3. Kernels
 4. Quantum Notation
 ***************************************************************************)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.Limits.Zero.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesForQuantum.
Require Import UniMath.CategoryTheory.Limits.BinBiproducts.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Notation "{ f }_ C ^†" := (dagger_category_to_dagger C _ _ f).

Section DaggerMonoidal.

  Definition is_unitary_cat
    (C : dagger_category)
    : UU 
    := ∏ (A B : C)(f : A --> B), (is_unitary C f).

  Definition pre_dag_monoid_cat : UU
    := ∑ (C : dagger_category), monoidal C.

  Definition pre_dag_monoid_cat_to_monoidal
    (C : pre_dag_monoid_cat)
    : monoidal_cat
    := (pr11 C ,, pr2 C).
  
  Coercion pre_dag_mon_to_mon (C : pre_dag_monoid_cat) : monoidal_cat := pre_dag_monoid_cat_to_monoidal C.

  Definition pre_dag_monoid_cat_to_dag
    (C : pre_dag_monoid_cat)
    : dagger_category
    := pr1 C.
  
  Coercion pre_dag_mon_to_dag (C : pre_dag_monoid_cat) : dagger_category := pre_dag_monoid_cat_to_dag C.
    
  Definition interact_monoidal
    (C : pre_dag_monoid_cat)
    : UU 
    := ∏ (A B A1 B1 : C)(f : A --> B)(g : A1 --> B1), { (f #⊗ g) }_ C ^†  = { f }_ C ^† #⊗ { g }_ C ^†.

  Definition monoidal_dag_cat_laws
    (C : pre_dag_monoid_cat)
    : UU
    := (interact_monoidal C) × (is_unitary_cat C).

  Definition monoidal_dagger_category : UU
    := ∑ (C : pre_dag_monoid_cat), monoidal_dag_cat_laws C.

  Definition monoidal_dagger_cat_to_pre_dag_mon_cat
    (C : monoidal_dagger_category)
    : pre_dag_monoid_cat
    := pr1 C.

  Coercion mon_dag_cat_to_pre_dag_mon_cat (C : monoidal_dagger_category): pre_dag_monoid_cat := monoidal_dagger_cat_to_pre_dag_mon_cat C.

  End DaggerMonoidal.
  
  Section DaggerBiproducts.

  Definition dag_bipr_ax1
    {C : dagger_category}
    (Z : Zero C)
    {A B : C}
    (P : bin_biproduct A B Z)
    : UU 
    := {bin_biproduct_i1 P}_ C ^† = bin_biproduct_pr1 P.

  Definition dag_bipr_ax2
    {C : dagger_category}
    (Z : Zero C)
    {A B : C}
    (P : bin_biproduct A B Z)
    : UU 
    := {bin_biproduct_i2 P}_ C ^† = bin_biproduct_pr2 P.

  Definition dagger_biproduct
    {C : dagger_category}
    (Z : Zero C)
    (A B : C)
    : UU
    := ∑ (P : bin_biproduct A B Z), (dag_bipr_ax1 Z P) × (dag_bipr_ax2 Z P).

  (* accessors for this object *)

  Definition dag_bipr_str
    (C : dagger_category)
    (Z : Zero C)
    : UU 
    := ∏ (A B : C), dagger_biproduct Z A B.

  Definition dag_bipr
    {C : dagger_category}
    (Z : Zero C)
    (A B : C)
    {D : dag_bipr_str C Z}
    : C
    := pr1 ((D A) B).

  End DaggerBiproducts.

  Section Kernels.
  
  Definition is_isometry
    {C : dagger_category}
    {A B : C}
    (f : A --> B)
    : UU
    := f · { f }_ C ^† = identity A.

  Definition is_dagger_kernel
    {C : dagger_category}
    (Z : Zero C)
    {A B K : C}
    (k : K --> A)
    (k1 : is_isometry k)
    (f : A --> B)
    : UU 
    := (k · f = ZeroArrow Z K B) × (∏ (X : C)(x : X --> A)(x1 : (x · f = ZeroArrow Z X B)), 
     ∑ (m : X --> K), m · k = x).

  Definition dagger_kernel
    {C : dagger_category}
    (Z : Zero C)
    {A B : C}
    (f : A --> B)
    : UU
    := ∑(K : C)(k : K --> A)(k1 : is_isometry k), is_dagger_kernel Z k k1 f.
  
  (* Accessors for dagger kernel *)

  Coercion ker_to_obj
    {C : dagger_category}
    {Z : Zero C}
    {A B : C}
    {f : A --> B}
    (T : dagger_kernel Z f)
    : C
    := pr1 T.
  
  Definition ker_mor
    {C : dagger_category}
    {Z : Zero C}
    {A B : C}
    {f : A --> B}
    (T : dagger_kernel Z f)
    : T --> A
    := pr12 T.

  Definition ker_isometry
    {C : dagger_category}
    {Z : Zero C}
    {A B : C}
    {f : A --> B}
    (T : dagger_kernel Z f)
    : is_isometry (ker_mor T)
    := pr122 T.

  Definition ker_ax1
    {C : dagger_category}
    {Z : Zero C}
    {A B : C}
    {f : A --> B}
    (T : dagger_kernel Z f)
    : ((ker_mor T) · f = ZeroArrow Z T B)
    := pr1 (pr222 T).

  Definition ker_ax2
    {C : dagger_category}
    {Z : Zero C}
    {A B : C}
    {f : A --> B}
    (T : dagger_kernel Z f)
    : ∏ (X : C)(x : X --> A)(x1 : (x · f = ZeroArrow Z X B)),  ∑ (m : X --> T), (m · (ker_mor T) = x).
  Proof.
    exact (pr2 (pr222 T)).
  Qed.

  Lemma zero_dag
    {C : dagger_category}
    (Z : Zero C)
    {A B : C}
    : { ZeroArrow Z A B }_ C ^† = ZeroArrow Z B A.
  Proof.
    unfold ZeroArrow.
    rewrite dagger_to_law_comp.
    rewrite ZeroArrowEq.
    apply idpath.
  Qed.

  Lemma isometries_have_dag_ker
    {C : dagger_category}
    {Z : Zero C}
    {A B : C}
    (f : A --> B)
    (f1 : is_isometry f)
    : ∑(K : C)(k : K --> A)(k1 : is_isometry k), is_dagger_kernel Z k k1 f.
  Proof.
    use tpair.
    exact (Z).
    use tpair.
    exact (ZeroArrow Z Z A).
    use tpair.
    unfold is_isometry.
    rewrite zero_dag.
    rewrite ZeroArrow_comp_left.
    symmetry. exact (ZeroEndo_is_identity C Z (ZeroArrow Z Z Z)).
    use tpair.
    rewrite ZeroArrow_comp_left. apply idpath.
    simpl.
    intros.
    use tpair.
    exact (x · { ZeroArrow Z Z A }_ C ^†).
    simpl. rewrite <- id_right.
    rewrite <- f1.
    rewrite assoc.
    rewrite x1.
    rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_right.
    reflexivity.
  Qed.

  Lemma dag_ker_of_iso_is_zero
    {C : dagger_category}
    {Z : Zero C}
    {A B : C}
    (f : A --> B)
    (f1 : is_isometry f)
    (T : dagger_kernel Z f)
    : (ker_mor T) = ZeroArrow Z T A.
  Proof.
    symmetry. rewrite <- id_right.
    rewrite <- f1.
    rewrite assoc.
    rewrite (ker_ax1 T).
    rewrite ZeroArrow_comp_left.
    reflexivity.
  Qed.

  Lemma nondegeneracy_kernel
    {C : dagger_category}
    {Z : Zero C}
    {A B : C}
    (f : A --> B)
    (T : ∏ (A1 B1 : C)(f1 : A1 --> B1), (dagger_kernel Z f1))
    (ax : f · {f}_ C ^† = ZeroArrow Z A A)
    : f = ZeroArrow Z A B.
  Proof.
    set (k := T B A {f}_ C ^†).
    set (k_ax := ker_ax2 k A f ax).
    rewrite <- (pr2 k_ax).
    set (m := pr1 k_ax).
    set (m_rw := id_right m).
    rewrite <- m_rw.
    rewrite <- (ker_isometry k).
    rewrite assoc.
    unfold m. rewrite (pr2 k_ax).
    set (k_ax1 := ker_ax1 k).
    apply (maponpaths (C k A)) in k_ax1.
    rewrite dagger_to_law_comp in k_ax1.
    rewrite dagger_to_law_idemp in k_ax1.
    rewrite k_ax1.
    rewrite zero_dag.
    rewrite ZeroArrow_comp_left.
    reflexivity.
  Qed.
  
  End Kernels.

  Section QuantumNotation.

  Definition states
    {C : monoidal_cat}
    (A : C)
    : UU
    := C⟦I_{C},A⟧.

  Definition effects
    {C : monoidal_cat}
    (A : C)
    : UU
    := C⟦A,I_{C}⟧.

  Definition prob
    {C : monoidal_dagger_category}
    {A : C}
    (a : states A)
    (x : effects A)
    : I_{C} --> I_{C}
    := a · x · { x }_ C ^† · { a }_ C ^†.

  Definition set_effects 
    {C : monoidal_cat}
    (A : C)
    : UU
    := ∏ (n : nat), (effects A).

  Definition sum_effects
    {C : monoidal_cat}
    {A : C}
    (S : set_effects A)
    (op : superpos_oper C)
    : ∏ (n : nat), (effects A).
  Proof.
    intro n.
    induction n.
    exact (S 0).
    exact (IHn +^{op} (S (n + 1))).
  Defined.

  Definition prob_set
    {C : monoidal_dagger_category}
    {A : C}
    (S : set_effects A)
    (a : states A)
    : ∏ (n : nat), C ⟦ I_{ C}, I_{ C} ⟧.
  Proof.
    intro n.
    exact (prob a (S n)).
  Defined.
  
  Definition set_effects_is_finite
    {C : monoidal_cat}
    {A : C}
    (S : set_effects A)
    (Z : Zero C)
    : UU
    := ∑ (N : nat), ∏ (n : nat)(p: n > N), S n = ZeroArrow Z A I_{C}.

  Definition satisf_born_rule
    {C : monoidal_dagger_category}
    {A : C}
    {N : nat}
    (Z : Zero C)
    (S : set_effects A)
    (f : set_effects_is_finite S Z)
    (a : states A)
    (p : is_isometry a)
    (op : superpos_oper C)
    : UU
    := ∑ (N : nat), ∏ (n : nat)(p: n > N), (sum_effects (prob_set S a) op) n = identity I_{C}.

  End QuantumNotation.
