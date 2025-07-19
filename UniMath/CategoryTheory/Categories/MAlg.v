(**

 Category of Monotone F-algebras

 As part of "Weakest Precondition in Fibrations" (https://doi.org/10.1016/j.entcs.2020.09.002),
 the notion of monotone F-algebras and their category give us a recipe for constructing monad liftings.

 Contents:
  1. MAlg precategory
  2. Malg category

 TODO: after implementing wp and Dijkstra structures, define wp(f, Q) as o ∘ T(Q) ∘ f 
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.MoreFoundations.All.

Local Open Scope cat.

Section MAlg.
Context (C : category)
        (Ω : C)
        (leq : ∏ X : ob C, C⟦X, Ω⟧ → C⟦X, Ω⟧ → hProp)
        (is_po_leq : ∏ X : ob C, isPartialOrder (leq X))
        (is_precomp_monotone_leq :  ∏ (X Y : ob C) (f : C⟦X, Y⟧)
        (g h : C⟦Y, Ω⟧),
        leq Y g h → leq X (g ∘ f) (h ∘ f)).


Definition is_monotone_Falg (F : functor C C) (o : C⟦F Ω, Ω⟧) : UU :=
  ∏ (X : ob C) (i i' : C⟦X, Ω⟧),
    leq X i i' → leq (F X) (o ∘ #F i) (o ∘ #F i').

Definition malg_object : UU := 
    ∑ (F : functor C C) (o : C⟦F Ω, Ω⟧),
        is_monotone_Falg F o.
    
Definition malg_morphism (A B : malg_object) : UU := 
∑ (α : nat_trans (pr1 A) (pr1 B)), 
leq _ (pr12 A) (pr12 B ∘ α Ω).


Definition malg_id (A : malg_object) : malg_morphism A A.
Proof.
  use tpair.
  - exact (nat_trans_id (pr1 A)).
  - unfold pr1. rewrite id_left. apply (is_po_leq (pr1 A Ω)). 
Defined.

Definition malg_comp {X Y Z : malg_object}
            (f : malg_morphism X Y) (g : malg_morphism Y Z) : malg_morphism X Z.
Proof.
  use tpair.
  - exact (nat_trans_comp _ _ _ (pr1 f) (pr1 g)).
  - simpl. eapply (pr11 (is_po_leq (pr1 X Ω))).
    + exact (pr2 f).
    + rewrite assoc'. apply (is_precomp_monotone_leq _ _ (pr1 f Ω)).
    exact (pr2 g).
Defined.

Definition malg_precategory_ob_mor : precategory_ob_mor :=
   make_precategory_ob_mor malg_object malg_morphism.

Definition malg_precategory_data : precategory_data.
Proof.
  use make_precategory_data.
  - exact malg_precategory_ob_mor.
  - exact  (λ X, malg_id X).
  - exact (λ X Y Z f g, malg_comp f g).
Defined.


Proposition is_precategory_malg : is_precategory malg_precategory_data.
Proof.
  repeat split; cbn.
  - intros a b f. use total2_paths2_f.
    + apply nat_trans_comp_id_left. exact C.
    + apply proofirrelevance. apply pr2.
  - intros a b f. use total2_paths2_f.
    + apply nat_trans_comp_id_right. exact C.
    + apply proofirrelevance. apply pr2.
  - intros a b c d f g h. use total2_paths2_f.
    + apply nat_trans_comp_assoc. exact C.
    + apply proofirrelevance. apply pr2.
  - intros a b c d f g h. use total2_paths2_f.
    + apply nat_trans_comp_assoc'. exact C.
    + apply proofirrelevance. apply pr2.
Defined. 

Definition malg_precat : precategory.
Proof.
  use make_precategory.
  - exact malg_precategory_data.
  - exact is_precategory_malg.
Defined.

Definition malg_cat : category.
Proof.
  use make_category.
  - exact malg_precat.
  - simpl. intros a b.
   apply isaset_total2.
   + apply isaset_nat_trans. apply C.
   + intro x. apply isasetaprop. apply pr2.
Defined.
