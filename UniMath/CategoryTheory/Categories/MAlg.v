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
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.FunctorCategory.

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

Definition disp_functor_cat : disp_cat (functor_category C C).
Proof.
  use disp_struct.
  - simpl. intro F.
    exact (∑ (o : C⟦F Ω, Ω⟧), is_monotone_Falg F o).
  - intros F G [o is_monotone_o] [o' is_monotone_o'] [α is_nat_trans].
    exact (leq _ o (o' ∘ α Ω)).
  - simpl. intros.
    apply leq.
  - simpl. intros F [o is_monotone_o].
    rewrite id_left.
    apply is_po_leq.
  - simpl. intros F G H [f is_monotone_f] [g is_monotone_o] [h is_monotone_h] α β A B.
    eapply (is_po_leq (F Ω)).
    + apply A.
    + rewrite assoc'. 
      apply (is_precomp_monotone_leq _ _ _ _ _ B).
Defined. 

Definition malg_cat : category := total_category disp_functor_cat.

End MAlg.