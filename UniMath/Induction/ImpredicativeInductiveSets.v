(** ** Impredicative Construction of Inductive Types that are Sets and Eliminate into Sets *)

(** This is based on Sam Speight's master's thesis *)

Require Import UniMath.Foundations.Init.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.categories.Types.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Section Specification.

Local Open Scope cat.

Variable A B: HSET.
Definition pre_prod: UU := ∏ (X: HSET), (pr1hSet A -> pr1hSet B -> pr1hSet X) -> pr1hSet X.
Lemma pre_prod_isaset: isaset pre_prod.
Proof.
  change (isofhlevel 2 pre_prod).
  apply impred.
  intro X.
  apply impred.
  intros _.
  apply setproperty.
Defined.
Definition pre_prod_as_set: HSET := hSetpair pre_prod pre_prod_isaset.

Definition nProduct (α: pre_prod): UU :=
  ∏(X Y : HSET) (f : pr1hSet X → pr1hSet Y) (h : pr1hSet A -> pr1hSet B -> pr1hSet X), f (α X h) = α Y (λ a b, f (h a b)).

Definition nProduct_isaset (α: pre_prod): isaset (nProduct α).
Proof.
  change (isofhlevel 2 (nProduct α)).
  apply impred.
  intro X.
  apply impred.
  intro Y.
  apply impred.
  intro f.
  apply impred.
  intro h.
Admitted.

Definition nProduct_as_set (α: pre_prod): HSET := hSetpair _ (nProduct_isaset α).

Definition Product: UU := ∑ α: pre_prod, pr1hSet (nProduct_as_set α).

Definition Pair (a : pr1hSet A) (b : pr1hSet B) : Product.
Proof.
  use tpair.
  - exact (λ X f, f a b).
  - cbn. red.
    intros; apply idpath.
Defined.

Definition Product_isaset: isaset Product.
Proof.
  Fail (apply isaset_total2_hSet).
Admitted.

Definition Product_as_set: HSET := hSetpair _ Product_isaset.

Definition Proj1: HSET ⟦Product_as_set, A⟧.
Abort.

(* copied from
-- System F encoding
definition  preProduct (A B : USet) : USet :=
  tΠ (X : USet), (A ⇒ B ⇒ X) ⇒ X

-- naturality condition
definition nProduct {A B : USet} (α : preProduct A B) : UPrp
  := tΠ(X Y : USet) (f : X → Y) (h : A ⇒ B ⇒ X), f (α X h) == α Y (λ a, f ∘ h a)

-- refined encoding
definition  Product (A B : USet) : USet := σ(α : preProduct A B), nProduct α

-- constructor
definition Pair {A B : USet} (a : A) (b : B) : Product A B
  := ⟨λ X f, f a b, λ X Y f g, rfl⟩

-- eliminators
definition Proj1 {A B : USet} : Product A B → A
  := sigma.rec (λ alpha p, alpha A (λ x y, x))

definition Proj2 {A B : USet} : Product A B → B
  := sigma.rec (λ alpha p, alpha B (λ x y, y))

-- recursor
definition Product_rec {A B C : Set} (f : A ⇒ B ⇒ C) (p : Product A B) : C
  := p.1 C f

-- β rule
definition Product_β {A B C : USet} (f : A → B → C) (a : A) (b : B)
  :  Product_rec f (Pair a b) = f a b := rfl

-- weak η rule
definition Product_weak_η {A B : USet} (x : Product A B)
  :  Product_rec Pair x = x
  := begin induction x with p n, fapply sigma_eq, apply eq_of_homotopy2,
                            intros X f, exact (n _ _ (Product_rec f) Pair), apply is_prop.elimo e
*)

(* preparation for the general case:
Variable F: HSET ⟦A, A⟧.
*)
End Specification.
