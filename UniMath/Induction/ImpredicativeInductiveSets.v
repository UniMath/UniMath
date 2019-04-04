(** ** Impredicative Construction of Inductive Types that are Sets and Eliminate into Sets *)

(** This is based on Sam Speight's master's thesis *)
(* test *)

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
  apply hlevelntosn.
  apply (setproperty Y).
Defined.

Definition nProduct_as_set (α: pre_prod): HSET := hSetpair _ (nProduct_isaset α).

Definition Product: UU := ∑ α: pre_prod, pr1hSet (nProduct_as_set α).

Definition Product_isaset: isaset Product.
Proof.
  apply (isaset_total2_hSet pre_prod_as_set).
Defined.

Definition Product_as_set: HSET := hSetpair _ Product_isaset.

Definition Pair (a : pr1hSet A) (b : pr1hSet B) : Product.
Proof.
  use tpair.
  - exact (λ X f, f a b).
  - cbn. red.
    intros; apply idpath.
Defined.

Definition Proj1: HSET ⟦Product_as_set, A⟧.
Proof.
  cbn.
  intro p.
  induction p as [α H].
  apply α.
  exact (fun x y => x).
Defined.

Definition Proj2: HSET ⟦Product_as_set, B⟧.
Proof.
  cbn.
  intro p.
  induction p as [α H].
  apply α.
  exact (fun x y => y).
Defined.

Definition Product_rec {C: HSET} (f: pr1hSet A -> pr1hSet B -> pr1hSet C) (p: Product) : pr1hSet C.
Proof.
  induction p.
  apply (pr1 C f).
Defined.

Lemma Product_beta (C: HSET) (f: pr1hSet A -> pr1hSet B -> pr1hSet C) (a: pr1hSet A) (b: pr1hSet B) : Product_rec f (Pair a b) = f a b.
Proof.
  apply idpath.
Defined.

Lemma Product_weak_eta (x: Product) : Product_rec (C := Product_as_set) Pair x = x.
Proof.
  induction x as [P H].
  use total2_paths_f.
  - cbn.
    UniMath.MoreFoundations.Tactics.show_id_type.
    unfold pre_prod in P.
    apply funextsec.
    intro X.
    use funextfun.
    intro f.
    cbn in H.
    red in H.
    exact (H Product_as_set X (fun x => pr1 x X f) Pair).
  - cbn.
    cbn in H.
    red in H.
    apply funextsec.
    intro X.
    apply funextsec.
    intro Y.
    apply funextsec.
    intro f.
    apply funextsec.
    intro h.
    apply (setproperty Y).
Defined.

(* copied from https://github.com/jonas-frey/Impredicative/blob/master/encode.hlean#L173 :
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
     intros X f, exact (n _ _ (Product_rec f) Pair), apply is_prop.elimo end

-- commuting conversion
definition Product_com_con {A B C D : USet} (f : A → B → C) (g : C → D)
  :  Product_rec (λ a b, g (f a b)) = g ∘ Product_rec f
  := (eq_of_homotopy (λ x, x.2 C D g f))⁻¹

-- strong η rule
definition Product_η {A B C : USet} (g : Product A B → C)
  :  Product_rec (λ a b, g (Pair a b)) = g
  := (Product_com_con Pair g) ⬝ eq_of_homotopy (λ x, ap g (Product_weak_η x))

-- classical η rule
definition Product_classical_η {A B : USet} (p : Product A B)
  :   Pair (Proj1 p) (Proj2 p) = p
  :=  ap (λ f, f p) (Product_η _)⁻¹ ⬝ (Product_weak_η p)

-- universal property
definition Product_univ_prop {A B C : USet} : is_equiv (@Product_rec A B C)
  := adjointify Product_rec
                (λ f a b, f (Pair a b))
                Product_η
                (λ g, eq_of_homotopy2 (Product_β g))
*)

(* preparation for the general case:
Variable F: HSET ⟦A, A⟧.
*)
End Specification.
