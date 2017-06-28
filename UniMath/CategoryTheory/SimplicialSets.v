(** * Homotopy theory of simplicial sets.

Vladimir Voevodsky

started on Nov. 22, 2014 (with Alexander Vishik)

*)

Unset Automatic Introduction.

(* Preamble *)

Require Import UniMath.MoreFoundations.Tactics.

Require Export UniMath.Combinatorics.FiniteSets.
(* Require Export UniMath.Combinatorics.OrderedSets. *)
Require Export UniMath.CategoryTheory.Categories.
Require Export UniMath.CategoryTheory.categories.category_hset.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.CategoryTheory.opp_precat.

(* To upstream files *)



(* The pre-category data for the category Delta *)

Local Open Scope stn.

Definition monfunstn ( n m : nat ) : UU := ∑ f : ⟦ n ⟧ -> ⟦ m ⟧, ∏ (x y: ⟦n⟧), x ≤ y -> f x ≤ f y.
Definition monfunstnpair { m n : nat } f is := (f,,is) : monfunstn m n.
Definition monfunstnpr1 {n m : nat} : monfunstn n m  -> ⟦ n ⟧ -> ⟦ m ⟧ := pr1.

Lemma monfunstnpr1_isInjective {m n} (f g : monfunstn m n) : monfunstnpr1 f = monfunstnpr1 g -> f = g.
Proof.
  intros ? ? ? ? e.
  apply subtypeEquality.
  { intros h. apply impred; intro i. apply impred; intro j. apply impred; intro l.
    apply propproperty. }
  exact e.
Defined.

Coercion monfunstnpr1 : monfunstn >-> Funclass .

Lemma isasetmonfunstn n m : isaset ( monfunstn n m ) .
Proof.
  intros . apply ( isofhleveltotal2 2 ) .
  { apply impred. intro t. apply isasetstn. }
  intro f. apply impred; intro i.  apply impred; intro j. apply impred; intro l.
  apply isasetaprop, propproperty.
Defined.

Definition monfunstnid n : monfunstn n n := monfunstnpair (idfun _) (λ x y is, is).

Definition monfunstncomp { n m k : nat } ( f : monfunstn n m ) ( g : monfunstn m k ) :
  monfunstn n k .
Proof.
  intros . exists ( g ∘ f ) . intros i j l. unfold funcomp.
  apply ( pr2 g ). apply ( pr2 f ) . assumption.
Defined.

Definition precatDelta : precategory .
Proof.
  use tpair.
  { use tpair.
    { exists nat. intros m n. exact (monfunstn (S m) (S n)). }
    { split.
      { intros m. apply monfunstnid. }
      { intros l m n f g. exact (monfunstncomp f g). } } }
  simpl. split.
  { simpl. split.
    { intros m n f. now apply monfunstnpr1_isInjective. }
    { intros m n f. now apply monfunstnpr1_isInjective. } }
  { simpl. intros m n o p f g h. now apply monfunstnpr1_isInjective. }
Defined.

Local Open Scope cat.

Definition sSet := [ precatDelta^op , HSET, pr2 is_univalent_HSET ] .
(* V.V. with Sasha Vishik, Nov. 23, 2014 *)


(* End of file *)
