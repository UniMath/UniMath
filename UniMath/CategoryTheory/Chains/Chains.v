(** * Chains

Chains are diagrams of the form X₀ → X₁ → ⋯.

Authors: Anders Mörtberg and Benedikt Ahrens, 2015-2016
 *)
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.initial.

Local Open Scope cat.

(** Define the chain:
<<
     0 --> 1 --> 2 --> 3 --> ...
>>
   with exactly one arrow from n to S n.
*)

Definition nat_graph : graph := make_graph nat (λ m n, 1 + m = n).

Notation "'chain'" := (diagram nat_graph).

Definition mapchain {C D : category} (F : functor C D)
           (c : chain C) : chain D := mapdiagram F c.

(** Any i < j gives a morphism in the chain via composition *)
Definition chain_mor {C : category} (c : chain C) {i j} :
  i < j -> C⟦dob c i, dob c j⟧.
Proof.
induction j as [|j IHj].
- intros Hi0; destruct (negnatlthn0 0 Hi0).
- intros Hij.
  destruct (natlehchoice4 _ _ Hij) as [|H].
  + apply (IHj h · dmor c (idpath (S j))).
  + apply dmor, (maponpaths S H).
Defined.

(** For any cocone `cc` under the chain, the following diagram commutes:

    <<
     c i --> c j
      |       |
      |       V
      +----> cc
    >>
 *)
Lemma chain_mor_coconeIn {C : category} (c : chain C) (x : C)
  (cc : cocone c x) i : ∏ j (Hij : i < j),
  chain_mor c Hij · coconeIn cc j = coconeIn cc i.
Proof.
induction j as [|j IHj].
- intros Hi0; destruct (negnatlthn0 _ Hi0).
- intros Hij; simpl.
  destruct (natlehchoice4 _ _ Hij).
  + rewrite <- (IHj h), <- assoc.
    apply maponpaths, coconeInCommutes.
  + destruct p.
    apply coconeInCommutes.
Qed.

(** One of the hypotheses of this lemma is redundant, however when stated this way the lemma can be
used for any two proofs making it easier to apply. *)
Lemma chain_mor_right {C : category} {c : chain C} {i j} (Hij : i < j) (HSij : S i < j) :
  dmor c (idpath (S i)) · chain_mor c HSij = chain_mor c Hij.
Proof.
induction j as [|j IHj].
- destruct (negnatlthn0 _ Hij).
- simpl.
  destruct (natlehchoice4 _ _ Hij).
  + destruct (natlehchoice4 _ _ HSij).
    * now rewrite <- (IHj h h0), assoc.
    * destruct p; simpl.
      destruct (natlehchoice4 _ _ h); [destruct (isirreflnatlth _ h0)|].
      apply cancel_postcomposition, maponpaths, isasetnat.
  + destruct p, (isirreflnatlth _ HSij).
Qed.

(** See comment for [chain_mor_right] about the redundant hypothesis *)
Lemma chain_mor_left {C : category} {c : chain C} {i j} (Hij : i < j) (HiSj : i < S j) :
  chain_mor c Hij · dmor c (idpath (S j)) = chain_mor c HiSj.
Proof.
destruct j.
- destruct (negnatlthn0 _ Hij).
- simpl; destruct (natlehchoice4 i (S j) HiSj).
  + destruct (natlehchoice4 _ _ h).
    * destruct (natlehchoice4 _ _ Hij); [|destruct p, (isirreflnatlth _ h0)].
      apply cancel_postcomposition, cancel_postcomposition, maponpaths, isasetbool.
    * destruct p; simpl.
      destruct (natlehchoice4 _ _ Hij); [destruct (isirreflnatlth _ h0)|].
      apply cancel_postcomposition, maponpaths, isasetnat.
  + generalize Hij; rewrite p; intros H.
    destruct (isirreflnatlth _ H).
Qed.

(** Construct the chain:
<<
         !          F!            F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...
>>
*)
Definition initChain {C : category} (InitC : Initial C) (F : functor C C) : chain C.
Proof.
exists (λ n, iter_functor F n InitC).
intros m n Hmn. destruct Hmn. simpl.
induction m as [|m IHm]; simpl.
- exact (InitialArrow InitC _).
- exact (# F IHm).
Defined.

(** ** Definition of (ω-)cocontinuous functors *)

Section cocont.

Context {C D : category} (F : functor C D).

Definition is_cocont : UU :=
  ∏ (g : graph) (d : diagram g C) (L : C) (cc : cocone d L),
    preserves_colimit F d L cc.

Definition is_omega_cocont : UU :=
  ∏ (c : chain C) (L : C) (cc : cocone c L),
    preserves_colimit F c L cc.

End cocont.

Definition omega_cocont_functor (C D : category) : UU :=
  ∑ (F : functor C D), is_omega_cocont F.
