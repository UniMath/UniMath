(** * Cochains

Cochains are diagrams of the form X₀ ← X₁ ← ⋯.

Author: Langston Barrett (@siddharthist), Febuary 2018
 *)
Require Import UniMath.Foundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.terminal.

Local Open Scope cat.

(** Define the cochain:
<<
     0 <-- 1 <-- 2 <-- 3 <-- ...
>>
   with exactly one arrow from S n to n.
*)

Definition conat_graph : graph :=
    mk_graph nat (λ m n, match m with S m' => m' = n | 0 => empty end).

Notation "'cochain'" := (diagram conat_graph).

Definition mapcochain {C D : precategory} (F : functor C D)
           (c : cochain C) : cochain D := mapdiagram F c.

(** Any j > i gives a morphism in the cochain via composition *)
Definition cochain_mor {C : precategory} (c : cochain C) {i j} :
  i < j -> C⟦dob c j, dob c i⟧.
Proof.
induction j as [|j IHj].
- intros Hi0; destruct (negnatlthn0 0 Hi0).
- intros Hij.
  destruct (natlehchoice4 _ _ Hij) as [|H].
  + refine (_ · IHj h).
    apply (dmor c), (idpath _).
  + apply (dmor c), (!H).
Defined.

(** Construct the cochain:
<<
         !          F!            F^2 !
     1 <----- F 1 <------ F^2 1 <-------- F^3 1 <--- ...
>>
*)
Definition termCochain {C : precategory} (TermC : Terminal C) (F : functor C C) :
  cochain C.
Proof.
  exists (λ n, iter_functor F n TermC).
  intros n m Hmn; compute in Hmn, n, m.
  destruct n; try induction Hmn.
  induction n as [|n IHn].
  - exact (TerminalArrow TermC _).
  - exact (# F IHn).
Defined.
