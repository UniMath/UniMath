(** * Cochains

Cochains are diagrams of the form X₀ ← X₁ ← ⋯.

Author: Langston Barrett (@siddharthist), Febuary 2018
 *)
Require Import UniMath.Foundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.CategoryTheory.Core.Functors.
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
    make_graph nat (λ m n, S n = m).

Notation "'cochain'" := (diagram conat_graph).

(** A diagram for a cochain is what it should be, a collection of objects and
    arrows arranged so: X₀ ⟵ X₁ ⟵ ⋯. This can be used to easily construct
    cochains, see e.g. [termCochain]. *)
Definition cochain_weq {C : precategory} :
  (∑ (obs : ∏ n : nat, ob C), (∏ n : nat, obs (S n) --> obs n)) ≃ cochain C.
Proof.
  use weqfibtototal; intro obs; cbn.
  use weq_iso.
  - intros ars a b aeqSb.
    refine (_ · ars b).
    exact (transportf (λ o, C ⟦ obs o, obs (S b) ⟧) aeqSb (identity _)).
  - exact (λ ars n, ars (S n) n (idpath _)).
  - intros ars; cbn.
    apply funextsec; intro n.
    apply id_left.
  - intros ars.
    cbn.
    apply funextsec; intro a.
    apply funextsec; intro b.
    apply funextsec; intro p.
    induction p.
    cbn.
    apply id_left.
Defined.

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
  + apply (dmor c), (maponpaths S H).
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
  use cochain_weq; use tpair.
  - exact (λ m, iter_functor F m TermC).
  - intros n; induction n as [|n IHn].
    * exact (TerminalArrow TermC _).
    * exact (# F IHn).
Defined.
