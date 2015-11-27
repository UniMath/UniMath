(* -*- coding: utf-8 -*- *)

Require Import
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Sets
        UniMath.Ktheory.Representation
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Precategories.
Local Open Scope cat.
Set Automatic Introduction.

Definition UnitFunctor (C:Precategory) : C ==> SET.
  refine (_,,_).
  { exists (λ c, unitset). exact (λ a b f, idfun unit). }
  { split.
    { intros a. reflexivity. }
    { intros a b c f g. reflexivity. } }
Defined.

Definition TerminalObject (C:Precategory) := Representation (UnitFunctor C^op).

Definition terminalObject {C} (t:TerminalObject C) : ob C := universalObject t.

Definition terminalArrow {C} (t:TerminalObject C) (c:ob C) : c → terminalObject t
  := t \\ tt.

Definition InitialObject (C:Precategory) := TerminalObject C^op.

Definition initialObject {C} (i:InitialObject C) : ob C := universalObject i.

Definition initialArrow {C} (i:InitialObject C) (c:ob C) : initialObject i → c
  := rm_opp_mor (i \\ tt).

Definition init_to_opp {C:Precategory} : InitialObject C -> TerminalObject C^op
  := λ i, i.

Definition term_to_opp {C:Precategory} : TerminalObject C -> InitialObject C^op.
Proof. intros. unfold InitialObject. now induction (opp_opp_precat C). Defined.

(** zero objects, as an alternative to ZeroObject.v *)

Definition ZeroObject (C:Precategory)
  := Σ z:ob C, Universal (UnitFunctor C^op) z × Universal (UnitFunctor C^op^op) z.

Definition zero_to_terminal (C:Precategory) : ZeroObject C -> TerminalObject C
  := λ z, pr1 z ,, pr1 (pr2 z).

Definition zero_to_initial (C:Precategory) : ZeroObject C -> InitialObject C
  := λ z, pr1 z ,, pr2 (pr2 z).

Definition zero_opp (C:Precategory) : ZeroObject C -> ZeroObject C^op.
Proof.
  intro z. induction z as [z k]. exists z.
  induction (opp_opp_precat C). 
  exact (pr2 k,,pr1 k).
Defined.

Definition hasZeroObject (C:Precategory) := ∥ ZeroObject C ∥.

Definition haszero_opp (C:Precategory) : hasZeroObject C -> hasZeroObject C^op
  := hinhfun (zero_opp C).

Definition zeroMap' (C:Precategory) (a b:ob C) (o:ZeroObject C) : Hom C a b
  := (zero_to_initial C o \\ tt) ∘ (zero_to_terminal C o \\ tt).

Lemma zero_eq_zero_opp (C:Precategory) (a b:ob C) (o:ZeroObject C) :
  zeroMap' C^op (opp_ob b) (opp_ob a) (zero_opp C o)
  =
  opp_mor (zeroMap' C a b o).
Proof.
  intros.
  try reflexivity.              (* compare to zeroMap'_opp in ZeroObject.v *)


Abort.

(*  *)