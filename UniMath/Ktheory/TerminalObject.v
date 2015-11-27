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

Definition unitFunctor (C:Precategory) : C ==> SET.
  intros. refine (_,,_).
  { refine (_,,_).
    { intros. exact Sets.unit. }
    { intros. exact (idfun _). } } 
  { split.
    { intros a. reflexivity. }
    { intros a b c f g. reflexivity. } } Defined.

Definition TerminalObject (C:Precategory) := Representation (unitFunctor C^op).

Definition terminalObject {C} (t:TerminalObject C) : ob C := universalObject t.

Definition terminalArrow {C} (t:TerminalObject C) (c:ob C) : c → terminalObject t
  := t \\ tt.

Definition InitialObject (C:Precategory) := TerminalObject C^op.

Definition initialObject {C} (i:InitialObject C) : ob C := universalObject i.

Definition initialArrow {C} (i:InitialObject C) (c:ob C) : initialObject i → c
  := rm_opp_mor (i \\ tt).

(*  *)