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

Definition InitialObject (C:Precategory) := Representation (unitFunctor C).

Definition initialObject {C} (i:InitialObject C) : ob C := universalObject i.

Definition initialArrow {C} (i:InitialObject C) (c:ob C) : initialObject i → c
  := universalMap i c tt.

Definition TerminalObject (C:Precategory) := Representation (unitFunctor C^op).

Definition terminalObject {C} (t:InitialObject C) : ob C := universalObject t.

Definition terminalArrow {C} (t:TerminalObject C) (c:ob C) : c → terminalObject t
  := universalMap t c tt.
