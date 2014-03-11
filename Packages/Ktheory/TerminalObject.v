(* -*- coding: utf-8 -*- *)

Unset Automatic Introduction.
Require Import 
        Foundations.hlevel2.hSet
        RezkCompletion.precategories
        RezkCompletion.functors_transformations 
        Ktheory.Utilities.
Require Ktheory.Precategories Ktheory.Sets Ktheory.Representation.
Import Utilities.Notation Precategories.Notation.
Definition unitFunctor_data (C:precategory) 
     : functor_data (Precategories.Precategory.obmor C) (Precategories.Precategory.obmor SET).
  intros. refine (tpair _ _ _).
  intros. exact Sets.unit. intros. exact (idfun _). Defined.
Definition unitFunctor C : C ==> SET.
  intros. exists (unitFunctor_data C).
  split. reflexivity. reflexivity. Defined.
Definition InitialObject (C:precategory) := Representation.Data (unitFunctor C).
Definition initialObject {C} (i:InitialObject C) : ob C.
  intros C i. exact (Representation.Object i). Defined.
Definition initialArrow {C} (i:InitialObject C) (c:ob C) : initialObject i → c.
  intros C [[i []] p] c. exact (pr1 (the (p (c,,tt)))). Defined.
Definition TerminalObject (C:precategory) 
  := Representation.Data (unitFunctor C^op).
Definition terminalObject {C} (t:InitialObject C) : ob C.
  intros C t. exact (Representation.Object t). Defined.
Definition terminalArrow {C} (t:TerminalObject C) (c:ob C) : c → terminalObject t.
  intros C [[i []] p] c. exact (pr1 (the (p (c,,tt)))). Defined.      
