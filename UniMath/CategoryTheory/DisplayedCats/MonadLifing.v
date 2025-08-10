Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Section Monad_Lifting.
Context (C: category)
        (D: disp_cat C)
        (T: Monad C)
        {H_posetal_fibration : ∏ (c c' : C) (f : c --> c') (x : D c) (y : D c'), isofhlevel 1 (x -->[f] y)}.


Definition monad_lifting_data (dot_F: disp_functor (pr1 T) D D) : UU :=
        (disp_nat_trans (η T) (disp_functor_identity D) dot_F) ×
        (disp_nat_trans (μ  T) (disp_functor_composite dot_F dot_F) dot_F).

Definition dη {dot_F: disp_functor (pr1 T) D D} (dot_T: monad_lifting_data dot_F):
        (disp_nat_trans (η T) (disp_functor_identity D) dot_F) := pr1 dot_T.

Definition dμ {dot_F: disp_functor (pr1 T) D D} (dot_T: monad_lifting_data dot_F):
        (disp_nat_trans (μ  T) (disp_functor_composite dot_F dot_F) dot_F) := pr2 dot_T.

Definition monad_lifting_law1 {dot_F : disp_functor (pr1 T) D D} (dot_T : monad_lifting_data dot_F) : UU :=
        ∏ (x : C) (dx : D x),
                comp_disp
                (dη dot_T (T x) (dot_F x dx))
                (dμ dot_T x dx)
                = transportf
                (fun p => dot_F x dx -->[ p ] dot_F x dx)
                (pathsinv0 (Monad_law1 x))
                (id_disp (dot_F x dx)).

Definition monad_lifting_law2 {dot_F : disp_functor (pr1 T) D D} (dot_T : monad_lifting_data dot_F) : UU :=
        ∏ (x : C) (dx : D x),
                comp_disp
                (disp_functor_on_morphisms dot_F (dη dot_T x dx))
                (dμ dot_T x dx)
                = transportf
                (fun p => dot_F x dx -->[ p ] dot_F x dx)
                (pathsinv0 (Monad_law2 x))
                (id_disp (dot_F x dx)).

Definition monad_lifting_law3 {dot_F : disp_functor (pr1 T) D D} (dot_T : monad_lifting_data dot_F) : UU :=
        ∏ (x : C) (dx : D x),
                comp_disp
                (disp_functor_on_morphisms dot_F (dμ dot_T x dx))
                (dμ dot_T x dx)
                =     transportf
                (fun p => 
                (disp_functor_composite dot_F (disp_functor_composite dot_F dot_F)) x dx -->[ p ] dot_F x dx)
                (pathsinv0 (Monad_law3 x))
                (comp_disp
                   (dμ dot_T (T x) (dot_F x dx))
                   (dμ dot_T x dx)).

Definition monad_lifting_laws {dot_F: disp_functor (pr1 T) D D} (dot_T: monad_lifting_data dot_F): UU
:=
        monad_lifting_law1 dot_T
        ×
        monad_lifting_law2 dot_T
        ×
        monad_lifting_law3 dot_T.
          
Definition monad_lifting (dot_F: disp_functor (pr1 T) D D) : UU :=
        ∑ (dot_T: monad_lifting_data dot_F),
        monad_lifting_laws dot_T.


End Monad_Lifting.