(*************************************************************************************

 Strict initial objects

 In this file, we define strict initial objects (i.e., initial objects such that every
 morphism into it is an isomorphism). We also prove some basic properties about them,
 namely that strict initial objects are preserves under isomorphism and that strict
 initial objects are stable under pullback.

 Contents
 1. Strict initial objects
 2. Strictness is preserved under isomorphism
 3. Stability of strict initial objects

 *************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodColimits.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

(** * 1. Strict initial objects *)
Definition is_strict_initial
           {C : category}
           (I : Initial C)
  : UU
  := ∏ (x : C)
       (f : x --> I),
     is_z_isomorphism f.

Proposition isaprop_is_strict_initial
            {C : category}
            (I : Initial C)
  : isaprop (is_strict_initial I).
Proof.
  do 2 (use impred ; intro).
  apply isaprop_is_z_isomorphism.
Qed.

Definition strict_initial_object
           (C : category)
  : UU
  := ∑ (I : Initial C),
     is_strict_initial I.

Proposition isaprop_strict_initial_object
            (C : univalent_category)
  : isaprop (strict_initial_object C).
Proof.
  use isaproptotal2.
  - intro.
    apply isaprop_is_strict_initial.
  - intros.
    apply (isaprop_Initial C (univalent_category_is_univalent C)).
Qed.

Definition make_strict_initial
           {C : category}
           (I : Initial C)
           (H : is_strict_initial I)
  : strict_initial_object C
  := I ,, H.

Coercion strict_initial_to_initial
         {C : category}
         (I : strict_initial_object C)
  : Initial C.
Proof.
  exact (pr1 I).
Defined.

Proposition is_strict_initial_strict_initial
            {C : category}
            (I : strict_initial_object C)
  : is_strict_initial I.
Proof.
  exact (pr2 I).
Defined.

Proposition is_initial_mor_to_strict_initial
            {C : category}
            (I : strict_initial_object C)
            (x : C)
            (f : x --> I)
  : isInitial _ x.
Proof.
  use (iso_to_Initial I).
  pose (f_iso := f ,, is_strict_initial_strict_initial I x f : z_iso x I).
  exact (z_iso_inv f_iso).
Defined.

(** * 2. Strictness is preserved under isomorphism *)
Definition strict_initial_z_iso
           {C : category}
           (I : strict_initial_object C)
           (I' : Initial C)
           (f : z_iso I I')
  : is_strict_initial I'.
Proof.
  intros x g.
  pose (H := is_strict_initial_strict_initial I x (g · inv_from_z_iso f)).
  pose (h := (_ ,, H) : z_iso x I).
  use make_is_z_isomorphism.
  - exact (inv_from_z_iso f · inv_from_z_iso h).
  - split.
    + abstract
        (rewrite !assoc ;
         exact (z_iso_inv_after_z_iso h)).
    + abstract
        (apply InitialArrowEq).
Defined.

Definition all_initial_strict
           {C : category}
           (I : strict_initial_object C)
           (I' : Initial C)
  : is_strict_initial I'.
Proof.
  use (strict_initial_z_iso I I').
  apply ziso_Initials.
Defined.

(** * 3. Stability of strict initial objects *)
Definition stict_initial_stable
           {C : category}
           (HC : Pullbacks C)
           (I : strict_initial_object C)
           {x y : C}
           (f : x --> y)
  : preserves_initial (cod_pb HC f).
Proof.
  use preserves_initial_if_preserves_chosen.
  {
    exact (initial_cod_fib y I).
  }
  unfold preserves_chosen_initial.
  use to_initial_slice ; cbn.
  use (is_initial_mor_to_strict_initial I).
  apply PullbackPr1.
Qed.
