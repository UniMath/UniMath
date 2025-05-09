(**

  Multimodules

  This file defines multimodules: abelian groups with compatible R_i-actions for all i : I. This
  is a generalization of R-S-bimodules, based on the following observation:
  The definition of a compatible R-S-bimodule structure is phrased in terms of associativity for
  left and right actions: (rm)s=r(ms). Modulo notation, this is really a statement about the actions
  intertwining one another and in the same way, we can define a multimodule based on every action
  being compatible.

  Contents
  1. Multimodules [multimodule]
  2. Multimodule morphisms
  2.1. Multilinearity [ismultilinear] [multilinearfun]
  2.2. Multimodule morphisms [multimodulefun]
  3. Properties of the ring actions

  Originally written by Langston Barrett (@siddharthist), November-December 2017

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Modules.Core.
Require Import UniMath.Algebra.RigsAndRings.

(** ** 1. Multimodules *)

(** Definition from Algebra by Bourbaki, II §1, no. 14. *)
Definition arecompatibleactions {R S G}
           (mr : module_struct R G) (ms : module_struct S G) :=
  let m1 := module_mult (G,, mr) in
  let m2 := module_mult (G,, ms)
  in ∏ (r1 : R) (r2 : S), (m1 r1 ∘ m2 r2 = m2 r2 ∘ m1 r1)%functions.

Definition multimodule_struct {I : UU} {rings : I -> ring} {G : abgr}
           (structs : ∏ i : I, module_struct (rings i) G) :=
  ∏ (i1 i2 : I) (ne : (i1 = i2) -> hfalse),
    arecompatibleactions (structs i1) (structs i2).

Definition multimodule {I : UU} (rings : I -> ring) : UU
  := ∑ G (ms : ∏ i : I, module_struct (rings i) G), multimodule_struct ms.

(** We define a few things in the same way for multimodules as we did for modules *)

Definition pr1multimodule {I : UU} {rings : I -> ring} (MM : multimodule rings) : abgr
  := pr1 MM.

Coercion pr1multimodule : multimodule >-> abgr.

Definition pr2multimodule {I : UU} {rings : I -> ring} (MM : multimodule rings)
  : ∏ i : I, module_struct (rings i) (pr1multimodule MM) := (pr1 (pr2 MM)).

Definition pr3bimodule {I : UU} {rings : I -> ring} (MM : multimodule rings)
  : multimodule_struct (pr2multimodule MM) := (pr2 (pr2 MM)).

Definition ith_module {I : UU} {rings : I -> ring} (MM : multimodule rings) (i : I)
  : module (rings i) := (pr1multimodule MM,, pr2multimodule MM i).

(** Propositions *)

Lemma isaproparecompatibleactions
      {R S G} (mr : module_struct R G) (ms : module_struct S G) :
  isaprop (arecompatibleactions mr ms).
Proof.
  do 2 (apply impred_isaprop; intro).
  refine ((_ : isaset _) _ _).
  apply funspace_isaset.
  apply setproperty.
Qed.

Lemma isapropmultimodule_struct {I : UU} {rings : I -> ring} {G : abgr}
                                (structs : ∏ i : I, module_struct (rings i) G) :
  isaprop (multimodule_struct structs).
Proof.
  apply (impredtwice 1); intros i1 i2.
  apply impredfun.
  apply isaproparecompatibleactions.
Qed.

(** * 2. Multimodule morphisms *)

(** ** 2.1. Multilinearity*)

(** A function is multilinear precisely when it is linear for each module *)

Definition ismultilinear {I : UU} {rings : I -> ring} {MM NN : multimodule rings} (f : MM -> NN)
  := ∏ i : I, @islinear (rings i) (ith_module MM i) (ith_module NN i) f.

Definition multilinearfun {I : UU} {rings : I -> ring} (MM NN : multimodule rings)
  : UU := ∑ f : MM -> NN, ismultilinear f.

Definition make_multilinearfun {I : UU} {rings : I -> ring} {MM NN : multimodule rings}
           (f : MM -> NN) (is : ismultilinear f) : multilinearfun MM NN
  := tpair _ f is.

Definition pr1multilinearfun {I : UU} {rings : I -> ring} {MM NN : multimodule rings}
           (f : multilinearfun MM NN) : MM -> NN := pr1 f.

Coercion pr1multilinearfun : multilinearfun >-> Funclass.

Definition ith_linearfun {I : UU} {rings : I -> ring} {MM NN : multimodule rings}
           (f : multilinearfun MM NN) (i : I) :
  linearfun (ith_module MM i) (ith_module NN i) :=
  (pr1 f,, pr2 f i).

Definition ismultilinearfuncomp {I : UU} {rings : I -> ring}
           {MM NN PP : multimodule rings} (f : multilinearfun MM NN)
           (g : multilinearfun NN PP) : ismultilinear (pr1 g ∘ pr1 f)%functions :=
  (fun i => islinearfuncomp (ith_linearfun f i) (ith_linearfun g i)).

Definition multilinearfuncomp {I : UU} {rings : I -> ring}
           {MM NN PP : multimodule rings} (f : multilinearfun MM NN)
           (g : multilinearfun NN PP) : multilinearfun MM PP :=
  (funcomp f g,, ismultilinearfuncomp f g).

(** ** 2.2. Multimodule morphisms *)

Definition ismultimodulefun {I : UU} {rings : I -> ring}
           {MM NN : multimodule rings} (f : MM -> NN) : UU :=
   (isbinopfun f) × (ismultilinear f).

Lemma isapropismultimodulefun {I : UU} {rings : I -> ring}
      {MM NN : multimodule rings} (f : MM -> NN) : isaprop (ismultimodulefun f).
Proof.
  refine (@isofhleveldirprod 1 (isbinopfun f) (ismultilinear f)
                             (isapropisbinopfun f) _).
  do 3 (apply (impred 1 _); intros ?).
  apply setproperty.
Defined.

Definition multimodulefun {I : UU} {rings : I -> ring}
           (MM NN : multimodule rings) : UU := ∑ f : MM -> NN, ismultimodulefun f.

Definition make_multimodulefun {I : UU} {rings : I -> ring}
           {MM NN : multimodule rings} (f : MM -> NN) (is : ismultimodulefun f) :
  multimodulefun MM NN := tpair _ f is.

Definition pr1multimodulefun {I : UU} {rings : I -> ring}
           {MM NN : multimodule rings} (f : multimodulefun MM NN) : MM -> NN := pr1 f.

Coercion pr1multimodulefun : multimodulefun >-> Funclass.

Definition multimodulefun_to_isbinopfun {I : UU} {rings : I -> ring}
           {MM NN : multimodule rings} (f : multimodulefun MM NN) :
  isbinopfun f := pr12 f.

Definition multimodulefun_to_binopfun {I : UU} {rings : I -> ring}
           {MM NN : multimodule rings} (f : multimodulefun MM NN) :
  binopfun MM NN := make_binopfun (pr1multimodulefun f)
                                   (multimodulefun_to_isbinopfun f).

Definition multimodulefun_to_ith_islinear {I : UU} {rings : I -> ring}
           {MM NN : multimodule rings} (f : multimodulefun MM NN) (i : I) :
  islinear (M := ith_module MM i) (N := ith_module NN i) f := pr22 f i.

Definition multimodulefun_to_ith_linearfun {I : UU} {rings : I -> ring}
           {MM NN : multimodule rings} (f : multimodulefun MM NN) (i : I) :
  linearfun (ith_module MM i) (ith_module NN i) :=
  make_linearfun (M := ith_module MM i) (N := ith_module NN i) f (multimodulefun_to_ith_islinear f i).

Definition ith_modulefun {I : UU} {rings : I -> ring} {MM NN : multimodule rings}
           (f : multimodulefun MM NN) (i : I) :
  modulefun (ith_module MM i) (ith_module NN i)
  := make_modulefun _
    (make_ismodulefun (M := ith_module MM i) (N := ith_module NN i) (multimodulefun_to_isbinopfun f) (multimodulefun_to_ith_islinear f i)).

(** * 3. Properties of the ring actions *)

Definition multimodule_ith_mult {I : UU} {rings : I -> ring}
           (MM : multimodule rings) (i : I) : (rings i) -> MM -> MM :=
  @module_mult (rings i) (ith_module MM i).

(** If you take the underlying group of the ith module, its the same as the
    underlying group of the multimodule. *)
Definition multimodule_same_abgrp {I : UU} {rings : I -> ring}
  (MM : multimodule rings) (i : I)
  : (MM : abgr) = (ith_module MM i)
  := idpath _.

(** Multiplying something by 0 always gives you the identity.
    Equationally, 0R * x = 0G for all x. *)
Definition multimodule_ith_mult_0_to_0 {I : UU} {rings : I -> ring}
           {MM : multimodule rings} (i : I) (x : MM) :
  multimodule_ith_mult MM i (@ringunel1 (rings i)) x = @unel MM :=
  @module_mult_0_to_0 (rings i) (ith_module MM i) x.

Definition multimodulefun_unel {I : UU} {rings : I -> ring}
  {MM NN : multimodule rings} (f : multimodulefun MM NN)
  : f (unel MM) = unel NN
  := binopfun_preserves_unit f (multimodulefun_to_isbinopfun _).
