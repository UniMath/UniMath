(** Authors Langston Barrett (@siddharthist), November-December 2017 *)

Require Import UniMath.Algebra.Modules.Core.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.Sets.

(** ** Contents
- Definitions
 - Propositions
- Multimodule morphisms
 - Multilinearity
 - Multimodule morphisms
*)

(** ** Definitions *)

(** The definition of a compatible R-S-bimodule structure is phrased in
    terms of associativity for left and right actions, (rm)s=r(ms). Modulo
    notation, this is really a statement about the actions intertwining one
    another. More generally, we can define a multimodule based on every action
    being compatible.

   Definition from Algebra by Bourbaki, II §1, no. 14.
 *)
Definition arecompatibleactions {R S G}
           (mr : module_struct R G) (ms : module_struct S G) :=
  let m1 := module_mult (G,, mr) in
  let m2 := module_mult (G,, ms)
  in ∏ (r1 : R) (r2 : S), (m1 r1 ∘ m2 r2 = m2 r2 ∘ m1 r1)%functions.

Definition multimodule_struct {I : UU} {rngs : I -> rng} {G : abgr}
           (structs : ∏ i : I, module_struct (rngs i) G) :=
  ∏ (i1 i2 : I) (ne : (i1 = i2) -> False),
    arecompatibleactions (structs i1) (structs i2).

Definition multimodule {I : UU} (rngs : I -> rng) : UU
  := ∑ G (ms : ∏ i : I, module_struct (rngs i) G), multimodule_struct ms.

(** We define a few things in the same way for multimodules as we did for modules *)

Definition pr1multimodule {I : UU} {rngs : I -> rng} (MM : multimodule rngs) : abgr
  := pr1 MM.

Coercion pr1multimodule : multimodule >-> abgr.

Definition pr2multimodule {I : UU} {rngs : I -> rng} (MM : multimodule rngs)
  : ∏ i : I, module_struct (rngs i) (pr1multimodule MM) := (pr1 (pr2 MM)).

Definition pr3bimodule {I : UU} {rngs : I -> rng} (MM : multimodule rngs)
  : multimodule_struct (pr2multimodule MM) := (pr2 (pr2 MM)).

Definition ith_module {I : UU} {rngs : I -> rng} (MM : multimodule rngs) (i : I)
  : module (rngs i) := (pr1multimodule MM,, pr2multimodule MM i).

(** **** Propositions *)

Lemma isaproparecompatibleactions
      {R S G} (mr : module_struct R G) (ms : module_struct S G) :
  isaprop (arecompatibleactions mr ms).
Proof.
  apply (impredtwice 1); intros r s.

  (* We'll prove that all the homotopies are identical *)
  apply (isofhlevelweqb 1
         (Y := (module_mult (G,, mr) r ∘ module_mult (G,, ms) s ~
                module_mult (G,, ms) s ∘ module_mult (G,, mr) r))).
  apply invweq.
  apply weqfunextsec.

  apply (impred 1); intros x.
  apply (pr2 (pr1 (pr1 G))).
Defined.

Lemma isapropmultimodule_struct {I : UU} {rngs : I -> rng} {G : abgr}
                                (structs : ∏ i : I, module_struct (rngs i) G) :
  isaprop (multimodule_struct structs).
Proof.
  apply (impredtwice 1); intros i1 i2.
  apply impredfun.
  apply isaproparecompatibleactions.
Defined.

(** *** Multimodule morphisms *)

(** **** Multilinearity*)

(** A function is multilinear precisely when it is linear for each module *)

Definition ismultilinear {I : UU} {rngs : I -> rng} {MM NN : multimodule rngs} (f : MM -> NN)
  := ∏ i : I, @islinear (rngs i) (ith_module MM i) (ith_module NN i) f.

Definition multilinearfun {I : UU} {rngs : I -> rng} (MM NN : multimodule rngs)
  : UU := ∑ f : MM -> NN, ismultilinear f.

Definition multilinearfunpair {I : UU} {rngs : I -> rng} {MM NN : multimodule rngs}
           (f : MM -> NN) (is : ismultilinear f) : multilinearfun MM NN
  := tpair _ f is.

Definition pr1multilinearfun {I : UU} {rngs : I -> rng} {MM NN : multimodule rngs}
           (f : multilinearfun MM NN) : MM -> NN := pr1 f.

Coercion pr1multilinearfun : multilinearfun >-> Funclass.

Definition ith_linearfun {I : UU} {rngs : I -> rng} {MM NN : multimodule rngs}
           (f : multilinearfun MM NN) (i : I) :
  linearfun (ith_module MM i) (ith_module NN i) :=
  (pr1 f,, pr2 f i).

Definition ismultilinearfuncomp {I : UU} {rngs : I -> rng}
           {MM NN PP : multimodule rngs} (f : multilinearfun MM NN)
           (g : multilinearfun NN PP) : ismultilinear (pr1 g ∘ pr1 f)%functions :=
  (fun i => islinearfuncomp (ith_linearfun f i) (ith_linearfun g i)).

Definition multilinearfuncomp {I : UU} {rngs : I -> rng}
           {MM NN PP : multimodule rngs} (f : multilinearfun MM NN)
           (g : multilinearfun NN PP) : multilinearfun MM PP :=
  (funcomp f g,, ismultilinearfuncomp f g).

(** **** Multimodule morphisms *)

Definition ismultimodulefun {I : UU} {rngs : I -> rng}
           {MM NN : multimodule rngs} (f : MM -> NN) : UU :=
   (isbinopfun f) × (ismultilinear f).

Lemma isapropismultimodulefun {I : UU} {rngs : I -> rng}
      {MM NN : multimodule rngs} (f : MM -> NN) : isaprop (ismultimodulefun f).
Proof.
  refine (@isofhleveldirprod 1 (isbinopfun f) (ismultilinear f)
                             (isapropisbinopfun f) _).
  do 3 (apply (impred 1 _); intros ?).
  apply setproperty.
Defined.

Definition multimodulefun {I : UU} {rngs : I -> rng}
           (MM NN : multimodule rngs) : UU := ∑ f : MM -> NN, ismultimodulefun f.

Definition multimodulefunpair {I : UU} {rngs : I -> rng}
           {MM NN : multimodule rngs} (f : MM -> NN) (is : ismultimodulefun f) :
  multimodulefun MM NN := tpair _ f is.

Definition pr1multimodulefun {I : UU} {rngs : I -> rng}
           {MM NN : multimodule rngs} (f : multimodulefun MM NN) : MM -> NN := pr1 f.

Coercion pr1multimodulefun : multimodulefun >-> Funclass.

Definition ith_modulefun {I : UU} {rngs : I -> rng} {MM NN : multimodule rngs}
           (f : multimodulefun MM NN) (i : I) :
  modulefun (ith_module MM i) (ith_module NN i) :=
  (pr1 f,, (dirprodpair (pr1 (pr2 f)) (pr2 (pr2 f) i))).

Definition multimodulefun_to_isbinopfun {I : UU} {rngs : I -> rng}
           {MM NN : multimodule rngs} (f : multimodulefun MM NN) :
  isbinopfun (pr1multimodulefun f) := pr1 (pr2 f).

Definition multimodulefun_to_binopfun {I : UU} {rngs : I -> rng}
           {MM NN : multimodule rngs} (f : multimodulefun MM NN) :
  binopfun MM NN := binopfunpair (pr1multimodulefun f)
                                   (multimodulefun_to_isbinopfun f).

Definition multimodulefun_to_ith_islinear {I : UU} {rngs : I -> rng}
           {MM NN : multimodule rngs} (f : multimodulefun MM NN) (i : I) :
  islinear (ith_modulefun f i) := pr2 (pr2 (ith_modulefun f i)).

Definition multimodulefun_to_ith_linearfun {I : UU} {rngs : I -> rng}
           {MM NN : multimodule rngs} (f : multimodulefun MM NN) (i : I) :
  linearfun (ith_module MM i) (ith_module NN i) :=
  linearfunpair (ith_modulefun f i) (multimodulefun_to_ith_islinear f i).

(** Properties of the ring actions *)

Definition multimodule_ith_mult {I : UU} {rngs : I -> rng}
           (MM : multimodule rngs) (i : I) : (rngs i) -> MM -> MM :=
  @module_mult (rngs i) (ith_module MM i).

(** If you take the underlying group of the ith module, its the same as the
    underlying group of the multimodule. *)
Lemma multimodule_same_abgrp {I : UU} {rngs : I -> rng}
      (MM : multimodule rngs) (i : I) : @eq abgr MM (ith_module MM i).
Proof.
  reflexivity.
Defined.

(** Multiplying something by 0 always gives you the identity.
    Equationally, 0R * x = 0G for all x. *)
Definition multimodule_ith_mult_0_to_0 {I : UU} {rngs : I -> rng}
           {MM : multimodule rngs} (i : I) (x : MM) :
  multimodule_ith_mult MM i (@rngunel1 (rngs i)) x = @unel MM :=
  @module_mult_0_to_0 (rngs i) (ith_module MM i) x.

(* TODO *)
Definition multimodulefun_unel {I : UU} {rngs : I -> rng}
           {MM NN : multimodule rngs} (f : multimodulefun MM NN) :
  f (unel MM) = unel NN.
Abort.