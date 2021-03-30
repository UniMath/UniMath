
(** * The Bourbaki-Witt theorem and variants

This file aims to state and develop the Bourbaki-Witt theorem and its variants, especially constructively provable ones.

In particular, it aims to formalise some of the results of Pataraia, Dacar, Bauer, and Lumsdaine, given in https://arxiv.org/abs/1201.0340 .

Note: There is some duplication with material in [Algebra.Dcpo] and [Combinatorics.WellOrderedSets], which should ideally be refactored (as indeed there is some ducplication between between those files).
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.WellOrderedSets.
Require Import UniMath.Algebra.Dcpo.

Local Open Scope poset. (* So we can write ≤ *)


(** ** Progressive maps

Progressive maps as also known as ascending, inflationary, and more.

Note these are just endo-_functions_, not “maps” in the sense of morphisms of posets. *)

Section ProgressiveMaps.

Definition isprogressive {P : Poset} (f : P -> P) : UU
  := ∏ (x : P), x ≤ f x.

Lemma isaprop_isprogressive {P : Poset} (f : P -> P) : isaprop (isprogressive f).
Proof.
  apply impred_isaprop; intro i; apply propproperty.
Qed.

(* TODO: refactor to use [hsubtype] & [carrier], to make relevant lemmas applicable? *)
Definition Progressive_map (P : Poset)
  := ∑ (f : P -> P), isprogressive f.

Definition pr1_Progressive_map {P : Poset}
  : Progressive_map P -> (P -> P)
:= pr1.
Coercion pr1_Progressive_map : Progressive_map >-> Funclass.

Definition isprogressive_Progressive_map {P} (f : Progressive_map P)
  : isprogressive f
:= pr2 f.

End ProgressiveMaps.


(** ** Fixpoints of endofunctions *)

Section Fixpoints.

(* TODO: refactor to [hsubtype]? *)
Definition Fixedpoint {P : Poset} (f : P -> P) : UU
  := ∑ (x:P), f x = x.

Coercion pr1_Fixedpoint {P : Poset} {f : P -> P}
  : Fixedpoint f -> P
:= pr1.

Definition isfixed_Fixedpoint  {P : Poset} {f : P -> P} (x : Fixedpoint f)
  : f x = x
:= pr2 x.

End Fixpoints.

(** ** Bourbaki-Witt for various classes of posets

Classically, B–W holds for all chain-complete partial orders. *)

Section Bourbaki_Witt.

(* This is a strong form of the Bourbaki–Witt property, supplying a specific fixed point. *)
Definition Bourbaki_Witt_property (P : Poset)
  := ∏ (f : Progressive_map P), Fixedpoint f.

(* A weaker form of the Bourbaki–Witt property asserts mere existence of a fixed point. *)
Definition weak_Bourbaki_Witt_property (P : Poset)
  := ∏ (f : Progressive_map P), ∥ Fixedpoint f ∥ .

Theorem classical_Bourbaki_Witt
  : LEM -> ∏ P : Poset, Bourbaki_Witt_property P.
Abort.

End Bourbaki_Witt.
