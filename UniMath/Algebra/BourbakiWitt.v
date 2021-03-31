
(** * The Bourbaki-Witt theorem and variants

This file aims to state and develop the Bourbaki-Witt and Tarski fixed-point theorems and their variants, especially constructively provable ones.

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

(** ** Completeness properties *)

Section LeastUpperBounds.

  (* We use the treatment of upper bounds from [Algebra.Dcpo], but give a slightly different treatment of _least_ upper bounds,
   factoring out the general definition of “least elements” of a family, or satisfying a predicate. *)

  Context {P : Poset}.

  Definition islowerbound {I} (p : I -> P) (x : P) : UU
  := ∏ (i : I), x ≤ p i.

  Definition least_of_family {I} (p : I -> P)
  := ∑ i : I, islowerbound p (p i).

  Definition least_of_family_index {I} {p : I -> P}
    : least_of_family p -> I
  := pr1.
  (* Would be nice to make [least_of_family_index] a coercion, but can’t since its target is an arbitrary type. The best we can do instead is [realise_least_of_family]: *)
  Coercion realise_least_of_family {I} (p : I -> P)
    : least_of_family p -> P
  := fun ih => p (pr1 ih).

  Definition least_is_least {I}  (p : I -> P) (x : least_of_family p)
    : islowerbound p x
  := pr2 x.

  Definition least_suchthat (A : P -> UU) : UU
  := least_of_family (pr1 : (∑ x:P, A x) -> P).

  Identity Coercion id_least_suchthat : least_suchthat >-> least_of_family.

  Definition least_suchthat_satisfies {A : P -> UU} (x : least_suchthat A)
      : A x
  := pr2 (least_of_family_index x).

  Definition least_upper_bound {I} (p : I -> P)
  := least_suchthat (isupperbound p).

End LeastUpperBounds.

Section Chains.

  Definition comparable {P : Poset} (x y : P) : hProp
  := (x ≤ y) ∨ (y ≤ x).

  Definition is_chain {P : Poset} {I} (p : I -> P) : UU
  := ∏ i j : I, comparable (p i) (p j).

  Definition Chain (P : Poset) : UU
  := ∑ A : hsubtype P, is_chain (pr1carrier A).

  Coercion Chain_hsubtype {P} : Chain P -> hsubtype P
  := pr1.

  Definition chain_is_chain {P} (C : Chain P) : is_chain (pr1carrier C)
  := pr2 C.

  Definition chain_family {P} (C : Chain P)
  := pr1carrier C.

End Chains.

Section Completeness.

  Definition is_chain_complete (P : Poset) : UU
  := ∏ C : Chain P, least_upper_bound (chain_family C).

  (* [is_chain_complete] is defined just in terms of hsubtype-chains, to agree with the classical definition and keep its quantification “small”.

  However, it implies least upper bounds for arbitarily-indexed chains. *)

  Definition chain_lub {P : Poset} (P_CC : is_chain_complete P)
      {I} (p : I -> P) (p_chain : is_chain p)
    : least_upper_bound p.
  Proof.
    set (p_hsubtype := fun x : P => ∥ hfiber p x ∥).
    assert (p_hsubtype_chain : is_chain (pr1carrier p_hsubtype)).
    { intros [x Hx] [y Hy]. simpl pr1carrier.
      refine (factor_through_squash_hProp _ _ Hx);
        intros [i e_ix]; destruct e_ix.
      refine (factor_through_squash_hProp _ _ Hy);
        intros [j e_jy]; destruct e_jy.
      apply p_chain.
    }
    set (p_Chain := (p_hsubtype ,, p_hsubtype_chain) : Chain P).
    assert (same_upper_bounds
      : ∏ x:P, isupperbound p x <-> isupperbound (pr1carrier p_hsubtype) x).
    { intros x; split.
      - intros x_ub [y Hy].
        refine (factor_through_squash_hProp _ _ Hy);
          intros [j e_jy]; destruct e_jy.
        apply x_ub.
      - intros x_ub y.
        refine (x_ub (p y,, hinhpr (y,, idpath _) )).
    }
    set (lub_p := P_CC p_Chain).
    destruct lub_p as [[x x_ub] x_least]. simpl in x_least.
    use tpair. { exists x. apply same_upper_bounds, x_ub. }
    simpl. intros [y y_ub].
    simpl. refine (x_least (y,, _)).
    apply same_upper_bounds, y_ub.
  Defined.
  (* TODO: could we usefully factor out some of the properties of the image used here, e.g. by factoring [image] via [hsubtype], and giving the universal property of the image as such? *)

End Completeness.

(** ** Bourbaki-Witt for various classes of posets

The classical Bourbaki–Witt theorem says: Any progressive map on a chain-complete partial order has a fixed point.

Constructively, this may fail, as shown in Bauer–Lumsdaine https://arxiv.org/abs/1201.0340. Here we aim to give both the classical theorem, and some weaker constructively-provable results.

*)

Section Bourbaki_Witt.

(* This is a strong form of the Bourbaki–Witt property, supplying a specific fixed point. *)
Definition Bourbaki_Witt_property (P : Poset)
  := ∏ (f : Progressive_map P), Fixedpoint f.

(* A weaker form of the Bourbaki–Witt property asserts mere existence of a fixed point. *)
Definition weak_Bourbaki_Witt_property (P : Poset)
  := ∏ (f : Progressive_map P), ∥ Fixedpoint f ∥ .

Theorem classical_Bourbaki_Witt
  : LEM -> ∏ P : Poset, is_chain_complete P -> Bourbaki_Witt_property P.
Proof.
  (* Proof sketch:
  Let C be the least subset closed under f and suprema of chains.
  It suffices to show that C is a chain; then its supremum must be a fixed point.
  To see C is a chain:

  Say x:C is “good” if every element of C is either ≤ or ≥ X.

  To show all x:C are good, it suffices to show the good elements are closed under f and suprema of chains.

  Say x good.  NTS: f(x) good.  Now just need to show: the elements comparable to f(x) are closed under f and suprema of chains.  This is be direct.

  Say X is a chain of good elements.  Now NTS: sup(X) is good.  Again, show the *)
Abort.


End Bourbaki_Witt.
