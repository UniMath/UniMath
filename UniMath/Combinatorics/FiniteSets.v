(** * Finite sets. Vladimir Voevodsky . Apr. - Sep. 2011.

    This file contains the definition and main properties of finite sets. In the
    file [Combinatorics/Tests.v] there are several elementary examples which are
    used as test cases to check that our constructions do not prevent Coq from
    normalizing terms of type nat to numerals.
 *)

(** ** Preamble *)

(** Imports. *)

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.DecidablePropositions.
Require Import UniMath.MoreFoundations.NegativePropositions.
Require Export UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.MoreFoundations.Subtypes.

Local Open Scope stn.

(** ** Sets with a given number of elements. *)

Section nelstructure.
  (** *** Structure of a set with [n] elements on [X] defined as a term in [⟦ n ⟧ ≃ X].  *)

  Definition nelstruct (n : nat) (X : UU) : UU
    := ⟦ n ⟧ ≃ X.

  Definition nelstructToFunction {n : nat} {X : UU} (S : nelstruct n X)
    : ⟦ n ⟧ -> X
    := pr1weq S.

  Coercion nelstructToFunction : nelstruct >-> Funclass.

  Definition nelstructonstn (n : nat) : nelstruct n (⟦ n ⟧)
    := idweq (⟦ n ⟧).

  Definition nelstructweqf {X Y : UU} {n : nat}
    (w : X ≃ Y) (sx : nelstruct n X)
    : nelstruct n Y
    := weqcomp sx w.

  Definition nelstructweqb {X Y : UU} {n : nat}
    (w : X ≃ Y) (sy : nelstruct n Y)
    : nelstruct n X
    := weqcomp sy (invweq w).

  Definition nelstructonempty : nelstruct 0 empty
    := weqstn0toempty.

  Definition nelstructonempty2 {X : UU} (nx : neg X)
    : nelstruct 0 X
    := weqcomp weqstn0toempty (invweq (weqtoempty nx)).

  Definition nelstructonunit : nelstruct 1 unit
    := weqstn1tounit.

  Definition nelstructoncontr {X : UU} (contrx : iscontr X)
    : nelstruct 1 X
    := weqcomp weqstn1tounit (invweq (weqcontrtounit contrx)).

  Definition nelstructonbool : nelstruct 2 bool := weqstn2tobool.

  Definition nelstructoncoprodwithunit {X : UU} {n : nat}
    (sx : nelstruct n X)
    : nelstruct (S n) (X ⨿ unit)
    := weqcomp (invweq (weqdnicoprod n lastelement)) (weqcoprodf1 sx).

  Definition nelstructoncompl {X : UU} {n : nat}
    (x : X)
    : nelstruct (S n) X -> nelstruct n (compl X x).
  Proof.
    intros sx.
    refine (invweq (weqoncompl (invweq sx) x) ∘ _ ∘ weqdnicompl (invweq sx x))%weq.
    apply compl_weq_compl_ne.
  Defined.

  Definition nelstructoncoprod {X Y : UU} {n m : nat}
    (sx : nelstruct n X)
    (sy : nelstruct m Y)
    : nelstruct (n + m) (X ⨿ Y)
    := ((weqcoprodf sx sy) ∘ (invweq (weqfromcoprodofstn n m)))%weq.

  Definition nelstructontotal2 {X : UU} {n : nat} (P : X -> UU)
    (f : X -> nat)
    (sx : nelstruct n X)
    (fs : ∏ x : X, nelstruct (f x) (P x))
    : nelstruct (stnsum (f ∘ sx)) (∑ (y : X), P y)
    := weqcomp
         (invweq (weqstnsum (P ∘ sx) (f ∘ sx) (fs ∘ sx)))
         (weqfp sx P).

  Definition nelstructondirprod {X Y : UU} {n m : nat}
    (sx : nelstruct n X)
    (sy : nelstruct m Y)
    : nelstruct (n * m) (X × Y)
    := (weqdirprodf sx sy ∘ invweq (weqfromprodofstn n m))%weq.

  (** For a generalization of [ weqfromdecsubsetofstn ] see below *)

  Definition nelstructonfun {X Y : UU} {n m : nat}
    (sx : nelstruct n X)
    (sy : nelstruct m Y)
    : nelstruct (natpower m n) (X -> Y)
    := (weqbfun Y (invweq sx) ∘ weqffun (⟦ n ⟧) sy ∘ invweq (weqfromfunstntostn n m))%weq.

  Definition nelstructonforall {X : UU} {n : nat} (P : X -> UU)
    (f : X -> nat)
    (sx : nelstruct n X)
    (fs : ∏ x : X , nelstruct (f x) (P x))
    : nelstruct (stnprod (f ∘ sx)) (∏ x : X , P x)
    := invweq (weqcomp
                 (weqonsecbase P sx)
                 (weqstnprod (P ∘ sx) (f ∘ sx) (λ i : ⟦ n ⟧, fs (sx i)))).

  Definition nelstructonweq {X : UU} {n : nat}
    (sx : nelstruct n X)
    : nelstruct (factorial n) (X ≃ X)
    := (weqfweq X sx ∘ weqbweq (⟦ n ⟧) (invweq sx) ∘ invweq (weqfromweqstntostn n))%weq.
End nelstructure.

Section nelproperty.

  (** *** The property of [ X ] to have [ n ] elements *)

  Definition isofnel (n : nat) (X : UU) : hProp
    := ∥ ⟦ n ⟧ ≃  X ∥.

  Definition isofneluniv {n : nat} {X : UU}  (P : hProp)
    : ((nelstruct n X) -> P) -> (isofnel n X -> P).
  Proof.
    intros pnel xofnel.
    exact(hinhuniv pnel xofnel).
  Defined.

  Definition isofnelstn (n : nat) : isofnel n (⟦ n ⟧)
    := hinhpr (nelstructonstn n).

  Definition isofnelweqf {X Y : UU} {n : nat}
    (w : X ≃ Y) (sx : isofnel n X)
    : isofnel n Y
    := hinhfun (nelstructweqf w) sx.

  Definition isofnelweqb {X Y : UU} {n : nat}
    (w : X ≃ Y) (sy : isofnel n Y)
    : isofnel n X
    := hinhfun (nelstructweqb w) sy.

  Definition isofnelempty : isofnel 0 empty
    := hinhpr nelstructonempty.

  Definition isofnelempty2 {X : UU} (nx : neg X) : isofnel 0 X
    := hinhpr (nelstructonempty2 nx).

  Definition isofnelunit : isofnel 1 unit
    := hinhpr nelstructonunit.

  Definition isofnelcontr {X : UU} (contrx : iscontr X) : isofnel 1 X
    := hinhpr (nelstructoncontr contrx).

  Definition isofnelbool : isofnel 2 bool
    := hinhpr nelstructonbool.

  Definition isofnelcoprodwithunit {X : UU} {n : nat}
    (sx : isofnel n X)
    : isofnel (S n) (X ⨿ unit)
    := hinhfun nelstructoncoprodwithunit sx.

  Definition isofnelcompl {X : UU} {n : nat}
    (x : X) (sx : isofnel (S n) X)
    : isofnel n (compl X x)
    := hinhfun (nelstructoncompl x) sx.

  Definition isofnelcoprod {X Y : UU} {n m : nat}
    (sx : isofnel n X) (sy : isofnel m Y)
    : isofnel (n + m) (X ⨿ Y)
    := hinhfun2 nelstructoncoprod sx sy.

  (** For a result corresponding to [ nelstructontotal2 ] see below . *)

  Definition isofnelondirprod {X Y : UU} {n m : nat}
    (sx : isofnel n X) (sy : isofnel m Y)
    : isofnel (n * m) (X × Y)
    := hinhfun2 nelstructondirprod sx sy.

  Definition isofnelonfun {X Y : UU} {n m : nat}
    (sx : isofnel n X) (sy : isofnel m Y)
    : isofnel (natpower m n) (X -> Y)
    := hinhfun2 nelstructonfun sx sy.

  (** For a result corresponding to [ nelstructonforall ] see below . *)

  Definition isofnelonweq {X : UU} {n : nat}
    (sx : isofnel n X)
    : isofnel (factorial n) (X ≃ X)
    := hinhfun nelstructonweq sx.
End nelproperty.

(** ** General finite sets. *)

Section finite_structure.
  (** *** Finite structure.

      A finite structure on a type [X] is defined as a pair [( n , w )]
      where [n : nat] and [w : ⟦ n ⟧ ≃ X]. *)

  Definition finstruct  (X : UU) : UU
    := ∑ (n : nat), nelstruct n X.

  Definition finstruct_cardinality {X : UU}
    (fs : finstruct X) : nat
    := pr1 fs.

  Definition finstructToFunction {X : UU} (S : finstruct X) : nelstruct (pr1 S) X
    := pr2 S.
  Coercion finstructToFunction : finstruct >-> nelstruct.

  Definition make_finstruct (X : UU) {n : nat} (w : ⟦ n ⟧ ≃ X) : finstruct X
    := (n ,, w).

  Definition finstructonstn (n : nat) : finstruct (⟦ n ⟧)
    := make_finstruct _ (nelstructonstn n).

  Definition finstructweqf {X Y : UU} (w : X ≃ Y) (sx : finstruct X)
    : finstruct Y
    := make_finstruct Y (nelstructweqf w sx).

  Definition finstructweqb {X Y : UU} (w : X ≃ Y) (sy : finstruct Y)
    : finstruct X
    := make_finstruct X (nelstructweqb w sy).

  Definition finstructonempty : finstruct empty
    := make_finstruct empty nelstructonempty.

  Definition finstructonempty2 {X : UU} (nx : neg X)
    : finstruct X
    := make_finstruct X (nelstructonempty2 nx).

  Definition finstructonunit : finstruct unit
    := make_finstruct unit nelstructonunit.

  Definition finstructoncontr {X : UU} (xcontr : iscontr X)
    : finstruct X
    := make_finstruct X (nelstructoncontr xcontr).

  (** It is not difficult to show that a direct summand of a finite set is a finite set. As a
    corrolary it follows that a proposition (a type of h-level 1) is a finite set if and only if it
    is decidable . *)

  Definition finstructonbool : finstruct bool
    := make_finstruct bool nelstructonbool.

  Definition finstructoncoprodwithunit {X : UU}
    (sx : finstruct X)
    : finstruct (X ⨿ unit)
    := make_finstruct (X ⨿ unit) (nelstructoncoprodwithunit sx).

  Definition finstructoncompl {X : UU} (x : X) (sx : finstruct X) : finstruct (compl X x).
  Proof.
    destruct sx as [n w].
    induction n as [| n ].
    - exact(fromempty (negstn0 (invweq w x))).
    - exact(make_finstruct (compl X x) (nelstructoncompl x w)).
  Defined.

  Definition finstructoncoprod {X Y : UU}
    (sx : finstruct X) (sy : finstruct Y)
    : finstruct (X ⨿ Y)
    := make_finstruct (X ⨿ Y) (nelstructoncoprod sx sy).

  Definition finstructontotal2 {X : UU} (P : X -> UU)
    (sx : finstruct X)
    (fs : ∏ x : X, finstruct (P x))
    : finstruct (∑ (x : X), P x)
    := make_finstruct _
         (nelstructontotal2 P
            (λ x : X, finstruct_cardinality (fs x))
            sx
            (λ x : X, fs x)).

  Definition finstructondirprod {X Y : UU}
    (sx : finstruct X) (sy : finstruct Y)
    : finstruct (X × Y)
    := make_finstruct (X × Y) (nelstructondirprod sx sy).

  Definition finstructondecsubset {X : UU}
    (f : X -> bool) (sx : finstruct X)
    : finstruct (hfiber f true)
    := make_finstruct _  (weqcomp (invweq (pr2 (weqfromdecsubsetofstn (f ∘ sx))))
                            (weqhfibersgwtog _ f true)).

  Definition finstructonfun {X Y : UU}
    (sx : finstruct X) (sy : finstruct Y)
    : finstruct (X -> Y)
    := make_finstruct _ (nelstructonfun sx sy).

  Definition finstructonforall {X : UU} (P : X -> UU)
    (sx : finstruct X)
    (fs : ∏ x : X , finstruct (P x))
    : finstruct (∏ x : X , P x)
    := make_finstruct _
         (nelstructonforall P _ sx fs).

  Definition finstructonweq {X : UU}
    (sx : finstruct X)
    : finstruct (X ≃ X)
    := make_finstruct (X ≃ X) (nelstructonweq sx).
End finite_structure.


Section finite_property.
  (** *** Finite types.

      A type [X] is finite if it is merely equipped with some finite
      structure.
   *)

  Definition isfinite (X : UU) : hProp
    := ∥ finstruct X ∥.

  Definition isfinite_isdeceq (X : UU)
    : isfinite X -> isdeceq X.
  (* uses funextemptyAxiom *)
  Proof.
    intros isfin.
    use(factor_through_squash (isapropisdeceq X) _ isfin).
    intro fstruct.
    use(isdeceqweqf _ (isdeceqstn (finstruct_cardinality fstruct))).
    apply fstruct.
  Defined.

  Definition isfinite_isaset (X : UU) : isfinite X -> isaset X.
  Proof.
    intros isfin.
    use(factor_through_squash (isapropisaset X) _ isfin).
    intros f.
    use(isofhlevelweqf 2 _ (isasetstn (finstruct_cardinality f))).
    apply f.
  Defined.

  Definition fincard {X : UU} (xf : isfinite X) : nat.
  Proof.
    apply (squash_pairs_to_set (λ n : nat, ⟦ n ⟧ ≃ X) isasetnat).
    {
      intros n n' w w'.
      apply weqtoeqstn.
      exact (invweq w' ∘ w)%weq.
    }
    assumption.
  Defined.

  Definition ischoicebasefiniteset {X : UU} (xf : isfinite X) : ischoicebase X.
  Proof.
    use(hinhuniv _ xf).
    intros [n w].
    exact(ischoicebaseweqf w (ischoicebasestn n)).
  Defined.

  Definition isfinitestn (n : nat) : isfinite (⟦ n ⟧)
    := hinhpr (finstructonstn n).

  Definition isfiniteweqf {X Y : UU} (w : X ≃ Y) (sx : isfinite X)
    : isfinite Y
    := hinhfun (finstructweqf w) sx.

  Definition isfiniteweqb {X Y : UU} (w : X ≃ Y) (sy : isfinite Y)
    : isfinite X
    := hinhfun (finstructweqb w) sy.

  Definition isfiniteempty : isfinite empty
    := hinhpr finstructonempty.

  Definition isfiniteempty2 {X : UU} (nx : neg X)
    : isfinite X
    := hinhpr (finstructonempty2 nx).

  Definition isfiniteunit : isfinite unit
    := hinhpr finstructonunit.

  Definition isfinitecontr {X : UU} (contrx : iscontr X)
    : isfinite X
    := hinhpr (finstructoncontr contrx).

  Definition isfinitebool : isfinite bool
    := hinhpr finstructonbool.

  Definition isfinitecoprodwithunit {X : UU}
    (sx : isfinite X)
    : isfinite (X ⨿ unit)
    := hinhfun finstructoncoprodwithunit sx.

  Definition isfinitecompl {X : UU}
    (x : X) (sx : isfinite X)
    : isfinite (compl X x)
    := hinhfun (finstructoncompl x) sx.

  Definition isfinitecoprod {X Y : UU}
    (sx : isfinite X) (sy : isfinite Y)
    : isfinite (X ⨿ Y)
    := hinhfun2 finstructoncoprod sx sy.

  Definition isfinitetotal2 {X : UU}
    (P : X -> UU)
    (sx : isfinite X)
    (fs : ∏ x : X , isfinite (P x))
    : isfinite (∑ (x : X), P x).
  Proof.
    set (fs' := ischoicebasefiniteset sx _ fs).
    use(hinhfun2 _ fs' sx).
    intros.
    apply finstructontotal2;
      assumption.
  Defined.

  Definition isfinitedirprod {X Y : UU}
    (sx : isfinite X) (sy : isfinite Y)
    : isfinite (X × Y)
    := hinhfun2 finstructondirprod sx sy.

  Definition isfinitedecsubset {X : UU}
    (f : X -> bool)  (sx : isfinite X)
    : isfinite (hfiber f true)
    := hinhfun (finstructondecsubset f) sx.

  Definition isfinitefun {X Y : UU}
    (sx : isfinite X) (sy : isfinite Y)
    : isfinite (X -> Y)
    := hinhfun2 finstructonfun sx sy.

  Definition isfiniteforall {X : UU}
    (P : X -> UU)
    (sx : isfinite X)
    (fs : ∏ x : X , isfinite (P x))
    : isfinite (∏ (x : X) , P x).
  Proof.
    set (fs' := ischoicebasefiniteset sx _ fs).
    exact(hinhfun2 (fun a b => finstructonforall P b a) fs' sx).
  Defined.

  Definition isfiniteweq {X : UU} (sx : isfinite X) : isfinite (X ≃ X)
    := hinhfun finstructonweq sx.
End finite_property.
(*

(* The cardinality of finite sets using double negation and decidability of equality in nat. *)

   Definition carddneg  (X : UU) (fx: isfinite X) : nat
              := pr1 (isfiniteimplisfinite0 X fx).

Definition preweq  ( X : UU ) (is: isfinite X): isofnel (carddneg X is) X.
Proof. intros X is X0.  set (c:= carddneg X is). set (dnw:= pr2 (isfiniteimplisfinite0 X is)). simpl in dnw. change (pr1 nat (λ n : nat, isofnel0 n X) (isfiniteimplisfinite0 X is)) with c in dnw.

assert (f: dirprod (finitestruct X) (dneg (weq (stn c) X)) -> weq (stn c) X). intro H. destruct H as [ t x ].  destruct t as [ t x0 ].
assert (dw: dneg ((stn t) ≃ (stn c))). set (ff:= fun ab:dirprod (weq (stn t) X)(weq (stn c) X) => weqcomp _ _ _ (pr1 ab) (invweq (pr2 ab))).  apply (dnegf _ _ ff (inhdnegand _ _ (todneg _ x0) x)).
assert (e:t = c). apply (stnsdnegweqtoeq _ _  dw). clear dnw. destruct e. assumption. unfold isofnel.
apply (hinhfun _ _ f (hinhand (finitestruct X) _ is (hinhpr dnw))). Defined.

*)

(* to be completed

Theorem carddnegweqf (X Y:UU)(f: X -> Y)(isw:isweq f)(isx: isfinite X): paths  (carddneg _ isx) (carddneg _ (isfiniteweqf _ _ _ isw isx)).
Proof. intros. *)

(* The cardinality of finite sets defined using the "impredicative" ishinh *)

Definition isfinite_to_DecidableEquality {X : UU}
  : isfinite X -> DecidableRelation X.
Proof.
  intros fin x y.
  exact (@isdecprop_to_DecidableProposition
           (x=y)
           (isdecpropif (x=y)
              (isfinite_isaset X fin x y)
              (isfinite_isdeceq X fin x y))).
Defined.

Definition subsetFiniteness {X : UU} (is : isfinite X) (P : DecidableSubtype X)
  : isfinite (decidableSubtypeCarrier P).
Proof.
  intros.
  assert (fin : isfinite (decidableSubtypeCarrier' P)).
  { now apply isfinitedecsubset. }
  refine (isfiniteweqf _ fin).
  apply decidableSubtypeCarrier_weq.
Defined.

Definition fincard_subset {X : UU}
  (fx : isfinite X) (P : DecidableSubtype X)
  : nat
  := fincard (subsetFiniteness fx P).

Definition fincard_standardSubset {n : nat}
  (P : DecidableSubtype (⟦ n ⟧))
  : nat
  := fincard (subsetFiniteness (isfinitestn n) P).

Local Definition bound01 (P : DecidableProposition) : ((choice P 1 0) ≤ 1)%nat.
Proof.
  unfold choice.
  choose P p q;
    reflexivity.
Defined.

Definition tallyStandardSubset {n : nat}
  (P : DecidableSubtype (⟦ n ⟧))
  : ⟦ S n ⟧.
Proof.
  exists (stnsum (λ x, choice (P x) 1 0)).
  apply natlehtolthsn.
  apply (istransnatleh (m := stnsum(λ _ : stn n, 1))).
  {
    apply stnsum_le; intro i.
    apply bound01.
  }
  assert (p : ∏ r s : nat, r = s -> (r ≤ s)%nat).
  {
    intros ? ? e.
    destruct e.
    apply isreflnatleh.
  }
  apply p.
  exact(stnsum_1 n).
Defined.

Definition tallyStandardSubsetSegment {n : nat}
  (P : DecidableSubtype (⟦ n ⟧))
  (i : ⟦ n ⟧)
  : ⟦ n ⟧.
Proof.
  (* count how many elements less than i satisfy P *)
  assert (k := tallyStandardSubset
                 (λ j : ⟦ i ⟧, P (stnmtostnn i n (natlthtoleh i n (pr2 i)) j))).

  apply (stnmtostnn (S i) n).
  {
    apply natlthtolehsn.
    exact(pr2 i).
  }

  exact k.
Defined.

Section finite_subsets.
  Local Open Scope subtype.

  Definition finite_subset (X : hSet) : UU
    := ∑ (A : hsubtype X),
      isfinite (carrier A).

  Definition make_finite_subset {X : hSet} (A : hsubtype X) (P : isfinite (carrier A))
    : finite_subset X
    := (A ,, P).

  Definition subtype_from_finite_subset {X : hSet} (A : finite_subset X) : hsubtype X
    := pr1 A.
  Coercion subtype_from_finite_subset : finite_subset >-> hsubtype.

  Lemma isfinite_singleton {X : hSet} {x : X} : isfinite (singleton x).
  Proof.
    apply isfinitecontr.
    apply iscontr_singleton.
  Qed.

  Definition finite_singleton {X : hSet} (x : X) : finite_subset X.
  Proof.
    use make_finite_subset.
    - exact(singleton x).
    - exact isfinite_singleton.
  Defined.

  Definition finite_singleton_is_in {X : hSet}
    (A : hsubtype X)
    (a : A)
    : finite_singleton (pr1 a) ⊆ A.
  Proof.
    apply singleton_is_in.
  Defined.

End finite_subsets.

Section FiniteSets.
  Definition FiniteSet : UU
    := ∑ (X : UU), isfinite X.

  Definition isfinite_to_FiniteSet {X : UU} (f : isfinite X) : FiniteSet
    := X ,, f.

  Definition FiniteSet_to_hSet (X : FiniteSet) : hSet
    := make_hSet (pr1 X) (isfinite_isaset (pr1 X) (pr2 X)).
  Coercion FiniteSet_to_hSet : FiniteSet >-> hSet.

  Definition FiniteSetSum {I : FiniteSet} (X : I -> FiniteSet) : FiniteSet.
  Proof.
    intros. exists (∑ i, X i).
    apply isfinitetotal2.
    - exact (pr2 I).
    - exact (λ (i : I), pr2 (X i)).
  Defined.

  Definition cardinalityFiniteSet (X : FiniteSet) : nat
    := fincard (pr2 X).

  Definition standardFiniteSet (n : nat) : FiniteSet
    := isfinite_to_FiniteSet (isfinitestn n).

  Definition subsetFiniteSet {X : FiniteSet} (P : DecidableSubtype X)
    : FiniteSet.
  Proof.
    exact(isfinite_to_FiniteSet (subsetFiniteness (pr2 X) P)).
  Defined.
End FiniteSets.

Declare Scope finset.
Delimit Scope finset with finset.

Notation "'∑' x .. y , P" := (FiniteSetSum (λ x,.. (FiniteSetSum (λ y, P))..))
                               (at level 200, x binder, y binder, right associativity) : finset.
(* type this in emacs in agda-input method with \sum *)
