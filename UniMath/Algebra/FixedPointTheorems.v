
(** * Fixed-point theorems on posets

This file aims to state and develop various fixed-point theorems on posets; in particular, the classical Tarski, Bourbaki-Witt, and Knaster–Tarski fixed-point theorems and their variants, especially constructively provable ones.

In particular, it aims to formalise some of the results of Pataraia, Dacar, Bauer, and Lumsdaine, given in https://arxiv.org/abs/1201.0340 .

Note: There is some duplication with material on posets elsewhere in the library, e.g. [Algebra.Dcpo] and [Combinatorics.WellOrderedSets], which should ideally be refactored. (Indeed, there is some duplication of material also between those files.)
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.WellOrderedSets.
Require Import UniMath.Algebra.Dcpo.

Local Open Scope poset. (* for ≤, < *)
Local Open Scope logic. (* for logic in hProp *)
Local Open Scope subtype.


(** ** Overview *)
Section Overview.
(** The following are the main results of the file (stated for now with some black boxes, for concepts not yet defined).

In [Section Check_Overview] at the end of the file, we confirm that these statements have been proven. *)

  Context (is_complete : Poset -> UU)
          (is_directed_complete : Poset -> UU)
          (is_chain_complete : Poset -> UU)
          (Progressive_map : forall P:Poset, hsubtype (P -> P))
          (Postfixedpoint : forall P:Poset, (P -> P) -> hsubtype P)
          (Fixedpoint : forall P:Poset, (P -> P) -> hsubtype P).

  Arguments Postfixedpoint {_} _.
  Arguments Fixedpoint {_} _.

  (** The master form of the Tarski/Knaster fixed-point theorems:
  the fixed points of a monotone map on a complete poset
  are themselves complete. *)
  Definition Tarski_fixpoint_theorem_statement
    := forall (P:Poset) (P_complete : is_complete P) (f : posetmorphism P P),
         is_complete (Fixedpoint f : Subposet P).

  (** A constructive fixed-point theorem, due to Pataraia. *)
  Definition fixpoint_for_monotone_on_dcpo_statement
    := forall (P : Poset) (P_dir: is_directed_complete P)
              (f : posetmorphism P P) (x : Postfixedpoint f),
         ∑ y : Fixedpoint f, pr1 x ≤ pr1 y.

  (** Classical theorem, usually attrib. Bourbaki (1949) and Witt (1951). *)
  Definition Bourbaki_Witt_fixpoint_theorem_statement
    := LEM ->
     forall (P : Poset) (_ : is_chain_complete P) (f : Progressive_map P),
       Fixedpoint (pr1 f).

End Overview.

(** ** Background material

Material not really belonging to this file.

All could (?should) eventually be upstreamed, and (in a few cases) unified with overlapping material upstream. *)
Section Auxiliary.

(** *** Partial orders *)

Definition lt_to_nleq {P : Poset} {x y : P} : x < y ⇒ ¬ (y ≤ x).
Proof.
  intros [leq_xy neq_xy] leq_yx.
  apply neq_xy.
  apply isantisymm_posetRelation; assumption.
Defined.

Definition isrefl'_posetRelation {P : Poset} {x y : P} : x = y ⇒ x ≤ y.
Proof.
  intros e; destruct e. apply isrefl_posetRelation.
Defined.


(* [isaposetmorphism] is defined as in [Foundations.Sets], but (a) isn’t an hProp, and (b) lacks access function. *)

Definition isaposetmorphism_hProp {P Q : Poset} (f : P -> Q) : hProp
  := ∀ x x' : P, x ≤ x' ⇒ f x ≤ f x'.

Definition posetmorphism_property {P Q} (f : posetmorphism P Q)
  : isaposetmorphism f
:= pr2 f.

Lemma isaposetmorphism_idfun {P : Poset} : isaposetmorphism (idfun P).
Proof.
  intros ? ? ?; assumption.
Defined.

Lemma isaposetmorphism_compose {P P' P'' : Poset}
    {f : P -> P'} (f_monot : isaposetmorphism f)
    {g : P' -> P''} (g_monot : isaposetmorphism g)
  : isaposetmorphism (g ∘ f).
Proof.
  intros x y le_xy.
  apply g_monot, f_monot, le_xy.
Defined.

(** *** HProp logic *)

(* TODO: look for naming convention for similar lemmas *)
Definition hdisj_monot {p q p' q'} : (p ⇒ p') ⇒ (q ⇒ q') ⇒ (p ∨ q ⇒ p' ∨ q').
Proof.
  intros ? ?.
  apply hconjtohdisj; split; intro;
    auto using hdisj_in1, hdisj_in2.
Defined.

(** This order of arguments is often more convenient to use than the original [hdisj_monot] *)
(* TODO: consider naming *)
Definition hdisj_monot' {p q p' q'} : (p ∨ q) ⇒ (p ⇒ p') ⇒ (q ⇒ q') ⇒ (p' ∨ q').
Proof.
  intros ? ? ?. eapply hdisj_monot; eassumption.
Defined.

(** This order of arguments is often more convenient to use than the original [hconjtohdisj] *)
(* TODO: consider naming *)
Definition hconjtohdisj' {p q r} : (p ∨ q) ⇒ (p ⇒ r) ⇒ (q ⇒ r) ⇒ r.
Proof.
  intros ? ? ?. apply (hconjtohdisj p q r); try split; assumption.
Defined.

(* TODO: look for naming convention for similar lemmas *)
Definition hdisj_comm {p q} : (p ∨ q) ⇒ (q ∨ p).
Proof.
  apply hconjtohdisj; split; intro; auto using hdisj_in1, hdisj_in2.
Defined.

(* TODO: consider naming *)
Definition exists_monotone {X:UU} (A B : X -> UU)
  : (forall x, A x -> B x) -> (∃ x, A x) -> ∃ x, B x.
Proof.
  intros le_A_B.
  apply hinhfun, totalfun, le_A_B.
Defined.


(** *** Hsubtypes *)

(* TODO: upstream, and factor out rest of [subtype_containment_isPartialOrder] too? *)
Definition istrans_subtype_containment {X} {A B C : hsubtype X}
    (leq_AB : A ⊆ B) (leq_BC : B ⊆ C)
  : A ⊆ C.
Proof.
  cbn in *; auto.
Defined.

(* A restricted-quantifier version of [neghexisttoforallneg] *)
Definition negexists_to_forallneg_restricted
    {X:UU} {A B : hsubtype X}
  : ¬ (∃ x, A x ∧ B x) ⇒ (∀ x, A x ⇒ ¬ B x).
Proof.
  intros H_nex x A_x B_x.
  use H_nex. apply hinhpr. exists x. split; assumption.
Defined.

(* A restricted-quantifier version of [negforall_to_existsneg] *)
Definition negforall_to_existsneg_restricted (H_LEM : LEM)
    {X:UU} {A B : hsubtype X}
  : ¬ (∀ x, A x ⇒ B x) ⇒ ∃ x, A x ∧ ¬ B x.
Proof.
  intros H_forall. apply (proof_by_contradiction H_LEM).
  intros H_nex.
  use H_forall. intros x A_x. apply (proof_by_contradiction H_LEM).
  use (negexists_to_forallneg_restricted H_nex); assumption.
Defined.

Definition subtype_binaryunion {X} (A B : hsubtype X) : hsubtype X
  := fun x => A x ∨ B x.

Notation "A ∪ B" := (subtype_binaryunion A B)
                              (at level 40, left associativity) : subtype.
  (* precedence tighter than "⊆", also than "-" [subtype_difference].  *)
  (* in agda-input method, type \cup or ∪ *)

Definition subtype_binaryintersection {X} (A B : hsubtype X) : hsubtype X
  := fun x => A x ∧ B x.

Notation "A ∩ B" := (subtype_binaryintersection A B)
                              (at level 40, left associativity) : subtype.
  (* precedence tighter than "⊆", also than "-" [subtype_difference].  *)
  (* in agda-input method, type \cap *)

Definition subtype_binaryintersection_leq1 {X} (A B : hsubtype X)
    : A ∩ B ⊆ A
:= fun x => pr1.

Definition subtype_binaryintersection_leq2 {X} (A B : hsubtype X)
    : A ∩ B ⊆ B
:= fun x => pr2.

(* TODO: upstream; rename to eg [binaryintersection_equiv]? *)
Definition hconj_equiv {X:UU}
    {A A' B B' : hsubtype X} (e_A : A ≡ A') (e_B : B ≡ B')
  : (A ∩ B) ≡ (A' ∩ B').
Proof.
  intros x; split; intros [? ?]; split;
    try apply e_A; try apply e_B; assumption.
Defined.

Definition subtype_binaryintersection_univ {X} (A B C : hsubtype X)
  : C ⊆ A ∩ B <-> C ⊆ A ∧ C ⊆ B.
Proof.
  split.
  - intros C_AB. split; apply (istrans_subtype_containment C_AB).
    + apply subtype_binaryintersection_leq1.
    + apply subtype_binaryintersection_leq2.
  - cbn. intros [? ?]; split; auto.
Defined.

(* *** Images of functions, as hsubtypes *)

(* TODO: surely this must be in the library somewhere, along with its essential properties?? *)
Definition image {X Y : UU} (f : X -> Y) : hsubtype Y
  := fun y => ∥ hfiber f y ∥.

Definition value_in_image {X Y : UU} (f : X -> Y) (x : X) : image f (f x)
  := hinhpr (x ,, idpath _).

Definition to_image {X Y : UU} (f : X -> Y) (x : X) : image f
  := (f x,, value_in_image f x).

(** See [image_univ] below for a version that plays better with [apply]. *)
Definition image_univ
    {X Y : UU} (f : X -> Y)
    (A : hsubtype Y )
  : (∀ x:X, A (f x)) <-> (image f ⊆ A).
Proof.
  split.
  - intros H_A y Hy.
    refine (factor_through_squash_hProp _ _ Hy);
      intros [x e_xy]; destruct e_xy.
    use H_A.
  - intros H_A x.
    use H_A. apply value_in_image.
Defined.

(** Alias of [image_univ] using explicit “forall” instead of “⊆” or “∀”, for easier use with the [apply] tactic. *)
Definition image_univ'
    {X Y : UU} (f : X -> Y)
    (A : hsubtype Y )
  : (forall x:X, A (f x)) <-> (forall y:Y, (image f y) -> A y).
Proof.
  apply image_univ.
Defined.

Definition image_carrier_univ
    {X Y : UU} (f : X -> Y)
    (A : hsubtype Y )
  : (∀ x:X, A (f x)) <-> (∀ y : image f, A (pr1 y)).
Proof.
  split.
  - intros H [y im_y]. eapply image_univ'; eassumption.
  - intros H; cbn. apply image_univ'.
    intros y im_y. exact (H (y,,im_y)).
Defined.

(** Like [image_univ'], alias using explicit “forall” instead of “∀”, for easier use with the [apply] tactic. *)
Definition image_carrier_univ'
    {X Y : UU} (f : X -> Y)
    (A : hsubtype Y )
  : (forall x:X, A (f x)) <-> (forall y : image f, A (pr1 y)).
Proof.
  apply image_carrier_univ.
Defined.

End Auxiliary.

Notation "A ∩ B" := (subtype_binaryintersection A B)
                              (at level 40, left associativity) : subtype.
  (* precedence tighter than "⊆", also than "-" [subtype_difference].  *)
  (* in agda-input method, type \cap *)

Notation "A ∪ B" := (subtype_binaryunion A B)
                              (at level 40, left associativity) : subtype.
  (* precedence tighter than "⊆", also than "-" [subtype_difference].  *)
  (* in agda-input method, type \cup or ∪ *)

(** ** Completeness properties *)

(** We use the treatment of upper bounds from [Algebra.Dcpo], but give a slightly different treatment of _least_ upper bounds,
 factoring out the general definitions of “greatest/least elements” and “upper/lower bounds”, both of a family, or satisfying some predicate. *)

Section LowerBounds.
(* NOTE: this should be kept in sync with [Section UpperBounds] below. *)

  Context {P : Poset}.

  Definition islowerbound {I} (p : I -> P) (x : P) : hProp
  := ∀ i : I, x ≤ p i.

  Definition islowerbound_subtype (A : hsubtype P) (x : P) : hProp
  := islowerbound (pr1carrier A) x.

  Definition islowerbound_subtype_equiv {A B : hsubtype P}
    : (A ≡ B)
    -> islowerbound_subtype A ≡ islowerbound_subtype B.
  Proof.
    intros e_A_B x; split;
      intros x_lb [y H_y]; refine (x_lb (_,,_)); apply e_A_B; assumption.
  Defined.

  (* NOTE: For an alternative approach to [is_lower_bound_subfamily] and [image_same_lower_bounds], see analogues for upper bounds below. *)
  Definition is_lower_bound_subfamily {I} (f : I -> P) {J} (g : J -> P)
      (ff : forall j, (image f) (g j))
      {x} (x_lb : islowerbound f x)
    : islowerbound g x.
  Proof.
    intros j. refine (factor_through_squash_hProp _ _ (ff j)).
    intros [i e]; destruct e. use x_lb.
  Defined.

  Definition image_same_lower_bounds {I} (f : I -> P) {x : P}
    : islowerbound f x
      <-> islowerbound_subtype (image f) x.
  Proof.
    apply (image_carrier_univ' f (fun y => _ ≤ y)).
  Defined.

End LowerBounds.

Section UpperBounds.
(* NOTE: this should be kept in sync with [Section LowerBounds] above. *)

  (* TODO: it would be natural to just refactor [isupperbound] in [Algebra.Dcpo]
  as an hProp from the start, using [∀] and so on.  However, that turns out
  to slightly interfere with the use of [apply] on lemmas in that file, especially
  bidirectional such as [pointwiselub_islubpointwise]. Is that cosmetic cost
  worth paying?  Or can it be avoided? *)

  Context {P : Poset}.

  Definition isupperbound_hprop {I} (p : I -> P) (x:P) : hProp
  := make_hProp _ (isaprop_isupperbound p x).

  Definition isupperbound_subtype (A : hsubtype P) (x : P) : hProp
  := isupperbound_hprop (pr1carrier A) x.

  Definition isupperbound_subtype_equiv {A B : hsubtype P}
    : (A ≡ B)
    -> isupperbound_subtype A ≡ isupperbound_subtype B.
  Proof.
    intros e_A_B x; split;
      intros x_ub [y H_y]; refine (x_ub (_,,_)); apply e_A_B; assumption.
  Defined.

  (* NOTE: An aternative approach alternative to comparing the upper bounds of families and their images: factor a bit.  Show that for two families, if f ≤ image g, then every upper bound of g is an upper bound for f. Thence: the non-image version.  Thence: image has same upper bounds, so same least upper bound. *)

  Definition is_upper_bound_subfamily {I} (f : I -> P) {J} (g : J -> P)
      (ff : forall j, (image f) (g j))
      {x} (x_ub : isupperbound f x)
    : isupperbound g x.
  Proof.
    intros j. refine (factor_through_squash_hProp _ _ (ff j)).
    intros [i e]; destruct e. apply x_ub.
  Defined.

  Definition image_same_upper_bounds {I} (f : I -> P) {x : P}
    : isupperbound f x
      <-> isupperbound_subtype (image f) x.
  Proof.
    apply (image_carrier_univ' f (fun y => y ≤ _)).
  Defined.

End UpperBounds.

Section Least.
(* NOTE: this should generally be kept in sync with [Section Greatest] below. *)

  Context {P : Poset}.

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

  Definition least_suchthat_is_least {A : P -> UU} (x : least_suchthat A)
    : ∏ y, A y -> x ≤ y.
  Proof.
    intros y A_y. exact (least_is_least _ x (_,,A_y)).
  Defined.

  (** It’s useful to define [least_suchthat] as above, for interaction with [least_of_family], etc; but also helpful to have a standalone predicate version. *)
  (* TODO: is that really useful? could it be better to refactor [least_suchthat] as [carrier (is_least_suchthat …)]? *)
  Definition is_least_suchthat (A : P -> hProp) (x : P) : hProp
  := (A x) ∧ (islowerbound_subtype A x).

  Definition least_suchthat_property {A : P -> hProp} (x : least_suchthat A)
    : is_least_suchthat A x.
  Proof.
    split.
    - apply @least_suchthat_satisfies.
    - apply least_is_least.
  Defined.

  Definition make_least_suchthat {A : P -> hProp}
      (x : P) (x_least : is_least_suchthat A x)
    : least_suchthat A.
  Proof.
    use tpair.
    { exists x. apply x_least. }
    apply x_least.
  Defined.

End Least.

Section Greatest.
(* NOTE: this should generally be kept in sync with [Section Least] above. *)

  Context {P : Poset}.

  Definition greatest_of_family {I} (p : I -> P)
  := ∑ i : I, isupperbound p (p i).

  Definition greatest_of_family_index {I} {p : I -> P}
    : greatest_of_family p -> I
  := pr1.
  (* Would be nice to make [greatest_of_family_index] a coercion, but can’t since its target is an arbitrary type. The best we can do instead is [realise_greatest_of_family]: *)
  Coercion realise_greatest_of_family {I} (p : I -> P)
    : greatest_of_family p -> P
  := fun ih => p (pr1 ih).

  Definition greatest_is_greatest {I}  (p : I -> P) (x : greatest_of_family p)
    : isupperbound p x
  := pr2 x.

  Definition greatest_suchthat (A : P -> UU) : UU
  := greatest_of_family (pr1 : (∑ x:P, A x) -> P).

  Identity Coercion id_greatest_suchthat : greatest_suchthat >-> greatest_of_family.

  Definition greatest_suchthat_satisfies {A : P -> UU} (x : greatest_suchthat A)
      : A x
  := pr2 (greatest_of_family_index x).

  Definition greatest_suchthat_is_greatest {A : P -> UU} (x : greatest_suchthat A)
    : ∏ y, A y -> y ≤ x.
  Proof.
    intros y A_y. exact (greatest_is_greatest _ x (_,,A_y)).
  Defined.

  (** It’s useful to define [greatest_suchthat] as above, for interaction with [greatest_of_family], etc; but also helpful to have a standalone predicate version. *)
  (* TODO: is that really useful? could it be better to refactor [greatest_suchthat] as [carrier (is_greatest_suchthat …)]? *)
  Definition is_greatest_suchthat (A : P -> hProp) (x : P) : hProp
  := (A x) ∧ (isupperbound_subtype A x).

  Definition greatest_suchthat_property {A : P -> hProp} (x : greatest_suchthat A)
    : is_greatest_suchthat A x.
  Proof.
    split.
    - apply @greatest_suchthat_satisfies.
    - apply greatest_is_greatest.
  Defined.

  Definition make_greatest_suchthat {A : P -> hProp}
      (x : P) (x_greatest : is_greatest_suchthat A x)
    : greatest_suchthat A.
  Proof.
    use tpair.
    { exists x. apply x_greatest. }
    apply x_greatest.
  Defined.

End Greatest.

Section LeastUpperBounds.

  Context {P : Poset}.

  Definition least_upper_bound {I} (p : I -> P)
  := least_suchthat (isupperbound_hprop p).
  Identity Coercion id_least_upper_bound : least_upper_bound >-> least_suchthat.

  Definition least_upper_bound_is_upper_bound {I} {p : I -> P}
             (x : least_upper_bound p)
    : isupperbound p x
  := least_suchthat_satisfies x.

  (** It’s useful to define [least_upper_bound] as above, for interaction with [upper_bound], etc; but also helpful to have a standalone predicate version. *)
  Definition is_least_upper_bound {I} (p : I -> P) (x : P) : hProp
    := is_least_suchthat (isupperbound_hprop p) x.

  Definition make_least_upper_bound {I} {p : I -> P}
      (x:P) (x_lub : is_least_upper_bound p x)
    : least_upper_bound p
  := make_least_suchthat x x_lub.

  Definition least_upper_bound_property {I} {p : I -> P}
      (x : least_upper_bound p)
    : is_least_upper_bound p x
  := least_suchthat_property x.

  (** The universal property of the least upper bound *)
  Definition least_upper_bound_univ {I} {p : I -> P}
             (x : least_upper_bound p) (x' : P)
    : x ≤ x' <-> isupperbound p x'.
  Proof.
    split.
    - intros xx' i.
      eapply istrans_posetRelation; try eassumption.
      apply least_upper_bound_is_upper_bound.
    - intros H. refine (least_is_least _ x (_,,H)).
  Defined.

  (** Specialisation of the above functions to least upper bounds of _subtypes_
   — a common use-case, and the functions are often easier to use in this form. *)
  Definition is_least_upper_bound_subtype (A : hsubtype P) (x : P) : hProp
    := is_least_upper_bound (pr1carrier A) x.

  Definition least_upper_bound_subtype (A : hsubtype P) : UU
    := least_upper_bound (pr1carrier A).

  Identity Coercion id_least_upper_bound_subtype
    : least_upper_bound_subtype >-> least_upper_bound.

  Definition least_upper_bound_subtype_is_upper_bound {A : hsubtype P}
      (x : least_upper_bound_subtype A) {y : P} (A_y : A y)
    : y ≤ x
  := least_upper_bound_is_upper_bound x (y,,A_y).

  Definition least_upper_bound_subtype_univ {A : hsubtype P}
             (x : least_upper_bound (pr1carrier A)) (x' : P)
    : x ≤ x' <-> (forall y, A y -> y ≤ x').
  Proof.
    split.
    - intros H y A_y.
      refine (pr1 (least_upper_bound_univ x x') H (_,,_)); assumption.
    - intros H.
      apply least_upper_bound_univ.
      intros [y A_y]; apply H; assumption.
  Defined.

  (** Comparison of least upper bounds between families and their images *)

  Definition is_least_upper_bound_image {I} (f : I -> P) {x : P}
    : is_least_upper_bound f x
      <-> is_least_upper_bound (pr1carrier (image f)) x.
  Proof.
    revert x. apply hconj_equiv.
    - use image_same_upper_bounds.
    - apply islowerbound_subtype_equiv. use image_same_upper_bounds.
  Defined.

  (* TODO: upgrade this to an equivalence?
     easiest if done once refactoring [least_upper_bound] as
     [carrier is_least_upper_bound]. *)
  Definition least_upper_bound_image {I} (f : I -> P)
    : least_upper_bound f <-> least_upper_bound (pr1carrier (image f)).
  Proof.
    split; intros x; apply (make_least_upper_bound x);
      apply is_least_upper_bound_image, least_upper_bound_property.
  Defined.

  (* A useful miscellaneous lemma *)
  Lemma greatest_if_contains_sup
      (A : hsubtype P) (x : P)
    : A x -> is_least_upper_bound_subtype A x -> is_greatest_suchthat A x.
  Proof.
    intros A_x x_lub. split.
    - assumption.
    - apply (pr1 x_lub).
  Defined.

End LeastUpperBounds.

(* TODO: give [Section GreatestLowerBounds] dual to the above section! *)

Section Chains.

  Definition comparable {P : Poset} (x y : P) : hProp
  := (x ≤ y) ∨ (y ≤ x).

  Definition is_chain {P : Poset} {I} (p : I -> P) : hProp
  := ∀ i j : I, comparable (p i) (p j).

  Definition Chain (P : Poset) : UU
  := ∑ (I : UU), ∑ (p : I -> P), is_chain p.

  Coercion chain_index {P} (C : Chain P) : UU
  := pr1 C.

  Definition chain_family {P} (C : Chain P) : C -> P
  := pr1 (pr2 C).
  Coercion chain_family : Chain >-> Funclass.

  Definition chain_property {P} (C : Chain P) : is_chain C
  := pr2 (pr2 C).

  Definition fmap_is_chain {P Q} (f : posetmorphism P Q)
      {I : UU} (p : I -> P)
    : is_chain p -> is_chain (f ∘ p).
  Proof.
    intros p_chain x y.
    apply (hdisj_monot' (p_chain x y));
    intro; apply posetmorphism_property; assumption.
  Defined.

  Definition fmap_chain {P Q} (f : posetmorphism P Q)
    : Chain P -> Chain Q.
  Proof.
    apply funfibtototal; intros I. use bandfmap.
    - apply (fun C => f ∘ C).
    - apply fmap_is_chain.
  Defined.

  Definition Chain_hsubtype (P : Poset) : UU
  := ∑ A : hsubtype P, is_chain (pr1carrier A).

  Coercion pr1_Chain_hsubtype {P} : Chain_hsubtype P -> hsubtype P
  := pr1.

  Coercion Chain_of_Chain_hsubtype (P : Poset)
    : Chain_hsubtype P -> Chain P.
  Proof.
    intros C. exact (carrier C,, (pr1carrier C,, pr2 C)).
  Defined.

  Definition image_is_chain {P:Poset} {I:UU} (p : I -> P)
    : is_chain p -> is_chain (pr1carrier (image p)).
  Proof.
    intros p_chain. unfold is_chain.
    apply (image_carrier_univ p (fun x => ∀ j, comparable x _)); intros i.
    apply (image_carrier_univ p); intros j.
    use p_chain.
  Defined.

  Definition image_chain {P:Poset}
      : Chain P -> Chain_hsubtype P.
  Proof.
    intros p. exists (image p).
    apply image_is_chain, chain_property.
  Defined.

End Chains.

Section Directed.

  Definition Directed_family (P : Poset) : UU
  := ∑ (I : UU), ∑ (p : I -> P), isdirected p.

  Coercion directed_index {P} (C : Directed_family P) : UU
  := pr1 C.

  Definition directed_family {P} (C : Directed_family P) : C -> P
  := pr1 (pr2 C).
  Coercion directed_family : Directed_family >-> Funclass.

  Definition directed_property {P} (C : Directed_family P) : isdirected C
  := pr2 (pr2 C).

  (* TODO: add similar builder function for chains *)
  Definition make_directed {P:Poset} {I} {p : I -> P} (p_directed : isdirected p)
    : Directed_family P
  := (I,,(p,,p_directed)).

  Definition fmap_is_directed {P Q} (f : posetmorphism P Q)
      {I : UU} (p : I -> P)
    : isdirected p -> isdirected (f ∘ p).
  Proof.
    intros p_directed; split.
    - eapply isdirected_inhabited, p_directed.
    - intros i j.
      eapply exists_monotone.
      2: { exact (isdirected_compatible p_directed i j). }
      intros x [le_i_x le_j_x].
      split; apply posetmorphism_property; assumption.
  Defined.

  Definition fmap_directed {P Q} (f : posetmorphism P Q)
    : Directed_family P -> Directed_family Q.
  Proof.
    apply funfibtototal; intros I. use bandfmap.
    - apply (fun C => f ∘ C).
    - apply fmap_is_directed.
  Defined.

  Definition Directed_hsubtype (P : Poset) : UU
  := ∑ A : hsubtype P, isdirected (pr1carrier A).

  Coercion pr1_Directed_hsubtype {P} : Directed_hsubtype P -> hsubtype P
  := pr1.

  Coercion Directed_of_Directed_hsubtype (P : Poset)
    : Directed_hsubtype P -> Directed_family P.
  Proof.
    intros C. exact (carrier C,, (pr1carrier C,, pr2 C)).
  Defined.

  Definition image_is_directed {P:Poset} {I:UU} (p : I -> P)
    : isdirected p -> isdirected (pr1carrier (image p)).
  Proof.
    intros p_directed. split.
    - apply (squash_to_hProp (isdirected_inhabited p_directed)).
      intros i; apply hinhpr.
      apply to_image; assumption.
    - use (pr1 (image_carrier_univ' p (fun x => ∀ j, ∃ k, x ≤ _ ∧ _))). intros i.
      use (pr1 (image_carrier_univ' p (fun y => ∃ k, _ ∧ y ≤ _))); intros j.
      apply (squash_to_hProp (isdirected_compatible p_directed i j)).
      intros [k [le_ik le_jk]].
      apply hinhpr. exists (to_image _ k).
      split; assumption.
  Defined.

  Definition image_directed {P:Poset}
      : Directed_family P -> Directed_hsubtype P.
  Proof.
    intros p. exists (image p).
    apply image_is_directed, directed_property.
  Defined.

End Directed.

Section Completeness.

  (* TODO: show that completeness is a property,
     once we’ve shown above that least upper bounds are unique. *)

  Definition is_complete (P : Poset) : UU
  := ∏ A : hsubtype P, least_upper_bound (pr1carrier A).

  (** [is_complete] is defined just in terms of hsubtypes, to agree with the classical definition and keep its quantification “small”.

  However, it implies completeness for arbitrarily families. *)
  (* TODO: consider naming! *)
  Definition family_lub {P:Poset} (P_complete : is_complete P)
      {I:UU} (f : I -> P)
    : least_upper_bound f.
  Proof.
    apply least_upper_bound_image, P_complete.
  Defined.

  Definition is_chain_complete (P : Poset) : UU
  := ∏ C : Chain_hsubtype P, least_upper_bound_subtype C.

  (** Like [is_complete], [is_chain_complete] is defined just in terms of hsubtype-chains, to keep quantification small.

  However, it implies least upper bounds for arbitarily-indexed chains. *)
  Definition chain_lub {P : Poset} (P_CC : is_chain_complete P)
      (p : Chain P)
    : least_upper_bound p.
  Proof.
    apply least_upper_bound_image.
    exact (P_CC (image_chain p)).
  Defined.

  (** Version with [is_chain] split out, for easier application *)
  Definition chain_lub' {P : Poset} (P_CC : is_chain_complete P)
      {I:UU} (p:I->P)
    : is_chain p -> least_upper_bound p.
  Proof.
    intros p_chain. exact (chain_lub P_CC (I,,(p,,p_chain))).
  Defined.

  Definition is_directed_complete (P : Poset) : UU
  := ∏ A : Directed_hsubtype P, least_upper_bound (directed_family A).

  (** Like [is_complete], [is_directed_complete] is defined just in terms of directed subtypes, to keep quantification small.

  However, it implies least upper bounds for arbitary directed families. *)
  Definition directed_lub {P : Poset} (P_DC : is_directed_complete P)
      (p : Directed_family P)
    : least_upper_bound p.
  Proof.
    apply least_upper_bound_image.
    exact (P_DC (image_directed p)).
  Defined.

  Definition isdirected_lub {P : Poset} (P_DC : is_directed_complete P)
      {I} (p : I -> P) (p_directed : isdirected p)
    : least_upper_bound p.
  Proof.
    exact (directed_lub P_DC (make_directed p_directed)).
  Defined.

  (* TODO: unify this treatment of directed completeness with that given in [Algebra.Dcpo] *)
End Completeness.

(** ** Upper bounds, completeness, etc in sub-posets *)
Section Subposets.

  (* TODO: upstream to [MoreFoundations.Subposets]? *)
  Definition subposet_incl {P : Poset} {A : Subposet' P} : posetmorphism A P
  := pr1 (pr2 A).

  Definition is_upper_bound_in_subposet {P : Poset} {A : Subposet P}
      {I} {p : I -> A} {x : A}
    : isupperbound (subposet_incl ∘ p) (subposet_incl x)
    <-> isupperbound p x.
  Proof.
    split; auto.
  Defined.

  (* TODO: unsure which arguments should be implicit. Revisit this after some use downstream! *)
  (** Given a chain in a sub-poset with a least upper bound in the ambient poset,
  if the l.u.b. lies in the sub-poset, then it’s an l.u.b. there. *)
  Definition is_least_upper_bound_in_subposet {P : Poset} {A : Subposet P}
      {I} {p : I -> A} {x : A}
      (x_lub : is_least_upper_bound (subposet_incl ∘ p) (subposet_incl x))
    : is_least_upper_bound p x.
  Proof.
    split.
    - apply is_upper_bound_in_subposet, x_lub.
    - intros [x' x'_ub].
      apply (least_upper_bound_univ (make_least_upper_bound _ x_lub)).
      apply is_upper_bound_in_subposet; assumption.
  Defined.

  Definition least_upper_bound_in_subposet {P : Poset} {A : Subposet P}
      {I} {p : I -> A}
      (x : least_upper_bound (pr1 ∘ p)) (x_A : A x)
    : least_upper_bound p.
  Proof.
    use make_least_upper_bound.
    { exists x. apply x_A. }
    apply is_least_upper_bound_in_subposet, least_upper_bound_property.
  Defined.

  Definition is_chain_in_subposet {P : Poset} {A : Subposet P}
      {I : Type} (p : I -> A)
    : is_chain p <-> is_chain (subposet_incl ∘ p).
  Proof.
    split; auto.
  Defined.

  (* This lemma can be given in several alternative forms,
  e.g. in terms of the canonical given lubs, or arbitrary lubs;
  and in terms of chains in [A], or chains in [P] satisfying [A];
  and in terms of general chains, or subtype-chains.

  TODO: once it’s in use, reconsider which form might be best. *)
  Definition is_chain_complete_subposet
      {P : Poset} (P_CC : is_chain_complete P) {A : Subposet P}
      (A_chain_closed : forall C : Chain_hsubtype A,
          A (chain_lub P_CC (fmap_chain subposet_incl C)))
    : is_chain_complete A.
  Proof.
    intros C.
    use make_least_upper_bound.
    { exists (chain_lub P_CC (fmap_chain subposet_incl C)).
      apply A_chain_closed. }
    apply is_least_upper_bound_in_subposet.
    apply least_upper_bound_property.
  Defined.

  (* TODO: add similar treatment of directed-completeness in subsets. *)

End Subposets.

(** ** Function posets

Products of posets; posets of (classes of) functions *)

Section Function_Posets.

  (** The most general poset of functions is just the product of a family of posets.

  We set this up first, and then give other posets of functions (e.g. the poset of poset maps) as subposets of this general one. *)
(* TODO: possibly some examples upstream could eventually be unified with this,
e.g. [dcpoofdcpomorphisms]? *)
  Definition pointwiseorder {X:UU} (P : X -> Poset) : hrel (∏ x, P x)
  := fun f g => ∀ x, f x ≤ g x.

  Lemma ispartialorder_pointwiseorder {X:UU} (P : X -> Poset)
    : isPartialOrder (pointwiseorder P).
  Proof.
    repeat split.
    - repeat intro. eapply istrans_posetRelation; auto.
    - repeat intro. apply isrefl_posetRelation.
    - intros f g le_f_g le_g_f.
      use funextsec; intro.
      apply isantisymm_posetRelation; auto.
  Defined.

  (** Note: could also be called e.g. [Poset_product], or various other names. *)
  (* TODO: consider naming convention. Are there analogous constructions elsewhere in UniMath that this should fit with?
  This name fits with type-theoretical lemmas in UniMath, but is less natural from a classical mathematical perspective.
*)
  Definition forall_Poset {X:UU} (P : X -> Poset) : Poset.
  Proof.
    use make_Poset. { exact (forall_hSet P). }
    use make_PartialOrder. { apply pointwiseorder. }
    apply ispartialorder_pointwiseorder.
  Defined.

  Definition arrow_Poset (X:UU) (P : Poset) : Poset
    := forall_Poset (fun _:X => P).

  Definition isupperbound_if_pointwise {X:UU} {P : X -> Poset}
      {I} {f : I -> forall_Poset P}
      {g : forall_Poset P}
    : isupperbound f g <-> forall x, isupperbound (fun i => f i x) (g x).
  Proof.
    split; intro H; repeat intro; use H.
  Defined.

  Definition is_least_upper_bound_pointwise {X:UU} {P : X -> Poset}
      {I} (f : I -> forall_Poset P)
      (g : forall_Poset P)
    : hProp
  := ∀ x, is_least_upper_bound (fun i => f i x) (g x).

  Definition is_least_upper_bound_if_pointwise {X:UU} {P : X -> Poset}
      {I} {f : I -> forall_Poset P}
      {g : forall_Poset P}
    : is_least_upper_bound_pointwise f g
      -> is_least_upper_bound f g.
  Proof.
    intro pointwise_lub.
    set (g_pwlub := fun x => make_least_upper_bound _ (pointwise_lub x)).
    split.
    - intros i x.
      apply (least_upper_bound_is_upper_bound (g_pwlub x)).
    - intros [g' g'_ub] x.
      apply (least_upper_bound_univ (g_pwlub x)).
      apply isupperbound_if_pointwise, g'_ub.
  Defined.

Lemma isaposetmorphism_pointwise_lub {P : Poset}
    {I} {f : I -> P -> P} (f_monot : forall i, isaposetmorphism (f i))
    {g} (g_pw_lub : is_least_upper_bound_pointwise f g)
  : isaposetmorphism g.
Proof.
  intros x y le_x_y.
  apply (least_upper_bound_univ (make_least_upper_bound _ (g_pw_lub _))).
  intros i.
  eapply istrans_posetRelation.
  2: { apply (least_upper_bound_is_upper_bound
                (make_least_upper_bound _ (g_pw_lub _))). }
  apply f_monot; assumption.
Defined.

End Function_Posets.


(** ** Classes of maps *)

(** Progressive maps as also known as ascending, inflationary, increasing, and more.

Note these are just endo-_functions_, not “maps” in the sense of morphisms of posets. *)

Section ProgressiveMaps.

Definition isprogressive {P : Poset} : hsubtype (P -> P) : UU
  := fun f => ∀ (x : P), x ≤ f x.

Definition Progressive_map (P : Poset) := carrier (@isprogressive P).

Definition pr1_Progressive_map {P : Poset} : Progressive_map P -> (P -> P)
:= pr1carrier _.
Coercion pr1_Progressive_map : Progressive_map >-> Funclass.

Definition progressive_property {P} (f : Progressive_map P)
  : isprogressive f
:= pr2 f.

Lemma isprogressive_idfun {P : Poset} : isprogressive (idfun P).
Proof.
  intro; apply isrefl_posetRelation.
Defined.

Lemma isprogressive_compose {P : Poset}
    {f g : P -> P} (f_prog : isprogressive f) (g_prog : isprogressive g)
  : isprogressive (f ∘ g).
Proof.
  intros x. eapply istrans_posetRelation.
  - use g_prog.
  - use f_prog.
Defined.


Lemma progressive_pointwise_lub {P : Poset}
    {I} {f : I -> P -> P} (f_prog : forall i, isprogressive (f i))
    {g} (g_pw_lub : is_least_upper_bound_pointwise f g)
    (I_inhab : ∥ I ∥)
  : isprogressive g.
Proof.
  intros x. eapply factor_through_squash_hProp. 2: { apply I_inhab. }
  intros i.
  eapply istrans_posetRelation. { use f_prog; apply i. }
  revert i.
  (* TODO: make version that takes the [is_lub] as separate input *)
  refine (@least_upper_bound_is_upper_bound _ _ _ (make_least_upper_bound _ _)).
  use g_pw_lub.
Defined.

End ProgressiveMaps.

(** ** Fixpoints of endofunctions *)

Section Fixpoints.

(* TODO: this approach to types of fixedpoints doesn’t play well with the setup of subposets. Perhaps try refactoring? But working with hsubtypes/subposets throughout creates so much extra [pr1] overhead, impacting readability; this approach avoids that nicely. *)

Definition isfixedpoint {P : Poset} (f : P -> P) : hsubtype P
  := fun (x:P) => f x = x.

Definition Fixedpoint {P : Poset} (f : P -> P) : UU := carrier (isfixedpoint f).

Coercion pr1_Fixedpoint {P : Poset} {f : P -> P} : Fixedpoint f -> P
:= pr1carrier _.

Definition fixedpoint_property  {P : Poset} {f : P -> P} (x : Fixedpoint f)
  : f x = x
:= pr2 x.

Definition ispostfixedpoint {P : Poset} (f : P -> P) : hsubtype P
  := fun (x:P) => x ≤ f x.

Definition Postfixedpoint {P : Poset} (f : P -> P) : UU
  := carrier (ispostfixedpoint f).

Coercion pr1_Postfixedpoint {P : Poset} {f : P -> P} : Postfixedpoint f -> P
:= pr1carrier _.

Definition postfixedpoint_property  {P : Poset} {f : P -> P} (x : Postfixedpoint f)
  : x ≤ f x
:= pr2 x.

End Fixpoints.


(** ** The (Knaster–)Tarski fixpoint theorems

This classical theorem is in several forms.  The strong general form, due to Tarski, states that given a monotone endo-map [f] on a complete poset [P], the sub-poset of fixed points of [f] is again complete.  The key lemma for this is close to the earlier weaker form, due essentially to Knaster and Tarski independently: a monotone endo-map [f] on a complete poset [P] has a least fixed point above any post-fixed point.
*)
Section Tarski.

Theorem Knaster_Tarski_fixpoint {P:Poset} (P_complete : is_complete P)
    (f : posetmorphism P P) {x0} (x0_postfix : x0 ≤ f x0)
  : least_suchthat (fun x:P => f x = x ∧ x0 ≤ x).
Proof.
  (* Let C be the least subset containing x0 that is closed under f and taking least upper bounds.
   We take some time to set up C and its universal property cleanly. *)
  set (is_f_closed := (fun A => (∀ y, A y ⇒ A (f y)))
    : hsubtype P -> hProp).
  set (is_sup_closed
      := (fun A => ∀ C' : hsubtype P, C' ⊆ A ⇒ A (P_complete C'))
    : hsubtype P -> hProp).
  set (C := (fun x =>
      ∀ A : hsubtype P, A x0 ⇒ is_f_closed A ⇒ is_sup_closed A ⇒ A x)
    : hsubtype P).
  assert (C_x0 : C x0).
  { intros A A_x0 A_f_closed A_sup_closed; assumption. }
  assert (C_f_closed : is_f_closed C).
  { intros x C_x A A_x0 A_f_closed A_sup_closed.
    use A_f_closed. use C_x; assumption. }
  assert (C_sup_closed : is_sup_closed C).
  { intros X C_X A A_x0 A_f_closed A_sup_closed.
    use A_sup_closed; intros ? ?; use C_X; assumption. }
  assert (C_induction : ∀ (A : hsubtype P),
    A x0 ⇒ is_f_closed (A ∩ C) ⇒ is_sup_closed (A ∩ C) ⇒ C ⊆ A).
  { intros A A_x0 A_sup_closed A_f_closed x Cx.
    apply (Cx (fun x => A x ∧ C x)); [ split | | ]; assumption. }
  (* Now establish a few facts about C and (post-)fixed points *)
  assert (postfix_supclosed : is_sup_closed (fun x => x ≤ f x)).
  { intros A A_postfix.
    apply least_upper_bound_subtype_univ. intros x A_x.
    eapply istrans_posetRelation. { use A_postfix; apply A_x. }
    apply posetmorphism_property.
    apply least_upper_bound_subtype_is_upper_bound, A_x.
  }
  assert (postfix_C : C ⊆  (fun x => x ≤ f x)).
  { use C_induction.
    - apply x0_postfix.
    - intros x [x_postfix C_x]. split. 2: { use C_f_closed; assumption. }
      apply posetmorphism_property, x_postfix.
    - intros A IH_A. split.
      2: { use C_sup_closed;
           apply (istrans_subtype_containment IH_A),
                 subtype_binaryintersection_leq2. }
      use postfix_supclosed.
      apply (istrans_subtype_containment IH_A).
      apply subtype_binaryintersection_leq1.
  }
  assert (C_below_allfix : ∏ x, (f x = x) ⇒ x0 ≤ x ⇒ C ⊆ (fun y => y ≤ x)).
  { intros x x_fix leq_x0_x.
    use C_induction.
    - assumption.
    - intros y [le_yx C_y]. split. 2: { use C_f_closed; assumption. }
      eapply istrans_posetRelation. { apply posetmorphism_property, le_yx. }
      apply isrefl'_posetRelation, x_fix.
    - intros A IH_A. split.
      2: { use C_sup_closed.
           apply (istrans_subtype_containment IH_A),
                 subtype_binaryintersection_leq2. }
      apply least_upper_bound_subtype_univ.
      apply (istrans_subtype_containment IH_A), subtype_binaryintersection_leq1.
  }
  (* From these, it follows that sup C is a least fixed point. *)
  set (sup_C := P_complete C).
  assert (C_sup_C : C sup_C). { use C_sup_closed. intros ? ?; assumption. }
  simple refine (((sup_C : P),,(_,,_)),,_); simpl.
  - apply isantisymm_posetRelation.
    + refine (least_upper_bound_is_upper_bound sup_C (_,,_)).
      use C_f_closed. apply C_sup_C.
    + use postfix_C. apply C_sup_C.
  - refine (least_upper_bound_is_upper_bound sup_C (_,,_)); assumption.
  - intros [x [x_fix leq_x0_x]]; simpl.
    apply least_upper_bound_subtype_univ, C_below_allfix; assumption.
Defined.

Theorem Tarski_fixpoint_theorem
    {P:Poset} (P_complete : is_complete P) (f : posetmorphism P P)
  : is_complete ((fun x:P => f x = x) : Subposet P).
Proof.
  intros A.
  set (A_in_P := (fun x:P => ∑ x_fix : (f x = x)%logic, A (x,,x_fix))%prop).
  set (sup_P_A := P_complete A_in_P).
  assert (sup_fix_A : least_suchthat (fun x:P => f x = x ∧ sup_P_A ≤ x)).
  { apply Knaster_Tarski_fixpoint; try assumption.
    apply least_upper_bound_subtype_univ.
    intros y [y_fix A_y].
    apply (istrans_posetRelation _ _ (f y)).
    { apply isrefl'_posetRelation, pathsinv0; assumption. }
    apply posetmorphism_property, least_upper_bound_subtype_is_upper_bound.
    use tpair; assumption.
  }
  assert (sup_A_isfix : f sup_fix_A = sup_fix_A).
  { apply (least_suchthat_satisfies sup_fix_A). }
  use make_least_upper_bound.
  { exists sup_fix_A. assumption. }
  split.
  - intros [[x x_fix] A_x]. simpl.
    apply (istrans_posetRelation _ _ (sup_P_A)).
    + apply least_upper_bound_subtype_is_upper_bound. use tpair; assumption.
    + apply (least_suchthat_satisfies sup_fix_A).
  - intros [[x x_fix] x_ub]. cbn.
    apply least_suchthat_is_least.
    split; try assumption.
    apply least_upper_bound_subtype_univ.
    intros y [y_fix A_y].
    use (x_ub ((_,,_),,_)); assumption.
Defined.

End Tarski.

(** ** Bourbaki-Witt

The classical Bourbaki–Witt theorem says: Any progressive map on a chain-complete partial order has a fixed point.

Constructively, this may fail, as shown in Bauer–Lumsdaine https://arxiv.org/abs/1201.0340. Here we aim to give both the classical theorem, and some weaker constructively-provable results.
*)

Section Bourbaki_Witt.

Definition Bourbaki_Witt_property (P : Poset)
  := ∏ (f : Progressive_map P), Fixedpoint f.

(** Theorem traditionally credited to Bourbaki (1949) and Witt (1951). This proof is based on Lang, Algebra (2002), Appendix 2, Thm 2.1. *)
Theorem Bourbaki_Witt_fixpoint
  : LEM -> ∏ P : Poset, is_chain_complete P -> Bourbaki_Witt_property P.
Proof.
(* Let C be the least subset closed under f and suprema of chains.
   We take some time to set up C and its universal property cleanly. *)
  intros H_LEM P P_CC f.
  set (is_f_closed := (fun A => (∀ y, A y ⇒ A (f y)))
    : hsubtype P -> hProp).
  set (is_chain_closed
      := (fun A => (∀ C' : Chain_hsubtype P, (∏ y:C', A (pr1 y)) ⇒ A (P_CC C')))
    : hsubtype P -> hProp).
  set (C := (fun x =>
      ∀ A : hsubtype P, is_f_closed A ⇒ is_chain_closed A ⇒ A x)
    : hsubtype P).
  assert (C_f_closed : is_f_closed C).
  { intros x C_x A A_f_closed A_chain_closed.
    use A_f_closed. use C_x; assumption. }
  assert (C_chain_closed : is_chain_closed C).
  { intros x C_x A A_f_closed A_chain_closed.
    use A_chain_closed. intro; use C_x; assumption. }
  assert (C_induction : ∀ (A : hsubtype P),
    is_f_closed (A ∩ C) ⇒ is_chain_closed (A ∩ C) ⇒ C ⊆ A).
  { intros A A_chain_closed A_f_closed x Cx.
    apply (Cx (fun x => A x ∧ C x)); assumption. }
  (* Now, if C is a chain, then its least upper bound will be a fixed point. *)
  assert (C_is_chain : is_chain (pr1carrier C)).
  2: {
    set (C_Chain := (C,, C_is_chain) : Chain_hsubtype P).
    exists (P_CC C_Chain).
    apply isantisymm_posetRelation. 2: { use progressive_property. }
    refine (least_upper_bound_is_upper_bound (P_CC _) (_,,_)).
    use C_f_closed.
    use C_chain_closed.
    intros [? ?]; assumption.
  }
  (* It remains to show C is a chain. This is the hard (and nonconstructive) part.
  Say [x ∈ C] is a _bottleneck_ if for all y ≤ x in C, either [f y ≤ x] or [y = x].
  We show, in each case by C-induction:
  (1) if x is a bottleneck, then for all y in C, y ≤ x or f x ≤ y;
  (2) every x ∈ C is a bottleneck.
  It follows that C is a chain.
  *)
  set (is_bottleneck := (fun x => ∀ y, C y ⇒ y ≤ x ⇒ (f y ≤ x) ∨ (y = x))
    : hsubtype P).
  assert (bottleneck_comparison : ∀ x, C x ⇒ is_bottleneck x
                                     ⇒ ∀ y, C y ⇒ (y ≤ x) ∨ (f x ≤ y)).
  { intros x C_x x_bottleneck. use C_induction.
    - intros y [y_comp C_y]. split. 2: { use C_f_closed; assumption. }
      apply (hconjtohdisj' y_comp).
      2: { intros leq_fx_y. apply hdisj_in2.
           eapply istrans_posetRelation; try eassumption.
           use progressive_property. }
      intros leq_y_x.
      use (hdisj_monot' (x_bottleneck y _ _)); try assumption.
      + intro; assumption.
      + intro e_yx; destruct e_yx; apply isrefl_posetRelation.
    - intros C' IH_C'. split. 2: { use C_chain_closed; intros; apply IH_C'. }
      destruct (H_LEM (∃ y, C' y ∧ f x ≤ y)) as [C'_passes_fx | C'_notpasses_fx ].
      + apply hdisj_in2.
        refine (factor_through_squash_hProp _ _ C'_passes_fx);
          intros [y [C'_y leq_fx_y]].
        eapply istrans_posetRelation; try eassumption.
        use least_upper_bound_subtype_is_upper_bound; assumption.
      + apply hdisj_in1.
        apply least_upper_bound_univ. intros [y C'_y].
        eapply hdisjtoimpl. apply hdisj_comm, IH_C'.
        intros leq_fx_y. apply C'_notpasses_fx.
        apply hinhpr; exists y. split; assumption.
  }
  assert (all_C_bottleneck : forall x, C x ⇒ is_bottleneck x).
  { use C_induction.
    - intros x [x_bottleneck C_x]. split. 2: { use C_f_closed; assumption. }
      intros y C_y le_y_fx.
      use (hconjtohdisj' (bottleneck_comparison x _ _ y _));
        try assumption.
      2: { intro. apply hdisj_in2, isantisymm_posetRelation; assumption. }
      intro le_yx. apply hdisj_in1.
      use (hconjtohdisj' (x_bottleneck y _ _)); try assumption.
      + intro. eapply istrans_posetRelation; try eassumption.
        use progressive_property.
      + intros e_yx; destruct e_yx. apply isrefl_posetRelation.
    - intros C' IH_C'. split. 2: { use C_chain_closed; intros; apply IH_C'. }
      intros x C_x le_x_supC'.
      destruct (H_LEM (∃ y, C' y ∧ f x ≤ y)) as [ C'_passes_fx | C'_notpasses_fx ].
      { apply hdisj_in1.
        refine (factor_through_squash_hProp _ _ C'_passes_fx); intros [y [? ?]].
        eapply istrans_posetRelation;
          eauto using least_upper_bound_subtype_is_upper_bound.
      }
      apply hdisj_in2.
      apply isantisymm_posetRelation; try assumption.
      apply least_upper_bound_subtype_univ. intros y C'_y.
      destruct (IH_C' (y,,C'_y)) as [y_bottleneck C_y].
      use (hconjtohdisj' (bottleneck_comparison y _ _ x _)); try assumption.
      2: { intro. eapply istrans_posetRelation; try eassumption.
           use progressive_property. }
      intro le_x_y. apply isrefl'_posetRelation, pathsinv0.
      refine (hdisjtoimpl (y_bottleneck x C_x _) _); try assumption.
        use (negexists_to_forallneg_restricted C'_notpasses_fx); assumption.
  }
  intros [x Cx] [y Cy]; simpl pr1carrier.
  assert (comparison : x ≤ y ∨ f y ≤ x).
  { use bottleneck_comparison; try apply all_C_bottleneck; assumption. }
  apply (hdisj_monot' comparison). { intro; assumption. }
  intro. eapply istrans_posetRelation; try eassumption.
  use progressive_property.
Defined.

(** “Pataraia’s Lemma”: on any DCPO, there is a maximal monotone+progressive endo-map.
 This is the main lemma for Pataraia’s theorem, [fixpoint_for_monotone_on_dcpo]. *)
Lemma maximal_progressive_endomorphism_on_dcpo
    {P : Poset} (P_DC : is_directed_complete P)
  : greatest_suchthat (fun f : arrow_Poset P P
      => isaposetmorphism_hProp f ∧ isprogressive f).
Proof.
  (* Outline:
  The monotone progressive maps form a directed set, so have a pointwise sup.
  Also, they are closed under (inhabited) sups.
  So their sup is a maximal such map.
  The proof follows this outline, but reasoning bottom-up/backwards. *)
  set (mon_prog_maps := (fun f : arrow_Poset P P
                              => isaposetmorphism_hProp f ∧ isprogressive f)
                                                                 : hsubtype _).
  cut (carrier (is_greatest_suchthat mon_prog_maps)). (* just munging the goal *)
  { intros f. exact (make_greatest_suchthat (pr1 f) (pr2 f)). }
  cut (carrier (mon_prog_maps ∩ is_least_upper_bound_subtype mon_prog_maps)).
  { use subtype_inc.
    intros ? [? ?]. apply greatest_if_contains_sup; assumption. }
  cut (carrier (is_least_upper_bound_pointwise (@pr1carrier _ mon_prog_maps))).
  { use subtype_inc.
    intros f f_pw_lub; split; [ split | ].
    - eapply isaposetmorphism_pointwise_lub; try eassumption.
      intros [g [g_mon g_prog]]; exact g_mon.
    - eapply progressive_pointwise_lub; try eassumption.
      { intros [g [g_mon g_prog]]; exact g_prog. }
      apply hinhpr. exists (idfun _); split.
      + apply isaposetmorphism_idfun.
      + apply isprogressive_idfun.
    - apply is_least_upper_bound_if_pointwise; assumption.
  }
  (* TODO: perhaps factor the following as “a directed set of functions has a pointwise l.u.b.”? *)
  use (foralltototal _ (fun _ y => is_least_upper_bound _ y)). (* munge goal again *)
  intros x.
  cut (least_upper_bound (fun g : mon_prog_maps => pr1 g x)).
  { intros p. exists p. apply least_upper_bound_property. }
  apply isdirected_lub; try assumption.
  split.
  - apply hinhpr. exists (idfun _); split.
    + apply isaposetmorphism_idfun.
    + apply isprogressive_idfun.
  - intros [f [f_mon f_prog]] [g [g_mon g_prog]].
    apply hinhpr.
    use tpair.
    { exists (f ∘ g); split.
      + apply isaposetmorphism_compose; assumption.
      + apply isprogressive_compose; assumption.
    }
    split; simpl.
    + use f_mon; use g_prog.
    + use f_prog.
Defined.

(** A constructive fixed-point theorem, due to Pataraia.
  This proof transmitted via Dacar and Bauer–Lumsdaine (where it is Thm 3.2). *)
Theorem fixpoint_for_monotone_on_dcpo
    {P : Poset} (P_dir: is_directed_complete P)
    (f : posetmorphism P P) (x : Postfixedpoint f)
  : ∑ y : Fixedpoint f, x ≤ y.
Proof.
  (* Outline:
  - restrict attention to the sub-poset of post-fixed-points of P
  - by Pataraia’s Lemma [maximal_progressive_endomorphism_on_dcpo], there is a maximal monotone progressive map on this sub-poset
  - note that values of this maximal map are fixed points of f
  *)
  revert x.
  set (postfix_f := (fun x => x ≤ f x) : Subposet P).
  assert (postfix_dc : is_directed_complete postfix_f).
  { intros [A A_dir].
    use least_upper_bound_in_subposet.
    { use (isdirected_lub P_dir). assumption. }
    (* Uncannily, [A_dir] works off the bat, without needing to be converted from
    directedness in Q to directedness in P!
    It’s clear that these types are convertible, but impressive that Coq recognises it so easily. *)
    apply least_upper_bound_univ. intros [[x x_postfix] x_A].
    eapply istrans_posetRelation. { apply x_postfix. }
    apply posetmorphism_property.
    refine (least_upper_bound_is_upper_bound _ (_,,_)).
    simple refine (value_in_image _ ((_,,_),,_)); assumption.
  }
  set (max_monprog_map := maximal_progressive_endomorphism_on_dcpo postfix_dc).
  destruct max_monprog_map as [[max_map [max_is_mon max_is_prog]] max_is_max].
  transparent assert (f_restr_postfix : (arrow_Poset postfix_f postfix_f)).
  { intros x. exists (f (pr1 x)).
    apply posetmorphism_property, postfixedpoint_property.
  }
  assert (max_map_gives_fixedpoints : f_restr_postfix ∘ max_map ~ max_map).
  { intros x; apply isantisymm_posetRelation.
    2: { apply postfixedpoint_property. }
    revert x. refine (max_is_max (_,,_)); split.
    - refine (@isaposetmorphism_compose _ _ _ max_map _ f_restr_postfix _).
      { assumption. }
      intros ? ?; apply (posetmorphism_property f).
      (* TODO: make argument order consistent on the [_compose] lemmas *)
    - refine (@isprogressive_compose _ f_restr_postfix max_map _ _).
      2: { assumption. }
      intro; apply postfixedpoint_property.
  }
  intros x. simple refine ((pr1 (max_map x),,_),,_); simpl.
  - exact (maponpaths _ (max_map_gives_fixedpoints x)).
  - use max_is_prog.
Defined.

End Bourbaki_Witt.


(** Finally, we check that the promises listed in the overview have been fulfilled.

  Note: we give these here to ensure that the overview always accurately reflects the theorems of the file.  However, we make them local, since they should probably not be used outside this file — the original versions proved above are the versions intended for use. *)
Section Check_Overview.

  Local Theorem fulfil_Tarski_fixpoint_theorem
    : Tarski_fixpoint_theorem_statement (is_complete) (@isfixedpoint).
  Proof.
    use @Tarski_fixpoint_theorem.
  Defined.

  Local Theorem fulfil_fixpoint_for_monotone_on_dcpo
    : fixpoint_for_monotone_on_dcpo_statement
        (is_directed_complete) (@ispostfixedpoint) (@isfixedpoint).
  Proof.
    use @fixpoint_for_monotone_on_dcpo.
  Defined.

  (** Classical theorem, usually attrbi. Bourbaki (1949) and Witt (1951). *)
  Local Theorem fulfil_Bourbaki_Witt_fixpoint_theorem
    : Bourbaki_Witt_fixpoint_theorem_statement
        (is_chain_complete) (@isprogressive) (@isfixedpoint).
  Proof.
    use @Bourbaki_Witt_fixpoint.
  Defined.

End Check_Overview.
