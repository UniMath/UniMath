
(** * The Bourbaki-Witt theorem and variants

This file aims to state and develop the Bourbaki-Witt and Tarski fixed-point theorems and their variants, especially constructively provable ones.

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

(** ** Background material

As ever, all these should eventually be upstreamed, and unified with overlapping material upstream where possible. *)
Section Auxiliary.

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

Definition subtype_binaryintersection {X} (A B : hsubtype X) : hsubtype X
  := fun x => A x ∧ B x.

End Auxiliary.

Notation "A ∩ B" := (subtype_binaryintersection A B)
                              (at level 40, left associativity) : subtype.
  (* precedence tighter than "⊆", also than "-" [subtype_difference].  *)
  (* in agda-input method, type \cap *)

Notation "A ∪ B" := (subtype_binaryunion A B)
                              (at level 40, left associativity) : subtype.
  (* precedence tighter than "⊆", also than "-" [subtype_difference].  *)
  (* in agda-input method, type \cup or ∪ *)

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

End ProgressiveMaps.

(** Monotone maps are precisely poset morphisms, and [isaposetmorphism] is defined as such in [Foundations.Sets]. *)
Section MonotoneMaps.

Definition posetmorphism_property {P Q} (f : posetmorphism P Q)
  : isaposetmorphism f
:= pr2 f.

End MonotoneMaps.

(** ** Fixpoints of endofunctions *)

Section Fixpoints.

Definition Fixedpoint {P : Poset} (f : P -> P) : UU
  := carrier (fun (x:P) => eqset (f x) x).

Coercion pr1_Fixedpoint {P : Poset} {f : P -> P} : Fixedpoint f -> P
:= pr1carrier _.

Definition fixedpoint_property  {P : Poset} {f : P -> P} (x : Fixedpoint f)
  : f x = x
:= pr2 x.

Definition Postfixedpoint {P : Poset} (f : P -> P) : UU
  := carrier (fun (x:P) => x ≤ (f x)).

Coercion pr1_Postfixedpoint {P : Poset} {f : P -> P} : Postfixedpoint f -> P
:= pr1carrier _.

Definition postfixedpoint_property  {P : Poset} {f : P -> P} (x : Postfixedpoint f)
  : x ≤ f x
:= pr2 x.

End Fixpoints.

(** ** Completeness properties *)

Section LeastUpperBounds.

  (* We use the treatment of upper bounds from [Algebra.Dcpo], but give a slightly different treatment of _least_ upper bounds,
   factoring out the general definition of “least elements” of a family, or satisfying a predicate. *)

  Context {P : Poset}.

  Definition islowerbound {I} (p : I -> P) (x : P) : hProp
  := ∀ i : I, x ≤ p i.

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
  Identity Coercion id_least_upper_bound : least_upper_bound >-> least_suchthat.

  Definition least_upper_bound_is_upper_bound {I} {p : I -> P}
             (x : least_upper_bound p)
    : isupperbound p x
  := least_suchthat_satisfies x.

  (* TODO: it would be natural to just refactor [isupperbound] in [Algebra.Dcpo]
  as an hProp from the start, using [∀] and so on.  However, that turns out
  to slightly interfere with the use of [apply] on lemmas in that file, espcially
  bidirectional such as [pointwiselub_islubpointwise]. Is that cosmetic cost
  worth paying?  Or can it be avoided? *)
  Definition isupperbound_hprop {P:Poset} {I} (p : I -> P) (x:P) : hProp
  := make_hProp _ (isaprop_isupperbound p x).

  (** It’s useful to define [least_upper_bound] as above, for interaction with [upper_bound], etc; but also helpful to have a standalone predicate version. *)
  Definition is_least_upper_bound {I} (p : I -> P) (x : P) : hProp
    := isupperbound_hprop p x
       ∧ islowerbound (pr1carrier (isupperbound_hprop p)) x.

  Definition make_least_upper_bound {I} {p : I -> P}
      {x:P} (x_lub : is_least_upper_bound p x)
    : least_upper_bound p
  := ((x,, pr1 x_lub),, pr2 x_lub).

  Definition least_upper_bound_property {I} {p : I -> P}
      (x : least_upper_bound p)
    : is_least_upper_bound p x
  := (pr2 (pr1 x),, pr2 x).

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

  (** Specialisation of the above functions to least upper bounds of _subsets_
   — a common use-case, and the functions are often easier to use in this form. *)

  Definition least_upper_bound_subtype_is_upper_bound {A : hsubtype P}
      (x : least_upper_bound (pr1carrier A)) {y : P} (A_y : A y)
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

End LeastUpperBounds.

Section Chains.

  Definition comparable {P : Poset} (x y : P) : hProp
  := (x ≤ y) ∨ (y ≤ x).

  Definition is_chain {P : Poset} {I} (p : I -> P) : UU
  := ∏ i j : I, comparable (p i) (p j).

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
      {I : Type} (p : I -> P)
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

End Chains.

Section Completeness.

  Definition is_chain_complete (P : Poset) : UU
  := ∏ C : Chain_hsubtype P, least_upper_bound (chain_family C).

  (* [is_chain_complete] is defined just in terms of hsubtype-chains, to agree with the classical definition and keep its quantification “small”.

  However, it implies least upper bounds for arbitarily-indexed chains. *)

  Definition chain_lub {P : Poset} (P_CC : is_chain_complete P)
      (p : Chain P)
    : least_upper_bound p.
  Proof.
    set (p_hsubtype := fun x : P => ∥ hfiber p x∥).
    assert (p_hsubtype_chain : is_chain (pr1carrier p_hsubtype)).
    { intros [x Hx] [y Hy]. simpl pr1carrier.
      refine (factor_through_squash_hProp _ _ Hx);
        intros [i e_ix]; destruct e_ix.
      refine (factor_through_squash_hProp _ _ Hy);
        intros [j e_jy]; destruct e_jy.
      apply chain_property.
    }
    set (p_Chain := (p_hsubtype ,, p_hsubtype_chain) : Chain_hsubtype P).
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
      apply (least_upper_bound_univ (make_least_upper_bound x_lub)).
      apply is_upper_bound_in_subposet; assumption.
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

Products of posets, and of classes of functions *)

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

  (** Note: could also be called e.g. [Poset_product], or various other names.
   This name gives better consistency with the rest of UniMath, but is less natural from a classical mathematical perspective. *)
  (* TODO: consider naming convention. Are there analogous constructions elsewhere in UniMath that this should fit with? *)
  Definition forall_Poset {X:UU} (P : X -> Poset) : Poset.
  Proof.
    use make_Poset. { exact (forall_hSet P). }
    use make_PartialOrder. { apply pointwiseorder. }
    apply ispartialorder_pointwiseorder.
  Defined.

  Definition isupperbound_pointwise {X:UU} (P : X -> Poset)
      {I} {f : I -> forall_Poset P}
      {g : forall_Poset P}
    : isupperbound f g <-> forall x, isupperbound (fun i => f i x) (g x).
  Proof.
    split; intro H; repeat intro; use H.
  Defined.

  Definition is_least_upper_bound_pointwise {X:UU} (P : X -> Poset)
      {I} {f : I -> forall_Poset P}
      {g : forall_Poset P}
    : (forall x, is_least_upper_bound (fun i => f i x) (g x))
      -> is_least_upper_bound f g.
  Proof.
    intro pointwise_lub.
    set (g_pwlub := fun x => make_least_upper_bound (pointwise_lub x)).
    split.
    - intros i x.
      apply (least_upper_bound_is_upper_bound (g_pwlub x)).
    - intros [g' g'_ub] x.
      apply (least_upper_bound_univ (g_pwlub x)).
      apply isupperbound_pointwise, g'_ub.
  Defined.

End Function_Posets.

(** ** Bourbaki-Witt for various classes of posets

The classical Bourbaki–Witt theorem says: Any progressive map on a chain-complete partial order has a fixed point.

Constructively, this may fail, as shown in Bauer–Lumsdaine https://arxiv.org/abs/1201.0340. Here we aim to give both the classical theorem, and some weaker constructively-provable results.

*)

Section Bourbaki_Witt.

Definition Bourbaki_Witt_property (P : Poset)
  := ∏ (f : Progressive_map P), Fixedpoint f.

(** Theorem traditionally credited to Bourbaki (1949) and Witt (1951). This proof is based on Lang, Algebra (2002), Appendix 2, Thm 2.1. *)
Theorem Bourbaki_Witt
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
  set (is_bottleneck := (fun x => ∀ y, C y ⇒ y ≤ x ⇒ (f y ≤ x) ∨ (eqset y x))
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

(** A constructive fixed-point theorem, originally due to Pataria; this proof transmitted via Dacar and Bauer–Lumsdaine (where it is Thm 3.2). *)
Theorem fixpoint_for_monotone_on_dcpo
    {P : dcpo} (f : posetmorphism P P) (x : Postfixedpoint f)
  : ∑ y : Fixedpoint f, x ≤ y.
Proof.
  (* Sketch:
  - restrict attention to the sub-poset Q of post-fixed-points of P
  - consider the poset of monotone, progressive maps Q -> Q with the pointwise order
  - show that this is directed-complete
  - show that this is itself directed, so has a maximal element
  - values of this maximal element must be fixed points

  Ingredients needed
  - a good treatment of sub-posets, their induced orders, and completness properties
  - a good treatment of posets of functions, and more generally, producs of posets, and their completeness properties
  *)
Abort.

End Bourbaki_Witt.
