
(** * The Bourbaki-Witt theorem and variants

This file aims to state and develop the Bourbaki-Witt and Tarski fixed-point theorems and their variants, especially constructively provable ones.

In particular, it aims to formalise some of the results of Pataraia, Dacar, Bauer, and Lumsdaine, given in https://arxiv.org/abs/1201.0340 .

Note: There is some duplication with material in [Algebra.Dcpo] and [Combinatorics.WellOrderedSets], which should ideally be refactored (as indeed there is some ducplication between between those files).
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
  Identity Coercion id_least_upper_bound : least_upper_bound >-> least_suchthat.

  Definition least_upper_bound_is_upper_bound {I} {p : I -> P}
             (x : least_upper_bound p)
    : isupperbound p x
  := least_suchthat_satisfies x.

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
      := (fun A => (∀ C' : Chain P, (∏ y:C', A (pr1 y)) ⇒ A (P_CC C')))
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
    set (C_Chain := (C,, C_is_chain) : Chain P).
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
      refine (hconjtohdisj _ _ _ _ y_comp); split.
      2: { intros leq_fx_y. apply hdisj_in2.
           eapply istrans_posetRelation; try eassumption.
           use progressive_property. }
      intros leq_y_x.
      eapply hdisj_monot. 3: { use (x_bottleneck y); assumption. }
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
      refine (hconjtohdisj _ _ _ _ (bottleneck_comparison x _ _ y _));
        try assumption; split.
      2: { intro. apply hdisj_in2, isantisymm_posetRelation; assumption. }
      intro le_yx. apply hdisj_in1.
      refine (hconjtohdisj _ _ _ _ (x_bottleneck y _ _)); try assumption; split.
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
      use (hconjtohdisj _ _ _ _ (bottleneck_comparison y _ _ x _));
        try assumption; split.
      2: { intro. eapply istrans_posetRelation; try eassumption.
           use progressive_property. }
      intro le_x_y. apply isrefl'_posetRelation, pathsinv0.
      refine (hdisjtoimpl (y_bottleneck x C_x _) _); try assumption.
        use (negexists_to_forallneg_restricted C'_notpasses_fx); assumption.
  }
  intros [x Cx] [y Cy]; simpl pr1carrier.
  assert (comparison : x ≤ y ∨ f y ≤ x).
  { use bottleneck_comparison; try apply all_C_bottleneck; assumption. }
  refine (hdisj_monot _ _ comparison). { intro; assumption. }
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
