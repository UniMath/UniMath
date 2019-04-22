(** * Axiom of choice *)

Require Export UniMath.MoreFoundations.DecidablePropositions.
Require Export UniMath.MoreFoundations.Sets.

(** ** Preliminaries  *)

Lemma pr1_issurjective {X : UU} {P : X -> UU} :
  (∏ x : X, ∥ P x ∥) -> issurjective (pr1 : (∑ x, P x) -> X).
(* move upstream later *)
Proof.
  intros ne x. simple refine (hinhuniv _ (ne x)).
  intros p. apply hinhpr.
  exact ((x,,p),,idpath _).
Defined.

(** ** Characterize equivalence relations on [bool] *)

Definition eqrel_on_bool (P:hProp) : eqrel boolset.
(* an equivalence relation on bool amounts to a single proposition *)
Proof.
  set (ifb := bool_rect (λ _:bool, hProp)).
  exists (λ x y, ifb (ifb htrue P y) (ifb P htrue y) x).
  repeat split.
  { intros x y z a b.
    induction x.
    - induction z.
      + exact tt.
      + induction y.
        * exact b.
        * exact a.
    - induction z.
      + induction y.
        * exact a.
        * exact b.
      + exact tt. }
  { intros x. induction x; exact tt. }
  { intros x y a. induction x; induction y; exact a. }
Defined.

Lemma eqrel_on_bool_iff (P:hProp) (E := eqrel_on_bool P) (f := setquotpr E) : f true = f false <-> P.
Proof.
  split.
  { intro q. change (E true false). apply (invmap (weqpathsinsetquot _ _ _)).
    change (f true = f false). exact q. }
  { intro p. apply iscompsetquotpr. exact p. }
Defined.

(** ** Statements of Axiom of Choice *)

Local Open Scope logic.

Local Open Scope set.

(** We write these axioms as types rather than as axioms, which would assert them to be true, to
    force them to be mentioned as explicit hypotheses whenever they are used. *)

Definition AxiomOfChoice : hProp := ∀ (X:hSet), ischoicebase X.

Definition AxiomOfChoice_surj : hProp :=
  ∀ (X:hSet) (Y:UU) (f:Y→X), issurjective f ⇒ ∃ g, ∀ x, f (g x) = x.
(** Notice that the equation above is a proposition only because X is a set, which is not required
    in the previous formulation.  The notation for "=" currently in effect uses [eqset] instead of
    [paths].  *)

(** ** Implications between forms of the Axiom of Choice *)

Lemma AC_impl2 : AxiomOfChoice <-> AxiomOfChoice_surj.
Proof.
  split.
  - intros AC X Y f surj.
    use (squash_to_prop (AC _ _ surj) (propproperty _)).
    intro s.
    use hinhpr.
    use tpair.
    + exact (λ y, hfiberpr1 f y (s y)).
    + exact (λ y, hfiberpr2 f y (s y)).
  - intros AC X P ne.
    use (hinhuniv _ (AC X _ _ (pr1_issurjective ne))).
    intros sec. use hinhpr. intros x.
    induction (pr2 sec x). exact (pr2 (pr1 sec x)).
Defined.

(** ** The Axiom of Choice implies a type receives a surjective map from a set *)

Theorem SetCovering (X:Type) : AxiomOfChoice -> ∃ (S:hSet) (f:S->X), issurjective f.
Proof.
  (** We use the axiom of choice to find a splitting f of the projection map g from X
     onto its set [pi0 X] of connected components.  Since the image of f contains one
     point in every component of X, f is surjective.
   *)
  intros ac.
  assert (ac' := pr1 AC_impl2 ac); clear ac; unfold AxiomOfChoice_surj in ac'.
  set (S := pi0 X : hSet).
  set (g := pi0pr X : X -> S).
  assert (f := ac' _ _ g (issurjsetquotpr _)); clear ac'.
  apply (squash_to_prop f).
  { apply propproperty. }
  clear f; intros [f eqn].
  apply hinhpr.
  exists S.
  exists f.
  intros x.
  use (@squash_to_prop (f (g x) = x)%type).
  { apply (invmap (weqpathsinsetquot (pathseqrel X) _ _)).
    change (g (f (g x)) = g x)%type.
    exact (eqn (g x)). }
  { apply propproperty. }
  intros e.
  apply hinhpr.
  exists (g x).
  exact e.
Defined.

(** ** The Axiom of Choice implies the Law of the Excluded Middle  *)

(** This result is covered in the HoTT book, is due to Radu Diaconescu, "Axiom of choice and
    complementation", Proceedings of the American Mathematical Society, 51 (1975) 176–178, and was
    first mentioned on page 4 in F. W. Lawvere, "Toposes, algebraic geometry and logic (Conf.,
    Dalhousie Univ., Halifax, N.S., 1971)", pp. 1–12, Lecture Notes in Math., Vol. 274, Springer,
    Berlin, 1972.

    The idea is to define an equivalence relation E on bool by setting [E true false := P], to use
    AC to split the surjection f from bool to its quotient Y by E with a function g, and to observe
    bool has decidable equality, and thus so does Y, because then Y is a retract of bool, to use
    that to decide whether [f true = f false], and thus to decide P. *)

Theorem AC_to_LEM : AxiomOfChoice -> LEM.
Proof.
  intros AC P.
  set (f := setquotpr _ : bool -> setquotinset (eqrel_on_bool P)).
  assert (q := pr1 AC_impl2 AC _ _ f (issurjsetquotpr _)).
  apply (squash_to_prop q).
  { apply isapropdec, propproperty. }
  intro sec. induction sec as [g h].
  (* reduce decidability of P to decidability of [f true = f false] *)
  apply (logeq_dec (eqrel_on_bool_iff P)).
  (* a retract of a type with decidable equality has decidable equality *)
  apply (retract_dec f g h isdeceqbool).
Defined.

(** A weaker Axiom of Choice *)

(** Having proved above that the Axiom of Choice implies the Law of the Excluded Middle, we would
    like to formulate a weaker axiom of choice that would be usable in formalization, but without
    implying the Law of the Excluded Middle, thus making it a more acceptable omniscience principle.
    Our idea here is to add the hypothesis that the base set have decidable equality.  Classically,
    there is no difference between the two axioms.  Recall from [isasetifdeceq] that a type with
    decidable equality is a set, so we don't include being a set explicitly in the statement of the
    axiom. *)

Definition AxiomOfDecidableChoice : hProp := ∀ (X:UU), isdeceq X ⇒ ischoicebase X.

Theorem AC_iff_ADC_and_LEM : AxiomOfChoice ⇔ AxiomOfDecidableChoice ∧ LEM.
Proof.
  split.
  - intros AC. split.
    + intros X i. exact (AC (make_hSet X (isasetifdeceq X i))).
    + exact (AC_to_LEM AC).
  - intros [adc lem] X. refine (adc X _). intros x y. exact (lem (x = y)).
Defined.
