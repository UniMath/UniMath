(** * Axiom of choice *)

Require Export UniMath.MoreFoundations.DecidablePropositions.

Local Open Scope logic.

Local Open Scope set.

(** We write these axioms as types rather than as axioms, which would assert them to be true, to
    force them to be mentioned as explicit hypotheses whenever they are used. *)

Definition AxiomOfChoice : hProp := ∀ (X:hSet), ischoicebase X.

Definition AxiomOfChoice_surj : hProp := ∀ (X:hSet) (Y:UU) (f:Y→X), issurjective f ⇒ ∃ g, ∀ x, f (g x) = x.

(** Notice that the equation above is a proposition only because X is a set, which is not required
    in the previous formulation.  The notation for "=" currently in effect uses [eqset] instead of
    [paths].  *)

(** ** Implications between forms of the Axiom of Choice *)

Lemma AC_impl2 : AxiomOfChoice <-> AxiomOfChoice_surj.
Proof.
  split.
  - intros AC X Y f surj.
    apply (squash_to_prop (AC _ _ surj) (propproperty _)).
    intro s. apply hinhpr.
    exists (λ y, hfiberpr1 f y (s y)).
    exact  (λ y, hfiberpr2 f y (s y)).
  - intros AC X P ne.
    set (T := (∑ x, P x)%type).
    set (f := pr1 : T -> X).
    assert (k : issurjective f).
    { intros x. simple refine (hinhuniv _ (ne x)); intro p. apply hinhpr. exists (x,,p). reflexivity. }
    simple refine (hinhuniv _ (AC X T f k)).
    intro sec. induction sec as [g e]. apply hinhpr. intro x.
    assert (e' := e x); simpl in e'; clear e.
    induction (g x) as [x' p]; simpl in e'.
    induction e'. exact p.
Defined.

(** ** The Axiom of Choice implies the Law of the Excluded Middle  *)

(** This result is covered in the HoTT book, is due to Radu Diaconescu, "Axiom of choice and
    complementation", Proceedings of the American Mathematical Society, 51 (1975) 176–178, and was
    first mentioned on page 4 in F. W. Lawvere, "Toposes, algebraic geometry and logic (Conf.,
    Dalhousie Univ., Halifax, N.S., 1971)", pp. 1–12, Lecture Notes in Math., Vol. 274, Springer,
    Berlin, 1972.

    The idea is to define an equivalence relation E on bool by setting [E true false := P], to use
    AC to split the surjection f from bool to its quotient by E with a function g, and to observe
    that the function [g ∘ f : bool -> bool] is constant iff P, and to observe that being constant is
    decidable, because equality in [bool] is decidable. *)

Theorem AC_to_LEM : AxiomOfChoice -> LEM.
Proof.
  intros AC P.
  set (ifb := bool_rect (λ _:bool, hProp)).
  set (R := λ x y, ifb (ifb htrue P y) (ifb P htrue y) x); simpl in R.
  assert (e : iseqrel R).
  { repeat split.
    { intros x y z a b. induction x.
      - induction y.
        + induction z; exact b.
        + induction z.
          * exact tt.
          * exact a.
      - induction y.
        + induction z.
          * exact a.
          * exact tt.
        + induction z; exact b. }
    { intros x. induction x; exact tt. }
    { intros x y a. induction x; induction y; exact a. } }
  set (E := R,,e : eqrel bool).
  set (Y := setquotinset E).
  set (f := setquotpr E : bool -> Y).
  assert (q := pr1 AC_impl2 AC Y boolset f (issurjsetquotpr E)).
  apply (squash_to_prop q).
  { apply isapropdec. apply propproperty. }
  clear q.
  intro sec.
  induction sec as [g h].
  (* prove P iff [g ∘ f] is constant *)
  assert (coll : P <-> g (f true) = g (f false)).
  { split.
    { intro p. apply maponpaths. apply iscompsetquotpr. exact p. }
    { intro q.
      assert (r : f true = f false).
      { intermediate_path (f (g (f true))).
        { apply pathsinv0, h. }
        intermediate_path (f (g (f false))).
        { apply maponpaths, q. }
        { apply h. } }
      change (E true false).
      apply (invmap (weqpathsinsetquot _ _ _)).
      change (f true = f false).
      exact r. } }
  (* the equation is decidable, and thus P is decidable, by the lemma above *)
  apply (logeq_dec (issymm_logeq _ _ coll)).
  apply isdeceqbool.
Defined.

(* end of file *)
