(** * Additionals theorems *)

Require Export UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.
Require Export UniMath.Combinatorics.FiniteSequences.
Require Export UniMath.Foundations.NaturalNumbers.

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

(** ** hProp *)

Lemma isaproptotal2' {X : UU} (P : X → UU) :
  isaset X →
  isPredicate P →
  (∏ x y : X, P x → P y → x = y) →
  isaprop (∑ x : X, P x).
Proof.
  intros X P HX HP Heq x y ; simpl.
  eapply iscontrweqb.
  apply subtypeInjectivity.
  exact HP.
  rewrite (Heq (pr1 y) (pr1 x)).
  apply iscontrloopsifisaset.
  exact HX.
  exact (pr2 y).
  exact (pr2 x).
Qed.

Lemma hinhuniv' {P X : UU} :
  isaprop P → (X → P) → (∥ X ∥ → P).
Proof.
  intros P X HP Hx.
  apply (hinhuniv (P := hProppair _ HP)).
  exact Hx.
Qed.
Lemma hinhuniv2' {P X Y : UU} :
  isaprop P → (X → Y → P) → (∥ X ∥ → ∥ Y ∥ → P).
Proof.
  intros P X Y HP Hxy.
  apply (hinhuniv2 (P := hProppair _ HP)).
  exact Hxy.
Qed.

(** ** A new tactic *)

Ltac apply_pr2 T :=
  first [ refine (pr2 (T) _)
        | refine (pr2 (T _) _)
        | refine (pr2 (T _ _) _)
        | refine (pr2 (T _ _ _) _)
        | refine (pr2 (T _ _ _ _) _)
        | refine (pr2 (T _ _ _ _ _) _)
        | refine (pr2 (T))
        | refine (pr2 (T _))
        | refine (pr2 (T _ _))
        | refine (pr2 (T _ _ _))
        | refine (pr2 (T _ _ _ _))
        | refine (pr2 (T _ _ _ _ _)) ].

Ltac apply_pr2_in T H :=
  first [ apply (pr2 (T)) in H
        | apply (λ H0, pr2 (T H0)) in H
        | apply (λ H0 H1, pr2 (T H0 H1)) in H
        | apply (λ H0 H1 H2, pr2 (T H0 H1 H2)) in H
        | apply (λ H0 H1 H2 H3, pr2 (T H0 H1 H2 H3)) in H
        | apply (λ H0 H1 H2 H3 H4, pr2 (T H0 H1 H2 H3 H4)) in H ].

(** ** About nat *)

Lemma max_le_l : ∏ n m : nat, (n ≤ max n m)%nat.
Proof.
  induction n as [ | n IHn] ; simpl max.
  - intros m ; reflexivity.
  - induction m as [ | m _].
    + now apply isreflnatleh.
    + now apply IHn.
Qed.
Lemma max_le_r : ∏ n m : nat, (m ≤ max n m)%nat.
Proof.
  induction n as [ | n IHn] ; simpl max.
  - intros m ; now apply isreflnatleh.
  - induction m as [ | m _].
    + reflexivity.
    + now apply IHn.
Qed.

(** ** More about Sequence *)

Definition singletonSequence {X} (A : X) : Sequence X := (1 ,, λ _, A).
Definition pairSequence {X} (A B : X) : Sequence X.
Proof.
  intros X A B.
  exists 2.
  intros m.
  induction m as [m _].
  induction m as [ | _ _].
  exact A.
  exact B.
Defined.

(** ** More about sets *)
(** union *)

Definition union {X : UU} (P : (X → hProp) → hProp) : X → hProp :=
  λ x : X, ∃ A : X → hProp, P A × A x.

Lemma union_hfalse {X : UU} :
  union (λ _ : X → hProp, hfalse) = (λ _ : X, hfalse).
Proof.
  intros X.
  apply funextfun ; intros x.
  apply hPropUnivalence.
  - apply hinhuniv.
    intros A.
    apply (pr1 (pr2 A)).
  - apply fromempty.
Qed.

Lemma union_or {X : UU} :
  ∏ A B : X → hProp,
    union (λ C : X → hProp, C = A ∨ C = B)
    = (λ x : X, A x ∨ B x).
Proof.
  intros X A B.
  apply funextfun ; intro x.
  apply hPropUnivalence.
  - apply hinhuniv.
    intros C.
    generalize (pr1 (pr2 C)).
    apply hinhfun.
    apply sumofmaps.
    + intro e.
      rewrite <- e.
      left.
      apply (pr2 (pr2 C)).
    + intro e.
      rewrite <- e.
      right.
      apply (pr2 (pr2 C)).
  - apply hinhfun ; apply sumofmaps ; [ intros Ax | intros Bx].
    + exists A.
      split.
      apply hinhpr.
      now left.
      exact Ax.
    + exists B.
      split.
      apply hinhpr.
      now right.
      exact Bx.
Qed.

Lemma union_hProp {X : UU} :
  ∏ (P : (X → hProp) → hProp),
    (∏ (L : (X → hProp) → hProp), (∏ A, L A → P A) → P (union L))
    → (∏ A B, P A → P B → P (λ x : X, A x ∨ B x)).
Proof.
  intros X.
  intros P Hp A B Pa Pb.
  rewrite <- union_or.
  apply Hp.
  intros C.
  apply hinhuniv.
  now apply sumofmaps ; intros ->.
Qed.

(** finite intersection *)

Definition finite_intersection {X : UU} (P : Sequence (X → hProp)) : X → hProp.
Proof.
  intros X P.
  intros x.
  simple refine (hProppair _ _).
  apply (∏ n, P n x).
  apply (impred_isaprop _ (λ _, propproperty _)).
Defined.

Lemma finite_intersection_htrue {X : UU} :
  finite_intersection nil = (λ _ : X, htrue).
Proof.
  intros X.
  apply funextfun ; intros x.
  apply hPropUnivalence.
  - intros _.
    apply tt.
  - intros _ m.
    generalize (pr1 m) (pr2 m).
    intros m' Hm.
    apply fromempty.
    revert Hm.
    apply negnatlthn0.
Qed.

Lemma finite_intersection_1 {X : UU} :
  ∏ (A : X → hProp),
    finite_intersection (singletonSequence A) = A.
Proof.
  intros X.
  intros A.
  apply funextfun ; intros x.
  apply hPropUnivalence.
  - intros H.
    simple refine (H _).
    now exists 0.
 - intros Lx m.
   exact Lx.
Qed.

Lemma finite_intersection_and {X : UU} :
  ∏ A B : X → hProp,
    finite_intersection (pairSequence A B)
    = (λ x : X, A x ∧ B x).
Proof.
  intros X.
  intros A B.
  apply funextfun ; intro x.
  apply hPropUnivalence.
  - intros H.
    split.
    simple refine (H (0,,_)).
    reflexivity.
    simple refine (H (1,,_)).
    reflexivity.
  - intros H m ; simpl.
    change m with (pr1 m,,pr2 m).
    generalize (pr1 m) (pr2 m).
    clear m.
    intros m Hm.
    induction m as [ | m _].
    + apply (pr1 H).
    + apply (pr2 H).
Qed.

Lemma finite_intersection_case {X : UU} :
  ∏ (L : Sequence (X → hProp)),
  finite_intersection L =
  sumofmaps (λ _ _, htrue)
            (λ (AB : (X → hProp) × Sequence (X → hProp)) (x : X), pr1 AB x ∧ finite_intersection (pr2 AB) x)
            (disassembleSequence L).
Proof.
  intros X.
  intros L.
  apply funextfun ; intros x.
  apply hPropUnivalence.
  - intros Hx.
    induction L as [n L].
    induction n as [ | n _] ; simpl.
    + apply tt.
    + split.
      * simple refine (Hx _).
      * intros m.
        simple refine (Hx _).
  - induction L as [n L].
    induction n as [ | n _] ; simpl.
    + intros _ n.
      apply fromempty.
      induction (negnatlthn0 _ (pr2 n)).
    + intros Hx m.
      change m with (pr1 m,,pr2 m).
      generalize (pr1 m) (pr2 m) ;
        clear m ;
        intros m Hm.
      induction (natlehchoice _ _ (natlthsntoleh _ _ Hm)) as [Hm' | ->].
      generalize (pr2 Hx (m,,Hm')).
      unfold funcomp, dni_lastelement ; simpl.
      assert (H : Hm = natlthtolths m n Hm' ).
      { apply (pr2 (natlth m (S n))). }
      now rewrite H.
      assert (H : lastelement = (n,, Hm)).
      { now apply subtypeEquality_prop. }
      rewrite <- H.
      exact (pr1 Hx).
Qed.
Lemma finite_intersection_append {X : UU} :
  ∏ (A : X → hProp) (L : Sequence (X → hProp)),
    finite_intersection (append L A) = (λ x : X, A x ∧ finite_intersection L x).
Proof.
  intros X A L.
  rewrite finite_intersection_case.
  simpl.
  rewrite append_fun_compute_2.
  apply funextfun ; intro x.
  apply maponpaths.
  apply map_on_two_paths.
  - induction L as [n L] ; simpl.
    apply maponpaths.
    apply funextfun ; intro m.
    unfold funcomp.
    rewrite <- replace_dni_last.
    apply append_fun_compute_1.
  - reflexivity.
Qed.

Lemma finite_intersection_hProp {X : UU} :
  ∏ (P : (X → hProp) → hProp),
    (∏ (L : Sequence (X → hProp)), (∏ n, P (L n)) → P (finite_intersection L))
    <-> (P (λ _, htrue) × (∏ A B, P A → P B → P (λ x : X, A x ∧ B x))).
Proof.
  intros X P.
  split.
  - split.
    + rewrite <- finite_intersection_htrue.
      apply X0.
      intros n.
            induction (negnatlthn0 _ (pr2 n)).
    + intros A B Pa Pb.
      rewrite <- finite_intersection_and.
      apply X0.
      intros n.
      change n with (pr1 n,,pr2 n).
      generalize (pr1 n) (pr2 n) ;
        clear n ;
        intros n Hn.
      now induction n as [ | n _] ; simpl.
  - intros Hp.
    apply (Sequence_rect (P := λ L : Sequence (X → hProp),
                                     (∏ n : stn (length L), P (L n)) → P (finite_intersection L))).
    + intros _.
      rewrite finite_intersection_htrue.
      exact (pr1 Hp).
    + intros L A IHl Hl.
      rewrite finite_intersection_append.
      apply (pr2 Hp).
      * rewrite <- (append_fun_compute_2 L A).
        now apply Hl.
      * apply IHl.
        intros n.
        rewrite <- (append_fun_compute_1 L A).
        apply Hl.
Qed.