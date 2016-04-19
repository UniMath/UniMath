(** * Additionals theorems *)

Require Export UniMath.Foundations.Basics.Sets.
Require Export UniMath.Foundations.Combinatorics.FiniteSequences.
Require Export UniMath.Foundations.NumberSystems.NaturalNumbers.
Require Import UniMath.Ktheory.Utilities.

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

(** ** hProp *)

Lemma isaproptotal2' {X : UU} (P : X -> UU) :
  isaset X ->
  isPredicate P ->
  (∀ x y : X, P x -> P y -> x = y) ->
  isaprop (Σ x : X, P x).
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
  isaprop P -> (X -> P) -> (∥ X ∥ -> P).
Proof.
  intros P X HP Hx.
  apply (hinhuniv (P := hProppair _ HP)).
  exact Hx.
Qed.
Lemma hinhuniv2' {P X Y : UU} :
  isaprop P -> (X -> Y -> P) -> (∥ X ∥ -> ∥ Y ∥ -> P).
Proof.
  intros P X Y HP Hxy.
  apply (hinhuniv2 (P := hProppair _ HP)).
  exact Hxy.
Qed.

(** ** About nat *)

Lemma max_le_l : ∀ n m : nat, (n ≤ max n m)%nat.
Proof.
  induction n ; simpl max.
  - intros ; reflexivity.
  - destruct m.
    + now apply isreflnatleh.
    + now apply IHn.
Qed.
Lemma max_le_r : ∀ n m : nat, (m ≤ max n m)%nat.
Proof.
  induction n ; simpl max.
  - intros ; now apply isreflnatleh.
  - destruct m.
    + reflexivity.
    + now apply IHn.
Qed.

(** ** More about Sequence *)

Definition singletonSequence {X} (A : X) : Sequence X := (1 ,, λ _, A).
Definition pairSequence {X} (A B : X) : Sequence X := (2 ,, λ m, match (pr1 m) with | O => A | _ => B end).

(** ** More about sets *)
(** union *)

Definition union {X : UU} (P : (X -> hProp) -> hProp) : X -> hProp :=
  λ x : X, ∃ A : X -> hProp, P A × A x.

Lemma union_hfalse {X : UU} :
  union (λ _ : X -> hProp, hfalse) = (λ _ : X, hfalse).
Proof.
  intros X.
  apply funextfun ; intros x.
  apply uahp.
  - apply hinhuniv.
    intros A.
    apply (pr1 (pr2 A)).
  - apply fromempty.
Qed.

Lemma union_or {X : UU} :
  ∀ A B : X -> hProp,
    union (λ C : X -> hProp, C = A ∨ C = B)
    = (λ x : X, A x ∨ B x).
Proof.
  intros X A B.
  apply funextfun ; intro x.
  apply uahp.
  - apply hinhuniv.
    intros C.
    generalize (pr1 (pr2 C)).
    apply hinhfun.
    intros [<- | <-].
    + left.
      apply (pr2 (pr2 C)).
    + right.
      apply (pr2 (pr2 C)).
  - apply hinhfun ; intros [Ax | Bx].
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
  ∀ (P : (X -> hProp) -> hProp),
    (∀ (L : (X -> hProp) -> hProp), (∀ A, L A -> P A) -> P (union L))
    -> (∀ A B, P A -> P B -> P (λ x : X, A x ∨ B x)).
Proof.
  intros X.
  intros P Hp A B Pa Pb.
  rewrite <- union_or.
  apply Hp.
  intros C.
  apply hinhuniv.
  now intros [-> | ->].
Qed.

(** finite intersection *)

Definition finite_intersection {X : UU} (P : Sequence (X -> hProp)) : X -> hProp.
Proof.
  intros X P.
  intros x.
  simple refine (hProppair _ _).
  apply (∀ n, P n x).
  apply (impred_isaprop _ (λ _, propproperty _)).
Defined.

Lemma finite_intersection_htrue {X : UU} :
  finite_intersection nil = (λ _ : X, htrue).
Proof.
  intros X.
  apply funextfun ; intros x.
  apply uahp.
  - intros _.
    apply tt.
  - intros _ (m,Hm).
    apply fromempty.
    revert Hm.
    apply negnatlthn0.
Qed.

Lemma finite_intersection_1 {X : UU} :
  ∀ (A : X -> hProp),
    finite_intersection (singletonSequence A) = A.
Proof.
  intros X.
  intros A.
  apply funextfun ; intros x.
  apply uahp.
  - intros H.
    apply H.
    now exists 0.
  - intros Lx (m,Hm).
    destruct m.
    exact Lx.
    apply fromempty.
    easy.
Qed.

Lemma finite_intersection_and {X : UU} :
  ∀ A B : X -> hProp,
    finite_intersection (pairSequence A B)
    = (λ x : X, A x ∧ B x).
Proof.
  intros X.
  intros A B.
  apply funextfun ; intro x.
  apply uahp.
  - intros H.
    split.
    simple refine (H (0,,_)).
    reflexivity.
    simple refine (H (1,,_)).
    reflexivity.
  - intros H (m,Hm) ; simpl.
    destruct m.
    apply (pr1 H).
    destruct m.
    apply (pr2 H).
    easy.
Qed.

Lemma finite_intersection_case {X : UU} :
  ∀ (L : Sequence (X -> hProp)),
    finite_intersection L = match disassembleSequence L with
                            | ii1 _ => λ _, htrue
                            | ii2 (A,,B) => (λ x : X, A x ∧ finite_intersection B x)
                            end.
Proof.
  intros X.
  intros L.
  apply funextfun ; intros x.
  apply uahp.
  - intros Hx.
    destruct L as [n L].
    destruct n ; simpl.
    + apply tt.
    + split.
      apply Hx.
      intros m.
      apply Hx.
  - destruct L as [n L].
    destruct n ; simpl.
    + intros _ (n,Hn).
      now apply fromempty.
    + intros Hx (m,Hm).
      destruct (natlehchoice _ _ (natlthsntoleh _ _ Hm)) as [Hm' | ->].
      generalize (pr2 Hx (m,,Hm')).
      unfold funcomp, dni_lastelement ; simpl.
      assert (H : Hm = natlthtolths m n Hm' ).
      { apply (pr2 (natlth m (S n))). }
      now rewrite H.
      assert (H : (lastelement n) = (n,, Hm)).
      { now apply subtypeEquality_prop. }
      rewrite <- H.
      exact (pr1 Hx).
Qed.
Lemma finite_intersection_append {X : UU} :
  ∀ (A : X -> hProp) (L : Sequence (X -> hProp)),
    finite_intersection (append L A) = (λ x : X, A x ∧ finite_intersection L x).
Proof.
  intros.
  rewrite finite_intersection_case.
  simpl.
  rewrite append_fun_compute_2.
  apply funextfun ; intro x.
  apply maponpaths.
  apply map_on_two_paths.
  destruct L ; simpl.
  apply maponpaths.
  apply funextfun ; intro n.
  apply append_fun_compute_1.
  reflexivity.
Qed.

Lemma finite_intersection_hProp {X : UU} :
  ∀ (P : (X -> hProp) -> hProp),
    (∀ (L : Sequence (X -> hProp)), (∀ n, P (L n)) -> P (finite_intersection L))
    <-> (P (λ _, htrue) × (∀ A B, P A -> P B -> P (λ x : X, A x ∧ B x))).
Proof.
  intros X P.
  split.
  - split.
    + rewrite <- finite_intersection_htrue.
      apply X0.
      now intros (n,Hn).
    + intros A B Pa Pb.
      rewrite <- finite_intersection_and.
      apply X0.
      intros (n,Hn).
      now destruct n ; simpl.
  - intros (P0,P2).
    apply (Sequence_rect (P := λ L : Sequence (X -> hProp),
                                     (∀ n : stn (length L), P (L n)) -> P (finite_intersection L))).
    + intros _.
      now rewrite finite_intersection_htrue.
    + intros L A IHl Hl.
      rewrite finite_intersection_append.
      apply P2.
      * rewrite <- (append_fun_compute_2 L A).
        now apply Hl.
      * apply IHl.
        intros n.
        rewrite <- (append_fun_compute_1 L A).
        apply Hl.
Qed.