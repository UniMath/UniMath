(** * Limits of chains and cochains in the precategory of types *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Univalence.
Require Import UniMath.MoreFoundations.WeakEquivalences.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.Types.

Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Cochains.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.

Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.M.Limits.
Require Import UniMath.Induction.M.Core.

(** The shifted chain (X', π') from (X, π) is one where Xₙ' = Xₙ₊₁ and πₙ' = πₙ₊₁. *)
Definition shift_chain (cha : chain type_precat) : chain type_precat.
Proof.
  use tpair.
  - exact (dob cha ∘ S).
  - exact (λ _ _ path, dmor cha (maponpaths S path)).
Defined.

(** The shifted cochain (X', π') from (X, π) is one where Xₙ' = Xₙ₊₁ and πₙ' = πₙ₊₁. *)
Definition shift_cochain {C : precategory} (cochn : cochain C) : cochain C.
Proof.
  use cochain_weq; use tpair.
  - exact (dob cochn ∘ S).
  - intros n; cbn.
    apply (dmor cochn).
    exact (idpath _).
Defined.

(** Interaction between transporting over (maponpaths S ed) and shifting the cochain *)
Definition transport_shift_cochain :
  ∏ cochn ver1 ver2 (ed : ver1 = ver2)
    (stdlim_shift : standard_limit (shift_cochain cochn)),
  transportf (dob cochn) (maponpaths S ed) (pr1 stdlim_shift ver1) =
  transportf (dob (shift_cochain cochn)) ed (pr1 stdlim_shift ver1).
Proof.
  intros cochn ver1 ver2 ed stdlim_shift.
  induction ed.
  reflexivity.
Defined.

(** Ways to prove that [dmor]s are equal on cochains *)
Lemma cochain_dmor_paths {C : precategory} {ver1 ver2 : vertex conat_graph}
      (cochn : cochain C) (p1 p2 : edge ver1 ver2) : dmor cochn p1 = dmor cochn p2.
Proof.
  apply maponpaths, proofirrelevance, isasetnat.
Defined.

(** More ways to prove that [dmor]s are equal on cochains *)
Lemma cochain_dmor_paths_type {ver1 ver2 ver3 : vertex conat_graph}
  (cochn : cochain type_precat) (p1 : edge ver1 ver3) (p2 : edge ver2 ver3)
  (q1 : ver1 = ver2) :
  ∏ v1 : dob cochn ver1, dmor cochn p1 v1 = dmor cochn p2 (transportf _ q1 v1).
Proof.
  intro v1; cbn in *.
  induction q1.
  cbn; unfold idfun.
  exact (toforallpaths _ _ _ (cochain_dmor_paths cochn p1 p2) v1).
Defined.


(** We use the following tactic notations to mirror the "equational style" of
    reasoning used in Ahrens, Capriotti, and Spadotti. *)
Local Tactic Notation "≃" constr(H) "by" tactic(t) := intermediate_weq H; [t|].
Local Tactic Notation "≃'" constr(H) "by" tactic(t) := intermediate_weq H; [|t].
Local Tactic Notation "≃" constr(H) := intermediate_weq H.
Local Tactic Notation "≃'" constr(H) := apply invweq; intermediate_weq H.

Local Lemma combine_over_nat_basic {X Y Z : nat → UU} :
  X 0 ≃ Z 0 → (∏ n : nat, Y (S n) ≃ Z (S n)) →
  (X 0 × ∏ n : nat, Y (S n)) ≃ ∏ n : nat, Z n.
Proof.
  intros x0z0 yszs.
  ≃ (Z 0 × (∏ n : nat, Z (S n))).
  - apply weqdirprodf; [apply x0z0|].
    apply weqonsecfibers, yszs.
  - use weq_iso.
    + intros x0xs.
      intros n; destruct n.
      * exact (dirprod_pr1 x0xs).
      * apply (dirprod_pr2 x0xs).
    + intros xs; use dirprodpair.
      * apply xs.
      * exact (xs ∘ S).
    + reflexivity.
    + intros xs.
      apply funextsec; intros n.
      destruct n; reflexivity.
Defined.

Local Lemma combine_over_nat {X : nat → UU} {P : (X 0 × (∏ n : nat, X (S n))) → UU} :
  (∑ x0 : X 0, ∑ xs : ∏ n : nat, X (S n), P (dirprodpair x0 xs)) ≃
  (∑ xs : ∏ n : nat, X n, P (dirprodpair (xs 0) (xs ∘ S))).
Proof.
  ≃ (∑ pair : (X 0 × ∏ n : nat, X (S n)), P pair) by apply weqtotal2asstol.
  use weqbandf.
  - apply (@combine_over_nat_basic X X X); intros; apply idweq.
  - intros x0xs; cbn.
    apply idweq.
Defined.

Local Lemma combine_over_nat' {X : nat → UU} {P : X 0 → (∏ n : nat, X (S n)) → UU} :
  (∑ x0 : X 0, ∑ xs : ∏ n : nat, X (S n), P x0 xs) ≃
  (∑ xs : ∏ n : nat, X n, P (xs 0) (xs ∘ S)).
Proof.
  ≃ (∑ (x0 : X 0) (xs : ∏ n : nat, X (S n)), (uncurry (Z := λ _, UU) P)
                                             (dirprodpair x0 xs)) by apply idweq.
  ≃' (∑ xs : ∏ n : nat, X n, uncurry P (Z := λ _, UU)
                                     (dirprodpair (xs 0) (xs ∘ S))) by apply idweq.
  apply combine_over_nat.
Defined.

(** If the base type is contractible, so is the type of sections over it. *)
Definition weqsecovercontr_uncurried {X : UU} {Y : X -> UU}
           (P : ∏ x : X, Y x -> UU) (isc : iscontr (∑ x : X, Y x)) :
  (∏ (x : X) (y : Y x), P x y) ≃ (P (pr1 (iscontrpr1 isc)) (pr2 (iscontrpr1 isc))).
Proof.
  ≃ (∏ pair : (∑ x : X, Y x), uncurry (Z := λ _, UU) P pair) by
    apply invweq, weqsecovertotal2.
  ≃' (uncurry (Z := λ _, UU) P (iscontrpr1 isc)) by (apply idweq).
  apply weqsecovercontr.
Defined.

(** Shifted cochains have equivalent limits.
    (Lemma 12 in Ahrens, Capriotti, and Spadotti) *)

Definition shifted_limit (cocha : cochain type_precat) :
  standard_limit (shift_cochain cocha) ≃ standard_limit cocha.
Proof.
  pose (X := dob cocha); cbn in X.
  pose (π n := (@dmor _ _ cocha (S n) n (idpath _))).
  unfold standard_limit, shift_cochain, funcomp, idfun; cbn.

  assert (isc : ∏ x : ∏ v : nat, dob cocha (S v),
                iscontr (∑ x0 : X 0, (π 0 (x 0)) = x0)).
  {
    intros x.
    use iscontrpair.
    + exact (π 0 (x 0),, idpath _).
    + intros other.
      use total2_paths_f.
      * exact (!(pr2 other)).
      * abstract (induction other as [x0' x0'eq];
                  induction x0'eq;
                  reflexivity).

  }

  (** Step (2) *)
  (** This is the direct product with the type proven contractible above *)
  ≃ (∑ xs : ∏ v : nat, X (S v),
    (∏ (u v : nat) (e : S v = u),
    (dmor cocha (idpath (S (S v)))
      ∘ transportf (λ o : nat, X (S o) → X (S (S v))) e
      (idfun (X (S (S v))))) (xs u) = xs v)
    × (∑ x0 : X 0, (π 0 (xs 0)) = x0)) by
    (apply weqfibtototal; intro; apply dirprod_with_contr_r; apply isc).

  (** Now, we swap the components in the direct product. *)
  ≃ (∑ xs : ∏ v : nat, X (S v),
    (∑ x0 : X 0, π 0 (xs 0) = x0) ×
    (∏ (u v : nat) (e : S v = u),
      (dmor cocha (idpath (S (S v)))
      ∘ transportf (λ o : nat, X (S o) → X (S (S v))) e
      (idfun (X (S (S v))))) (xs u) = xs v)) by
    (apply weqfibtototal; intro; apply weqdirprodcomm).

  (** Using associativity of Σ-types, *)
  ≃ (∑ xs : ∏ v : nat, X (S v),
     ∑ x0 : X 0,
     (π 0 (xs 0) = x0) ×
     (∏ (u v : nat) (e : S v = u),
       (dmor cocha (idpath (S (S v)))
       ∘ transportf (λ o : nat, X (S o) → X (S (S v))) e
       (idfun (X (S (S v))))) (xs u) = xs v)) by
    (apply weqfibtototal; intro; apply weqtotal2asstor).

  (** And again by commutativity of ×, we swap the first components *)
  ≃ (∑ x0 : X 0,
     ∑ xs : ∏ n : nat, X (S n),
     (π 0 (xs 0) = x0) ×
     (∏ (u v : nat) (e : S v = u),
       (dmor cocha (idpath (S (S v)))
       ∘ transportf (λ o : nat, X (S o) → X (S (S v))) e
       (idfun (X (S (S v))))) (xs u) = xs v)) by (apply weqtotal2comm).

  (** Step 3: combine the first bits *)
  ≃ (∑ xs : ∏ n : nat, X n,
      (π 0 (xs 1) = xs 0) ×
      (∏ (u v : nat) (e : S v = u),
        (dmor cocha (idpath (S (S v)))
        ∘ transportf (λ o : nat, dob cocha (S o) → dob cocha (S (S v))) e
        (idfun (dob cocha (S (S v))))) (xs (S u)) = xs (S v))).
  apply (@combine_over_nat' X
        (λ x0 xs,
        π 0 (xs 0) = x0
        × (∏ (u v : nat) (e : S v = u),
            (dmor cocha (idpath (S (S v)))
            ∘ transportf (λ o : nat, X (S o) → X (S (S v))) e (idfun (X (S (S v)))))
              (xs u) = xs v))).

  (** Now the first component is the same. *)
  apply weqfibtototal; intros xs.

  ≃ (π 0 (xs 1) = xs 0
    × (∏ (v u : nat) (e : S v = u),
      (dmor cocha (idpath (S (S v)))
        ∘ transportf (λ o : nat, dob cocha (S o) → dob cocha (S (S v))) e
            (idfun (dob cocha (S (S v))))) (xs (S u)) = xs (S v))) by
    apply weqdirprodf; [apply idweq|apply flipsec_weq].

  ≃' (∏ (v u : nat) (e : S v = u), dmor cocha e (xs u) = xs v) by
    apply flipsec_weq.

  (** Split into cases on n = 0 or n > 0. *)
  (** Coq is bad about coming up with these implicit arguments, so we have to be
      very excplicit. *)
  apply (@combine_over_nat_basic
           (λ n, π n (xs (S n)) = xs n)
           (λ v, ∏ (u : nat) (e : v = u),
             (dmor cocha (idpath (S v))
               ∘ _ (idfun (dob cocha (S v)))) (xs (S u)) = xs v)
           (λ v, ∏ (u : nat) (e : S v = u), dmor cocha e (xs u) = xs v)).

  (** We use the following fact over and over to simplify the remaining types:
      for any x : X, the type ∑ y : X, x = y is contractible. *)
  - apply invweq.
    apply (@weqsecovercontr_uncurried
             nat (λ n, 1 = n) (λ _ _, _ = xs 0) (iscontr_paths_from 1)).
  - intros u.
    ≃ ((dmor cocha (idpath (S (S u)))
            ∘ transportf (λ o : nat, dob cocha (S o) → dob cocha (S (S u)))
                (idpath (S u)) (idfun (dob cocha (S (S u))))) (xs (S (S u))) =
          xs (S u)).
    + apply (@weqsecovercontr_uncurried
               nat (λ n, (S u) = n) (λ _ _, _ _ = xs (S u)) (iscontr_paths_from _)).
    + cbn; unfold funcomp, idfun.
      apply invweq.
      apply (@weqsecovercontr_uncurried
               nat (λ n, (S (S u)) = n) (λ _ _, _ = xs (S u)) (iscontr_paths_from _)).
Defined.

Section theorem_7.
  Context (A : UU) (B : A → UU).

Definition apply_on_chain (cha : cochain type_precat) : cochain type_precat :=
  mapcochain (polynomial_functor A B) cha.

Definition weq_polynomial_functor_on_limit (cha : cochain type_precat) :
  (polynomial_functor A B)(standard_limit cha) ≃ standard_limit (apply_on_chain cha).
Proof.
  induction cha as [X π]; unfold apply_on_chain. simpl.
  unfold mapcochain, mapdiagram, standard_limit; cbn.
  unfold polynomial_functor_obj, polynomial_functor_arr.
  admit.
Admitted.

Definition terminal_cochain  : cochain type_precat :=
  termCochain (TerminalType) (polynomial_functor A B).

Definition m_type  := standard_limit terminal_cochain.

Definition terminal_cochain_shifted :
  standard_limit (shift_cochain terminal_cochain) ≃
                 standard_limit (apply_on_chain terminal_cochain).
Proof.
  admit.
Admitted.
(*
  unfold standard_limit.
  unfold polynomial_functor.
  cbn.
  unfold polynomial_functor_obj.
  fold.
  apply weqfibtototal.
  unfold functor_data_from_functor.
  unfold mk_functor.
  unfold functor_on_objects.
  unfold polynomial_functor_data.
*)


Definition m_in : (polynomial_functor A B) m_type ≃ m_type.
  eapply weqcomp.
  exact (weq_polynomial_functor_on_limit terminal_cochain).
  eapply weqcomp.
  exact (invweq terminal_cochain_shifted).
  exact (shifted_limit terminal_cochain).
Defined.

Definition m_coalgebra : coalgebra (polynomial_functor A B) := m_type,, (invweq m_in :(type_precat ⟦ m_type, (polynomial_functor A B) m_type ⟧)%Cat).

Lemma m_coalgebra_is_final : is_final m_coalgebra.
Proof.
  admit.
Admitted.
