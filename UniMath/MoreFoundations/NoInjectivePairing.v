Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Univalence.

(** We prove that the following lemma ("injective pairing") is inconsistent with univalence: *)
Definition injective_pairing_statement :=
  ∏ A (B : A → UU) a (b b' : B a),
  a ,, b = a ,, b' →
  b = b'.

(** Proof sketch by Folkmar Frederik Ramcke. Formalisation by Jannis Limperg with help from Joj
   Helfer. *)


(** * Preliminaries *)

Lemma univalence_pathsinv0 {A B : UU} (p : A = B) :
  univalence _ _ (!p) = invweq (univalence _ _ p).
Proof.
  apply eqweqmap_pathsinv0.
Defined.

(** Inverting the path obtained from an equivalence is the same as inverting the equivalence. *)
Lemma pathsinv0_weqtopaths {A B : UU} (eq : A ≃ B) :
  ! (weqtopaths eq) = weqtopaths (invweq eq).
Proof.
  type_induction eq e.
  rewrite <- univalence_pathsinv0.
  unfold weqtopaths.
  rewrite 2 homotinvweqweq.
  apply idpath.
Defined.


(** * Refutation of Injective Pairing *)

(** Boolean negation is a weak equivalence. *)
Definition negb_weq : bool ≃ bool.
Proof.
  exists negb.
  cbv. intros.
  use tpair.
  - use tpair.
    + exact (negb y).
    + induction y; apply idpath.
  - cbn. intro t.
    induction t as [b eq].
    induction b; induction eq; apply idpath.
Defined.

(** Thus, we can construct two equal pairs whose second components are different: *)
Definition negb_weq_pair
  : @paths (∑ A : UU, A → bool) (bool ,, idfun bool) (bool ,, negb).
Proof.
  refine (
    total2_paths_f (B := λ A, A → bool) (s := bool ,, idfun bool) (s' := bool ,, negb)
      (weqtopaths negb_weq) _
  ).
  etrans.
  { apply (transportf_fun (idfun UU)). }
  change (transportb (idfun UU) (weqtopaths negb_weq) = negb).
  etrans.
  { refine (maponpaths _ (pathsinv0_weqtopaths _ )). }
  apply weqpath_transport.
Defined.

(** By injective pairing, we get [idfun bool = negb], a contradiction. *)
Theorem no_injective_pairing :
  injective_pairing_statement -> ∅.
Proof.
  intro contra.
  specialize (contra _ _ _ _ _ negb_weq_pair).
  apply toforallpaths in contra.
  exact (nopathstruetofalse (contra true)).
Defined.


(** * Injective Pairing <-> Uniqueness of Identity Proofs *)

(** Another way to see why injective pairing cannot hold: It is logically equivalent to uniqueness
    of identity proofs, which is in turn equivalent to the K axiom and incompatible with univalence. *)

Definition uip_statement :=
  ∏ A (x y : A) (p q : x = y), p = q.

(** Injective pairing implies uniqueness of identity proofs. *)
Theorem injective_pairing_uip :
  injective_pairing_statement → uip_statement.
Proof.
  intros injpair A x y p q.
  assert (eqpair : @paths (∑ x, x = y) (x ,, p) (x ,, q)).
    { induction p. induction q. use total2_paths_f; apply idpath. }
  unfold injective_pairing_statement in injpair.
  exact (injpair _ (λ x, x = y) x p q eqpair).
Defined.

(** Uniqueness of identity proofs implies injective pairing. *)
Theorem uip_injective_pairing :
  uip_statement → injective_pairing_statement.
Proof.
  intros uip A B a b b' eqpair.
  set (eqa := base_paths _ _ eqpair).
  assert (eqb : transportf _ eqa b = b').
    { apply (fiber_paths eqpair). }
  assert (eqa_idpath : eqa = idpath _).
    { apply uip. }
  symmetry.
  etrans.
  { exact (! eqb). }
  exact (maponpaths (λ p, transportf B p b) eqa_idpath).
Defined.
