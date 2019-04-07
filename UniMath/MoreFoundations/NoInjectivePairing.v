Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Univalence.

(** We prove that the following proposition ("injective pairing") is inconsistent with univalence: *)
Definition injective_pairing_statement :=
  ∏ A (B : A → UU) a (b b' : B a),
  a ,, b = a ,, b' →
  b = b'.

(** Proof sketch by Folkmar Frederik Ramcke. Formalisation by Jannis Limperg with help from Joj
   Helfer. *)


(** * Preliminaries *)

(** [idfun] is a left identity of [funcomp]. *)
Lemma funcomp_id_l {A B} (f : A → B) :
  idfun B ∘ f = f.
Proof.
  apply funextsec; intro. apply idpath.
Defined.

(** Weak equivalences are injective. *)
Lemma isinj_weq {A B} (eq : A ≃ B) : isInjective (pr1weq eq).
Proof.
  apply isweqonpathsincl.
  apply isofhlevelfweq.
Defined.

(** Inverting the path obtained from an equivalence is the same as inverting the equivalence. *)
Lemma pathsinv0_weqtopaths {A B : UU} (eq : A ≃ B) :
  ! (weqtopaths eq) = weqtopaths (invweq eq).
Proof.
  apply (Injectivity _ (isinj_weq (univalence _ _))). cbn.
  etrans.
  { apply eqweqmap_pathsinv0. }
  etrans.
  { exact (maponpaths invweq (weqpathsweq _)). }
  apply pathsinv0.
  apply weqpathsweq.
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
  etrans.
  { apply funcomp_id_l. }
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
