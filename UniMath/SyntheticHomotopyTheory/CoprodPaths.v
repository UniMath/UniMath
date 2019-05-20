
(** * Compute the path space of a coproduct via encode-decode *)
(**
  Follows the exposition in the HoTT book, Theorem 2.12.5

  Main result: [coprod_paths]

*)


Require Import UniMath.Foundations.All.

Section coprod_paths.

Variables A B : UU.
Variable a : A.

Definition code : A ⨿ B → UU.
Proof.
  use coprod_rect; cbn.
  - exact (fun x => a = x).
  - exact (fun _ => empty).
Defined.

Definition decode : ∏ t : A ⨿ B, code t → (inl a = t).
Proof.
  induction t.
  - cbn. apply maponpaths.
  - cbn. apply fromempty.
Defined.

Definition encode : ∏ t : A ⨿ B, (inl a = t) → code t.
Proof.
  cbn.
  intros t p.
  apply (transportf _ p).
  apply idpath.
Defined.

Lemma encode_decode : ∏ (t : A ⨿ B) (p : inl a = t), decode _ (encode _ p) = p.
Proof.
  intros t p.
  induction p.
  apply idpath.
Defined.

Lemma decode_encode : ∏ (t : A ⨿ B) (p : code t), encode _ (decode _ p) = p.
Proof.
  intro t.
  induction t.
  - cbn. intro p. induction p. apply idpath.
  - cbn. intro.  apply fromempty. apply p.
Defined.

Lemma coprod_paths : ∏ t : A ⨿ B, (inl a = t) ≃ code t.
Proof.
  intro t.
  exists (encode _ ).
  use isweq_iso.
  - exact (decode _ ).
  - apply encode_decode.
  - apply decode_encode.
Defined.

End coprod_paths.

Definition paths_inl (A B : UU) (a a' : A) : @inl A B a = inl a' ≃ a = a'.
Proof.
  apply coprod_paths.
Defined.

Definition paths_inl_inr (A B : UU) (a : A) (b : B) : inl a = inr b ≃ empty.
Proof.
  apply coprod_paths.
Defined.
