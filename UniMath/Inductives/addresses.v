Require Export UniMath.Inductives.algebras.


(* Addresses in trees *)

Section Addresses.

  (* T represents an abstract type of trees.
     A tree has nodes. Each node has a label and subtrees given by [arg]. *)
  Context {I} {T A : Fam I} {B : ∏ i, A i -> Fam I}
          {label : T ->__i A} {arg : ∏ i t, B i (label i t) ->__i T}.

  Fixpoint Addr0 (n : nat) {i} (t : T i) : UU :=
    match n with
    | 0 => unit
    | S n => ∑ j b, Addr0 n (arg i t j b)
    end.

  (* the type of addresses of a tree *)
  Definition Addr {i} (t : T i) :=
    ∑ n, Addr0 n t.

  (* constructors of addresses *)
  Definition root_addr {i} (t : T i) : Addr t :=
    (0,, tt).

  Definition subtree_addr {i} (t : T i) {j} (b : B i (label i t) j)
             (addr' : Addr (arg i t j b)) : Addr t :=
    let '(n,, addr') := addr' in
    (S n,, j,, b,, addr').

  (* induction principle for addresses *)
  Definition addresses_induction'
               (P : ∏ i (t : T i), Addr t -> UU)
               (base : ∏ i t, P i t (root_addr t))
               (ind_case : ∏ i t j b addr',
                           P j (arg i t j b) addr' ->
                           P i t (subtree_addr t b addr'))
               (n : nat) {i} (t : T i) (addr0 : Addr0 n t) :
    P i t (n,, addr0).
  Proof.
    revert i t addr0; induction n as [| n' ind']; intros i t addr0.
      - destruct addr0. exact (base i t).
      - induction addr0 as [j [b addr0']].
        exact (ind_case i t j b (n' ,, addr0') (ind' j (arg i t j b) addr0')).
  Defined.

  Definition addresses_induction
               (P : ∏ i (t : T i), Addr t -> UU)
               (base : ∏ i t, P i t (root_addr t))
               (ind_case : ∏ i t j b addr',
                           P j (arg i t j b) addr' ->
                           P i t (subtree_addr t b addr'))
               {i} (t : T i) (addr : Addr t) : P i t addr.
  Proof.
    intros. set (n := pr1 addr). set (addr0 := pr2 addr).
    exact (addresses_induction' P base ind_case n t addr0).
  Defined.

  Definition index_at {i} {t : T i} (addr : Addr t) : I :=
    addresses_induction (λ i t addr, I)
                        (λ i t, i)
                        (λ i t j b addr' IH, IH)
                        t
                        addr.

  (* given an address and a tree, we get the tree at that address *)
  Definition subtree_at {i} {t : T i} (addr : Addr t) : T (index_at addr) :=
    addresses_induction (λ i t addr, T (index_at addr))
                        (λ i t, t)
                        (λ i t j b addr' IH, IH)
                        t
                        addr.

  (* we also get its label *)
  Definition label_at {i} {t : T i} (addr : Addr t) : A (index_at addr) :=
    label (index_at addr) (subtree_at addr).

  Definition extend_addr {i} (t : T i) (addr : Addr t)
             {j} (b : B (index_at addr) (label_at addr) j) :
    Addr t :=
    addresses_induction (λ i t addr, ∏ j, B _ (label_at addr) j -> Addr t)
                        (λ i t j b, subtree_addr t b (root_addr _))
                        (λ i t j b addr' IH j' b', subtree_addr t b (IH j' b'))
                        t
                        addr
                        j
                        b.

  (* Check @extend_addr. *)
  (* Lemma subtree_at_extend_addr {i} {t : T i} (addr : Addr t) : *)
  (*   (λ (j : I) (b : B (index_at addr) (label_at addr) j), *)
  (*    subtree_at (extend_addr t addr b)) = *)
  (*   (λ (j : I) (b : B (index_at addr) (label_at addr) j), *)
  (*    arg (index_at addr) (subtree_at addr) j b). *)
  (* Proof. *)
  (*   eapply addresses_induction. *)
  (*   - reflexivity. *)
  (*   - intros t b addr' IH. *)
  (*     exact IH. *)
  (* Defined. *)

End Addresses.
