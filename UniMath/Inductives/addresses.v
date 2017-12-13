(** The following line has to be removed for the file to compile with Coq8.2 *)
Unset Automatic Introduction.

Unset Kernel Term Sharing.

(** Imports *)

Require Export UniMath.Inductives.algebras.


(* Addresses *)

Section Addresses.

  Context {T A : UU} {B : A -> UU} {label : T -> A} {arg : ∏ t : T, B (label t) -> T}.

  Definition Addr0 (n : nat) (t : T) : UU.
  Proof.
    intros n.
    induction n as [|n' Addr0'].
      - exact (fun _ => unit).
      - intro t. exact (total2 (fun b : B (label t) => Addr0' (arg t b))).
  Defined.

  Definition Addr (t : T) : UU.
  Proof.
    intros.
    exact (total2 (fun n => Addr0 n t)).
  Defined.

  (* constructors *)
  Definition root_addr (t : T) : Addr t :=
    (0 ,, tt).

  Definition subtree_addr (t : T) (b : B (label t)) (nx : Addr (arg t b)) : Addr t.
  Proof.
    intros.
    destruct nx as [n x].
    exact (S n ,, (b ,, x)).
  Defined.

  (* induction principle for addresses *)
  Definition addresses_induction'
               (P : ∏ t : T, Addr t -> UU)
               (base : ∏ t : T, P t (root_addr t))
               (ind_case : ∏ t : T, ∏ b : B (label t), ∏ addr : Addr (arg t b),
                             P (arg t b) addr -> P t (subtree_addr t b addr))
               (n : nat) (t : T) (addr0 : Addr0 n t) : P t (n ,, addr0).
  Proof.
    intros ? ? ? ?.
    induction n as [| n' ind'].
      - intros. destruct addr0. exact (base t).
      - intros. destruct addr0 as [b addr0'].
        exact (ind_case t b (n' ,, addr0') (ind' (arg t b) addr0')).
  Defined.

  Definition addresses_induction
               (P : ∏ t : T, Addr t -> UU)
               (base : ∏ t : T, P t (root_addr t))
               (ind_case : ∏ t : T, ∏ b : B (label t), ∏ addr : Addr (arg t b),
                             P (arg t b) addr -> P t (subtree_addr t b addr))
               (t : T) (addr : Addr t) : P t addr.
  Proof.
    intros. destruct addr as [n addr0].
    exact (addresses_induction' P base ind_case n t addr0).
  Defined.

  Definition subtree_at (t : T) (addr : Addr t) : T.
  Proof.
    apply addresses_induction.
      - exact (idfun _).
      - exact (fun _ _ _ t' => t').
  Defined.

  Definition label_at (t : T) (addr : Addr t) : A :=
    label (subtree_at t addr).

  Definition extend_addr (t : T) (addr : Addr t) (b : B (label_at t addr)) : Addr t.
  Proof.
    apply (addresses_induction (fun t addr => B (label_at t addr) -> Addr t)).
      - exact (fun t b => subtree_addr t b (root_addr _)).
      - intros t b addr' extend_addr' b'. exact (subtree_addr t b (extend_addr' b')).
  Defined.

End Addresses.
