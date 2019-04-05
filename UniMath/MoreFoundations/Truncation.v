Require Import UniMath.MoreFoundations.All.

Definition trunc (n : nat) (A : UU) := forall B : UU, isofhlevel n B -> (A -> B) -> B.
Definition in_trunc (n : nat) {A : UU} (a : A) : trunc n A := λ B _ f, f a.
Definition trunc_ind {n : nat} {A B : UU} (sb : isofhlevel n B) (f : A -> B) : trunc n A -> B :=
  λ F, F B sb f.

Lemma trunc_isofhlevel : forall (n : nat) (A : UU), isofhlevel n (trunc n A).
Proof.
  intros n A. unfold trunc.
  apply impred.
  intros B; apply impred.
  intros; apply impredfun; assumption.
Defined.

Definition trunc_rect_tot (n : nat) {A : UU} {B : trunc n A -> UU} (sb : forall a, isofhlevel n (B a)) (f : forall a : A, B (in_trunc n a)) : trunc n A -> total2 B.
Proof.
  intros.
  apply X.
  - apply isofhleveltotal2; [ apply trunc_isofhlevel | assumption ].
  - intros a; exists (in_trunc n a). apply f.
Defined.

(* Not the right induction principle: the return type should be B a *)
Definition trunc_rect_aux {n : nat} {A} {B} sb f a : B (pr1 (trunc_rect_tot n sb f a)) := pr2 (@trunc_rect_tot n A B sb f a).

(* Does not seem provable with the current definition of trunc. *)
Definition trunc_rect {n : nat} {A} {B} (sb : forall a, isofhlevel n (B a)) (f : forall a : A, B (in_trunc n a)) (a : trunc n A) : B a.
Proof.
assert (pr1 (trunc_rect_tot n sb f a) = a).
- admit.
- induction X.
  apply trunc_rect_aux.
Admitted.

Lemma trunc_ind_eq {n : nat} {A B : UU} (sb : isofhlevel n B) (f : A -> B) : forall a : A, trunc_ind sb f (in_trunc n a) = f a.
  intros; reflexivity.
Defined.

Lemma trunc_rect_aux_eq {n : nat} {A : UU} {B : trunc n A -> UU} (sb : forall a, isofhlevel n (B a)) (f : forall a, B (in_trunc n a)) : forall a : A, trunc_rect_aux sb f (in_trunc n a) = f a.
  intros; reflexivity.
Defined.