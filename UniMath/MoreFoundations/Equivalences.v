Require Import UniMath.Foundations.PartD.

Definition weq_total2_fiber_dirprod_total2 :
  ∏ (X : UU) (P1 P2 : X → UU), (∑ x : X, (P1 x) × (P2 x)) ≃ (∑ D : (∑ (x : X), P1 x), P2 (pr1 D)).
Proof.
  intros X P1 P2.
  use weqpair.
  - intros Y. exact (tpair _ (tpair _ (pr1 Y) (dirprod_pr1 (pr2 Y))) (dirprod_pr2 (pr2 Y))).
  - use gradth.
    + intros Y. exact (tpair _ (pr1 (pr1 Y)) (dirprodpair (pr2 (pr1 Y)) (pr2 Y))).
    + intros Y. induction Y as [Y1 Y23]. induction Y23 as [Y2 Y3]. use idpath.
    + intros Y. induction Y as [Y12 Y3]. induction Y12 as [Y1 Y2]. use idpath.
Defined.
Opaque weq_total2_fiber_dirprod_total2.

Definition weqtotal2assoc :
  ∏ (X : UU) (P : X → UU) (Q : ∏ (x : X), P x -> UU),
  (∑ x : X, (∑ p : P x, Q x p)) ≃ (∑ D : (∑ (x : X), P x), Q (pr1 D) (pr2 D)).
Proof.
  intros X P Q.
  use weqpair.
  - intros Y. exact (tpair _ (tpair _ (pr1 Y) (pr1 (pr2 Y))) (pr2 (pr2 Y))).
  - use gradth.
    + intros Y. exact (tpair _ (pr1 (pr1 Y)) (tpair _ (pr2 (pr1 Y)) (pr2 Y))).
    + intros Y. induction Y as [Y1 Y23]. induction Y23 as [Y2 Y3]. use idpath.
    + intros Y. induction Y as [Y12 Y3]. induction Y12 as [Y1 Y2]. use idpath.
Defined.
Opaque weqtotal2assoc.
