(** This file contain various results that could be upstreamed to Foundations *)
Require Import UniMath.MoreFoundations.Foundations.

Section various.

Lemma base_paths_pair_path_in2 {X : UU} (P : X → UU) {x : X} {p q : P x} (e : p = q) :
  base_paths _ _ (pair_path_in2 P e) = idpath x.
Proof.
now induction e.
Qed.

End various.

(** Various algebraic properties of hProp *)
Section hProp_logic.

Lemma isassoc_hconj (P Q R : hProp) : ((P ∧ Q) ∧ R) = (P ∧ (Q ∧ R)).
Proof.
apply hPropUnivalence.
- intros PQR.
  exact (pr1 (pr1 PQR),,(pr2 (pr1 PQR),,pr2 PQR)).
- intros PQR.
  exact ((pr1 PQR,,pr1 (pr2 PQR)),,pr2 (pr2 PQR)).
Qed.

Lemma iscomm_hconj (P Q : hProp) : (P ∧ Q) = (Q ∧ P).
Proof.
apply hPropUnivalence.
- intros PQ.
  exact (pr2 PQ,,pr1 PQ).
- intros QP.
  exact (pr2 QP,,pr1 QP).
Qed.

Lemma isassoc_hdisj (P Q R : hProp) : ((P ∨ Q) ∨ R) = (P ∨ (Q ∨ R)).
Proof.
apply hPropUnivalence.
- apply hinhuniv; intros hPQR.
  induction hPQR as [hPQ|hR].
  + use (hinhuniv _ hPQ); clear hPQ; intros hPQ.
    induction hPQ as [hP|hQ].
    * exact (hinhpr (ii1 hP)).
    * exact (hinhpr (ii2 (hinhpr (ii1 hQ)))).
  + exact (hinhpr (ii2 (hinhpr (ii2 hR)))).
- apply hinhuniv; intros hPQR.
  induction hPQR as [hP|hQR].
  + exact (hinhpr (ii1 (hinhpr (ii1 hP)))).
  + use (hinhuniv _ hQR); clear hQR; intros hQR.
    induction hQR as [hQ|hR].
    * exact (hinhpr (ii1 (hinhpr (ii2 hQ)))).
    * exact (hinhpr (ii2 hR)).
Qed.

Lemma iscomm_hdisj (P Q : hProp) : (P ∨ Q) = (Q ∨ P).
Proof.
apply hPropUnivalence.
- apply hinhuniv; intros PQ.
  induction PQ as [hP|hQ].
  + exact (hinhpr (ii2 hP)).
  + exact (hinhpr (ii1 hQ)).
- apply hinhuniv; intros PQ.
  induction PQ as [hQ|hP].
  + exact (hinhpr (ii2 hQ)).
  + exact (hinhpr (ii1 hP)).
Qed.

Lemma hconj_absorb_hdisj (P Q : hProp) : (P ∧ (P ∨ Q)) = P.
Proof.
apply hPropUnivalence.
- intros hPPQ; apply (pr1 hPPQ).
- intros hP.
  split; [ apply hP | apply (hinhpr (ii1 hP)) ].
Qed.

Lemma hdisj_absorb_hconj (P Q : hProp) : (P ∨ (P ∧ Q)) = P.
Proof.
apply hPropUnivalence.
- apply hinhuniv; intros hPPQ.
  induction hPPQ as [hP|hPQ].
  + exact hP.
  + exact (pr1 hPQ).
- intros hP; apply (hinhpr (ii1 hP)).
Qed.

Lemma hfalse_hdisj (P : hProp) : (∅ ∨ P) = P.
Proof.
apply hPropUnivalence.
- apply hinhuniv; intros hPPQ.
  induction hPPQ as [hF|hP].
  + induction hF.
  + exact hP.
- intros hP; apply (hinhpr (ii2 hP)).
Qed.

Lemma htrue_hconj (P : hProp) : (htrue ∧ P) = P.
Proof.
apply hPropUnivalence.
- intros hP; apply (pr2 hP).
- intros hP.
  split; [ apply tt | apply hP ].
Qed.

End hProp_logic.