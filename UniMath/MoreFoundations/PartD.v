Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.All.

Lemma eqweqmap_transportb {T U: Type} (p: T = U) :
 (λ u:U, eqweqmap (! p) u) = transportb (λ X:Type, X) p.
Proof.
  induction p. reflexivity.
Defined.

Lemma eqweqmap_weqtopaths {T U} (w : T≃U) : eqweqmap (weqtopaths w) = w.
Proof.
  exact (homotweqinvweq (univalence T U) w).
Defined.

Lemma sum_of_fibers {A B:Type} (f: A -> B) :
  (∑ b:B, hfiber f b) ≃ A.
Proof.
  use weqpair.
  - intro bap. exact (pr1 (pr2 bap)).
  - intro a. use iscontrpair.
    + use hfiberpair.
      * exists (f a).
        use hfiberpair.
        { exact a. }
        { reflexivity. }
      * cbn. reflexivity.
    + intro b1a1p1p. induction b1a1p1p as [b1a1p1 p]. induction p.
      induction b1a1p1 as [b1 [a1 p1]]. induction p1. reflexivity.
Defined.

Definition display {A: Type} :
  (∑ B, B -> A) -> (A -> Type).
Proof.
  intro Bf. exact (hfiber (pr2 Bf)).
Defined.

Definition totalfst {A: Type} :
  (A -> Type) -> (∑ B, B -> A).
Proof.
  intro P. exists (∑ a:A, P a). exact pr1.
Defined.

Lemma totalfst_display {A: Type} (Bf: ∑ B, B -> A) : totalfst (display Bf) = Bf.
Proof.
  use total2_paths_f.
  - apply weqtopaths. apply sum_of_fibers.
  - rewrite transportf_fun.
    rewrite <- eqweqmap_transportb.
    rewrite eqweqmap_pathsinv0.
    rewrite eqweqmap_weqtopaths.
    reflexivity.
Defined.

Lemma display_totalfst {A: Type} (P: A -> Type) : display(totalfst(P)) = P.
Proof.
  apply funextsec; intro a.
  apply pathsinv0.
  apply weqtopaths.
  apply ezweqpr1.
Defined.

Lemma display_weq (A:Type) :
  (∑ B, B -> A) ≃ (A -> Type).
Proof.
  exists display.
  apply (isweq_iso display totalfst).
  - exact totalfst_display.
  - exact display_totalfst.
Defined.
