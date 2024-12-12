Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.HVecRel.

Local Open Scope sorted.

Definition shrel {S : UU} (A : sUU S) : UU
  := ∏ (s:S), hrel (A s).

Definition extensionallift
  {S : UU} {A : sUU S} (R : shrel A)
  (P : ∏ (s:S) (R:hrel (A s)), UU) : UU
  := ∏ (s:S), P s (R s).

Definition siseqrel {S : UU} {A : sUU S} (R : shrel A)
  := extensionallift R (λ _ R, iseqrel R).

(*Generalization of [[iscomprelfun]]*)
Definition iscomprelfunrel {X Y : UU}
  (RX : hrel X) (RY : hrel Y) (f : X -> Y)
  : UU
  := ∏ x x' : X, RX x x' -> RY (f x) (f x').

Definition shrelList
  {σ : signature} {A : algebra σ} (R : shrel A) (l : list (sorts σ))
  : hrel (A⋆ l).
Proof.
  unfold star.
  use hrelhvec.
  change (hvec (((vec_map hrel) ∘ (vec_map (support A))) l)).
  use (transportf hvec (vec_map_comp (support A) (hrel) l)).
  use h01map.
  exact R.
Defined.

Definition iscompatible {σ : signature}
  (A : algebra σ) (R : shrel A)
 := ∏ nm: names σ, iscomprelfunrel (shrelList R (arity nm)) (R (sort nm)) (ops A nm).

Definition iscong {σ : signature}
  (A : algebra σ) (R : shrel A)
  := siseqrel R × iscompatible A R.

Definition congruence {σ : signature} (A : algebra σ)
  := ∑ (R : shrel A), iscong A R.

(*TODO: make this a coercion*)
Definition eqrelofcong {σ : signature} {A : algebra σ} (R : congruence A) (s: sorts σ)
  : eqrel (support A s)
  := (pr1 R) s ,, (pr12 R) s.

Definition quotalgebra {σ : signature} (A : algebra σ) (R : congruence A)
  : algebra σ.
Proof.
Proof.
  use make_algebra.
  - intro s.
    exact (setquot (eqrelofcong R s)).
  - simpl.
    intros nm xs.
    use (setquotuniv _ (setquot (eqrelofcong R (sort nm)),,_)).
    + exact (A⋆ (arity nm)).
    + use shrelList.
      apply R.
    + use isasetsetquot.
    + apply (funcomp (ops A nm) (setquotpr ((eqrelofcong R) (sort nm)))).
    + simpl.
      intros a1s b1s rel_ab.
      simpl.
      use (iscompsetquotpr (eqrelofcong R (sort nm))).
      use (pr2 (pr2 R) nm _ _ rel_ab). (*TODO: name pr2 and make opportune coercions*)
    + simpl.
      use hvectosetquot.
      unfold star in xs.
      refine (eqweqmap (maponpaths hvec _) xs).
      eapply pathscomp0. { use h01maph1lower.  }
      eapply pathscomp0. { use h1lower_vec_map_comp. exact (support A). }
      use maponpaths.
      use pathsinv0.
      use h1h01map_transport_vec_map_comp.
Defined.