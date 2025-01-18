(** * The ground term algebra and the proof it is initial. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2023 *)

Require Import UniMath.Foundations.All.

Require Export UniMath.Algebra.Universal.Algebras.
Require Export UniMath.Algebra.Universal.Terms.

Local Open Scope sorted.
Local Open Scope hom.

Section TermAlgebra.

  Definition term_algebra (σ: signature): algebra σ
    := make_algebra (gterm σ) build_gterm.

  Definition has_supportsets_termalgebra (σ: signature): has_supportsets (term_algebra σ)
    := λ (s: sorts σ), isasetterm s.

  Definition term_hSetalgebra (σ: signature): hSetalgebra σ
    := make_hSetalgebra (has_supportsets_termalgebra σ).

  Context {σ: signature}.

  Definition geval (a: algebra σ): term_algebra σ s→ a
    := @fromgterm σ a (ops a).

  Lemma gevalstep {a: algebra σ} (nm: names σ) (v: (gterm σ)⋆ (arity nm))
    : geval a _ (build_gterm nm v) = ops a nm (h1map (geval a) v).
  Proof.
    unfold geval.
    apply fromtermstep.
  Defined.

  Lemma ishomgeval (a: algebra σ): ishom (geval a).
  Proof.
    red.
    intros.
    unfold starfun.
    apply gevalstep.
  Defined.

  Definition gevalhom (a: algebra σ): term_algebra σ ↷ a
    := make_hom (ishomgeval a).

  Lemma gevalhom_is_unique {a: algebra σ} (f: term_algebra σ ↷ a):
    pr1 f = pr1 (gevalhom a).
  Proof.
    induction f as [f fishom].
    apply funextsec.
    intro s.
    apply funextfun.
    intro t.
    apply (term_ind (λ s t, f s t = geval a s t)).
    unfold term_ind_HP.
    intros.
    change (build_gterm nm v) with (ops (term_algebra σ) nm v) at 1.
    rewrite fishom.
    rewrite gevalstep.
    apply maponpaths.
    unfold starfun.
    apply h1map_path.
    exact IH.
  Qed.

  Definition iscontrhomsfromgterm (a: algebra σ) (setprop: has_supportsets a)
    : iscontr (term_algebra σ ↷ a).
  Proof.
    exists (gevalhom a).
    intro f.
    apply subtypePairEquality'.
    - apply gevalhom_is_unique.
    - apply isapropishom.
      exact setprop.
  Defined.

End TermAlgebra.
