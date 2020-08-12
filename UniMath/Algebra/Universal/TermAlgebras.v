(** * The term algebra and the proof it is initial *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.DecSet.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.HVectors.
Require Import UniMath.Algebra.Universal.Terms.

Local Open Scope sorted_scope.
Local Open Scope hom.

(** ** The term algebra and the proof it is initial *)

Section TermAlgebra.

  Definition term_algebra (σ: signature): algebra σ
    := make_algebra (λ s: sorts σ, termset s) build_term.

  Context {σ: signature}.

  Definition eval (a: algebra σ): term_algebra σ s→ a
    := @fromterm σ a (ops a).

  Lemma evalstep {a: algebra σ} (nm: names σ) (v: (term σ) * (arity nm)) 
    : eval a _ (build_term nm v) = ops a nm (hmap (eval a) v).
  Proof.
    unfold eval.
    apply fromtermstep.
  Defined.

  Lemma ishomeval (a: algebra σ): ishom (eval a).
  Proof.
    red.
    intros.
    unfold starfun.
    apply evalstep.
  Defined.

  Definition evalhom (a: algebra σ): term_algebra σ ↦ a
    := make_hom (ishomeval a).

  Definition iscontrhomsfromterm (a: algebra σ): iscontr (term_algebra σ ↦ a).
  Proof.
    exists (evalhom a).
    intro f.
    induction f as [f fishom].
    apply subtypePairEquality'.
    2: apply isapropishom.
    apply funextsec.
    intro s.
    apply funextfun.
    intro t.
    apply (term_ind (λ s t, f s t = eval a s t)).
    unfold term_ind_HP.
    intros.
    change (build_term nm v) with (ops (term_algebra σ) nm v) at 1.
    rewrite fishom.
    rewrite evalstep.
    apply maponpaths.
    unfold starfun.
    apply hmap_path.
    exact IH.
  Defined.

End TermAlgebra.
