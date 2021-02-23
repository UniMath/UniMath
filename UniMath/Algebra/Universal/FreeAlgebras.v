(** * Free algebras. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)
(**
This file contains a formalization of free algebras over a signature (i.e., the algebra
of terms over a signature and a set of variables.
*)

Require Import UniMath.Foundations.All.

Require Export UniMath.Algebra.Universal.Algebras.
Require Export UniMath.Algebra.Universal.VTerms.

Local Open Scope sorted.
Local Open Scope hom.

Section FreeAlgebras.

  Definition free_algebra (σ: signature) (V: varspec σ): algebra σ :=
    @make_algebra σ (termset σ V) build_term.

  Context {σ: signature} (a : algebra σ) {V: varspec σ} (α: assignment a V).

  Definition eval: free_algebra σ V s→ a := fromterm (ops a) α.

  Lemma evalstep (nm: names σ) (v:  (term σ V)⋆ (arity nm))
    : eval (sort nm) (build_term nm v) = ops a nm (eval⋆⋆ (arity nm) v).
  Proof.
    unfold eval.
    change (sort nm) with (sort nm).
    apply fromtermstep.
  Defined.

  Lemma ishomeval: ishom eval.
  Proof.
    red.
    intros.
    apply evalstep.
  Defined.

  Definition evalhom: free_algebra σ V ↷ a := make_hom ishomeval.

  Definition universalmap: ∑ h: free_algebra σ V ↷ a, ∏ v: V, h _ (varterm v) = α v.
  Proof.
    exists evalhom.
    intro v.
    simpl.
    unfold eval, varterm.
    apply fromtermstep'.
  Defined.

  Definition iscontr_universalmap
    : iscontr (∑ h: free_algebra σ V ↷ a, ∏ v: V, h (varsort v) (varterm v) = α v).
  Proof.
    exists universalmap.
    intro h.
    induction h as [h honvars].
    apply subtypePairEquality'.
    - induction h as [h hishom].
      apply subtypePairEquality'.
      2: apply isapropishom.
      apply funextsec.
      intro s.
      apply funextfun.
      unfold homot.
      revert s.
      apply (term_ind(σ := vsignature σ V)).
      unfold term_ind_HP.
      intros nm hv IHhv.
      induction nm as [nm | v].
      * change (inl nm) with (namelift V nm).
        change (sort (namelift V nm)) with (sort nm).
        change (build_gterm (namelift V nm) hv) with (ops (free_algebra σ V) nm hv) at 1.
        change (build_gterm (namelift V nm) hv) with (build_term nm hv).
        rewrite hishom.
        rewrite evalstep.
        apply maponpaths.
        revert hv IHhv.
        change (@arity (vsignature σ V) (inl nm)) with (arity nm).
        generalize (arity nm).
        refine (list_ind _ _ _).
        -- reflexivity.
        -- intros x xs IHxs hv IHhv.
           unfold starfun.
             simpl.
             simpl in IHhv.
             apply hcons_paths.
             + exact (pr1 IHhv).
             + exact (IHxs (pr2 hv) (pr2 IHhv)).
      * induction hv.
        change (inr v) with (varname v).
        change (sort (varname v)) with (varsort v).
        change (build_gterm (varname v) tt) with (varterm v).
        rewrite honvars.
        unfold eval.
        rewrite fromtermstep'.
        apply idpath.
   - apply impred_isaprop.
     intros.
     apply (supportset a (varsort t)).
  Defined.

End FreeAlgebras.
