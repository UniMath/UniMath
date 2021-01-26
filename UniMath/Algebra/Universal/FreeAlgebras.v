(** * Free algebras. *)

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
    @make_algebra σ (vtermset σ V) (build_term ∘ namelift).

  Context {σ: signature} (a : algebra σ) {V: varspec σ} (α: assignment a V).

  Definition veval: free_algebra σ V s→ a := fromvterm (ops a) α.

  Lemma vevalstep (nm: names σ) (v:  (term (vsignature σ V))⋆ (arity nm))
    : veval (sort (namelift nm)) (build_term (namelift nm) v) = ops a nm (veval⋆⋆ (arity nm) v).
  Proof.
    unfold veval.
    change (sort (namelift nm)) with (sort nm).
    apply fromvtermstep.
  Defined.

  Lemma ishomveval: ishom veval.
  Proof.
    red.
    intros.
    apply vevalstep.
  Defined.

  Definition vevalhom: free_algebra σ V ↦ a := make_hom ishomveval.

  Definition universalmap: ∑ h: free_algebra σ V ↦ a, ∏ v: V, h _ (varterm v) = α v.
  Proof.
    exists vevalhom.
    intro v.
    simpl.
    unfold veval, varterm.
    apply fromvtermstep'.
  Defined.

  Definition iscontr_universalmap
    : iscontr (∑ h: free_algebra σ V ↦ a, ∏ v: V, h (varsort v) (varterm v) = α v).
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
      * change (inl nm) with (namelift(V:=V) nm).
        change (sort (namelift nm)) with (sort nm) at 2.
        change (build_term (namelift nm) hv) with (free_algebra σ V nm hv) at 1.
        rewrite hishom.
        rewrite vevalstep.
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
        rewrite honvars.
        unfold veval.
        rewrite fromvtermstep'.
        apply idpath.
   - apply impred_isaprop.
     intros.
     apply (supportset a (varsort t)).
  Defined.

End FreeAlgebras.
