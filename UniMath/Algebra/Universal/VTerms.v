(** ** Variables and terms with variables *)

(**
Given a signature σ, a [varspec] (variable specification) is a map from an [hSet] of _variables_
to the corresponding sort. A signature σ and a variable specification [V] give origin to a new
signature, [vsignature σ V] where variables in [v] become constant symbols. A term over
signature σ and variables in V is, i.e., a [vterm σ v], is a plain (ground) term over this
extended signature.
*)

Require Import UniMath.Foundations.All.

Require Import UniMath.Algebra.Universal.SortedTypes.
Require Export UniMath.Algebra.Universal.Terms.

Local Open Scope sorted.

Section Variables.

  Definition varspec (σ: signature) := ∑ V: hSet, V → sorts σ.

  Definition make_varspec (σ: signature) (varsupp: hSet) (varsorts: varsupp → sorts σ)
    : varspec σ := (varsupp,, varsorts).

  Coercion varsupp {σ: signature}: varspec σ → hSet := pr1.

  Definition varsort {σ: signature} {V: varspec σ}: V → sorts σ := pr2 V.

  Definition vsignature (σ : signature) (V: varspec σ): signature
    := make_signature (sorts σ) (setcoprod (names σ) V) (sumofmaps (ar σ) (λ v, nil ,, varsort v)).

  Context {σ : signature}.

  Definition namelift {V: varspec σ} (nm: names σ): names (vsignature σ V) := inl nm.

  Definition varname {V: varspec σ} (v: V): names (vsignature σ V) := inr v.

  Definition vterm (σ: signature) (V: varspec σ): sUU (sorts σ) := term (vsignature σ V).

  Definition vtermset (σ: signature) (V: varspec σ): shSet (sorts σ) := termset (vsignature σ V).

  Definition varterm {V: varspec σ} (v: V): vterm σ V (varsort v) := build_term (varname v) [()].

  Definition assignment {σ: signature} (A: sUU (sorts σ)) (V: varspec σ) : UU := ∏ v: V, A (varsort v).

  (** Evaluation maps for terms and corresponding unfolding properties *)

  Definition fromvterm {A: sUU (sorts σ)} {V: varspec σ}
                       (op : (∏ nm : names σ, A⋆ (arity nm) → A (sort nm)))
                       (α : assignment A V)
    : vterm σ V s→ A.
  Proof.
    refine (@fromterm (vsignature σ V) A _).
    induction nm as [nm | v].
    - exact (op nm).
    - exact (λ _, α v).
  Defined.

  Lemma fromvtermstep {A: sUU (sorts σ)} {V: varspec σ}
                      (op : (∏ nm : names σ, A⋆ (arity nm) → A (sort nm)))
                      (α : assignment A V)
                      (nm: names σ) (v:  (vterm σ V)⋆ (arity nm))
    : fromvterm op α (sort nm) (build_term (namelift nm) v) = op nm ((fromvterm op α)⋆⋆ (arity nm) v).
  Proof.
    unfold fromvterm, fromterm.
    rewrite (term_ind_step _ _  (namelift nm)).
    simpl.
    rewrite h2lower_h1map_h1lift.
    apply idpath.
  Defined.

  (** This used to be provable with apply idpath in the single sorted case **)
  Lemma fromvtermstep' {A: sUU (sorts σ)} {V: varspec σ}
                       (op : (∏ nm : names σ, A⋆ (arity nm) → A (sort nm)))
                       (α : assignment A V)
                       (v: V)
    : fromvterm op α (varsort v) (build_term (varname v) [()]) = α v.
  Proof.
    unfold fromvterm, fromterm.
    rewrite (term_ind_step _ _  (varname v)).
    apply idpath.
  Defined.

End Variables.