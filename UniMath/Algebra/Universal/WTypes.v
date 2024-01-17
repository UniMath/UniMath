(** * Algebra, functor algebras and w-types. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.W.Core.
Require Import UniMath.Induction.W.Wtypes.
Require Import UniMath.Induction.FunctorAlgebras_legacy.

Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Algebras.
Require Import UniMath.Algebra.Universal.HVectors.
Require Import UniMath.Algebra.Universal.Terms.
Require Import UniMath.Algebra.Universal.TermAlgebras.

Local Open Scope stn.
Local Open Scope vec.
Local Open Scope sorted.

Section alegbra_functoralgebra.

  Section lemmas.

    (** Correspondence between a vector of types and an hvector of level 1 with constant arguments *)

    Definition h1const_to_vec {A: UU} {n: nat} {B: A} {P: A → UU}
                              (hv: hvec (vec_map P (vec_fill B n)) )
      : vec (P B) n.
    Proof.
      induction n.
      - exact vnil.
      - simpl in hv.
        exact (pr1 hv ::: IHn (pr2 hv)).
    Defined.

    Definition vec_to_h1const {A: UU} {n: nat} {B: A} {P: A → UU} (v: vec (P B) n)
      : hvec (vec_map P (vec_fill B n)).
    Proof.
      induction n.
      - exact hnil.
      - simpl in v.
        simpl.
        exact (pr1 v ::: IHn (pr2 v))%hvec.
    Defined.

    Definition h1const_vec_h1const {A: UU} {n: nat} {B: A} {P: A → UU}
                                  (hv: hvec (vec_map P (vec_fill B n)) )
      : vec_to_h1const (h1const_to_vec hv) = hv.
    Proof.
      induction n.
      - induction hv.
        apply idpath.
      - simpl in hv.
        simpl.
        change hv with (pr1 hv ::: pr2 hv)%hvec.
        apply maponpaths.
        apply (IHn (pr2 hv)).
    Defined.

    Definition vec_h1const_vec {A: UU} {n: nat} {B: A} {P: A → UU} (v: vec (P B) n)
      : h1const_to_vec ( vec_to_h1const v ) = v.
    Proof.
      induction n.
      - induction v.
        apply idpath.
      - simpl in v.
        simpl.
        change v with (pr1 v ::: pr2 v).
        apply maponpaths.
        apply (IHn (pr2 v)).
    Defined.
    (** This is the inverse of eta_unit **)
    Lemma eta_unit' {X : UU} (f : unit -> X) : (λ _, f tt) = f.
    Proof.
      apply funextfun.
      intro x.
      induction x.
      apply idpath.
    Defined.

    (** Helper lemma on transport *)

    Definition transportf_dirprod' (A : UU) (B B' : A -> UU) (a a': A) (x: B a)
                                  (x': B' a) (p : a = a')
      : transportf (λ a, B a × B' a) p (x,, x') =
          make_dirprod (transportf (λ a, B a) p x) (transportf (λ a, B' a) p x').
    Proof.
      induction p.
      apply idpath.
    Qed.

    Lemma transportb_sec_constant {A B : UU} {C : A -> B -> UU} {x1 x2 : A} (p : x1 = x2)
                                  (f : ∏ y : B, C x2 y)
    : transportb (λ x, ∏ y : B, C x y) p f = (λ y, transportb (λ x, C x y) p (f y)).
    Proof.
    induction p.
    apply idpath.
    Qed.

    Lemma transportb_fun {P: (unit → UU) → UU} {Q: (unit → UU) → UU} {a a': unit → UU}
                        {p: a = a'} {f: P a' → Q a'} {x: P a}
      : transportb (λ x: unit → UU, P x → Q x) p f x =
          transportb (λ x: unit → UU, Q x) p (f (transportf (λ x: unit → UU, P x) p x)).
    Proof.
      induction p.
      apply idpath.
    Qed.

    Lemma transportf_eta_unit' {P: (unit → UU) → UU} {a: unit → UU} (y: a tt)
      : transportf (λ x0 : unit → UU, x0 tt) (eta_unit' a) y = y.
    Proof.
      rewrite (transportf_funextfun
                (λ A:UU, A) _ _
                (λ x : unit, unit_rect (λ x0 : unit, a tt = a x0) (idpath (a tt)) x)
              ).
    unfold unit_rect.
    rewrite idpath_transportf.
    apply idpath.
    Qed.

    Lemma transportb_eta_unit'{P: (unit → UU) → UU} {a: unit → UU} (y: a tt)
      : transportb (λ x0 : unit → UU, x0 tt) (eta_unit' a) y = y.
    Proof.
      apply (transportb_transpose_left(P:= λ x0: unit → UU, x0 tt)(e:=eta_unit' a)).
      apply pathsinv0.
      apply (transportf_eta_unit'(P:= λ x0: unit → UU, x0 tt)).
    Qed.

    (** Helper lemma for interaction between h1const and eta_unit *)

    Lemma h1const_to_vec_eta_unit' {f: sUU unit} {n: nat} {hv: hvec (vec_map (λ _ : unit, f tt) (vec_fill tt n))}
      : h1const_to_vec hv =
        h1const_to_vec (transportf (λ X, hvec (vec_map X (vec_fill tt n))) (eta_unit' f) hv).

    Proof.
      induction n.
      - apply idpath.
      - simpl.
        rewrite transportf_dirprod'.
        use total2_paths2.
        + simpl.
          rewrite (transportf_eta_unit'(P:=λ a: unit → UU, a tt)).
          apply idpath.
        + apply (IHn (pr2 hv)).
    Defined.

  End lemmas.

  Local Open Scope cat.
  Local Open Scope hom.

  Context (σ: signature_simple_single_sorted).

  Let A := names σ.

  Let B (a: A) := ⟦ length (arity a) ⟧.

  (* Polynomial functor corresponding to the signature σ *)

  Local Notation F := (polynomial_functor A B).

  (** Prove that algebra_ob and algebra are equal types *)

    Definition algebra_to_functoralgebra (a: algebra σ)
      : algebra_ob F.
    Proof.
      induction a as [carrier ops].
      unfold algebra_ob.
      exists (carrier tt).
      simpl.
      intro X.
      induction X as [nm subterms].
      refine (ops nm _).
      apply vec_to_h1const.
      exact (make_vec subterms).
    Defined.

    Definition functoralgebra_to_algebra (FAlg: algebra_ob F)
      : algebra σ.
    Proof.
      induction FAlg as [carrier ops].
      simpl in ops.
      exists (λ _, carrier).
      intro nm.
      intro subterms.
      apply h1const_to_vec in subterms.
      exact (ops (nm ,, el subterms)).
    Defined.

    Lemma alg_funcalg_alg (a: algebra_ob F)
      : algebra_to_functoralgebra (functoralgebra_to_algebra a) = a.
    Proof.
      use total2_paths2_f.
      - apply idpath.
      - rewrite idpath_transportf.
        apply funextfun.
        intro X.
        simpl.
        rewrite vec_h1const_vec.
        rewrite el_make_vec_fun.
        apply idpath.
    Qed.

    Lemma funcalg_alg_funcalg (a: algebra σ)
      : functoralgebra_to_algebra (algebra_to_functoralgebra a) = a.
    Proof.
      use total2_paths2_b.
      - apply eta_unit'.
      - apply funextsec.
        intro nm.
        apply funextfun.
        intro x.
        simpl.
        rewrite make_vec_el.
        rewrite h1const_to_vec_eta_unit'.
        rewrite h1const_vec_h1const.
        rewrite transportb_sec_constant.
        rewrite transportb_fun.
        rewrite (transportb_eta_unit'(P:=(λ x0 : unit → UU, x0 (sort nm)))).
        apply idpath.
    Defined.

    Definition alegbra_weq_functoralgebra: algebra σ ≃ algebra_ob F.
    Proof.
      apply (weq_iso algebra_to_functoralgebra functoralgebra_to_algebra).
      exact funcalg_alg_funcalg.
      exact alg_funcalg_alg.
    Defined.

    Definition alegbra_eq_functoralgebra: algebra σ = algebra_ob F.
    Proof.
      apply univalence.
      exact alegbra_weq_functoralgebra.
    Defined.

End alegbra_functoralgebra.


Section groundTermAlgebraWtype.

(** Prove that the ground term algebra is a W-type *)

  Section lemmas.

    Definition comp_maponsecfibers {X : UU} {P Q : X → UU} (f : (∏ x : X, (P x ≃ Q x))) {p} {x}
      : (weqonsecfibers P Q f) p x = (f x) (p x).
    Proof.
      apply idpath.
    Defined.

    Definition inv_weqonsecbase {X Y} {P:Y→UU} (f:X≃Y) {xz} {y}
      : invmap (weqonsecbase P f) xz y = transportf _ (homotweqinvweq f y) (xz (invmap f y)).
    Proof.
      apply idpath.
    Defined.

    Section Comp_weqonsec.

    Context {X Y} {P:X->Type} {Q:Y->Type}
            {f:X ≃ Y} {g:∏ x, weq (P x) (Q (f x))}.

    Definition comp_weqonsec  :
      pr1weq (weqonsec P Q f g) =
      (λ xp y, transportf Q (homotweqinvweq f y) ((g (invmap f y)) (xp (invmap f y)))).
      Proof.
        apply idpath.
      Defined.
    End Comp_weqonsec.

    Definition inv_weqonsecfibers {X : UU} {P Q : X → UU} (f : (∏ x : X, (P x ≃ Q x)))
      : invmap (weqonsecfibers P Q f) = (λ q x, invmap (f x) (q x)).
    Proof.
      use funextsec.
      intro q.
      use funextsec.
      intro x.
      use maponpaths.
      simpl.
      use proofirrelevance.
      fold ((hfiber (f x) (q x))).
      use isapropifcontr.
      use weqproperty.
    Defined. (*it is possible to improve computation time here?*)

    Definition inv_weqonsec {X Y} {P:X->Type} {Q:Y->Type}
              {f:X ≃ Y} {g:∏ x, weq (P x) (Q (f x))} :
      (invmap (weqonsec P Q f g)) =
      (λ yq x, invmap (g x) (yq ( f x)) ).
    Proof.
      use funextsec.
      intro yq.
      use funextsec.
      intro x.

      unfold weqonsec.
      rewrite invmap_weqcomp_expand.
      simpl.
      rewrite inv_weqonsecfibers.
      apply idpath.
    Defined.

  End lemmas.

  Context (σ: signature_simple_single_sorted).

  Let A := names σ.
  Let B (a: A) := ⟦ length (arity a) ⟧.
  Let U := gterm σ tt.

  Section sup.

    Definition gtweq_sec (x:A) : (gterm σ)⋆ (arity x) ≃ (B x → U).
    Proof.
      unfold star.
      use (weqcomp helf_weq).
      use weqonsecfibers.
      intro i.
      use eqweqmap.
      use el_vec_map_vec_fill.
    Defined.

    Definition gtweq_sec_comp {x:A} (v:(gterm σ)⋆ (arity x)) (i : B x) : gtweq_sec x v i = eqweqmap (el_vec_map_vec_fill (gterm σ) tt i) (hel v i).
    Proof.
      apply idpath.
    Defined.

    Definition gtweq_sectoU (x:A)
      : ((gterm σ)⋆ (arity x) → U) ≃ ((B x → U) → U)
      := invweq (weqbfun U (gtweq_sec x)).

    Definition gtweqtoU
      : (∏ x : A, (gterm σ)⋆ (arity x) → U) ≃ (∏ x : A, (B x → U) → U)
      := (weqonsecfibers _ _ gtweq_sectoU).

    Definition sup: ∏ x : A, (B x → U) → U.
    Proof.
      use (gtweqtoU).
      use build_gterm.
    Defined.

  End sup.

  Section ind.

    Definition ind_HP (P:U → UU) : UU
      := ∏ (x : A) (f : B x → U), (∏ u : B x, P (f u)) → P (sup x f).

    Definition lower_predicate : (∏ (s: sorts σ), gterm σ s → UU) ≃ (U → UU).
    Proof.
      use (weqsecoverunit (λ s, gterm σ s → UU)).
    Defined.

    Context
        (P:(∏ (s: sorts σ), gterm σ s → UU)).
      Let lowP := lower_predicate P.

    Section ind_HP.

      Context
        (nm:names σ)
        (v : (gterm σ)⋆ (arity nm)).
      Let f := gtweq_sec nm v.

      Theorem ind_HP_Hypo : hvec (h1map_vec P v) ≃ (∏ u : B nm, lowP (f u)).
      Proof.
        use (weqcomp helf_weq).
        use weqonsecfibers.
        intro i.
        use eqweqmap.
        use hel_h1map_vec_vec_fill.
      Defined.

      Theorem ind_HP_Th : P (sort nm) (build_gterm nm v) ≃ lowP (sup nm f).
      Proof.
        change (sort nm) with tt.

        change (lowP) with (P tt).

        use eqweqmap.
        use maponpaths.
        unfold sup.
        unfold gtweqtoU.

        change (build_gterm nm v = transportf (λ _ : B nm → U, U) (homotweqinvweq (gtweq_sec nm) f) (build_gterm nm (invmap (gtweq_sec nm) f))).
        (*
        (* to see why the computation above works step by step run the following code *)
        rewrite comp_maponsecfibers.
        unfold gtweq_sectoU, weqbfun.
        simpl.
        rewrite (inv_weqonsecbase (P:=(λ _ : B nm → U, U)) (gtweq_sec nm)).
        *)
        rewrite transportf_const.
        induction ((homotweqinvweq (gtweq_sec nm) f)).
        use pathsinv0.
        etrans.
        { use idpath_transportf. }
        use maponpaths.
        induction (!homotweqinvweq (gtweq_sec nm) f).
        use pathsinv0.
        use homotinvweqweq0.
      Defined.

    End ind_HP.

    Theorem HP_weq : term_ind_HP P ≃ ind_HP (lowP).
    Proof.
      use weqonsecfibers.
      intro x.
      cbn beta.
      use weqonsec.
      + use gtweq_sec.
      + intro v.
        use weqonsec.
        - use ind_HP_Hypo.
        - intro HypOnSub.
          use ind_HP_Th.
    Defined.

    Theorem toLowerPredicateWeq : (∏ (s : sorts σ) (t : gterm σ s), P s t) ≃ (∏ w : U, lowP w).
    Proof.
      use weqsecoverunit.
    Defined.

  End ind.

  Definition ind_weq
    : (∏ P : ∏ s : sorts σ, gterm σ s → UU, term_ind_HP P → ∏ (s : sorts σ) (t : gterm σ s), P s t) ≃
    (∏ P : U → UU, ind_HP P → ∏ w : U, P w).
  Proof.
    use weqonsec.
    + exact lower_predicate.
    + intro P.
      use weqonsec.
      - use HP_weq.
      - intros H.
        cbn beta.
        use toLowerPredicateWeq.
  Defined.

  Definition ind: ∏ P : U → UU, ind_HP P → ∏ w : U, P w.
    Proof.
      use ind_weq.
      use term_ind.
    Defined.

  Theorem invind : term_ind = (invweq ind_weq) ind.
    Proof.
      use pathsweq1.
      unfold ind.
      apply idpath.
    Defined.

  Section beta_simplecase.
    Context
      (P:(∏ (s: sorts σ), gterm σ s → UU))
      (nm: names σ)
      (v : (gterm σ)⋆ (arity nm))
      (R : ∏ (nm : names σ) (v : (gterm σ)⋆ (arity nm)), hvec (h1map_vec P v) → P (sort nm) (build_gterm nm v)).
    Let lowP := lower_predicate P.
    Let f := gtweq_sec nm v.
    Let e_s : ∏ (x: A) (f: B x → U) (IH: ∏ u: B x, lowP (f u)), lowP (sup x f) := HP_weq P R.

    Section lemmas.

      Theorem termInd_ind : ind lowP e_s = term_ind P R.
      Proof.
        rewrite invind.
        unfold ind_weq.
        simpl.

        rewrite inv_weqonsec.
        rewrite inv_weqonsec.

        use maponpaths.
        apply idpath.
      Defined.

      Theorem ind_HP_Th_termInd
      : ind_HP_Th P nm v (term_ind P R (build_gterm nm v)) = term_ind P R (sup nm (gtweq_sec nm v)).
      Proof.
        use eqweqmap_ap.
      Defined.

      Theorem UnderstangHP_weq : R = invweq (HP_weq P) e_s.
      Proof.
        use pathsweq1.
        apply idpath.
      Defined.

      Theorem UnderstandingR
      : R nm v = (invweq ((ind_HP_Th P nm v)))∘(e_s nm f)∘(ind_HP_Hypo P nm v).
      Proof.
        rewrite UnderstangHP_weq.
        change (invweq (HP_weq P) e_s nm v) with (invmap (HP_weq P) e_s nm v).
        unfold HP_weq.
        rewrite (inv_weqonsecfibers
          (P:=(λ x : names σ, ∏ v0 : (gterm σ)⋆ (arity x), hvec (h1map_vec P v0) → P (sort x) (build_gterm x v0)))
          (Q:=(λ x : names σ, ∏ f0 : B x → U, (∏ u : B x, lower_predicate P (f0 u)) → lower_predicate P (sup x f0)))).
        rewrite inv_weqonsec.
        rewrite inv_weqonsec.
        apply idpath.
      Defined.

      Theorem ind_HP_Hypo_h2map
      : ind_HP_Hypo P nm v (h2map (λ (s : sorts σ) (t _ : gterm σ s), term_ind P R t) (h1lift v)) = (λ u : B nm, ind lowP e_s (f u)).
      Proof.
        use pathsweq1'.
        unfold ind_HP_Hypo.
        rewrite invmap_weqcomp_expand.
        rewrite inv_helf_weq.
        rewrite inv_weqonsecfibers.
        unfold funcomp.
        rewrite termInd_ind.
        use h2map_makehvec_basevecfill.
      Defined.

    End lemmas.

    Definition beta_simplecase : ind lowP e_s (sup nm f) = (e_s nm f (λ u, ind lowP e_s (f u))).
    Proof.
      use (weqonpaths2 _ _ _ (term_ind_step P R nm v)).
      + apply ind_HP_Th.
      + etrans.
        { apply ind_HP_Th_termInd. }
        use toforallpaths.
        use (!termInd_ind).
      + rewrite UnderstandingR.
        unfold funcomp.
        use pathsweq1'.
        use maponpaths.
        use maponpaths.
        use ind_HP_Hypo_h2map.
    Defined.

  End beta_simplecase.

  Section beta.
    Context
      (P:U → UU)
      (x: names σ)
      (f : B x → U)
      (e_s : ∏ (x: A) (f: B x → U) (IH: ∏ u: B x, P (f u)), P (sup x f) ).

    Definition beta: ind P e_s (sup x f) = e_s x f (λ u, ind P e_s (f u)).
    Proof.
      revert P x f e_s.
      use (invweq (weqonsecbase (λ pred, ∏ x f e_s, ind pred e_s (sup x f) = e_s x f (λ u : B x, ind pred e_s (f u))) lower_predicate)).
      intro P.
      cbn beta.
      intro nm.
      use (invweq (weqonsecbase (λ hponSub , ∏ e_s, ind (lower_predicate P) e_s (sup nm hponSub) = e_s nm hponSub (λ u : B nm, ind (lower_predicate P) e_s (hponSub u))) (gtweq_sec nm))).
      intro v.
      cbn beta.
      use (invweq (weqonsecbase (λ hpi, ind (lower_predicate P) hpi (sup nm (gtweq_sec nm v)) = hpi nm (gtweq_sec nm v) (λ u : B nm, ind (lower_predicate P) hpi (gtweq_sec nm v u))) (HP_weq P))).
      intro R.
      cbn beta.
      use beta_simplecase.
    Defined.

  End beta.

End groundTermAlgebraWtype.