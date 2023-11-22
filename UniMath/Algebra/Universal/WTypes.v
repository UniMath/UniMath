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
Local Open Scope cat.
Local Open Scope hom.
Local Open Scope vec.
Local Open Scope sorted.


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

Context (σ: signature_simple_single_sorted).

Definition A := names σ.

Definition B (a: A) := ⟦ length (arity a) ⟧.

(* Polynomial functor corresponding to signature σ *)

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

(** Prove that the ground term algebra is a W-type *)

(* Definition make_h1const {A: UU} {n: nat}: (⟦ n ⟧ → A) → *)

Local Definition U := gterm σ tt.

Local Definition sup: ∏ x : A, (B x → U) → U.
Proof.
  intros nm subterms.
  refine (build_gterm nm _).
  apply vec_to_h1const.
  exact (make_vec subterms).
Defined.

Local Lemma build_gterm_sup (nm: A) (v: (gterm σ)⋆ (arity nm)):
  build_gterm nm v = sup nm (el (h1const_to_vec v)).
Proof.
  unfold sup.
  apply maponpaths.
  apply pathsinv0.
  etrans.
  + apply maponpaths.
    apply make_vec_el.
  + apply h1const_vec_h1const.
Qed.

Local Definition lift_predicate (P : gterm σ tt → UU): ∏ (s: sorts σ), gterm σ s → UU.
Proof.
  intros s t.
  induction s.
  exact (P t).
Defined.

Local Lemma lemma_ind (n: nat) (K: ∏ x: unit, UU) (H: ∏ x: unit, K x → UU)
                      (h1v: hvec (vec_map K (vec_fill tt n))) (u: ⟦ n ⟧)
   : el (h1lower (h1map H h1v)) u = H tt (el (h1const_to_vec h1v) u).
Proof.
  induction n.
  - exact (fromstn0 u).
  - induction u as [u uproof].
    induction u.
    + apply idpath.
    + apply IHn.
Defined.

Local Lemma lemma_ind' (n: nat) (K: ∏ x: unit, UU) (H: ∏ x: unit, K x → UU)
                       (h1v: hvec (vec_map K (vec_fill tt n))) (u: ⟦ n ⟧)
                       (z:  el (h1lower (h1map H h1v)) u)
   : H tt (el (h1const_to_vec h1v) u).
Proof.
  induction n.
  - exact (fromstn0 u).
  - induction u as [u uproof].
    induction u.
    + apply z.
    + apply IHn.
      apply z.
Defined.

Local Definition ind: ∏ P : U → UU, (∏ (x : A) (f : B x → U)
                                     , (∏ u : B x, P (f u)) → P (sup x f)) → ∏ w : U, P w.
Proof.
  unfold U in *.
  intros P e_s w.
  set (H := lift_predicate P).
  change (P w) with (H tt w).
  apply term_ind.
  intros nm v IH.
  simpl.
  set (f:= el (h1const_to_vec v)).
  apply (transportb _ (build_gterm_sup nm v)).
  apply e_s.
  intro u.
  unfold f.
  set (IHu := hel IH u).
  unfold h1map_vec in IHu.
  change P with (H tt).
  apply lemma_ind'.
  apply IHu.
Defined.

(*
Lemma transport_lemma {C : UU} (P: C → UU) (e_s : ∏ (x : A) (f : B x → U), (∏ u : B x, P (f u)) → P (sup x f)
  : transportb B p (e_s x f) = e_s x (transportb (H x)).


Local Lemma lemma_beta (P : U → UU) (e_s : ∏ (x: A) (f: B x → U) (IH: ∏ u: B x, P (f u)), P (sup x f)) (x: A) (f: B x → U)
                       (IH: ∏ u: B x, P (el (h1const_to_vec (vec_to_h1const (make_vec f))) u))
  : ∑ A:(∏ u: B x, P (f u)), transportb P (build_gterm_sup x (vec_to_h1const (make_vec f))) (e_s x (el (h1const_to_vec (vec_to_h1const (make_vec f)))) IH)
    = e_s x f A.
Proof.
  eexists.
  set (path := build_gterm_sup x (vec_to_h1const (make_vec f))).
  clearbody path.
  unfold sup in path.

  revert path.
  rewrite vec_h1const_vec.

  generalize path.
  intro path0
  Search transportb "fun".
Abort.

Lemma transport_const {X Y Z: UU} (P: Z → UU) (f: ∏ (x: X) (y: Y), Z) (i: ∏ (x: X) (y: Y), P (f x y)) (x: X) (y1 y2: Y) (p: f x y1 = f x y2)
  : transportb P p (i x y2) = i x y1.
Proof.

Local Definition beta (P : U → UU) (e_s : ∏ (x: A) (f: B x → U) (IH: ∏ u: B x, P (f u)), P (sup x f))
                      (x : A) (f : B x → U)
  : ind P e_s (sup x f) = e_s x f (λ u, ind P e_s (f u)).
Proof.
  unfold ind.
  unfold sup.
  rewrite (term_ind_step _ _ x).

  rewrite XX.
  rewrite <- functtransportb
  Search transportb maponpaths.

  simpl.
Abort.
*)