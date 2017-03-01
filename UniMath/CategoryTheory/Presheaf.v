(** **********************************************************

Theory about set-valued presheaves. We write PreShv C for [C^op,HSET].

Contents:

- Limits ([Lims_PreShv], [Lims_PreShv_of_shape])
- Colimits ([Colims_PreShv], [Colims_PreShv_of_shape])
- Binary products ([BinProducts_PreShv])
- Indexed products ([Products_PreShv])
- Binary coproducts ([BinCoproducts_PreShv])
- Indexed coproducts ([Coproducts_PreShv])
- Initial object ([Initial_PreShv])
- Terminal object ([Terminal_PreShv])
- Pullbacks ([Pullbacks_PreShv])
- Exponentials ([has_exponentials_PreShv])
- Constant presheaf ([constant_PreShv])
- Definition of the subobject classifier (without proof) ([Ω_PreShv], [Ω_mor])


Written by: Anders Mörtberg, 2017

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.Lattice.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.LatticeObject.

Local Open Scope cat.

Notation "'PreShv' C" := [C^op,HSET,has_homsets_HSET] (at level 3) : cat.

(* TODO: upstream *)
Section hProp_lattice.

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

Definition hProp_lattice : lattice (hProp,,isasethProp).
Proof.
use mklattice.
- intros P Q; exact (P ∧ Q).
- simpl; intros P Q; exact (P ∨ Q).
- repeat split.
  + intros P Q R; apply isassoc_hconj.
  + intros P Q; apply iscomm_hconj.
  + intros P Q R; apply isassoc_hdisj.
  + intros P Q; apply iscomm_hdisj.
  + intros P Q; apply hconj_absorb_hdisj.
  + intros P Q; apply hdisj_absorb_hconj.
Defined.

End hProp_lattice.

(** Various limits and colimits in PreShv C *)
Section limits.

Context {C : precategory}.

Lemma Lims_PreShv : Lims (PreShv C).
Proof.
now apply LimsFunctorCategory, LimsHSET.
Defined.

Lemma Lims_PreShv_of_shape (g : graph) : Lims_of_shape g (PreShv C).
Proof.
now apply LimsFunctorCategory_of_shape, LimsHSET_of_shape.
Defined.

Lemma Colims_PreShv : Colims (PreShv C).
Proof.
now apply ColimsFunctorCategory, ColimsHSET.
Defined.

Lemma Colims_PreShv_of_shape (g : graph) : Colims_of_shape g (PreShv C).
Proof.
now apply ColimsFunctorCategory_of_shape, ColimsHSET_of_shape.
Defined.

Lemma BinProducts_PreShv : BinProducts (PreShv C).
Proof.
now apply BinProducts_functor_precat, BinProductsHSET.
Defined.

Lemma Products_PreShv I : Products I (PreShv C).
Proof.
now apply Products_functor_precat, ProductsHSET.
Defined.

Lemma BinCoproducts_PreShv : BinCoproducts (PreShv C).
Proof.
now apply BinCoproducts_functor_precat, BinCoproductsHSET.
Defined.

Lemma Coproducts_PreShv I (HI : isaset I) : Coproducts I (PreShv C).
Proof.
now apply Coproducts_functor_precat, CoproductsHSET, HI.
Defined.

Lemma Initial_PreShv : Initial (PreShv C).
Proof.
now apply Initial_functor_precat, InitialHSET.
Defined.

Lemma Terminal_PreShv : Terminal (PreShv C).
Proof.
now apply Terminal_functor_precat, TerminalHSET.
Defined.

Lemma Pullbacks_PreShv : Pullbacks (PreShv C).
Proof.
now apply FunctorPrecategoryPullbacks, PullbacksHSET.
Defined.

Lemma has_exponentials_PreShv (hsC : has_homsets C) :
  has_exponentials BinProducts_PreShv.
Proof.
now apply has_exponentials_functor_HSET, has_homsets_opp, hsC.
Defined.

End limits.

(** * Define some standard presheaves *)
Section presheaves.

Context {C : precategory}.

Definition constant_PreShv (A : HSET) : PreShv C.
Proof.
use mk_functor.
+ mkpair.
  - intros _; apply A.
  - intros a b f; apply idfun.
+ now split.
Defined.

Definition empty_PreShv : PreShv C := constant_PreShv emptyHSET.

End presheaves.

(** Definition of the subobject classifier in a presheaf
    TODO: Prove that Ω actually is the subobject classifier  *)
Section Ω_PreShv.

Context {C : precategory}.

Definition sieve_def (c : C) : UU.
Proof.
use total2.
- apply (∏ (x : C) (f : C⟦x,c⟧), hProp).
- intros S.
  apply (∏ (x : C) (f : C⟦x,c⟧), S x f → ∏ (y : C) (f' : C⟦y,x⟧), S y (f' · f)).
Defined.

Lemma isaset_sieve (c : C) : isaset (sieve_def c).
Proof.
use isaset_total2.
- repeat (apply impred_isaset; intro); apply isasethProp.
- intros S; simpl; repeat (apply impred_isaset; intro); apply isasetaprop, propproperty.
Qed.

(* If I use HSET here the coercion isn't triggered later and I need to insert pr1 explicitly *)
Definition sieve (c : C) : hSet := (sieve_def c,,isaset_sieve c).

Lemma sieve_eq (c : C) (s t : sieve c) (H : pr1 s = pr1 t) : s = t.
Proof.
apply subtypeEquality; try assumption.
now intros x; repeat (apply impred; intros); apply propproperty.
Qed.

Definition maximal_sieve (c : C) : sieve c.
Proof.
mkpair.
- apply (λ _ _, htrue).
- apply (λ _ _ _ _ _, tt).
Defined.

Definition empty_sieve (c : C) : sieve c.
Proof.
mkpair.
- apply (λ _ _, hfalse).
- intros x f S y g; apply S.
Defined.

Definition intersection_sieve (c : C) : binop (sieve c).
Proof.
intros S1 S2.
mkpair.
- intros x f.
  (* How can I get rid of the pr1's? *)
  apply (pr1 S1 x f ∧ pr1 S2 x f).
- simpl; intros x f S y f'.
  split.
  + apply (pr2 S1 _ _ (pr1 S)).
  + apply (pr2 S2 _ _ (pr2 S)).
Defined.

Definition union_sieve (c : C) : binop (sieve c).
Proof.
intros S1 S2.
mkpair.
- intros x f.
  (* How can I get rid of the pr1's? *)
  apply (pr1 S1 x f ∨ pr1 S2 x f).
- intros x f S y f'; apply S; clear S; intros S.
  apply hinhpr.
  induction S as [S|S].
  + apply ii1, (pr2 S1 _ _ S).
  + apply ii2, (pr2 S2 _ _ S).
Defined.

Definition sieve_lattice (c : C) : lattice (sieve c).
Proof.
use mklattice.
- apply intersection_sieve.
- apply union_sieve.
- repeat split.
  + intros S1 S2 S3.
    apply sieve_eq, funextsec; intro x; apply funextsec; intro f.
    apply isassoc_hconj.
  + intros S1 S2.
    apply sieve_eq, funextsec; intro x; apply funextsec; intro f.
    apply iscomm_hconj.
  + intros S1 S2 S3.
    apply sieve_eq, funextsec; intro x; apply funextsec; intro f.
    apply isassoc_hdisj.
  + intros S1 S2.
    apply sieve_eq, funextsec; intro x; apply funextsec; intro f.
    apply iscomm_hdisj.
  + intros S1 S2.
    apply sieve_eq, funextsec; intro x; apply funextsec; intro f.
    apply hconj_absorb_hdisj.
  + intros S1 S2.
    apply sieve_eq, funextsec; intro x; apply funextsec; intro f.
    apply hdisj_absorb_hconj.
Defined.

Definition sieve_bounded_lattice (c : C) : bounded_lattice (sieve c).
Proof.
use mkbounded_lattice.
- apply sieve_lattice.
- apply empty_sieve.
- apply maximal_sieve.
- split.
  + intros S.
    apply sieve_eq, funextsec; intro x; apply funextsec; intro f.
    apply hfalse_hdisj.
  + intros S.
    apply sieve_eq, funextsec; intro x; apply funextsec; intro f.
    apply htrue_hconj.
Defined.

Definition sieve_mor a b (f : C⟦b,a⟧) : sieve a → sieve b.
Proof.
intros S.
mkpair.
- intros y g.
  apply (pr1 S y (g · f)).
- abstract (intros y g H z h; simpl; rewrite <- assoc; apply (pr2 S), H).
Defined.

Local Definition Ω_PreShv_data : functor_data C^op HSET := (sieve,,sieve_mor).

Local Lemma is_functor_Ω_PreShv_data : is_functor Ω_PreShv_data.
Proof.
split.
- intros x; apply funextfun; intros [S hS]; simpl.
  apply subtypeEquality; simpl.
  + intros X; repeat (apply impred; intro); apply propproperty.
  + now repeat (apply funextsec; intro); rewrite id_right.
- intros x y z f g; apply funextfun; intros [S hS]; simpl.
  apply subtypeEquality; simpl.
  + intros X; repeat (apply impred; intro); apply propproperty.
  + now repeat (apply funextsec; intro); rewrite <- assoc.
Qed.

Definition Ω_PreShv : PreShv C := (Ω_PreShv_data,,is_functor_Ω_PreShv_data).

Let Ω := Ω_PreShv.

Definition Ω_mor : (PreShv C)⟦Terminal_PreShv,Ω⟧.
Proof.
use mk_nat_trans.
- simpl; apply (λ c _, maximal_sieve c).
- intros x y f; simpl in *; apply funextfun; cbn; intros _.
  apply sieve_eq; simpl.
  now repeat (apply funextsec; intros).
Defined.

Lemma isMonic_Ω_mor : isMonic Ω_mor.
Proof.
now apply from_terminal_isMonic.
Qed.

Local Notation "c '⊗' d" := (BinProductObject _ (BinProducts_PreShv c d)) (at level 75) : cat.

Definition Ω_meet : PreShv(C) ⟦Ω ⊗ Ω,Ω⟧.
Proof.
use mk_nat_trans.
+ intros c S1S2.
  apply (intersection_sieve c (pr1 S1S2) (pr2 S1S2)).
+ intros x y f.
  apply funextsec; cbn; intros [S1 S2].
  now apply sieve_eq.
Defined.

Definition Ω_join : PreShv(C) ⟦Ω ⊗ Ω,Ω⟧.
Proof.
use mk_nat_trans.
+ intros c S1S2.
  apply (union_sieve c (pr1 S1S2) (pr2 S1S2)).
+ intros x y f.
  apply funextsec; cbn; intros [S1 S2].
  now apply sieve_eq.
Defined.

Definition Ω_lattice : latticeob BinProducts_PreShv Ω_PreShv.
Proof.
use mklatticeob.
+ apply Ω_meet.
+ apply Ω_join.
+ repeat split.
  - apply (nat_trans_eq has_homsets_HSET); intro c.
    apply funextsec; intros S.
    apply (isassoc_Lmin (sieve_lattice c)).
  - apply (nat_trans_eq has_homsets_HSET); intro c.
    apply funextsec; intros S.
    apply (iscomm_Lmin (sieve_lattice c)).
  - apply (nat_trans_eq has_homsets_HSET); intro c.
    apply funextsec; intros S.
    apply (isassoc_Lmax (sieve_lattice c)).
  - apply (nat_trans_eq has_homsets_HSET); intro c.
    apply funextsec; intros S.
    apply (iscomm_Lmax (sieve_lattice c)).
  - apply (nat_trans_eq has_homsets_HSET); intro c.
    apply funextsec; intros S.
    apply (Lmin_absorb (sieve_lattice c)).
  - apply (nat_trans_eq has_homsets_HSET); intro c.
    apply funextsec; intros S.
    apply (Lmax_absorb (sieve_lattice c)).
Defined.

End Ω_PreShv.
