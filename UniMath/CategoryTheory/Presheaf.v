(** ****************************************************************************

Theory about set-valued presheaves. We write PreShv C for [C^op,HSET].

Contents:

- Limits ([Lims_PreShv_of_shape])
- Colimits ([Colims_PreShv_of_shape])
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
- Proof that [Ω_PreShv] is a bounded lattice object ([Ω_PreShv_lattice],
  [Ω_PreShv_bounded_lattice])

Written by: Anders Mörtberg, 2017

********************************************************************************)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Algebra.Lattice.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
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

Notation "'PreShv' C" := [C^op,SET] (at level 4) : cat.

Section basics.

Lemma transportf_PreShv {C : precategory} (F : PreShv C) {x y z : C}
  (e : x = y) (f : C⟦x,z⟧) (u : pr1 (pr1 F z)) :
  transportf (λ x, pr1 (pr1 F x)) e (# (pr1 F) f u) =
  # (pr1 F) (transportf (@precategory_morphisms C^op z) e f) u.
Proof.
now induction e.
Qed.

End basics.

(** Various limits and colimits in PreShv C *)
Section limits.

Context {C : precategory}.

(* This should be only small limits *)
(* Lemma Lims_PreShv : Lims (PreShv C). *)
(* Proof. *)
(* now apply LimsFunctorCategory, LimsHSET. *)
(* Defined. *)

Lemma Lims_PreShv_of_shape (g : graph) : Lims_of_shape g (PreShv C).
Proof.
now apply LimsFunctorCategory_of_shape, LimsHSET_of_shape.
Defined.

(* This should be only small colimits *)
(* Lemma Colims_PreShv : Colims (PreShv C). *)
(* Proof. *)
(* now apply ColimsFunctorCategory, ColimsHSET. *)
(* Defined. *)

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
now apply FunctorcategoryPullbacks, PullbacksHSET.
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

(** * Definition of the subobject classifier in a presheaf. *)
(**
See: "Sheaves in Geometry and Logic" by Mac Lane and Moerdijk (page 37)
*)
(* TODO: Prove that Ω actually is the subobject classifier  *)
Section Ω_PreShv.

Context {C : precategory}.

Definition sieve_def (c : C) : UU.
Proof.
use total2.
- apply (hsubtype (∑ (x : C),C⟦x,c⟧)).
- intros S.
  apply (∏ (s1 : ∑ (x : C),C⟦x,c⟧), S s1 →
         ∏ y (f : C⟦y,pr1 s1⟧), S (y,, f · pr2 s1)).
Defined.

Lemma isaset_sieve (c : C) : isaset (sieve_def c).
Proof.
use isaset_total2.
- apply isasethsubtype.
- intros S; repeat (apply impred_isaset; intro); apply isasetaprop, propproperty.
Qed.

(* If I use HSET here the coercion isn't triggered later and I need to insert pr1 explicitly *)
Definition sieve (c : C) : hSet := (sieve_def c,,isaset_sieve c).

Definition pr1sieve {c : C} : sieve_def c → hsubtype _ := @pr1 _ _.
Coercion pr1sieve : sieve_def >-> hsubtype.

Lemma sieve_eq (c : C) (s t : sieve c) (H : pr1 s = pr1 t) : s = t.
Proof.
apply subtypeEquality; [|apply H].
now intros x; repeat (apply impred; intros); apply propproperty.
Qed.

Definition maximal_sieve (c : C) : sieve c.
Proof.
mkpair.
- intro S; apply htrue.
- intros; apply tt.
Defined.

Definition empty_sieve (c : C) : sieve c.
Proof.
mkpair.
- intros S; apply hfalse.
- intros f S y g; apply S.
Defined.

Definition intersection_sieve (c : C) : binop (sieve c).
Proof.
simpl; intros S1 S2.
mkpair.
- intros f.
  apply (S1 f ∧ S2 f).
- simpl; intros f S f'.
  split.
  + apply (pr2 S1 _ (pr1 S)).
  + apply (pr2 S2 _ (pr2 S)).
Defined.

Definition union_sieve (c : C) : binop (sieve c).
Proof.
simpl; intros S1 S2.
mkpair.
- intros f.
  apply (S1 f ∨ S2 f).
- intros f S y f'; simpl in S; apply S; clear S; intro S.
  apply hinhpr.
  induction S as [S|S].
  + apply ii1, (pr2 S1 _ S).
  + apply ii2, (pr2 S2 _ S).
Defined.

Definition sieve_lattice (c : C) : lattice (sieve c).
Proof.
use mklattice.
- apply intersection_sieve.
- apply union_sieve.
- repeat split; intros S1; intros;
  apply sieve_eq, funextsec; intro f; simpl.
  + apply (isassoc_Lmin hProp_lattice).
  + apply (iscomm_Lmin hProp_lattice).
  + apply (isassoc_Lmax hProp_lattice).
  + apply (iscomm_Lmax hProp_lattice).
  + apply (Lmin_absorb hProp_lattice).
  + apply (Lmax_absorb hProp_lattice).
Defined.

Definition sieve_bounded_lattice (c : C) : bounded_lattice (sieve c).
Proof.
use mkbounded_lattice.
- apply sieve_lattice.
- apply empty_sieve.
- apply maximal_sieve.
- split; intros S; apply sieve_eq, funextsec; intro f; simpl.
  + apply (islunit_Lmax_Lbot hProp_bounded_lattice).
  + apply (islunit_Lmin_Ltop hProp_bounded_lattice).
Defined.

Definition sieve_mor a b (f : C⟦b,a⟧) : sieve a → sieve b.
Proof.
simpl; intros S.
mkpair.
- intros g.
  apply (S (pr1 g,,pr2 g · f)).
- abstract (intros g H y h; simpl; rewrite <- assoc; apply (pr2 S (pr1 g,,pr2 g · f)), H).
Defined.

Local Definition Ω_PreShv_data : functor_data C^op HSET := (sieve,,sieve_mor).

Local Lemma is_functor_Ω_PreShv_data : is_functor Ω_PreShv_data.
Proof.
split.
- intros x; apply funextfun; intros [S hS]; simpl.
  apply subtypeEquality; simpl.
  + intros X; repeat (apply impred; intro); apply propproperty.
  + now apply funextsec; intro; rewrite id_right.
- intros x y z f g; apply funextfun; intros [S hS]; simpl.
  apply subtypeEquality; simpl.
  + intros X; repeat (apply impred; intro); apply propproperty.
  + now repeat (apply funextsec; intro); rewrite <- assoc.
Qed.

Definition Ω_PreShv : PreShv C := (Ω_PreShv_data,,is_functor_Ω_PreShv_data).

Definition Ω_mor : (PreShv C)⟦Terminal_PreShv,Ω_PreShv⟧.
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

Definition Ω_PreShv_meet : PreShv(C)⟦Ω_PreShv ⊗ Ω_PreShv,Ω_PreShv⟧.
Proof.
use mk_nat_trans.
+ intros c S1S2.
  apply (intersection_sieve c (pr1 S1S2) (pr2 S1S2)).
+ intros x y f.
  apply funextsec; cbn; intros [S1 S2].
  now apply sieve_eq.
Defined.

Definition Ω_PreShv_join : PreShv(C)⟦Ω_PreShv ⊗ Ω_PreShv,Ω_PreShv⟧.
Proof.
use mk_nat_trans.
+ intros c S1S2.
  apply (union_sieve c (pr1 S1S2) (pr2 S1S2)).
+ intros x y f.
  apply funextsec; cbn; intros [S1 S2].
  now apply sieve_eq.
Defined.

Definition Ω_PreShv_lattice : latticeob BinProducts_PreShv Ω_PreShv.
Proof.
use mk_latticeob.
+ apply Ω_PreShv_meet.
+ apply Ω_PreShv_join.
+ repeat split; apply (nat_trans_eq has_homsets_HSET); intro c;
                apply funextsec; intros S; simpl.
  - apply (isassoc_Lmin (sieve_lattice c)).
  - apply (iscomm_Lmin (sieve_lattice c)).
  - apply (isassoc_Lmax (sieve_lattice c)).
  - apply (iscomm_Lmax (sieve_lattice c)).
  - apply (Lmin_absorb (sieve_lattice c)).
  - apply (Lmax_absorb (sieve_lattice c)).
Defined.

Definition Ω_PreShv_bottom : PreShv(C)⟦Terminal_PreShv,Ω_PreShv⟧.
Proof.
use mk_nat_trans.
+ intros c _; apply empty_sieve.
+ now intros x y f; apply funextsec; intros []; apply sieve_eq.
Defined.

Definition Ω_PreShv_top : PreShv(C)⟦Terminal_PreShv,Ω_PreShv⟧.
Proof.
use mk_nat_trans.
+ intros c _; apply maximal_sieve.
+ now intros x y f; apply funextsec; intros []; apply sieve_eq.
Defined.

Definition Ω_PreShv_bounded_lattice :
  bounded_latticeob BinProducts_PreShv Terminal_PreShv Ω_PreShv.
Proof.
use mk_bounded_latticeob.
- exact Ω_PreShv_lattice.
- exact Ω_PreShv_bottom.
- exact Ω_PreShv_top.
- split; apply (nat_trans_eq has_homsets_HSET); intro c;
         apply funextsec; cbn; intros S.
  + apply (islunit_Lmax_Lbot (sieve_bounded_lattice c)).
  + apply (islunit_Lmin_Ltop (sieve_bounded_lattice c)).
Defined.

End Ω_PreShv.
