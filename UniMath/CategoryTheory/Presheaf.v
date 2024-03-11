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
- Exponentials ([Exponentials_PreShv])
- Constant presheaf ([constant_PreShv])
- Definition of the subobject classifier (without proof) ([Ω_PreShv], [Ω_mor])
- Proof that [Ω_PreShv] is a bounded lattice object ([Ω_PreShv_lattice],
  [Ω_PreShv_bounded_lattice])
- Construction of isomorphisms of functors between presheaf categories
  ([make_PreShv_functor_iso])

Written by: Anders Mörtberg, 2017-2019

********************************************************************************)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.OrderTheory.Lattice.Bounded.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.LatticeObject.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.

Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Local Open Scope cat.

Notation "'PreShv' C" := [C^op, HSET] (at level 4) : cat.

Section basics.

Lemma transportf_PreShv {C : category} (F : PreShv C) {x y z : C}
  (e : x = y) (f : C⟦x,z⟧) (u : ((F : functor _ _) z : hSet)) :
  transportf (λ x, pr1 (pr1 F x)) e (# (pr1 F) f u) =
  # (pr1 F) (transportf (@precategory_morphisms C^op z) e f) u.
Proof.
now induction e.
Qed.

End basics.

(** Various limits and colimits in PreShv C *)
Section limits.

Context {C : category}.

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

Lemma Exponentials_PreShv :
  Exponentials BinProducts_PreShv.
Proof.
now apply Exponentials_functor_HSET.
Defined.

End limits.

(** * Define some standard presheaves *)
Section presheaves.

Context {C : category}.

Definition constant_PreShv (A : HSET) : PreShv C.
Proof.
use make_functor.
+ use tpair.
  - intros _; apply A.
  - cbn. intros a b f. apply idfun.
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

Context {C : category}.

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
apply subtypePath; [|apply H].
now intros x; repeat (apply impred; intros); apply propproperty.
Qed.

Definition maximal_sieve (c : C) : sieve c.
Proof.
use tpair.
- intro S; apply htrue.
- cbn. intros; apply tt.
Defined.

Definition empty_sieve (c : C) : sieve c.
Proof.
use tpair.
- intros S; apply hfalse.
- intros f S y g; apply S.
Defined.

Definition intersection_sieve (c : C) : binop (sieve c).
Proof.
simpl; intros S1 S2.
use tpair.
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
use tpair.
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
use make_lattice.
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
use make_bounded_lattice.
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
use tpair.
- intros g.
  apply (S (pr1 g,,pr2 g · f)).
- abstract (intros g H y h; simpl; rewrite <- assoc; apply (pr2 S (pr1 g,,pr2 g · f)), H).
Defined.

Local Definition Ω_PreShv_data : functor_data C^op HSET := (sieve,,sieve_mor).

Local Lemma is_functor_Ω_PreShv_data : is_functor Ω_PreShv_data.
Proof.
split.
- intros x; apply funextfun; intros [S hS]; simpl.
  apply subtypePath; simpl.
  + intros X; repeat (apply impred; intro); apply propproperty.
  + now apply funextsec; intro; rewrite id_right.
- intros x y z f g; apply funextfun; intros [S hS]; simpl.
  apply subtypePath; simpl.
  + intros X; repeat (apply impred; intro); apply propproperty.
  + now repeat (apply funextsec; intro); rewrite <- assoc.
Qed.

Definition Ω_PreShv : PreShv C := (Ω_PreShv_data,,is_functor_Ω_PreShv_data).

Definition Ω_mor : (PreShv C)⟦Terminal_PreShv,Ω_PreShv⟧.
Proof.
use make_nat_trans.
- red; simpl; apply (λ c _, maximal_sieve c).
- intros x y f; simpl in *; apply funextfun; cbn; intros _.
  apply sieve_eq; simpl.
  now repeat (apply funextsec; intros).
Defined.

Lemma isMonic_Ω_mor : isMonic Ω_mor.
Proof.
now apply global_element_isMonic.
Qed.

Local Notation "c ⊗ d" := (BinProductObject _ (BinProducts_PreShv c d)) : cat.

Definition Ω_PreShv_meet : PreShv(C)⟦Ω_PreShv ⊗ Ω_PreShv,Ω_PreShv⟧.
Proof.
use make_nat_trans.
+ intros c S1S2.
  apply (intersection_sieve c (pr1 S1S2) (pr2 S1S2)).
+ intros x y f.
  apply funextsec; cbn; intros [S1 S2].
  now apply sieve_eq.
Defined.

Definition Ω_PreShv_join : PreShv(C)⟦Ω_PreShv ⊗ Ω_PreShv,Ω_PreShv⟧.
Proof.
use make_nat_trans.
+ intros c S1S2.
  apply (union_sieve c (pr1 S1S2) (pr2 S1S2)).
+ intros x y f.
  apply funextsec; cbn; intros [S1 S2].
  now apply sieve_eq.
Defined.

Definition Ω_PreShv_lattice : latticeob BinProducts_PreShv Ω_PreShv.
Proof.
use make_latticeob.
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
use make_nat_trans.
+ intros c _; apply empty_sieve.
+ now intros x y f; apply funextsec; intros []; apply sieve_eq.
Defined.

Definition Ω_PreShv_top : PreShv(C)⟦Terminal_PreShv,Ω_PreShv⟧.
Proof.
use make_nat_trans.
+ intros c _; apply maximal_sieve.
+ now intros x y f; apply funextsec; intros []; apply sieve_eq.
Defined.

Definition Ω_PreShv_bounded_lattice :
  bounded_latticeob BinProducts_PreShv Terminal_PreShv Ω_PreShv.
Proof.
use make_bounded_latticeob.
- exact Ω_PreShv_lattice.
- exact Ω_PreShv_bottom.
- exact Ω_PreShv_top.
- split; apply (nat_trans_eq has_homsets_HSET); intro c;
         apply funextsec; cbn; intros S.
  + apply (islunit_Lmax_Lbot (sieve_bounded_lattice c)).
  + apply (islunit_Lmin_Ltop (sieve_bounded_lattice c)).
Defined.

End Ω_PreShv.

(** Construction of isomorphisms of functors between presheaf categories *)
Section iso_presheaf.

Context {C : category}.

Local Definition make_PreShv_functor_z_iso_helper (F G : functor (PreShv C) (PreShv C))
      (set_iso : ∏ X c, z_iso (pr1 (F X) c) (pr1 (G X) c))
      (nat_in_c : ∏ X, is_nat_trans _ _ (λ c, set_iso X c))
      (nat_in_X : is_nat_trans F G (λ X, make_nat_trans _ _ _ (nat_in_c X))) :
      [PreShv C, PreShv C] ⟦ F, G ⟧.
Proof.
  use make_nat_trans.
    + intros X.
      use make_nat_trans.
      * intros c.
        exact (set_iso X c).
      * use nat_in_c.
    + exact nat_in_X.
Defined.

Lemma make_PreShv_functor_z_iso (F G : functor (PreShv C) (PreShv C))
      (set_iso : ∏ X c, z_iso (pr1 (F X) c) (pr1 (G X) c))
      (nat_in_c : ∏ X, is_nat_trans _ _ (λ c, set_iso X c))
      (nat_in_X : is_nat_trans F G (λ X, make_nat_trans _ _ _ (nat_in_c X))) :
      @z_iso [PreShv C, PreShv C] F G.
Proof.
  exists (make_PreShv_functor_z_iso_helper F G set_iso nat_in_c nat_in_X).
  use make_is_z_isomorphism.
  + use make_PreShv_functor_z_iso_helper.
      * intros X c.
        exact (z_iso_inv_from_z_iso (set_iso X c)).
      * abstract (intros X c y f;
                  apply pathsinv0, z_iso_inv_on_left; rewrite <- assoc;
                  now apply pathsinv0, z_iso_inv_on_right, (nat_in_c X)).
      * abstract (intros X Y α;
                  apply nat_trans_eq; [ apply homset_property|];
                  intro x; simpl;
                  apply pathsinv0, (z_iso_inv_on_left _ _ _ _ (set_iso Y x));
                  rewrite <- assoc; apply pathsinv0, (z_iso_inv_on_right (C:=HSET));
                  exact (eqtohomot (maponpaths pr1 (nat_in_X X Y α)) x)).
    + abstract (use make_is_inverse_in_precat;
                [ apply nat_trans_eq; [ apply homset_property |]; intro X;
                  apply nat_trans_eq; [ apply homset_property |]; intro x;
                  exact (z_iso_inv_after_z_iso (set_iso X x))
                | apply nat_trans_eq; [ apply homset_property |]; intro X;
                  apply nat_trans_eq; [ apply homset_property |]; intro x;
                  apply funextsec; intros y;
                  exact (eqtohomot (z_iso_after_z_iso_inv (set_iso X x)) y) ]).
Defined.

End iso_presheaf.
