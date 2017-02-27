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
- Definition of the subobject classifier (without proof) ([Ω_PreShv], [Ω_mor])


Written by: Anders Mörtberg, 2017

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

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

Local Open Scope cat.

Notation "'PreShv' C" := [C^op,HSET,has_homsets_HSET] (at level 3) : cat.

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

End Ω_PreShv.
