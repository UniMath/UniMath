(** **********************************************************

Theory about set-valued presheafs. We write Psh C for [C^op,HSET].

Contents:

- Limits ([Lims_Psh], [Lims_Psh_of_shape])
- Colimits ([Colims_Psh], [Colims_Psh_of_shape])
- Binary products ([BinProducts_Psh])
- Indexed products ([Products_Psh])
- Binary coproducts ([BinCoproducts_Psh])
- Indexed coproducts ([Coproducts_Psh])
- Initial object ([Initial_Psh])
- Terminal object ([Terminal_Psh])
- Pullbacks ([Pullbacks_Psh])
- Exponentials ([has_exponentials_Psh])
- Definition of the subobject classifier (without proof) ([Ω_Psh])


Written by: Anders Mörtberg, 2017

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
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

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "'Psh' C" := [C^op,HSET,has_homsets_HSET] (at level 3).
Arguments nat_trans_comp {_ _ _ _ _} _ _.

(** Various limits and colimits in Psh C *)
Section limits.

Context {C : precategory}.

Lemma Lims_Psh : Lims (Psh C).
Proof.
now apply LimsFunctorCategory, LimsHSET.
Defined.

Lemma Lims_Psh_of_shape (g : graph) : Lims_of_shape g (Psh C).
Proof.
now apply LimsFunctorCategory_of_shape, LimsHSET_of_shape.
Defined.

Lemma Colims_Psh : Colims (Psh C).
Proof.
now apply ColimsFunctorCategory, ColimsHSET.
Defined.

Lemma Colims_Psh_of_shape (g : graph) : Colims_of_shape g (Psh C).
Proof.
now apply ColimsFunctorCategory_of_shape, ColimsHSET_of_shape.
Defined.

Lemma BinProducts_Psh : BinProducts (Psh C).
Proof.
now apply BinProducts_functor_precat, BinProductsHSET.
Defined.

Lemma Products_Psh I : Products I (Psh C).
Proof.
now apply Products_functor_precat, ProductsHSET.
Defined.

Lemma BinCoproducts_Psh : BinCoproducts (Psh C).
Proof.
now apply BinCoproducts_functor_precat, BinCoproductsHSET.
Defined.

Lemma Coproducts_Psh I (HI : isaset I) : Coproducts I (Psh C).
Proof.
now apply Coproducts_functor_precat, CoproductsHSET, HI.
Defined.

Lemma Initial_Psh : Initial (Psh C).
Proof.
now apply Initial_functor_precat, InitialHSET.
Defined.

Lemma Terminal_Psh : Terminal (Psh C).
Proof.
now apply Terminal_functor_precat, TerminalHSET.
Defined.

Lemma Pullbacks_Psh : Pullbacks (Psh C).
Proof.
now apply FunctorPrecategoryPullbacks, PullbacksHSET.
Defined.

Lemma has_exponentials_Psh (hsC : has_homsets C) :
  has_exponentials BinProducts_Psh.
Proof.
now apply has_exponentials_functor_HSET, has_homsets_opp, hsC.
Defined.

End limits.

(** Definition of the subobject classifier in a presheaf
    TODO: Prove that Ω actually is the subobject classifier  *)
Section Ω_Psh.

Context {C : precategory}.

Definition sieve_def (c : C) : UU.
Proof.
use total2.
- apply (∏ (x : C) (f : C⟦x,c⟧), hProp).
- intros S.
  apply (∏ (x : C) (f : C⟦x,c⟧), S x f → ∏ (y : C) (f' : C⟦y,x⟧), S y (f' ;; f)).
Defined.

Lemma isaset_sieve (c : C) : isaset (sieve_def c).
Proof.
use isaset_total2.
- repeat (apply impred_isaset; intro); apply isasethProp.
- intros S; simpl; repeat (apply impred_isaset; intro); apply isasetaprop, propproperty.
Qed.

Definition sieve (c : C) : hSet := (sieve_def c,,isaset_sieve c).

Definition sieve_mor a b (f : C⟦b,a⟧) : sieve a → sieve b.
Proof.
intros S.
mkpair.
- intros y g.
  apply (pr1 S y (g ;; f)).
- abstract (intros y g H z h; simpl; rewrite <- assoc; apply (pr2 S), H).
Defined.

Local Definition Ω_Psh_data : functor_data C^op HSET := (sieve,,sieve_mor).

Local Lemma is_functor_Ω_Psh_data : is_functor Ω_Psh_data.
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

Definition Ω_Psh : Psh C := (Ω_Psh_data,,is_functor_Ω_Psh_data).

End Ω_Psh.
