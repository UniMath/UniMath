(** This file defines two category structures on well-ordered sets:

1. This first where the morphisms are maps that preserve the ordering and initial segments
([wosetfuncat]).

2. The second with arbitrary set theoretic functions as morphisms ([WOSET]).

Both of these have initial ([Initial_wosetfuncat], [Initial_WOSET]) and terminal objects
([Terminal_wosetfuncat], [Terminal_WOSET]). The former doesn't seem to have binary products (see
discussion below), but using Zermelo's well-ordering theorem (and hence the axiom of choice) I have
proved that the latter merely has binary products ([hasBinProducts_WOSET]). I believe that the
proofs that WOSET has all limits and colimits carry over exactly like the proof for binary products,
but because the category only merely has binary products I ran into all kinds of problems when
trying to prove that it merely has exponentials, see discussion at the end of the file.

Written by: Anders Mörtberg (Feb 2018)

*)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.OrderedSets.
Require Import UniMath.Combinatorics.WellOrderedSets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.exponentials.

Local Open Scope cat.
Local Open Scope woset.
Local Open Scope functions.

(** * The category of well-ordered sets with order preserving morphisms *)
Section wosetfuncat.

Definition wosetfun_precategory : precategory.
Proof.
use mk_precategory.
- exists (WellOrderedSet,,wofun).
  split; simpl.
  + intros X.
    apply (_,,iswofun_idfun).
  + intros X Y Z f g.
    apply (_,,iswofun_funcomp f g).
- abstract (now repeat split; simpl; intros; apply wofun_eq).
Defined.

Lemma has_homsets_wosetfun_precategory : has_homsets wosetfun_precategory.
Proof.
intros X Y.
apply (isasetsubset (pr1wofun X Y)).
- apply isaset_set_fun_space.
- apply isinclpr1; intro f.
  apply isaprop_iswofun.
Qed.

Definition wosetfuncat : category :=
  (wosetfun_precategory,,has_homsets_wosetfun_precategory).

(** TODO: remove this assumption by proving it *)
Definition wo_setcategory (isaset_WellOrderedSet : isaset WellOrderedSet) :
  setcategory.
Proof.
exists wosetfun_precategory.
split.
- apply isaset_WellOrderedSet.
- apply has_homsets_wosetfun_precategory.
Defined.

Lemma Initial_wosetfuncat : Initial wosetfuncat.
Proof.
use mk_Initial.
- exact empty_woset.
- apply mk_isInitial; intro a; simpl.
  use tpair.
  + exists fromempty.
    abstract (now split; intros []).
  + abstract (now intros f; apply wofun_eq, funextfun; intros []).
Defined.

Lemma Terminal_wosetfuncat : Terminal wosetfuncat.
Proof.
use mk_Terminal.
+ exact unit_woset.
+ apply mk_isTerminal; intro a.
  use tpair.
  - exists (λ _, tt).
    abstract (split; [intros x y H|intros x [] []]; apply (WO_isrefl unit_woset)).
  - abstract (now intros f; apply wofun_eq, funextfun; intros x; induction (pr1 f x)).
Defined.

(** Can we prove any further properties of wosetcat? It doesn't seem like it has binary products, at
least the lexicographic ordering does not work. Consider {0,1} × {2,3}, in it we have (0,3) < (1,2)
but pr2 doesn't preserve the ordering. (Thanks Dan for pointing this out to me!) *)

End wosetfuncat.

(** * The category of well-ordered sets with arbitrary functions as morphisms *)
Section WOSET.

(** TODO: prove the following missing result *)
Variable isaset_WellOrderedSet : isaset WellOrderedSet.

Definition WOSET_precategory : precategory.
Proof.
use mk_precategory.
- use tpair.
  + exists ((WellOrderedSet,,isaset_WellOrderedSet) : hSet).
    apply (λ X Y, pr11 X → pr11 Y).
  + split; simpl.
    * intros X; apply idfun.
    * intros X Y Z f g; apply (g ∘ f).
- abstract (now intros).
Defined.

Lemma has_homsets_WOSET : has_homsets WOSET_precategory.
Proof.
now intros X Y; apply hset_fun_space.
Qed.

Definition WOSET : category := (WOSET_precategory,,has_homsets_WOSET).

Definition WOSET_setcategory : setcategory.
Proof.
exists WOSET.
split.
- apply setproperty.
- apply has_homsets_WOSET.
Defined.

Lemma Initial_WOSET : Initial WOSET.
Proof.
use mk_Initial.
- exact empty_woset.
- apply mk_isInitial; intro a.
  use tpair.
  + simpl; intro e; induction e.
  + abstract (intro f; apply funextfun; intro e; induction e).
Defined.

Lemma Terminal_WOSET : Terminal WOSET.
Proof.
use mk_Terminal.
- exact unit_woset.
- apply mk_isTerminal; intro a.
  exists (λ _, tt).
  abstract (simpl; intro f; apply funextfun; intro x; case (f x); apply idpath).
Defined.

(** Direct proof that woset has binary products using Zermelo's well-ordering theorem. We could
prove this using the lexicograpic ordering, but it seems like we need decidable equality for this to
work which would not work very well when we construct exponentials. *)
Lemma hasBinProducts_WOSET (AC : AxiomOfChoice) : hasBinProducts WOSET.
Proof.
intros A B.
set (AB := BinProductObject _ (BinProductsHSET (pr1 A) (pr1 B)) : hSet).
apply (squash_to_hProp (@ZermeloWellOrdering AB AC)); intros R.
apply hinhpr.
use mk_BinProduct.
- exists AB.
  exact R.
- apply (BinProductPr1 _ (BinProductsHSET _ _)).
- apply (BinProductPr2 _ (BinProductsHSET _ _)).
- intros H.
  apply (isBinProduct_BinProduct _ (BinProductsHSET _ _) (pr1 H)).
Defined.

(** Using the axiom of choice we can push the quantifiers into the truncation. Hopefully this will
help with using this definition below for defining exponentials. However it might run into problems
with AC not computing. *)
Definition squash_BinProducts_WOSET (AC : AxiomOfChoice) : ∥ BinProducts WOSET ∥.
Proof.
use AC; intros A; use AC; intros B.
apply (hasBinProducts_WOSET AC).
Defined.

(** Below follows an attempt to prove that this category has exponentials *)

(* I first define a weaker formulation of when a category has exponentials. This only requires the
binary products to merely exists. We could reformulate this condition in various ways, for instance
by defining when the product with an element a : C merely exists or unfolding the definitions to
state the property explicitly. I'm not sure which is the best. *)
(* Definition hasExponentials (C : precategory) : UU := *)
(*   ∏ (a : C), ∃ (H : BinProducts C), is_exponentiable H a. *)

(* I have run into some serious problems when trying to define the functor X ↦ X^A *)
(* Definition exponential_functor_WOSET (AC : AxiomOfChoice) (A : WOSET) : ∥ functor WOSET WOSET ∥. *)
(* Proof. *)
(* The idea is to well-order the function space using Zermelo's well-ordering theorem, but I can't
figure out how to write down the definition. It essentially boils down to some truncation juggling
and various issues with AC not computing and hence getting in the way. *)

(* Once I have figured out how to write the above definition I should be able to prove *)
(* Lemma hasExponentials_WOSET (AC : AxiomOfChoice) : hasExponentials WOSET. *)
(* Admitted. *)

End WOSET.