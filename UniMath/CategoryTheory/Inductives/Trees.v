(**

Definition of binary trees ([Tree]) implemented similarily to lists as the initial algebra of the
tree functor.

Written by: Anders Mörtberg (2016)

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.Inductives.Lists.

Local Open Scope cat.

(** * Binary trees *)
Section bintrees.

Variable A : HSET.

Local Open Scope cocont_functor_hset_scope.

(** The tree functor: F(X) = 1 + A * X * X *)
Definition treeOmegaFunctor : omega_cocont_functor HSET HSET := '1 + 'A * (Id * Id).

Let treeFunctor : functor HSET HSET := pr1 treeOmegaFunctor.
Let is_omega_cocont_treeFunctor : is_omega_cocont treeFunctor := pr2 treeOmegaFunctor.

Lemma treeFunctor_Initial :
  Initial (precategory_FunctorAlg treeFunctor has_homsets_HSET).
Proof.
apply (colimAlgInitial _ InitialHSET is_omega_cocont_treeFunctor (ColimCoconeHSET _ _)).
Defined.

(** The type of binary trees *)
Definition Tree : HSET :=
  alg_carrier _ (InitialObject treeFunctor_Initial).

Let Tree_mor : HSET⟦treeFunctor Tree,Tree⟧ :=
  alg_map _ (InitialObject treeFunctor_Initial).

Let Tree_alg : algebra_ob treeFunctor :=
  InitialObject treeFunctor_Initial.

Definition leaf_map : HSET⟦unitHSET,Tree⟧.
Proof.
simpl; intro x.
simple refine (Tree_mor _).
apply inl, x.
Defined.

Definition leaf : pr1 Tree := leaf_map tt.

Definition node_map : HSET⟦(A × (Tree × Tree))%set,Tree⟧.
Proof.
intros xs.
simple refine (Tree_mor _).
exact (inr xs).
Defined.

Definition node : pr1 A × (pr1 Tree × pr1 Tree) -> pr1 Tree := node_map.

(** Get recursion/iteration scheme:
<<
     x : X           f : A × X × X -> X
  ------------------------------------
        foldr x f : Tree A -> X
>>
*)
Definition mk_treeAlgebra (X : HSET) (x : pr1 X)
  (f : HSET⟦(A × X × X)%set,X⟧) : algebra_ob treeFunctor.
Proof.
set (x' := λ (_ : unit), x).
apply (tpair _ X (sumofmaps x' f) : algebra_ob treeFunctor).
Defined.

Definition foldr_map (X : HSET) (x : pr1 X) (f : HSET⟦(A × X × X)%set,X⟧) :
  algebra_mor _ Tree_alg (mk_treeAlgebra X x f).
Proof.
apply (InitialArrow treeFunctor_Initial (mk_treeAlgebra X x f)).
Defined.

Definition foldr (X : HSET) (x : pr1 X)
  (f : pr1 A × pr1 X × pr1 X -> pr1 X) : pr1 Tree -> pr1 X.
Proof.
apply (foldr_map _ x f).
Defined.

(* Maybe quantify over "λ _ : unit, x" instead of nil? *)
Lemma foldr_leaf (X : hSet) (x : X) (f : pr1 A × X × X -> X) : foldr X x f leaf = x.
Proof.
assert (F := maponpaths (fun x => BinCoproductIn1 _ (BinCoproductsHSET _ _) · x)
                        (algebra_mor_commutes _ _ _ (foldr_map X x f))).
apply (toforallpaths _ _ _ F tt).
Qed.

Lemma foldr_node (X : hSet) (x : X) (f : pr1 A × X × X -> X)
                 (a : pr1 A) (l1 l2 : pr1 Tree) :
  foldr X x f (node (a,,l1,,l2)) = f (a,,foldr X x f l1,,foldr X x f l2).
Proof.
assert (F := maponpaths (fun x => BinCoproductIn2 _ (BinCoproductsHSET _ _)· x)
                        (algebra_mor_commutes _ _ _ (foldr_map X x f))).
assert (Fal := toforallpaths _ _ _ F (a,,l1,,l2)).
clear F.
(* apply Fal. *) (* This doesn't work here. why? *)
unfold compose in Fal.
simpl in Fal.
apply Fal.
Opaque foldr_map.
Qed. (* This Qed is slow unless foldr_map is Opaque *)
Transparent foldr_map.

(** This defines the induction principle for trees using foldr *)
Section tree_induction.

Variables (P : pr1 Tree -> UU) (PhSet : ∏ l, isaset (P l)).
Variables (P0 : P leaf)
          (Pc : ∏ (a : pr1 A) (l1 l2 : pr1 Tree), P l1 -> P l2 -> P (node (a,,l1,,l2))).

Let P' : UU := ∑ l, P l.
Let P0' : P' := (leaf,, P0).
Let Pc' : pr1 A × P' × P' -> P'.
Proof.
intros ap.
apply (tpair _ (node (pr1 ap,,pr1 (pr1 (pr2 ap)),,pr1 (pr2 (pr2 ap))))).
apply (Pc _ _ _ (pr2 (pr1 (pr2 ap))) (pr2 (pr2 (pr2 ap)))).
  (* λ ap : pr1 A × P' × P', node (pr1 ap,, pr1 (pr2 ap)),,Pc (pr1 ap) (pr1 (pr2 ap)) (pr2 (pr2 ap)). *)
Defined.

Definition P'HSET : HSET.
Proof.
apply (tpair _ P').
abstract (apply (isofhleveltotal2 2); [ apply setproperty | intro x; apply PhSet ]).
Defined.

(* This line is crucial for isalghom_pr1foldr to typecheck *)
Opaque is_omega_cocont_treeFunctor.

Lemma isalghom_pr1foldr :
  is_algebra_mor _ Tree_alg Tree_alg (fun l => pr1 (foldr P'HSET P0' Pc' l)).
Proof.
apply BinCoproductArrow_eq_cor.
- apply funextfun; intro x; destruct x.
  apply (maponpaths pr1 (foldr_leaf P'HSET P0' Pc')).
- apply funextfun; intro x; destruct x as [a [l1 l2]].
  apply (maponpaths pr1 (foldr_node P'HSET P0' Pc' a l1 l2)).
Qed.

Transparent is_omega_cocont_treeFunctor.

Definition pr1foldr_algmor : algebra_mor _ Tree_alg Tree_alg :=
  tpair _ _ isalghom_pr1foldr.

Lemma pr1foldr_algmor_identity : identity _ = pr1foldr_algmor.
Proof.
now rewrite <- (InitialEndo_is_identity _ treeFunctor_Initial pr1foldr_algmor).
Qed.

Lemma treeInd l : P l.
Proof.
assert (H : pr1 (foldr P'HSET P0' Pc' l) = l).
  apply (toforallpaths _ _ _ (!pr1foldr_algmor_identity) l).
rewrite <- H.
apply (pr2 (foldr P'HSET P0' Pc' l)).
Defined.

End tree_induction.

Lemma treeIndProp (P : pr1 Tree -> UU) (HP : ∏ l, isaprop (P l)) :
  P leaf -> (∏ a l1 l2, P l1 → P l2 → P (node (a,,l1,,l2))) -> ∏ l, P l.
Proof.
intros Pnil Pcons.
apply treeInd; try assumption.
intro l; apply isasetaprop, HP.
Defined.

End bintrees.

(** Some tests *)
Section nat_examples.

Local Open Scope nat_scope.

Definition size : pr1 (Tree natHSET) -> nat :=
  foldr natHSET natHSET 0 (fun x => S (pr1 (pr2 x) + pr2 (pr2 x))).

Lemma size_node a l1 l2 : size (node natHSET (a,,l1,,l2)) = 1 + size l1 + size l2.
Proof.
unfold size.
now rewrite foldr_node.
Qed.

Definition map (f : nat -> nat) (l : pr1 (Tree natHSET)) : pr1 (Tree natHSET) :=
  foldr natHSET (Tree natHSET) (leaf natHSET)
      (λ a, node natHSET (f (pr1 a),, pr1 (pr2 a),, pr2 (pr2 a))) l.

Lemma size_map (f : nat -> nat) : ∏ l, size (map f l) = size l.
Proof.
apply treeIndProp.
- intros l. apply isasetnat.
- now unfold map; rewrite foldr_leaf.
- intros a l1 l2 ih1 ih2; unfold map.
  now rewrite foldr_node, !size_node, <- ih1, <- ih2.
Qed.

Definition sum : pr1 (Tree natHSET) -> nat :=
  foldr natHSET natHSET 0 (fun x => pr1 x + pr1 (pr2 x) + pr2 (pr2 x)).

Definition testtree : pr1 (Tree natHSET).
Proof.
  use node_map; repeat split.
  - apply 5.
  - use node_map; repeat split.
    + apply 6.
    + exact (leaf_map _ tt).
    + exact (leaf_map _ tt).
  - exact (leaf_map _ tt).
Defined.


End nat_examples.

(** ** Flattening of a tree into a list *)
Local Notation "a :: b" := (cons _ a b).
(* Check concatenate. *)
Definition flatten (A : HSET) : pr1 (Tree A) -> List A.
Proof.
  intro t.
  use (foldr A).
  - apply nil.
  - intro all'.
    set (a := pr1 all').
    set (l := pr1 (pr2 all')).
    set (l' := pr2 (pr2 all')). cbn beta in l'.
    exact (concatenate _ l (concatenate _ (a :: nil _ ) l')).
  - exact t.
Defined.

Eval lazy in Lists.sum (flatten _ testtree).
Eval lazy in sum testtree.
