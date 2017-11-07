(**

This file contains formalizations of lists. First over sets as the initial algebra of the list
functor ([List]) and then more generally over any type defined as iterated products ([list]).

Written by: Anders Mörtberg, 2016

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.Combinatorics.Lists.

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
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.

Local Open Scope cat.

(** * Lists as the colimit of a chain given by the list functor: F(X) = 1 + A * X *)
Section lists.

Variable A : HSET.

Local Open Scope cocont_functor_hset_scope.

(** F(X) = 1 + (A * X) *)
Definition L_A : omega_cocont_functor HSET HSET := '1 + 'A * Id.

Let listFunctor : functor HSET HSET := pr1 L_A.

Let is_omega_cocont_listFunctor : is_omega_cocont listFunctor := pr2 L_A.

Lemma listFunctor_Initial :
  Initial (precategory_FunctorAlg listFunctor has_homsets_HSET).
Proof.
apply (colimAlgInitial _ InitialHSET is_omega_cocont_listFunctor (ColimCoconeHSET _ _)).
Defined.

(** The type of lists of A's *)
Definition μL_A : HSET :=
  alg_carrier _ (InitialObject listFunctor_Initial).

Definition List : UU := pr1 μL_A.

Let List_mor : HSET⟦listFunctor μL_A,μL_A⟧ :=
  alg_map _ (InitialObject listFunctor_Initial).

Let List_alg : algebra_ob listFunctor :=
  InitialObject listFunctor_Initial.

Definition nil_map : HSET⟦unitHSET,μL_A⟧ :=
  BinCoproductIn1 _ (BinCoproductsHSET _ _) · List_mor.

Definition nil : List := nil_map tt.

Definition cons_map : HSET⟦(A × μL_A)%set,μL_A⟧ :=
  BinCoproductIn2 _ (BinCoproductsHSET _ _) · List_mor.

Definition cons : pr1 A → List -> List := λ a l, cons_map (a,,l).

(** Get recursion/iteration scheme:
<<
     x : X           f : A × X -> X
  ------------------------------------
       foldr x f : List A -> X
>>
*)
Definition mk_listAlgebra (X : HSET) (x : pr1 X)
  (f : HSET⟦(A × X)%set,X⟧) : algebra_ob listFunctor.
Proof.
set (x' := λ (_ : unit), x).
apply (tpair _ X (sumofmaps x' f) : algebra_ob listFunctor).
Defined.

Definition foldr_map (X : HSET) (x : pr1 X) (f : HSET⟦(A × X)%set,X⟧) :
  algebra_mor _ List_alg (mk_listAlgebra X x f).
Proof.
apply (InitialArrow listFunctor_Initial (mk_listAlgebra X x f)).
Defined.

(** Iteration/fold *)
Definition foldr (X : HSET) (x : pr1 X)
  (f : pr1 A → pr1 X → pr1 X) : List → pr1 X.
Proof.
apply (foldr_map _ x (λ a, f (pr1 a) (pr2 a))).
Defined.

(* Maybe quantify over "λ _ : unit, x" instead of nil? *)
Lemma foldr_nil (X : hSet) (x : X) (f : pr1 A → X -> X) : foldr X x f nil = x.
Proof.
assert (F := maponpaths (λ x, BinCoproductIn1 _ (BinCoproductsHSET _ _) · x)
                        (algebra_mor_commutes _ _ _ (foldr_map X x (λ a, f (pr1 a) (pr2 a))))).
apply (toforallpaths _ _ _ F tt).
Qed.

Lemma foldr_cons (X : hSet) (x : X) (f : pr1 A → X -> X)
                 (a : pr1 A) (l : List) :
  foldr X x f (cons a l) = f a (foldr X x f l).
Proof.
assert (F := maponpaths (λ x, BinCoproductIn2 _ (BinCoproductsHSET _ _) · x)
                        (algebra_mor_commutes _ _ _ (foldr_map X x (λ a, f (pr1 a) (pr2 a))))).
assert (Fal := toforallpaths _ _ _ F (a,,l)).
clear F.
unfold compose in Fal.
simpl in Fal.
apply Fal.
Opaque foldr_map.
Qed. (* This Qed is slow unless foldr_map is Opaque *)
Transparent foldr_map.

(** The induction principle for lists defined using foldr *)
Section list_induction.

Variables (P : List -> UU) (PhSet : ∏ l, isaset (P l)).
Variables (P0 : P nil)
          (Pc : ∏ a l, P l -> P (cons a l)).

Let P' : UU := ∑ l, P l.
Let P0' : P' := (nil,, P0).
Let Pc' : pr1 A  → P' -> P' :=
  λ (a : pr1 A) (p : P'), cons a (pr1 p),,Pc a (pr1 p) (pr2 p).

Definition P'HSET : HSET.
Proof.
apply (tpair _ P').
abstract (apply (isofhleveltotal2 2); [ apply setproperty | intro x; apply PhSet ]).
Defined.

(** This line is crucial for isalghom_pr1foldr to typecheck *)
Opaque is_omega_cocont_listFunctor.

Lemma isalghom_pr1foldr :
  is_algebra_mor _ List_alg List_alg (λ l, pr1 (foldr P'HSET P0' Pc' l)).
Proof.
apply (BinCoproductArrow_eq_cor _ BinCoproductsHSET).
- apply funextfun; intro x; induction x.
  apply (maponpaths pr1 (foldr_nil P'HSET P0' Pc')).
- apply funextfun; intro x; destruct x as [a l].
  apply (maponpaths pr1 (foldr_cons P'HSET P0' Pc' a l)).
Qed.

Transparent is_omega_cocont_listFunctor.

Definition pr1foldr_algmor : algebra_mor _ List_alg List_alg :=
  tpair _ _ isalghom_pr1foldr.

Lemma pr1foldr_algmor_identity : identity _ = pr1foldr_algmor.
Proof.
now rewrite <- (InitialEndo_is_identity _ listFunctor_Initial pr1foldr_algmor).
Qed.

(** The induction principle for lists *)
Lemma listInd l : P l.
Proof.
assert (H : pr1 (foldr P'HSET P0' Pc' l) = l).
  apply (toforallpaths _ _ _ (!pr1foldr_algmor_identity) l).
rewrite <- H.
apply (pr2 (foldr P'HSET P0' Pc' l)).
Defined.

End list_induction.

Lemma listIndhProp (P : List → hProp) :
  P nil → (∏ a l, P l → P (cons a l)) → ∏ l, P l.
Proof.
intros Pnil Pcons.
apply listInd; try assumption.
intro l; apply isasetaprop, propproperty.
Defined.

(* This variation is easier to use *)
Lemma listIndProp (P : List → UU) (HP : ∏ l, isaprop (P l)) :
  P nil → (∏ a l, P l → P (cons a l)) → ∏ l, P l.
Proof.
intros Pnil Pcons.
apply listInd; try assumption.
intro l; apply isasetaprop, HP.
Defined.

Local Open Scope nat_scope.

Local Notation "'A'" := (pr1 A).

Definition length : List -> nat := foldr natHSET 0 (λ _ (n : nat), 1 + n).

Definition map (f : A -> A) : List -> List :=
  foldr _ nil (λ (x : A) (xs : List), cons (f x) xs).

Lemma length_map (f : A -> A) : ∏ xs, length (map f xs) = length xs.
Proof.
apply listIndProp.
- intros l; apply isasetnat.
- now unfold map; rewrite foldr_nil.
- simpl; unfold map, length; simpl; intros a l Hl.
  now rewrite !foldr_cons, <- Hl.
Qed.

Definition concatenate : List -> List -> List :=
  λ l l', foldr _ l cons l'.

End lists.

(** Some examples of computations with lists over nat *)
Section nat_examples.

Definition cons_nat a l : List natHSET := cons natHSET a l.

Local Infix "::" := cons_nat.
Local Notation "[]" := (nil natHSET) (at level 0, format "[]").

Definition testlist : List natHSET := 5 :: 2 :: [].

Definition testlistS : List natHSET :=
  map natHSET S testlist.

Definition sum : List natHSET -> nat :=
  foldr natHSET natHSET 0 (λ x y, x + y).

(* None of these compute *)
(* Eval cbn in length _ (nil natHSET). *)
(* Eval vm_compute in length _ testlist. *)
(* Eval vm_compute in length _ testlistS. *)
(* Eval vm_compute in sum testlist. *)
(* Eval vm_compute in sum testlistS. *)

(* All of these compute *)
Eval lazy in length _ (nil natHSET).
Eval lazy in length _ testlist.
Eval lazy in length _ testlistS.
Eval lazy in sum testlist.
Eval lazy in sum testlistS.
Eval lazy in length _ (concatenate _ testlist testlistS).
Eval lazy in sum (concatenate _ testlist testlistS).

Goal (∏ l, length _ (2 :: l) = S (length _ l)).
simpl.
intro l.
try apply idpath. (* this doesn't work *)
unfold length, cons_nat.
rewrite foldr_cons. cbn.
apply idpath.
Abort.

(* some experiments: *)

(* Definition const {A B : UU} : A -> B -> A := λ x _, x. *)

(* Eval compute in const 0 (nil natHSET). *)

(* Axiom const' : ∏ {A B : UU}, A -> B -> A. *)

(* Eval compute in const' 0 1. *)
(* Eval compute in const' 0 (nil natHSET). *)

(* Time Eval vm_compute in nil natHSET.  (* This crashes my computer by using up all memory *) *)

End nat_examples.

(** * Equivalence with lists as iterated products *)
Section list.

Lemma isaset_list (A : HSET) : isaset (list (pr1 A)).
Proof.
apply isaset_total2; [apply isasetnat|].
intro n; induction n as [|n IHn]; simpl; [apply isasetunit|].
apply isaset_dirprod; [ apply setproperty | apply IHn ].
Qed.

Definition to_List (A : HSET) : list (pr1 A) -> List A.
Proof.
intros l.
destruct l as [n l].
induction n as [|n IHn].
+ exact (nil A).
+ apply (cons _ (pr1 l) (IHn (pr2 l))).
Defined.

Definition to_list (A : HSET) : List A -> list (pr1 A).
Proof.
apply (foldr A (list (pr1 A),,isaset_list A)).
* apply (0,,tt).
* intros a L; simpl in *.
  apply (tpair _ (S (pr1 L)) (a,,pr2 L)).
Defined.

Lemma to_listK (A : HSET) : ∏ x : list (pr1 A), to_list A (to_List A x) = x.
Proof.
intro l; destruct l as [n l]; unfold to_list, to_List.
induction n as [|n IHn]; simpl.
- rewrite foldr_nil.
  now destruct l.
- rewrite foldr_cons; simpl.
  now rewrite IHn.
Qed.

Lemma to_ListK (A : HSET) : ∏ y : List A, to_List A (to_list A y) = y.
Proof.
apply listIndProp.
* intro l; apply setproperty.
* now unfold to_list; rewrite foldr_nil.
* unfold to_list, to_List; intros a l IH.
  rewrite foldr_cons; simpl.
  apply maponpaths, pathsinv0.
  eapply pathscomp0; [eapply pathsinv0, IH|]; simpl.
  now destruct foldr.
Qed.

(** Equivalence between list and List for A a set *)
Lemma weq_list (A : HSET) : list (pr1 A) ≃ List A.
Proof.
use tpair.
- apply to_List.
- use gradth.
  + apply to_list.
  + apply to_listK.
  + apply to_ListK.
Defined.

(* This doesn't compute: *)
(* Eval compute in (to_list _ testlist). *)

(* This does compute: *)
Eval lazy in (to_list _ testlist).


End list.

(** Alternative version of lists using a more direct proof of omega-cocontinuity. This definition
    has slightly better computational properties. *)
Module AltList.

(* The functor "x * F" is omega_cocont. This is only proved for set at the
   moment as it needs that the category is cartesian closed *)
Section constprod_functor.

Variables (x : HSET).

Definition constprod_functor : functor HSET HSET :=
  BinProduct_of_functors HSET HSET BinProductsHSET (constant_functor HSET HSET x)
                                         (functor_identity HSET).

Definition flip {A B C : UU} (f : A -> B -> C) : B -> A -> C := λ x y, f y x.

Lemma omega_cocontConstProdFunctor : is_omega_cocont constprod_functor.
Proof.
intros hF c L ccL HcL cc.
simple refine (tpair _ _ _).
- transparent assert (HX : (cocone hF (hset_fun_space x HcL))).
  { simple refine (mk_cocone _ _).
    * simpl; intro n; apply flip, curry, (pr1 cc).
    * abstract (destruct cc as [f hf]; simpl; intros m n e;
                rewrite <- (hf m n e); destruct e; simpl;
                repeat (apply funextfun; intro); apply idpath).
  }
  simple refine (tpair _ _ _).
  + simpl; apply uncurry, flip.
    apply (colimArrow (mk_ColimCocone _ _ _ ccL) (hset_fun_space x HcL)).
    apply HX.
  + cbn.
    destruct cc as [f hf]; simpl; intro n.
    apply funextfun; intro p.
    change p with (pr1 p,,pr2 p).
    assert (XR := colimArrowCommutes (mk_ColimCocone hF c L ccL) _ HX n).
    unfold flip, curry, colimIn in *; simpl in *.
    now rewrite <- (toforallpaths _ _ _ (toforallpaths _ _ _ XR (pr2 p)) (pr1 p)).
- abstract (
  intro p; unfold uncurry; simpl; apply subtypeEquality; simpl;
  [ intro g; apply impred; intro t;
    simple refine (let ff : HSET ⟦(x × dob hF t)%set,HcL⟧ := _ in _);
    [ simpl; apply (pr1 cc)
    | apply (@has_homsets_HSET _ HcL _ ff) ]
  | destruct p as [t p]; simpl;
    apply funextfun; intro xc; destruct xc as [x' c']; simpl;
    simple refine (let g : HSET⟦colim (mk_ColimCocone hF c L ccL),
                                hset_fun_space x HcL⟧ := _ in _);
    [ simpl; apply flip, curry, t
    | rewrite <- (colimArrowUnique _ _ _ g); [apply idpath | ];
      destruct cc as [f hf]; simpl in *;
      now intro n; simpl; rewrite <- (p n) ]
  ]).
Defined.

End constprod_functor.

(* The functor "x + F" is omega_cocont.
   Assumes that the category has coproducts *)
Section constcoprod_functor.

Variables (C : precategory) (hsC : has_homsets C) (x : C) (PC : BinCoproducts C).

Definition constcoprod_functor : functor C C :=
  BinCoproduct_of_functors C C PC (constant_functor C C x) (functor_identity C).

Lemma omega_cocontConstCoprodFunctor : is_omega_cocont constcoprod_functor.
Proof.
intros hF c L ccL HcL cc.
simple refine (tpair _ _ _).
- simple refine (tpair _ _ _).
  + eapply BinCoproductArrow.
    * exact (BinCoproductIn1 _ (PC x (dob hF 0)) · pr1 cc 0).
    * simple refine (let ccHcL : cocone hF HcL := _ in _).
      { simple refine (mk_cocone _ _).
        - intros n; exact (BinCoproductIn2 _ (PC x (dob hF n)) · pr1 cc n).
        - abstract (
            intros m n e; destruct e; simpl;
            destruct cc as [f hf]; simpl in *; unfold BinCoproduct_of_functors_ob in *;
            rewrite <- (hf m _ (idpath _)), !assoc; apply cancel_postcomposition;
            now unfold BinCoproduct_of_functors_mor; rewrite BinCoproductOfArrowsIn2). }
      apply (pr1 (pr1 (ccL HcL ccHcL))).
  + abstract (
    destruct cc as [f hf]; simpl in *; unfold BinCoproduct_of_functors_ob in *;
    simpl; intro n; unfold BinCoproduct_of_functors_mor in *;
    rewrite precompWithBinCoproductArrow; apply pathsinv0, BinCoproductArrowUnique;
    [ rewrite id_left; induction n as [|n IHn]; [apply idpath|];
      now rewrite <- IHn, <- (hf n _ (idpath _)), assoc,
                  BinCoproductOfArrowsIn1, id_left
    | rewrite <- (hf n _ (idpath _)); destruct ccL as [t p]; destruct t as [t p0]; simpl in *;
      rewrite p0; apply maponpaths, hf]).
- abstract (
  destruct cc as [f hf]; simpl in *; unfold BinCoproduct_of_functors_ob in *;
  intro t; apply subtypeEquality; simpl;
  [ intro g; apply impred; intro; apply hsC
  | destruct t as [t p]; destruct ccL as [t0 p0]; unfold BinCoproduct_of_functors_mor in *; destruct t0 as [t0 p1]; simpl;
    apply BinCoproductArrowUnique;
    [ now rewrite <- (p 0), assoc, BinCoproductOfArrowsIn1, id_left
    | simple refine (let temp : ∑ x0 : C ⟦ c, HcL ⟧, ∏ v : nat,
         coconeIn L v · x0 = BinCoproductIn2 C (PC x (dob hF v)) · f v := _ in _);
         [ apply (tpair _ (BinCoproductIn2 C (PC x c) · t));
          now intro n; rewrite <- (p n), !assoc, BinCoproductOfArrowsIn2|];
      apply (maponpaths pr1 (p0 temp))]]).
Defined.

End constcoprod_functor.

(* Lists as the colimit of a chain given by the list functor: F(X) = 1 + A * X *)
Section lists.

Variable A : HSET.

(* F(X) = A * X *)
Definition stream : functor HSET HSET := constprod_functor1 BinProductsHSET A.

(* F(X) = 1 + (A * X) *)
Definition listFunctor : functor HSET HSET :=
  functor_composite stream (constcoprod_functor _ unitHSET BinCoproductsHSET).

Lemma omega_cocont_listFunctor : is_omega_cocont listFunctor.
Proof.
apply (is_omega_cocont_functor_composite has_homsets_HSET).
- apply omega_cocontConstProdFunctor.
(* If I use this length doesn't compute with vm_compute... *)
(* - apply (omega_cocont_constprod_functor1 _ _ has_homsets_HSET has_exponentials_HSET). *)
- apply (omega_cocontConstCoprodFunctor _ has_homsets_HSET).
Defined.

Lemma listFunctor_Initial :
  Initial (precategory_FunctorAlg listFunctor has_homsets_HSET).
Proof.
apply (colimAlgInitial _ InitialHSET omega_cocont_listFunctor (ColimCoconeHSET _ _)).
Defined.

Definition List : HSET :=
  alg_carrier _ (InitialObject listFunctor_Initial).

Let List_mor : HSET⟦listFunctor List,List⟧ :=
  alg_map _ (InitialObject listFunctor_Initial).

Let List_alg : algebra_ob listFunctor :=
  InitialObject listFunctor_Initial.

Definition nil_map : HSET⟦unitHSET,List⟧.
Proof.
simpl; intro x.
refine (List_mor _).
apply inl.
exact x.
Defined.

Definition nil : pr1 List := nil_map tt.

Definition cons_map : HSET⟦(A × List)%set,List⟧.
Proof.
intros xs.
refine (List_mor _).
exact (inr xs).
Defined.

Definition cons : pr1 A × pr1 List -> pr1 List := cons_map.

(* Get recursion/iteration scheme: *)

(*    x : X           f : A × X -> X *)
(* ------------------------------------ *)
(*       foldr x f : List A -> X *)

Definition mk_listAlgebra (X : HSET) (x : pr1 X)
  (f : HSET⟦(A × X)%set,X⟧) : algebra_ob listFunctor.
Proof.
set (x' := λ (_ : unit), x).
apply (tpair _ X (sumofmaps x' f) : algebra_ob listFunctor).
Defined.

Definition foldr_map (X : HSET) (x : pr1 X) (f : HSET⟦(A × X)%set,X⟧) :
  algebra_mor _ List_alg (mk_listAlgebra X x f).
Proof.
apply (InitialArrow listFunctor_Initial (mk_listAlgebra X x f)).
Defined.

Definition foldr (X : HSET) (x : pr1 X)
  (f : pr1 A × pr1 X -> pr1 X) : pr1 List -> pr1 X.
Proof.
apply (foldr_map _ x f).
Defined.

(* Maybe quantify over "λ _ : unit, x" instead of nil? *)
Lemma foldr_nil (X : hSet) (x : X) (f : pr1 A × X -> X) : foldr X x f nil = x.
Proof.
assert (F := maponpaths (λ x, BinCoproductIn1 _ (BinCoproductsHSET _ _) · x)
                        (algebra_mor_commutes _ _ _ (foldr_map X x f))).
apply (toforallpaths _ _ _ F tt).
Qed.

Lemma foldr_cons (X : hSet) (x : X) (f : pr1 A × X -> X)
                 (a : pr1 A) (l : pr1 List) :
  foldr X x f (cons (a,,l)) = f (a,,foldr X x f l).
Proof.
assert (F := maponpaths (λ x, BinCoproductIn2 _ (BinCoproductsHSET _ _) · x)
                        (algebra_mor_commutes _ _ _ (foldr_map X x f))).
apply (toforallpaths _ _ _ F (a,,l)).
Qed.

(* This defines the induction principle for lists using foldr *)
Section list_induction.

Variables (P : pr1 List -> UU) (PhSet : ∏ l, isaset (P l)).
Variables (P0 : P nil)
          (Pc : ∏ (a : pr1 A) (l : pr1 List), P l -> P (cons (a,,l))).

Let P' : UU := ∑ l, P l.
Let P0' : P' := (nil,, P0).
Let Pc' : pr1 A × P' -> P' :=
  λ ap : pr1 A × P', cons (pr1 ap,, pr1 (pr2 ap)),,Pc (pr1 ap) (pr1 (pr2 ap)) (pr2 (pr2 ap)).

Definition P'HSET : HSET.
Proof.
apply (tpair _ P').
abstract (apply (isofhleveltotal2 2); [ apply setproperty | intro x; apply PhSet ]).
Defined.

Lemma isalghom_pr1foldr :
  is_algebra_mor _ List_alg List_alg (λ l, pr1 (foldr P'HSET P0' Pc' l)).
Proof.
apply BinCoproductArrow_eq_cor.
- apply funextfun; intro x; destruct x; apply idpath.
- apply funextfun; intro x; destruct x as [a l].
  apply (maponpaths pr1 (foldr_cons P'HSET P0' Pc' a l)).
Qed.

Definition pr1foldr_algmor : algebra_mor _ List_alg List_alg :=
  tpair _ _ isalghom_pr1foldr.

Lemma pr1foldr_algmor_identity : identity _ = pr1foldr_algmor.
Proof.
now rewrite <- (InitialEndo_is_identity _ listFunctor_Initial pr1foldr_algmor).
Qed.

Lemma listInd l : P l.
Proof.
assert (H : pr1 (foldr P'HSET P0' Pc' l) = l).
  apply (toforallpaths _ _ _ (!pr1foldr_algmor_identity) l).
rewrite <- H.
apply (pr2 (foldr P'HSET P0' Pc' l)).
Defined.

End list_induction.

Lemma listIndProp (P : pr1 List -> UU) (HP : ∏ l, isaprop (P l)) :
  P nil -> (∏ a l, P l → P (cons (a,, l))) -> ∏ l, P l.
Proof.
intros Pnil Pcons.
apply listInd; try assumption.
intro l; apply isasetaprop, HP.
Defined.

Definition natHSET : HSET.
Proof.
exists nat.
abstract (apply isasetnat).
Defined.

Definition length : pr1 List -> nat :=
  foldr natHSET 0 (λ x, S (pr2 x)).

Definition map (f : pr1 A -> pr1 A) : pr1 List -> pr1 List :=
  foldr _ nil (λ xxs : pr1 A × pr1 List, cons (f (pr1 xxs),, pr2 xxs)).

Lemma length_map (f : pr1 A -> pr1 A) : ∏ xs, length (map f xs) = length xs.
Proof.
apply listIndProp.
- intros l; apply isasetnat.
- apply idpath.
- simpl; unfold map, length; simpl; intros a l Hl.
  simpl.
  now rewrite !foldr_cons, <- Hl.
Qed.

End lists.

(* Some examples of computations with lists over nat *)
Section nat_examples.

Definition cons_nat a l : pr1 (List natHSET) := cons natHSET (a,,l).

Infix "::" := cons_nat.
Notation "[]" := (nil natHSET) (at level 0, format "[]").

Definition testlist : pr1 (List natHSET) := 5 :: 2 :: [].

Definition testlistS : pr1 (List natHSET) :=
  map natHSET S testlist.

Definition sum : pr1 (List natHSET) -> nat :=
  foldr natHSET natHSET 0 (λ xy, pr1 xy + pr2 xy).

(* All of these work *)
(* Eval cbn in length _ (nil natHSET). *)
(* Eval vm_compute in length _ testlist. *)
(* Eval vm_compute in length _ testlistS. *)
(* Eval vm_compute in sum testlist. *)
(* Eval vm_compute in sum testlistS. *)

(* Goal length _ testlist = 2. *)
(* vm_compute. *)
(* Restart. *)
(* cbn. *)
(* Restart. *)
(* compute.  (* does not work when foldr is opaque with "Opaque foldr." *) *)
(* Restart. *)
(* cbv.   (* does not work when foldr is opaque with "Opaque foldr." *) *)
(* Restart. *)
(* native_compute. *)
(* Abort. *)

Goal (∏ l, length _ (2 :: l) = S (length _ l)).
simpl.
intro l.
try apply idpath. (* this doesn't work *)
unfold length, cons_nat.
rewrite foldr_cons. cbn.
apply idpath.
Abort.

End nat_examples.
End AltList.