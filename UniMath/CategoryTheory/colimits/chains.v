(************************************************************
      Benedikt Ahrens and Anders Mörtberg, October 2015
*************************************************************)

(** *********************************************************

Contents :

   Definition of chains of endofunctors

   Construction of the initial algebra of the initial chain

*************************************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.colimits.colimits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).

Section move_upstream.

(* Move to limits.initial *)

Fixpoint iter_functor {C : precategory} (F : functor C C) (n : nat) : functor C C := match n with
  | O => functor_identity C
  | S n' => functor_composite _ _ _ (iter_functor F n') F
  end.

(* TODO : state this for any object and morphism, that is,
+   - Id^n a = a
+   - #(Id^n) f = f
+   thus avoiding use of funext
+
+  TODO: similar for
+   - (G o F)^n (a) = G^n(a) o F^n(a)
+   - #(G o F)^n (f) = #G^n(f) o #F^n(f)
+
*)

End move_upstream.

(* Local Notation "F ^ n" := (iter_functor _ F n) (at level 10, format "F ^ n"). *)

Section chains.

(* Define the chain:

     0 --> 1 --> 2 --> 3 --> ...

   with exactly one arrow from n to S n.
*)
Definition nat_graph : graph :=
  tpair (λ D : UU, D → D → UU) nat (λ m n, S m = n).

Local Notation "'chain'" := (diagram nat_graph).

Definition mapchain {C D : precategory} (F : functor C D)
  (c : chain C) : chain D := mapdiagram F c.

(* Construct the chain:

         !          F!            F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...

*)
Definition initChain {C : precategory} (InitC : Initial C) (F : functor C C) : chain C.
Proof.
exists (λ n, iter_functor F n InitC).
intros m n Hmn; destruct Hmn; simpl.
induction m; simpl.
- exact (InitialArrow InitC _).
- exact (# F IHm).
Defined.

End chains.

Notation "'chain'" := (diagram nat_graph).

Definition omega_cocont {C D : precategory} (F : functor C D) : UU :=
  forall (c : chain C) (L : C) (cc : cocone c L),
  preserves_colimit F c L cc.

(* This section proves that (L,α : F L -> L) is the initial algebra
   where L is the colimit of the inital chain:

         !          F !           F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...

*)
Section colim_initial_algebra.

Variables (C : precategory) (hsC : has_homsets C).
Variables (F : functor C C) (HF : omega_cocont F).
Variables (InitC : Initial C).

Let Fchain : chain C := initChain InitC F.

Variable (CC : ColimCocone Fchain).

Let L : C := colim CC.
Let FFchain : chain C := mapchain F Fchain.

Let Fa : cocone FFchain (F L) := mapcocone F _ (colimCocone CC).
Let FHC' : isColimCocone FFchain (F L) Fa :=
  HF Fchain L (colimCocone CC) (isColimCocone_from_ColimCocone CC).
Let FHC : ColimCocone FFchain := mk_ColimCocone _ _ _ FHC'.

Definition shiftCocone : cocone FFchain L.
Proof.
simple refine (mk_cocone _ _).
- intro n; apply (coconeIn (colimCocone CC) (S n)).
- intros m n e; destruct e.
  apply (coconeInCommutes (colimCocone CC) (S m) _ (idpath _)).
Defined.

Definition unshiftCocone (x : C) : cocone FFchain x -> cocone Fchain x.
Proof.
intros cc.
simple refine (mk_cocone _ _).
- simpl; intro n.
  destruct n as [|n]; simpl.
  + apply InitialArrow.
  + apply (coconeIn cc _).
- simpl; intros m n e; destruct e; simpl.
  destruct m as [|m].
  + apply InitialArrowUnique.
  + apply (coconeInCommutes cc m _ (idpath _)).
Defined.

Definition shiftIsColimCocone : isColimCocone FFchain L shiftCocone.
Proof.
intros x cc; simpl.
simple refine (tpair _ _ _).
+ simple refine (tpair _ _ _).
  * apply colimArrow, (unshiftCocone _ cc).
  * simpl; intro n.
    apply (colimArrowCommutes CC x (unshiftCocone x cc) (S n)).
+ simpl; intros p.
  apply subtypeEquality.
  * intro f; apply impred; intro; apply hsC.
  * apply colimArrowUnique; simpl; intro n.
    destruct n as [|n]; [ apply InitialArrowUnique | apply (pr2 p) ].
Defined.

Definition shiftColimCocone : ColimCocone FFchain :=
  mk_ColimCocone FFchain L shiftCocone shiftIsColimCocone.

Definition α_mor : C⟦F L,L⟧ := colimArrow FHC L shiftCocone.

Definition is_iso_α_mor : is_iso α_mor :=
  isColim_is_iso _ FHC _ _ shiftIsColimCocone.

Let α : iso (F L) L := isopair _ is_iso_α_mor.
Let α_inv : iso L (F L) := iso_inv_from_iso α.
Let α_alg : algebra_ob F := tpair (λ X : C, C ⟦ F X, X ⟧) L α.

(* Why does this not compute? *)
Lemma unfold_inv_from_iso_α :
  inv_from_iso α = colimArrow shiftColimCocone _ (colimCocone FHC).
Proof.
cbn.
apply id_right.
Qed.

(* Given an algebra:

          a
   F A ------> A

 we now define an algebra morphism ad:

          α
   F L ------> L
    |          |
    |          | ad
    |          |
    V     a    V
   F A ------> A


*)
Section algebra_mor.

Variable (Aa : algebra_ob F).

Local Notation A := (alg_carrier _ Aa).
Local Notation a := (alg_map _ Aa).

Definition cocone_over_alg (n : nat) : C ⟦ dob Fchain n, A ⟧.
Proof.
induction n as [|n Fn]; simpl.
- now apply InitialArrow.
- now apply (# F Fn ;; a).
Defined.

(* a_n : F^n 0 -> A *)
Local Notation an := cocone_over_alg.

(* This makes Coq not unfold dmor during simpl *)
Arguments dmor : simpl never.

Lemma isCoconeOverAlg n Sn (e : edge n Sn) : dmor Fchain e ;; an Sn = an n.
Proof.
destruct e.
induction n as [|n IHn].
- now apply InitialArrowUnique.
- simpl; rewrite assoc.
  apply cancel_postcomposition, pathsinv0.
  eapply pathscomp0; [|simpl; apply functor_comp].
  now apply maponpaths, pathsinv0, IHn.
Qed.

(* ad = a† = a dagger *)
Local Definition ad : C⟦L,A⟧.
Proof.
apply colimArrow.
simple refine (mk_cocone _ _).
- apply cocone_over_alg.
- apply isCoconeOverAlg.
Defined.

Lemma ad_is_algebra_mor : is_algebra_mor _ α_alg Aa ad.
Proof.
apply pathsinv0, iso_inv_to_left, colimArrowUnique; simpl; intro n.
destruct n as [|n].
- now apply InitialArrowUnique.
- rewrite assoc, unfold_inv_from_iso_α.
  eapply pathscomp0;
    [apply cancel_postcomposition, (colimArrowCommutes shiftColimCocone)|].
  simpl; rewrite assoc, <- functor_comp.
  apply cancel_postcomposition, maponpaths, (colimArrowCommutes CC).
Qed.

Definition ad_mor : algebra_mor F α_alg Aa := tpair _ _ ad_is_algebra_mor.

End algebra_mor.

Lemma colimAlgIsInitial : isInitial (precategory_FunctorAlg F hsC) α_alg.
Proof.
apply mk_isInitial; intros Aa.
exists (ad_mor Aa); simpl; intro Fa'.
apply (algebra_mor_eq _ hsC); simpl.
apply colimArrowUnique; simpl; intro n.
destruct Fa' as [f hf]; simpl.
unfold is_algebra_mor in hf; simpl in hf.
induction n as [|n IHn]; simpl.
- now apply InitialArrowUnique.
- rewrite <- IHn, functor_comp, <- assoc.
  eapply pathscomp0; [| eapply maponpaths; apply hf].
  rewrite assoc.
  apply cancel_postcomposition, pathsinv0, (iso_inv_to_right _ _ _ _ _ α).
  rewrite unfold_inv_from_iso_α; apply pathsinv0.
  now eapply pathscomp0; [apply (colimArrowCommutes shiftColimCocone)|].
Qed.

Definition colimAlgInitial : Initial (precategory_FunctorAlg F hsC) :=
  mk_Initial _ colimAlgIsInitial.

End colim_initial_algebra.

Section polynomial_functors.

Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Variables (C : precategory) (hsC : has_homsets C) (InitC : Initial C).
Variables (F : functor C C).

(* "good" functors *)
Let good F := @omega_cocont C C F.

(* TODO: Prove that polynomial functors are good *)
(* good(F), good(G) |- good(F * G) *)
(* good(F), good(G) |- good(F + G) *)
(*                  |- good(constant_functor A) *)
(*                  |- good(identity_functor) *)

Section constant_functor.

Variable (x : C).

Let Fx : functor C C := constant_functor C C x.

Lemma goodConstantFunctor : good Fx.
Proof.
intros c L ccL HcL y ccy; simpl.
simple refine (tpair _ _ _).
- simple refine (tpair _ _ _).
  + apply (coconeIn ccy 0).
  + simpl; intro n; rewrite id_left.
    destruct ccy as [f Hf]; simpl in *.
    induction n; [apply idpath|].
    now rewrite IHn, <- (Hf n (S n) (idpath _)), id_left.
- simpl; intro p; apply subtypeEquality.
  + intros f; apply impred; intro; apply hsC.
  + now simpl; destruct p as [p H]; rewrite <- (H 0), id_left.
Defined.

End constant_functor.

Section identity_functor.

Let Fid : functor C C := functor_identity C.

Lemma goodIdentityFunctor : good Fid.
Proof.
intros c L ccL HcL.
apply (preserves_colimit_identity hsC _ _ _ HcL).
Defined.

End identity_functor.

End polynomial_functors.

(*
(* WIP below of here *)
Section lists.

(* TODO: Move *)

Variable A : HSET.

(* F(X) = A * X *)
Definition streamFunctor : functor HSET HSET :=
  product_functor HSET HSET ProductsHSET
                  (constant_functor HSET HSET A)
                  (functor_identity HSET).

(* F(X) = 1 + (A * X) *)

(*
Definition listFunctor : functor HSET HSET :=
  coproduct_functor HSET HSET CoproductsHSET
                    (constant_functor HSET HSET (TerminalObject TerminalHSET))
                    streamFunctor.
*)

(* Let ColimCoconeF F := ColimCocone *)
(*          (Fchain F (InitialObject InitialHSET) *)
(*             (InitialArrow InitialHSET (F (InitialObject InitialHSET)))). *)

Lemma listFunctor_omega_cocontinuous : good listFunctor.
Proof.
unfold listFunctor, streamFunctor.
apply goodCoproduct; [ apply goodConstant |].
apply goodProduct; [ apply goodConstant | apply goodIdentity].
Defined.

Lemma listFunctor_Initial :
  Initial (precategory_FunctorAlg listFunctor has_homsets_HSET).
Proof.
simple refine (colimAlgInitial _ _ _ _ _ _).
- apply InitialHSET.
- apply ColimCoconeHSET.
- apply listFunctor_omega_cocontinuous.
Defined.


(* Get recursion/iteration scheme: *)

(*    x : X           f : A × X -> X *)
(* ------------------------------------ *)
(*       iter x f : List A -> X *)

(* Get induction as well? *)

End lists.
*)
