(************************************************************
      Benedikt Ahrens and Anders Mörtberg, October 2015
*************************************************************)

(** *********************************************************

Contents :

   Definition of chains of endofunctors

   Construction of the initial algebra of the initial chain

*************************************************************)

Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.colimits.colimits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).

Section move_upstream.

(* Move to limits.initial *)

Definition iter_functor {C : precategory} (F : functor C C) (n : nat) : functor C C.
Proof.
induction n as [|n Fn].
  now apply functor_identity.
now apply (functor_composite _ _ _ Fn F).
Defined.

End move_upstream.

(* Local Notation "F ^ n" := (iter_functor _ F n) (at level 10, format "F ^ n"). *)

Section chains.

Variables (C : precategory) (hsC : has_homsets C).

(* Define the chain:

     0 --> 1 --> 2 --> 3 --> ...

   with exactly one arrow from n to S n.
*)
Definition nat_graph : graph :=
  tpair (λ D : UU, D → D → UU) nat (λ m n, S m = n).

(* Alternative definition of chains: *)
(* Definition chain := Σ (f0 : nat -> C), ∀ n, C⟦f0 n,f0 (S n)⟧. *)

(* Definition to_chain : diagram nat_graph C -> chain. *)
(* Proof. *)
(* intro D. *)
(* exists (pr1 D); intro n. *)
(* now apply (pr2 D). *)
(* Defined. *)

(* Definition from_chain : chain -> diagram nat_graph C. *)
(* Proof. *)
(* intro c. *)
(* exists (pr1 c); simpl; intros m n Hmn. *)
(* destruct Hmn. *)
(* now apply (pr2 c). *)
(* Defined. (* Maybe define using idtoiso? *) *)

(* Drop the first element of the diagram *)
Definition shift (d : diagram nat_graph C) : diagram nat_graph C.
Proof.
exists (λ n, pr1 d (S n)); simpl; intros m n Hmn.
destruct Hmn.
now apply (pr2 d).
Defined.

(* Construct a cocone over the shifted diagram *)
Definition shift_cocone {D : diagram nat_graph C}
  {x : C} (cx : cocone D x) : cocone (shift D) x.
Proof.
refine (tpair _ _ _).
- now intro n; apply (coconeIn cx).
- abstract (now intros m n Hmn; destruct Hmn; apply (coconeInCommutes cx)).
Defined.

(* Construct a cocone over the non-shifted diagram *)
Definition unshift_cocone {D : diagram nat_graph C}
  {x : C} (cx : cocone (shift D) x) : cocone D x.
Proof.
refine (mk_cocone _ _).
- intro n.
  now apply (@dmor _ _ _ n _ (idpath _) ;; coconeIn cx n).
- abstract (now intros m n Hmn; destruct Hmn; simpl;
            apply maponpaths, (coconeInCommutes cx _ _ (idpath _))).
Defined.

Lemma unshift_shift_cocone (D : diagram nat_graph C)
  (x : C) (cx : cocone D x) : unshift_cocone (shift_cocone cx) = cx.
Proof.
apply subtypeEquality; simpl.
- intro. now repeat (apply impred; intro); apply hsC.
- now apply funextsec; intro n; apply (coconeInCommutes cx).
Qed.

Lemma shift_unshift_cocone (D : diagram nat_graph C)
  (x : C) (cx : cocone (shift D) x) : shift_cocone (unshift_cocone cx) = cx.
Proof.
apply subtypeEquality; simpl.
- intro. now repeat (apply impred; intro); apply hsC.
- now apply funextsec; intro n; apply (coconeInCommutes cx _ _ (idpath _)).
Qed.

(* Construct the colimit of the shifted diagram *)
Definition shift_colim (D : diagram nat_graph C) (CC : ColimCocone D) :
  ColimCocone (shift D).
Proof.
apply (mk_ColimCocone _ (colim CC) (shift_cocone (colimCocone CC))).
intros x fx.
refine (tpair _ _ _).
+ exists (colimArrow CC x (unshift_cocone fx)).
  abstract (intro n; simpl;
            eapply pathscomp0;
              [ apply (colimArrowCommutes _ _ (unshift_cocone _))
              | now apply (coconeInCommutes fx _ _ (idpath _)) ]).
+ abstract (simpl; intro f;
            apply subtypeEquality; simpl;
              [ intro; now apply impred; intro; apply hsC | ];
            apply colimArrowUnique; simpl; intro n;
            destruct f as [f Hf]; simpl;
            rewrite <- (Hf n), assoc;
            now apply cancel_postcomposition, pathsinv0, (@colimInCommutes C)).
Defined.

(* Construct the colimit of the unshifted diagram *)
Definition unshift_colim (D : diagram nat_graph C) (CC : ColimCocone (shift D)) :
  ColimCocone D.
Proof.
apply (mk_ColimCocone _ (colim CC) (unshift_cocone (colimCocone CC))).
intros x fx.
refine (tpair _ _ _).
+ exists (colimArrow CC x (shift_cocone fx)).
  abstract (simpl; intro n;
            rewrite <- assoc;
            eapply pathscomp0;
              [ apply maponpaths, (colimArrowCommutes CC x _ n)
              | simpl; now eapply pathscomp0;
                  [|apply (coconeInCommutes fx _ _ (idpath _))]]).
+ abstract (simpl; intro f;
            apply subtypeEquality;
              [ intro; now apply impred; intro; apply hsC|]; simpl;
            apply colimArrowUnique; simpl; intro n;
            destruct f as [f Hf]; simpl;
            rewrite <- Hf;
            apply cancel_postcomposition, pathsinv0;
            now apply (colimInCommutes CC _ _ (idpath _))).
Defined.

Definition colim_shift_iso (D : diagram nat_graph C)
 (CC : ColimCocone D) : iso (colim CC) (colim (shift_colim D CC)).
Proof.
now apply identity_iso.
Defined.

End chains.

Section functor_chain.

Context {C : precategory} (hsC : has_homsets C) (F : functor C C).
Context (c : C) (s : C⟦c,F c⟧).

(* Construct the chain:

         s          Fs            F^2 s
     c -----> F c ------> F^2 c --------> F^3 c ---> ...

*)
Definition Fdiagram : diagram nat_graph C.
Proof.
exists (λ n, iter_functor F n c); simpl; intros m n Hmn.
destruct Hmn; simpl.
induction m; simpl.
- exact s.
- exact (# F IHm).
Defined.

Variables (CC : ColimCocone Fdiagram).

Local Notation L := (colim CC).
Local Notation LF := (colim (shift_colim C hsC Fdiagram CC)).

Definition Fcocone : cocone Fdiagram (F L).
Proof.
refine (mk_cocone _ _).
- intro n.
  destruct n; simpl.
  + exact (s ;; # F (colimIn CC 0)).
  + exact (# F (colimIn CC n)).
- abstract (simpl; intros m n Hmn; destruct Hmn; simpl; destruct m; simpl;
            [apply idpath|]; simpl; rewrite <- functor_comp; apply maponpaths;
            apply (colimInCommutes CC _ _ (idpath _))).
Defined.

(* this is m^-1 : L -> FL in TACL slides page 9 *)
Definition from_colim_shift : C⟦LF,F L⟧ := colimArrow _ _ Fcocone.

(* This uses that LF and L are convertible *)
Definition from_colim : C⟦L,F L⟧ := from_colim_shift.

Definition chain_cocontinuous : UU := is_iso from_colim_shift.

(* This could also be defined as: *)
(* Definition chain_cocontinuous : UU := is_iso from_colim. *)

Variable Hcc : chain_cocontinuous.
Let minv : iso L (F L) := isopair _ Hcc.
Let m : C⟦F L,L⟧ := inv_from_iso minv.

Lemma mCommutes (n : nat) : coconeIn (colimCocone CC) n = coconeIn Fcocone n ;; m.
Proof.
now apply iso_inv_on_left, pathsinv0, (colimArrowCommutes _ _ Fcocone).
Qed.

Lemma minvCommutes (n : nat) : coconeIn (colimCocone CC) n ;; minv = coconeIn Fcocone n.
Proof.
now apply (colimArrowCommutes _ _ Fcocone).
Qed.

End functor_chain.

(* Proves that (L,m : F L -> L) is the initial algebra where L is the
   colimit of the inital chain:

         !          F !           F^2 !
     0 -----> F 0 ------> F^2 0 --------> F^3 0 ---> ...

*)
Section colim_initial_algebra.

Variables (C : precategory) (F : functor C C).
Variables (hsC : has_homsets C) (Init : Initial C).

Definition initDiag : diagram nat_graph C :=
  Fdiagram F (InitialObject Init) (InitialArrow Init (F (InitialObject Init))).

Variable (CC : ColimCocone initDiag).
Variable (Fcont : chain_cocontinuous hsC F (InitialObject Init) (InitialArrow Init _) CC).

Local Notation L := (colim CC).
Local Notation minv := (isopair _ Fcont).

Local Definition m : C⟦F L,L⟧ := inv_from_iso minv.
Local Definition colimAlg : algebra_ob F := tpair (λ X : C, C ⟦ F X, X ⟧) L m.

Section algebra.

Variable (Aa : algebra_ob F).

Local Notation A := (alg_carrier _ Aa).
Local Notation a := (alg_map _ Aa).

Definition cocone_over_alg (n : nat) : C ⟦ dob initDiag n, A ⟧.
Proof.
induction n as [|n Fn]; simpl.
- now apply InitialArrow.
- now apply (# F Fn ;; a).
Defined.

(* a_n : F^n 0 -> A *)
Local Notation an := cocone_over_alg.

(* This makes Coq not unfold dmor during simpl *)
Arguments dmor : simpl never.

Lemma isCoconeOverAlg n Sn (e : edge n Sn) : dmor initDiag e ;; an Sn = an n.
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
refine (mk_cocone _ _).
- apply cocone_over_alg.
- apply isCoconeOverAlg.
Defined.

Lemma adaggerCommutes (n : nat) : colimIn CC n ;; ad = an n.
Proof.
now apply colimArrowCommutes.
Qed.

Lemma adaggerCommutes2 (n : nat) : colimIn CC n ;; minv ;; # F ad ;; a = an n.
Proof.
induction n as [|n IHn].
- now apply InitialArrowUnique.
- rewrite <- assoc.
  eapply pathscomp0;
    [ eapply cancel_postcomposition; apply (minvCommutes hsC F _ _ CC Fcont (S n))|].
  rewrite assoc; simpl; rewrite <- functor_comp.
  now apply cancel_postcomposition, maponpaths, adaggerCommutes.
Qed.

Lemma adaggerDef : ad = minv ;; #F ad ;; a.
Proof.
apply pathsinv0, colimArrowUnique; simpl; intro n.
rewrite !assoc.
now apply adaggerCommutes2.
Qed.

Lemma ad_is_algebra_mor : is_algebra_mor _ colimAlg Aa ad.
Proof.
unfold is_algebra_mor; simpl; unfold colimAlg.
apply iso_inv_on_right.
rewrite assoc.
now apply adaggerDef.
Qed.

Definition adaggerMor : algebra_mor F colimAlg Aa := tpair _ _ ad_is_algebra_mor.

End algebra.

Lemma colimAlgIsInitial : isInitial (precategory_FunctorAlg F hsC) colimAlg.
Proof.
refine (mk_isInitial _ _).
intros Aa.
exists (adaggerMor Aa); simpl; intro Fa.
apply (algebra_mor_eq _ hsC); simpl.
unfold ad.
apply colimArrowUnique; simpl; intro n.
destruct Fa as [f hf]; simpl.
unfold is_algebra_mor in hf.
simpl in hf.
induction n as [|n IHn]; simpl.
- now apply InitialArrowUnique.
- rewrite <- IHn, functor_comp, <- assoc.
  eapply pathscomp0; [| eapply maponpaths; apply hf].
  rewrite assoc.
  now apply cancel_postcomposition, (mCommutes _ _ _ _ _ _ (S n)).
Qed.

Definition colimAlgInitial : Initial (precategory_FunctorAlg F hsC) :=
  mk_Initial _ colimAlgIsInitial.

End colim_initial_algebra.


(* WIP below of here *)
(* Section lists. *)

(* (* TODO: Move *) *)
(* Require Import UniMath.SubstitutionSystems.Auxiliary. *)
(* Require Import UniMath.SubstitutionSystems.FunctorsPointwiseProduct. *)
(* Require Import UniMath.SubstitutionSystems.FunctorsPointwiseCoproduct. *)
(* Require Import UniMath.CategoryTheory.limits.products. *)
(* Require Import UniMath.CategoryTheory.limits.coproducts. *)
(* Require Import UniMath.CategoryTheory.limits.terminal. *)

(* Variable A : HSET. *)

(* Lemma ProductsHSET : Products HSET. *)
(* Admitted. *)

(* Lemma CoproductsHSET : Coproducts HSET. *)
(* Admitted. *)

(* Lemma TerminalHSET : Terminal HSET. *)
(* Admitted. *)

(* Lemma InitialHSET : Initial HSET. *)
(* Admitted. *)

(* (* *)
(* F(X) = A * X *)
(* *) *)
(* Definition streamFunctor : functor HSET HSET := *)
(*   product_functor HSET HSET ProductsHSET *)
(*                   (constant_functor HSET HSET A) *)
(*                   (functor_identity HSET). *)


(* Definition unitHSET : HSET. *)
(* Proof. *)
(* exists unit. *)
(* apply isasetaprop. *)
(* apply isapropifcontr. *)
(* apply iscontrunit. *)
(* Defined. *)

(* (* *)
(* F(X) = 1 + (A * X) *)
(* *) *)
(* Definition listFunctor : functor HSET HSET := *)
(*   coproduct_functor HSET HSET CoproductsHSET *)
(*                     (constant_functor HSET HSET unitHSET) *)
(*                     streamFunctor. *)

(* Definition temp : ColimCocone *)
(*    (Fdiagram listFunctor InitialHSET *)
(*       (InitialArrow HSET InitialHSET (listFunctor InitialHSET))). *)
(* Proof. *)
(* apply ColimCoconeHSET. *)
(* Defined. *)

(* Lemma listFunctor_chain_cocontinuous : chain_cocontinuous has_homsets_HSET listFunctor *)
(*   (InitialObject _ InitialHSET) (InitialArrow _ InitialHSET _) temp. *)
(* Proof. *)
(* unfold chain_cocontinuous. *)
(* Admitted. *)

(* (* *)

(* P(F), P(G) |- P(F * G) *)
(* P(F), P(G) |- P(F + G) *)
(*            |- P(constant_functor A) *)
(*            |- P(identity_functor) *)

(* *) *)

(* Lemma listFunctor_Initial : *)
(*   Initial (precategory_FunctorAlg HSET listFunctor has_homsets_HSET). *)
(* Proof. *)
(* refine (adaggerMorInitial _ _ _ _ _ _). *)
(* - apply InitialHSET. *)
(* - apply temp. *)
(* - apply listFunctor_chain_cocontinuous. *)
(* Defined. *)

(* (* *)

(* Get recursion/iteration scheme: *)

(*    x : X           f : A × X -> X *)
(* ------------------------------------ *)
(*       iter x f : List A -> X *)


(* Get induction as well? *)

(* *) *)

(* End lists. *)