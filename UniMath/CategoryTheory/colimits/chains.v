(****************************************************
  Benedikt Ahrens and Anders Mörtberg, October 2015
*****************************************************)

Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.colimits.colimits.
Require Import UniMath.CategoryTheory.category_hset.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).

(* Definition graph := Σ (D : UU) , D -> D -> UU. *)

(* Definition vertex : graph -> UU := pr1. *)
(* Definition edge {g : graph} : vertex g -> vertex g -> UU := pr2 g. *)

(* Definition diagram (g : graph) (C : precategory) : UU := *)
(*   Σ (f : vertex g -> C), ∀ (a b : vertex g), edge a b -> C⟦f a, f b⟧. *)

Section nat_graph.

Variable C : precategory.
Variable (hsC : has_homsets C).

Definition nat_graph : graph.
Proof.
exists nat.
exact (fun m n => S m = n).
Defined.

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

(* Drop the first element of the chain *)
Definition shift (d : diagram nat_graph C) : diagram nat_graph C.
Proof.
exists (λ n, pr1 d (S n)); simpl; intros m n Hmn.
destruct Hmn.
now apply (pr2 d).
Defined.

Definition cocone_shift {D : diagram nat_graph C}
  {x : C} (cx : cocone (shift D) x) : cocone D x.
  (* (fx : ∀ v : nat, C ⟦ dob (shift D) v, x ⟧) *)
  (* (Hx : ∀ u v (e : edge u v), dmor (shift D) e ;; fx v = fx u) : *)
  (* Σ (f : ∀ v, C ⟦ dob D v, x ⟧),  *)
  (*   (∀ u v (e : edge u v), dmor D e ;; f v = f u). *)
Proof.
refine (mk_cocone _ _).
- intro n.
  set (p := @dmor _ _ D n (S n) (idpath _)).
  now apply (p ;; coconeIn cx n).
- abstract (now intros m n Hmn; destruct Hmn; simpl;
            apply maponpaths, (coconeInCommutes cx _ _ (idpath _))).
Defined.

Definition shift_cocone {D : diagram nat_graph C}
  {x : C} (cx : cocone D x) : cocone (shift D) x.
 (* (fx : ∀ v : nat, C ⟦ dob D v, x ⟧) *)
 (*  (Hx : ∀ u v (e : edge u v), dmor D e ;; fx v = fx u) : *)
  (* Σ (f : ∀ v, C ⟦ dob (shift D) v, x ⟧),  *)
  (*   (∀ u v (e : edge u v), dmor (shift D) e ;; f v = f u). *)
Proof.
refine (tpair _ _ _).
- intro n.
  now apply (coconeIn cx).
  (* set (p := @dmor _ _ D (S n) _ (idpath _)). *)
  (* now apply (p ;; coconeIn _ cx (S (S n))). *)
- abstract (intros m n Hmn; destruct Hmn; apply (coconeInCommutes cx)).
Defined.

Lemma shift_cocone_cocone_shift (D : diagram nat_graph C)
  (x : C) (cx : cocone D x) : cocone_shift (shift_cocone cx) = cx.
Proof.
apply total2_paths_second_isaprop; simpl.
- now repeat (apply impred; intro); apply hsC.
- now apply funextsec; intro n; apply (coconeInCommutes cx).
Qed.

Lemma cocone_shift_shift_cocone (D : diagram nat_graph C)
  (x : C) (cx : cocone (shift D) x) : shift_cocone (cocone_shift cx) = cx.
Proof.
apply total2_paths_second_isaprop; simpl.
- now repeat (apply impred; intro); apply hsC.
- now apply funextsec; intro n; apply (coconeInCommutes cx _ _ (idpath _)).
Qed.

(**** TODO: Continue from here *)

Definition shift_colim (D : diagram nat_graph C) (CC : ColimCocone D) :
  ColimCocone (shift D).
Proof.
refine (mk_ColimCocone _ _ _ _).
- apply (colim CC).
- apply (shift_cocone (colimCocone CC)).
- simpl.
intros x fx.
refine (tpair _ _ _).
+ set (cs := cocone_shift fx).
set (ca := colimArrow CC x cs).
exists ca.
simpl; intro n.
unfold ca; simpl.
set (Hp := colimArrowCommutes CC x cs (S n)).
simpl in Hp.
eapply pathscomp0.
apply Hp.
apply (coconeInCommutes fx _ _ (idpath _)).
+ simpl.
intro f.
apply total2_paths_second_isaprop; simpl.
* now apply impred; intro; apply hsC.
*
apply colimArrowUnique; simpl; intro n.
destruct f as [f Hf]; simpl.
rewrite <- (Hf n).
rewrite assoc.
apply cancel_postcomposition.
apply pathsinv0.
now apply (@colimInCommutes C).
Defined. (* parts of this should be opaque? *)

Definition colim_shift (D : diagram nat_graph C) (CC : ColimCocone (shift D)) :
  ColimCocone D.
Proof.
refine (mk_ColimCocone _ _ _ _).
- apply (colim CC).
- apply (cocone_shift (colimCocone CC)).
- (* simpl; intros m n Hmn; destruct Hmn. *)
  (* now rewrite <- (colimInCommutes _ CC m (S m) (idpath _)). *)
intros x fx.
refine (tpair _ _ _).
+
(* set (cs := cocone_shift D (colim _ CC) (colimIn _ CC) (colimInCommutes _ CC)). *)
set (test := shift_cocone fx).
set (ca := colimArrow CC x test).
exists ca.
simpl.
intro n.
unfold ca.
rewrite <- assoc.
eapply pathscomp0.
apply maponpaths.
apply (colimArrowCommutes CC x test n).
unfold test.
simpl.
eapply pathscomp0; [|apply (coconeInCommutes fx _ _ (idpath _))].
apply idpath.
+
simpl; intro f.
apply total2_paths_second_isaprop;
  [now apply impred; intro; apply hsC|]; simpl.
apply colimArrowUnique; simpl; intro n.
destruct f as [f Hf]; simpl.
rewrite <- Hf.
apply cancel_postcomposition, pathsinv0.
apply (colimInCommutes CC _ _ (idpath _)).
Defined.

Definition colim_shift_iso (D : diagram nat_graph C)
 (CC : ColimCocone D) : iso (colim CC) (colim (shift_colim D CC)).
Proof.
now apply identity_iso.
Defined.

End nat_graph.

Section functor_diagram.

Variables (C : precategory) (F : functor C C).
Variables (c : C) (s : C⟦c,F c⟧).

Definition iter (n : nat) : functor C C.
Proof.
induction n as [|n Fn].
  now apply functor_identity.
now apply (functor_composite _ _ _ Fn F).
Defined.

Definition Fdiagram : diagram nat_graph C.
Proof.
exists (λ n, iter n c); simpl; intros m n Hmn.
destruct Hmn; simpl.
induction m; simpl.
- exact s.
- exact (# F IHm).
(* now apply (# (iter m) s). *)
Defined.

Variables (hsC : has_homsets C) (CC : ColimCocone Fdiagram).

Local Notation L := (colim CC).
Local Notation LF := (colim (shift_colim C hsC Fdiagram CC)).

Definition Fcocone : cocone Fdiagram (F L).
Proof.
refine (mk_cocone _ _).
- simpl; intro n.
destruct n; simpl.
+ set (x := # F (colimIn CC 0)).
simpl in x.
exact (s ;; x).
+ set (x := # F (colimIn CC n)).
simpl in *.
apply x.
- abstract (simpl; intros m n Hmn; destruct Hmn; simpl; destruct m; simpl ;
     [apply idpath|];simpl;rewrite <- functor_comp;apply maponpaths;apply (colimInCommutes CC _ _ (idpath _))).
Defined.

(* this is m^-1 : L -> FL in TACL slides page 9 *)
Definition from_colim_shift : C⟦LF,F L⟧.
Proof.
change (colim (shift_colim C hsC Fdiagram CC)) with (colim CC).
refine (colimArrow _ _ _).
apply Fcocone.

(* refine (colimArrow _ _ _ _). *)
(* refine (mk_cocone _ _ _ _ _). *)
(* - simpl; intro n. *)
(* set (# F (colimIn _ CC n)). *)
(* simpl in p. *)
(* apply p. *)
(* - abstract ( *)
(*    simpl; intros m n Hmn; destruct Hmn; simpl; destruct m; simpl; *)
(*     [ rewrite <- functor_comp; apply maponpaths; exact (colimInCommutes _ CC 0 1 (idpath _)) *)
(*     | rewrite <- functor_comp; apply maponpaths; now apply (colimInCommutes _ CC _ _ (idpath (S (S m)))) ]). *)
Defined.

Definition from_colim : C⟦L,F L⟧.
Proof.
apply from_colim_shift.
Defined.

Definition chain_cocontinuous : UU := is_iso from_colim_shift.
(* Definition chain_cocontinuous : UU := is_iso from_colim. *)

Variable Hcc : chain_cocontinuous.
Let minv : iso L (F L) := isopair _ Hcc.
Let m : C⟦F L,L⟧ := inv_from_iso minv.

Lemma mCommutes (n : nat) : coconeIn (colimCocone CC) n = coconeIn Fcocone n ;; m.
Proof.
unfold m.
apply iso_inv_on_left.
simpl.
apply pathsinv0.
now apply (@colimArrowCommutes C _ _ CC (F L) Fcocone n).
Qed.

Lemma minvCommutes (n : nat) : coconeIn (colimCocone CC) n ;; minv = coconeIn Fcocone n.
Proof.
now apply (@colimArrowCommutes C _ _ CC (F L) Fcocone n).
Qed.

End functor_diagram.

(* TODO: Move up *)
(* Arguments iter _ _ n : simpl never. *)
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.

(* Move to limits.initial *)
Lemma InitialArrowUnique (D : precategory) (I : Initial D) (a : D) (f : D⟦InitialObject _ I,a⟧) :
  f = InitialArrow _ I _.
Proof.
now apply (pr2 (pr2 I a)).
Defined.

Section colim_initial_algebra.

Variables (C : precategory) (F : functor C C).
Variables (hsC : has_homsets C) (Init : Initial C).
Let initDiag : diagram nat_graph C := Fdiagram C F Init (InitialArrow C Init (F Init)).

Variable (CC : ColimCocone initDiag).
Variable (Fcont : chain_cocontinuous C F (InitialObject _ Init) (InitialArrow _ Init _) hsC CC).

Let L := colim CC.
Let minv : iso (colim (shift_colim C hsC initDiag CC)) (F L) := isopair _ Fcont.

(* Morally we need to insert colim_shift_iso (ie the identity iso) *)
Local Definition m : C⟦F L,L⟧ := inv_from_iso minv.

Local Definition mAlg : algebra_ob _ F.
Proof.
exists L.
apply m.
Defined. (* apply tpair didn't work here? *)

Section algebra.

Variable (Aa : algebra_ob _ F).
Let A : C := alg_carrier _ _ Aa.
Let a : C⟦F A,A⟧:= alg_map _ _ Aa.

Definition cocone_over_alg (n : nat) : C ⟦ dob initDiag n, A ⟧.
Proof.
induction n as [|n Fn]; simpl.
- now apply InitialArrow.
- now apply (# F Fn ;; a).
Defined.

(* a_n : F^n 0 -> A *)
Local Notation an := cocone_over_alg.

Lemma unfold_cocone_over_alg n : cocone_over_alg (S n) = # F (cocone_over_alg n) ;; a.
Proof.
now apply idpath.
Qed.

Lemma isCoconeOverAlg n Sn (e : edge n Sn) : dmor initDiag e ;; an Sn = an n.
Proof.
destruct e.
induction n as [|n IHn].
- now apply InitialArrowUnique.
- rewrite unfold_cocone_over_alg.
  rewrite assoc.
  rewrite unfold_cocone_over_alg.
  apply cancel_postcomposition.
  rewrite unfold_cocone_over_alg in IHn.
  apply pathsinv0.
  eapply pathscomp0.
  Focus 2.
  simpl.
  apply functor_comp.
  apply maponpaths.
  apply pathsinv0.
  now apply IHn.
Qed.

(* ad = a† = a dagger *)
Local Definition ad : C⟦L,A⟧.
Proof.
refine (colimArrow _ _ _).
refine (mk_cocone _ _).
- apply cocone_over_alg.
- apply isCoconeOverAlg.
Defined.

Lemma adaggerCommutes (n : nat) : colimIn CC n ;; ad = an n.
Proof.
apply colimArrowCommutes.
Qed.

Lemma adaggerCommutes2 (n : nat) : colimIn CC n ;; minv ;; # F ad ;; a = an n.
Proof.
induction n as [|n IHn].
- now apply InitialArrowUnique.
-
rewrite <- assoc.
eapply pathscomp0.
eapply cancel_postcomposition.
apply (minvCommutes C F _ _ hsC CC Fcont (S n)).
rewrite assoc.
simpl.
rewrite <- functor_comp.
apply cancel_postcomposition, maponpaths.
now apply adaggerCommutes.
Qed.

Lemma adaggerDef : ad = minv ;; #F ad ;; a.
Proof.
apply pathsinv0.
apply colimArrowUnique; simpl; intro n.
repeat rewrite assoc.
now apply adaggerCommutes2.
Qed.

Lemma ad_is_algebra_mor : is_algebra_mor _ _ mAlg Aa ad.
Proof.
unfold is_algebra_mor; simpl; unfold mAlg.
apply iso_inv_on_right.
rewrite assoc.
now apply adaggerDef.
Qed.

Definition adaggerMor : algebra_mor C F mAlg Aa := tpair _ _ ad_is_algebra_mor.

End algebra.

Lemma adaggerMorIsInitial : isInitial (precategory_FunctorAlg C F hsC) mAlg.
Proof.
intro Aa.
exists (adaggerMor Aa); simpl.
intros Fa.
apply (algebra_mor_eq _ _ hsC).
simpl.
unfold ad.
apply colimArrowUnique; simpl; intro n.
destruct Fa as [f hf]; simpl.
unfold is_algebra_mor in hf.
simpl in hf.
induction n as [|n IHn].
simpl.
apply InitialArrowUnique.
simpl.
rewrite <- IHn.
rewrite functor_comp.
rewrite <- assoc.
eapply pathscomp0.
Focus 2.
eapply maponpaths.
apply hf.
rewrite assoc.
apply cancel_postcomposition.
apply (mCommutes _ _ _ _ _ _ _ (S n)).
Qed.

Definition adaggerMorInitial : Initial (precategory_FunctorAlg C F hsC) :=
  tpair _ _ adaggerMorIsInitial.

End colim_initial_algebra.

Check adaggerMorIsInitial.

Section lists.

(* TODO: Move *)
Require Import UniMath.SubstitutionSystems.Auxiliary.
Require Import UniMath.SubstitutionSystems.FunctorsPointwiseProduct.
Require Import UniMath.SubstitutionSystems.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Variable A : HSET.

Lemma ProductsHSET : Products HSET.
Admitted.

Lemma CoproductsHSET : Coproducts HSET.
Admitted.

Lemma TerminalHSET : Terminal HSET.
Admitted.

Lemma InitialHSET : Initial HSET.
Admitted.

(*
F(X) = A * X
*)
Definition streamFunctor : functor HSET HSET :=
  product_functor HSET HSET ProductsHSET
                  (constant_functor HSET HSET A)
                  (functor_identity HSET).


Definition unitHSET : HSET.
Proof.
exists unit.
apply isasetaprop.
apply isapropifcontr.
apply iscontrunit.
Defined.

(*
F(X) = 1 + (A * X)
*)
Definition listFunctor : functor HSET HSET :=
  coproduct_functor HSET HSET CoproductsHSET
                    (constant_functor HSET HSET unitHSET)
                    streamFunctor.

Definition temp : ColimCocone
   (Fdiagram HSET listFunctor InitialHSET
      (InitialArrow HSET InitialHSET (listFunctor InitialHSET))).
Proof.
apply ColimCoconeHSET.
Defined.

Lemma listFunctor_chain_cocontinuous : chain_cocontinuous HSET listFunctor
  (InitialObject _ InitialHSET) (InitialArrow _ InitialHSET _) has_homsets_HSET
  temp.
Proof.
unfold chain_cocontinuous.
Admitted.

(*

P(F), P(G) |- P(F * G)
P(F), P(G) |- P(F + G)
           |- P(constant_functor A)
           |- P(identity_functor)

*)

Lemma listFunctor_Initial :
  Initial (precategory_FunctorAlg HSET listFunctor has_homsets_HSET).
Proof.
refine (adaggerMorInitial _ _ _ _ _ _).
- apply InitialHSET.
- apply temp.
- apply listFunctor_chain_cocontinuous.
Defined.

(*

Get recursion/iteration scheme:

   x : X           f : A × X -> X
------------------------------------
      iter x f : List A -> X


Get induction as well?

*)

End lists.