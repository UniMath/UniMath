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

Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (at level 50).

(* Definition graph := Σ (D : UU) , D -> D -> UU. *)

(* Definition vertex : graph -> UU := pr1. *)
(* Definition edge {g : graph} : vertex g -> vertex g -> UU := pr2 g. *)

(* Definition diagram (g : graph) (C : precategory) : UU := *)
(*   Σ (f : vertex g -> C), ∀ (a b : vertex g), edge a b -> C⟦f a, f b⟧. *)

Section nat_graph.

Variable C : precategory.

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

Definition cocone_shift (D : diagram nat_graph C)
  (x : C) (fx : ∀ v : nat, C ⟦ dob (shift D) v, x ⟧)
  (Hx : ∀ u v (e : edge u v), dmor (shift D) e ;; fx v = fx u) :
  Σ (f : ∀ v, C ⟦ dob D v, x ⟧), 
    (∀ u v (e : edge u v), dmor D e ;; f v = f u).
Proof.
simpl.
refine (tpair _ _ _).
- intro n.
  set (@dmor _ _ D n (S n) (idpath _)).
  now apply (p ;; fx n). 
- abstract (now intros m n Hmn; destruct Hmn; simpl;
            apply maponpaths, (Hx _ _ (idpath _))).
Defined.

Definition colim_shift (hsC : has_homsets C) (D : diagram nat_graph C) (CC : ColimCocone C D) :
  ColimCocone C (shift D).
Proof.
refine (mk_ColimCocone _ _ _ _ _ _).
- now apply (colim _ CC).
- simpl; intro n.
  now apply (colimIn _ CC).
- simpl; intros m n e.
  destruct e; simpl.
  now apply (colimInCommutes _ CC).
- simpl.
intros x fx Hx.
refine (tpair _ _ _).
+ set (cs := cocone_shift D x fx Hx).
set (ca := colimArrow _ CC x (pr1 cs) (pr2 cs)).
exists ca.
simpl; intro n.
unfold ca; simpl.
set (Hp := @colimArrowCommutes _ _ D CC x (λ n0 : nat, dmor D (idpath (S n0)) ;; fx n0)
                           (cocone_shift_subproof D x fx Hx) (S n)).
simpl in Hp.
eapply pathscomp0.
apply Hp.
now apply (Hx _ _ (idpath _)).
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
now apply colimInCommutes.
Defined. (* parts of this should be opaque? *)

Definition shift_cocone (D : diagram nat_graph C)
  (x : C) (fx : ∀ v : nat, C ⟦ dob D v, x ⟧)
  (Hx : ∀ u v (e : edge u v), dmor D e ;; fx v = fx u) :
  Σ (f : ∀ v, C ⟦ dob (shift D) v, x ⟧), 
    (∀ u v (e : edge u v), dmor (shift D) e ;; f v = f u).
Proof.
simpl.
refine (tpair _ _ _).
- intro n.
  set (@dmor _ _ D (S n) _ (idpath _)).
  now apply (p ;; fx (S (S n))).
- abstract (now intros m n Hmn; destruct Hmn; simpl;
            apply maponpaths, (Hx _ _ (idpath _))).
Defined.


Definition shift_colim (hsC : has_homsets C) (D : diagram nat_graph C) (CC : ColimCocone C (shift D)) :
  ColimCocone C D.
Proof.
refine (mk_ColimCocone _ _ _ _ _ _).
- now apply (colim _ CC).
- simpl; intro n.
  set (cs := cocone_shift D (colim _ CC) (colimIn _ CC) (colimInCommutes _ CC)).
  exact (pr1 cs n).
- simpl; intros m n Hmn; destruct Hmn.
  now rewrite <- (colimInCommutes _ CC m (S m) (idpath _)).
- intros x fx Hx.
refine (tpair _ _ _).
+ 
set (cs := cocone_shift D (colim _ CC) (colimIn _ CC) (colimInCommutes _ CC)).
set (test := shift_cocone D x fx Hx).
set (ca := colimArrow _ CC x (pr1 test) (pr2 test)).
exists ca.
simpl.
intro n.
unfold ca.
rewrite <- assoc.
eapply pathscomp0.
apply maponpaths.
apply (colimArrowCommutes _ CC x (pr1 test) (pr2 test) n).
unfold test.
simpl.
eapply pathscomp0; [|apply (Hx _ _ (idpath _))].
now apply maponpaths, Hx.
+
simpl; intro f.
apply total2_paths_second_isaprop; 
  [now apply impred; intro; apply hsC|]; simpl.
apply colimArrowUnique; simpl; intro n.
destruct f as [f Hf]; simpl.
rewrite <- Hf, assoc.
apply cancel_postcomposition, pathsinv0.
eapply pathscomp0.
apply maponpaths, (colimInCommutes _ CC (S n) _ (idpath _)).
now apply (colimInCommutes _ CC _ _ (idpath _)).
Defined.

Definition colim_shift_iso (hsC : has_homsets C) (D : diagram nat_graph C)
 (CC : ColimCocone C D) : iso (colim _ CC) (colim _ (colim_shift hsC D CC)).
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

Definition from_colim_shift (hsC : has_homsets C) (CC : ColimCocone _ Fdiagram) :
  C⟦colim _ (colim_shift _ hsC Fdiagram CC),F (colim _ CC)⟧.
Proof.
refine (colimArrow _ _ _ _ _).
- simpl; intro n.
set (# F (colimIn _ CC n)).
simpl in p.
apply p.
- abstract (
   simpl; intros m n Hmn; destruct Hmn; simpl; destruct m; simpl;
    [ rewrite <- functor_comp; apply maponpaths; exact (colimInCommutes _ CC 0 1 (idpath _))
    | rewrite <- functor_comp; apply maponpaths; now apply (colimInCommutes _ CC _ _ (idpath (S (S m)))) ]).
Defined.

Definition chain_cocontinuous (hsC : has_homsets C)
  (CC : ColimCocone _ Fdiagram) : UU := is_iso (from_colim_shift hsC CC).

End functor_diagram.

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

Variable (CC : ColimCocone C initDiag).
Variable (Fcont : chain_cocontinuous C F (InitialObject _ Init) (InitialArrow _ Init _) hsC CC).

Let c := colim _ CC.
Let Fcomm : iso (colim C (colim_shift C hsC initDiag CC)) (F c) := isopair _ Fcont.

(* Morally we need to insert colim_shift_iso (ie the identity iso) *)
Local Definition inc : C⟦F c,c⟧ := inv_from_iso Fcomm.

Local Definition cinc : algebra_ob _ F. 
Proof.
exists c.
apply inc.
Defined. (* WTF *)

Variable (Aa : algebra_ob _ F).
Let A : C := alg_carrier _ _ Aa.
Let a : C⟦F A,A⟧:= alg_map _ _ Aa.

Definition cocone_over_alg (n : nat) : C ⟦ dob initDiag n, A ⟧.
Proof.
induction n as [|n Fn]; simpl.
- now apply InitialArrow.
- now apply (# F Fn ;; a).
Defined.

Lemma unfold_cocone_over_alg n : cocone_over_alg (S n) = # F (cocone_over_alg n) ;; a.
Proof.
now apply idpath.
Qed.

Lemma isCoconeOverAlg u v (e : edge u v) : dmor initDiag e ;; cocone_over_alg v = cocone_over_alg u.
Proof.
destruct e.
induction u.
- now apply InitialArrowUnique.
- 
rewrite unfold_cocone_over_alg.
rewrite assoc.
rewrite unfold_cocone_over_alg.
apply cancel_postcomposition.
rewrite unfold_cocone_over_alg in IHu.
apply pathsinv0.
eapply pathscomp0.
Focus 2.
simpl.
apply functor_comp.
apply maponpaths.
apply pathsinv0.
now apply IHu.
Qed.

Local Definition b : C⟦c,A⟧.
Proof.
refine (colimArrow _ _ _ _ _).
- apply cocone_over_alg.
- apply isCoconeOverAlg.
Defined.

Lemma b_is_algebra_mor : is_algebra_mor _ _ cinc Aa b.
Proof.
unfold is_algebra_mor; simpl; unfold inc.
apply iso_inv_on_right, pathsinv0.
assert (H : colim_shift_iso _ hsC initDiag CC ;; Fcomm ;; (# F b ;; a) =
            colimArrow C CC A cocone_over_alg isCoconeOverAlg).
  apply colimArrowUnique.
simpl.
intro n.
rewrite id_left.

induction n.
- now apply InitialArrowUnique.
- simpl.
repeat rewrite assoc.

unfold from_colim_shift.
Check (colimArrow C
                           (colim_shift C hsC
                              (Fdiagram C F Init
                                 (InitialArrow C Init (F Init))) CC)
                           (F (colim C CC))
                           (λ n0 : nat, # F (colimIn C CC n0))
                           (from_colim_shift_subproof C F Init
                              (InitialArrow C Init (F Init)) hsC CC) ).
Search colimArrow.

unfold from_colim_shift in IHn.
rewrite IHn.

eapply pathscomp0.
eapply cancel_postcomposition.

apply colimArrowCommutes.
simpl.
repeat rewrite functor_comp.

unfold colimIn.
simpl.
- rewrite id_left in H.
exact H.
Admitted.


 ().

End colim_initial_algebra.