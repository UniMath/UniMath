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

Definition chain := Σ (f0 : nat -> C), ∀ n, C⟦f0 n,f0 (S n)⟧.

Definition to_chain : diagram nat_graph C -> chain.
Proof.
intro D.
exists (pr1 D); intro n.
now apply (pr2 D).
Defined.

Definition from_chain : chain -> diagram nat_graph C.
Proof.
intro c.
exists (pr1 c); simpl; intros m n Hmn.
destruct Hmn.
now apply (pr2 c).
Defined. (* Maybe define using idtoiso? *)

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
Admitted.
(* Proof. *)
(* simpl. *)
(* refine (tpair _ _ _). *)
(* - intro n. *)
(*   set (@dmor _ _ D n (S n) (idpath _)). *)
(*   now apply (p ;; fx n).  *)
(* - abstract (now intros m n Hmn; destruct Hmn; simpl; *)
(*             apply maponpaths, (Hx _ _ (idpath _))). *)
(* Defined. *)


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
admit.
+ admit.
Admitted.

End nat_graph.

Section functor_diagram. 

Variables (C : precategory) (F : functor C C).
Variables (c : C) (s : C⟦c,F c⟧).

Definition iter (n : nat) : functor C C.
Proof.
induction n as [|n Fn].
  now apply functor_identity.
now apply (functor_composite _ _ _ F Fn).
Defined.

Definition Fdiagram : diagram nat_graph C.
Proof.
exists (λ n, iter n c); simpl; intros m n Hmn.
destruct Hmn; simpl.
now apply (# (iter m) s).
Defined.

End functor_diagram.
