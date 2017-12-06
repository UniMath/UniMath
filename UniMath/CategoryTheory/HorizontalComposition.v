(** **********************************************************

Contents:

- Definition of horizontal composition for natural transformations ([horcomp])

Written by: Benedikt Ahrens, Ralph Matthes (2015)

************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.

Section horizontal_composition.

Variables C D E : precategory.

Variables F F' : functor C D.
Variables G G' : functor D E.

Variable α : F ⟹ F'.
Variable β : G ⟹ G'.

Lemma is_nat_trans_horcomp : is_nat_trans (G □ F) (G' □ F')
  (λ c : C, β (F c) · #G' (α _ )).
Proof.
  intros c d f; simpl.
  rewrite assoc, nat_trans_ax, <- !assoc; apply maponpaths.
  now rewrite <- !functor_comp, nat_trans_ax.
Qed.

Definition horcomp : nat_trans (G □ F) (G' □ F') := tpair _ _ is_nat_trans_horcomp.

End horizontal_composition.

Arguments horcomp { _ _ _ } { _ _ _ _ } _ _ .

Lemma horcomp_id_prewhisker {C D E : precategory} (hsE : has_homsets E)
  (X : functor C D) (Z Z' : functor D E) (f : nat_trans Z Z') :
  horcomp (nat_trans_id X) f = pre_whisker _ f.
Proof.
apply (nat_trans_eq hsE); simpl; intro x.
now rewrite functor_id, id_right.
Qed.

Lemma horcomp_id_left (C D : precategory) (X : functor C C) (Z Z' : functor C D)(f : nat_trans Z Z')
  :
  ∏ c : C, horcomp (nat_trans_id X) f c = f (X c).
Proof.
  intro c; simpl.
  now rewrite functor_id, id_right.
Qed.

Lemma horcomp_id_postwhisker (A B C : precategory)
   (hsB : has_homsets B) (hsC : has_homsets C) (X X' : [A, B, hsB]) (α : X --> X')
   (Z : [B ,C, hsC])
  : horcomp α (nat_trans_id _ ) = post_whisker α Z.
Proof.
  apply (nat_trans_eq hsC); intro a; apply id_left.
Qed.

Definition functorial_composition_data (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) :
  functor_data (precategory_binproduct_data [A, B, hsB] [B, C, hsC])
               [A, C, hsC].
Proof.
  exists (λ FG, functor_composite (pr1 FG) (pr2 FG)).
  intros a b αβ.
  induction αβ as [α β].
  exact (horcomp α β).
Defined.

Definition functorial_composition (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) :
  functor (precategory_binproduct [A, B, hsB] [B, C, hsC]) [A, C, hsC].
Proof.
  exists (functorial_composition_data A B C hsB hsC).
  split.
  - unfold functor_idax.
    intros FG.
    apply nat_trans_eq.
    apply hsC.
    intros x.
    apply remove_id_left.
    reflexivity.
    simpl.
    exact (functor_id (pr2 FG) ((pr1 (pr1 FG)) x)).
  - unfold functor_compax.
    intros FG1 FG2 FG3 αβ1 αβ2.
    induction αβ1 as [α1 β1].
    induction αβ2 as [α2 β2].

    apply nat_trans_eq.
    apply hsC.
    intros a.

    simpl.
    rewrite <- ?assoc.
    apply cancel_precomposition.
    rewrite (functor_comp _).
    rewrite -> ?assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply nat_trans_ax.
Defined.

Lemma horcomp_pre_post
      (C D:precategory) ( E : category) (F F' : functor C D) (G G' : functor D E) (f:nat_trans F F')
      (g:nat_trans G G') :
  horcomp f g = compose (C:=functor_category C E) (a:= (G □ F)) (b:= (G' □ F)) (c:= (G' □ F'))
                        (pre_whisker F g)
                        (post_whisker f G').
Proof.
  intros.
  apply nat_trans_eq.
  apply homset_property.
  intros;
    apply idpath.
Qed.