(** **********************************************************

Contents:

- Definition of horizontal composition for natural transformations ([horcomp])

Written by: Benedikt Ahrens, Ralph Matthes (2015)

************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.

Local Open Scope cat.

Section horizontal_composition.

Variables C D E : precategory.

Variables F F' : functor C D.
Variables G G' : functor D E.

Variable α : F ⟹ F'.
Variable β : G ⟹ G'.


Definition horcomp_data : nat_trans_data (G □ F) (G' □ F') := λ c : C, β (F c) · #G' (α c).

Lemma is_nat_trans_horcomp : is_nat_trans _ _ horcomp_data.
Proof.
  intros c d f; unfold horcomp_data; simpl.
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
apply (nat_trans_eq hsE); intro x; simpl; unfold horcomp_data; simpl. now rewrite functor_id, id_right.
Qed.

Lemma horcomp_id_left (C D : precategory) (X : functor C C) (Z Z' : functor C D)(f : nat_trans Z Z') :
  ∏ c : C, horcomp (nat_trans_id X) f c = f (X c).
Proof.
  intro c; simpl. unfold horcomp_data; simpl.
  now rewrite functor_id, id_right.
Qed.

Lemma horcomp_id_postwhisker (A B C : precategory)
   (hsB : has_homsets B) (hsC : has_homsets C) (X X' : [A, B, hsB]) (α : X --> X')
   (Z : [B ,C, hsC]) :
  horcomp α (nat_trans_id _ ) = post_whisker α Z.
Proof.
  apply (nat_trans_eq hsC); intro a; apply id_left.
Qed.

Definition functorial_composition_data (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) :
  functor_data (precategory_binproduct_data [A, B, hsB] [B, C, hsC])
               [A, C, hsC].
Proof.
  exists (λ FG, functor_composite (pr1 FG) (pr2 FG)).
  intros a b αβ.
  exact (horcomp (pr1 αβ) (pr2 αβ)).
Defined.

Lemma is_functor_functorial_composition_data (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) : is_functor (functorial_composition_data A B C hsB hsC).
Proof.
  split.
  - red. intros FG.
    apply (nat_trans_eq hsC).
    intros x.
    apply remove_id_left.
    + apply idpath.
    + exact (functor_id (pr2 FG) ((pr1 (pr1 FG)) x)).
  - red. intros FG1 FG2 FG3 αβ1 αβ2.
    induction αβ1 as [α1 β1].
    induction αβ2 as [α2 β2].
    apply (nat_trans_eq hsC).
    intros a.
    simpl. unfold horcomp_data; simpl.
    rewrite <- ?assoc.
    apply cancel_precomposition.
    rewrite functor_comp.
    rewrite -> ?assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    apply nat_trans_ax.
Qed.

Definition functorial_composition (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) :
  functor (precategory_binproduct [A, B, hsB] [B, C, hsC]) [A, C, hsC].
Proof.
  exists (functorial_composition_data A B C hsB hsC).
  apply is_functor_functorial_composition_data.
Defined.

Lemma horcomp_pre_post
      (C D:precategory) ( E : category) (F F' : functor C D) (G G' : functor D E) (f:nat_trans F F')
      (g:nat_trans G G') :
  horcomp f g = compose (C:=functor_category C E) (a:= (G □ F)) (b:= (G' □ F)) (c:= (G' □ F'))
                        (pre_whisker F g)
                        (post_whisker f G').
Proof.
  intros.
  apply (nat_trans_eq (homset_property E)).
  intros; apply idpath.
Qed.

(* the other view as composition is not by definition but follows from naturality *)
Lemma horcomp_post_pre
      (C D:precategory) ( E : category) (F F' : functor C D) (G G' : functor D E) (f:nat_trans F F')
      (g:nat_trans G G') :
  horcomp f g = compose (C:=functor_category C E) (a:= (G □ F)) (b:= (G □ F')) (c:= (G' □ F'))
                        (post_whisker f G)
                        (pre_whisker F' g).
Proof.
  intros.
  apply (nat_trans_eq (homset_property E)).
  intro x.
  unfold horcomp, horcomp_data.
  cbn.
  apply pathsinv0.
  apply nat_trans_ax.
Qed.

(** now in the functor category *)

Lemma functorial_composition_pre_post (C D E: precategory) (hsD : has_homsets D) (hsE : has_homsets E)
      (F F' : [C, D, hsD]) (G G' : [D, E, hsE]) (f: [C, D, hsD]⟦F, F'⟧) (g: [D, E, hsE]⟦G, G'⟧) :
  # (functorial_composition _ _ _ hsD hsE) (f,, g:precategory_binproduct [C, D, hsD] [D, E, hsE] ⟦(F,,G), (F',,G')⟧) =
  # (pre_composition_functor _ _ _ hsD hsE F) g · # (post_composition_functor _ _ _ hsD hsE G') f.
Proof.
  apply (nat_trans_eq hsE).
  intro c.
  apply idpath.
Qed.

Lemma functorial_composition_post_pre (C D E: precategory) (hsD : has_homsets D) (hsE : has_homsets E)
      (F F' : [C, D, hsD]) (G G' : [D, E, hsE]) (f: [C, D, hsD]⟦F, F'⟧) (g: [D, E, hsE]⟦G, G'⟧) :
  # (functorial_composition _ _ _ hsD hsE) (f,, g:precategory_binproduct [C, D, hsD] [D, E, hsE] ⟦(F,,G), (F',,G')⟧) =
  # (post_composition_functor _ _ _ hsD hsE G) f · # (pre_composition_functor _ _ _ hsD hsE F') g.
Proof.
  apply (nat_trans_eq hsE).
  intro c.
  cbn.
  apply pathsinv0, nat_trans_ax.
Qed.


(** ** currying functorial composition *)

(** we define the two possible curried forms anew for better applicability *)

Definition pre_composition_as_a_functor_data (A B C: precategory) (hsB: has_homsets B) (hsC: has_homsets C):
  functor_data [A , B, hsB] [[B, C, hsC], [A, C, hsC], functor_category_has_homsets A C hsC].
Proof.
  use make_functor_data.
  - apply pre_composition_functor.
  - intros H1 H2 η.
    use make_nat_trans.
    + intro G.
      cbn.
      exact (# (post_composition_functor _ _ _ hsB hsC G) η).
    + intros G G' β.
      etrans.
      apply pathsinv0, functorial_composition_pre_post.
      apply functorial_composition_post_pre.
Defined.

Lemma pre_composition_as_a_functor_data_is_fun (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C):
  is_functor (pre_composition_as_a_functor_data A B C hsB hsC).
Proof.
  split.
  - intro H.
    apply (nat_trans_eq (functor_category_has_homsets A C hsC)).
    intro G.
    cbn.
    apply post_whisker_identity; exact hsC.
  - intros H1 H2 H3 β β'.
    apply (nat_trans_eq (functor_category_has_homsets A C hsC)).
    intro G.
    cbn.
    apply post_whisker_composition; exact hsC.
Qed.

Definition pre_composition_as_a_functor (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C):
  functor [A , B, hsB] [[B, C, hsC], [A, C, hsC], functor_category_has_homsets A C hsC] :=
  _ ,, pre_composition_as_a_functor_data_is_fun A B C hsB hsC.


Definition post_composition_as_a_functor_data (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C):
  functor_data [B, C, hsC] [[A, B, hsB], [A, C, hsC], functor_category_has_homsets A C hsC].
Proof.
  use make_functor_data.
  - apply post_composition_functor.
  - intros H1 H2 η.
    use make_nat_trans.
    + intro G.
      cbn.
      exact (# (pre_composition_functor _ _ _ hsB hsC G) η).
    + intros G G' β.
      etrans.
      2: { apply functorial_composition_pre_post. }
      apply pathsinv0, functorial_composition_post_pre.
Defined.

Definition post_composition_as_a_functor_data_is_fun (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C):
  is_functor (post_composition_as_a_functor_data A B C hsB hsC).
Proof.
  split.
  - intro H.
    apply (nat_trans_eq (functor_category_has_homsets A C hsC)).
    intro G.
    cbn.
    apply pre_whisker_identity; exact hsC.
  - intros H1 H2 H3 β β'.
    apply (nat_trans_eq (functor_category_has_homsets A C hsC)).
    intro G.
    cbn.
    apply pre_whisker_composition; exact hsC.
Qed.

Definition post_composition_as_a_functor (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C):
  functor [B, C, hsC] [[A, B, hsB], [A, C, hsC], functor_category_has_homsets A C hsC] :=
  _ ,, post_composition_as_a_functor_data_is_fun A B C hsB hsC.
