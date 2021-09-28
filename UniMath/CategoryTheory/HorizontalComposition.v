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
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.UnitorsAndAssociatorsForEndofunctors.

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

Definition functorial_composition_legacy_data (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) :
  functor_data (precategory_binproduct_data [A, B, hsB] [B, C, hsC])
               [A, C, hsC].
Proof.
  exists (λ FG, functor_composite (pr1 FG) (pr2 FG)).
  intros a b αβ.
  exact (horcomp (pr1 αβ) (pr2 αβ)).
Defined.

Lemma is_functor_functorial_composition_legacy_data (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) : is_functor (functorial_composition_legacy_data A B C hsB hsC).
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

Definition functorial_composition_legacy (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) :
  functor (precategory_binproduct [A, B, hsB] [B, C, hsC]) [A, C, hsC].
Proof.
  exists (functorial_composition_legacy_data A B C hsB hsC).
  apply is_functor_functorial_composition_legacy_data.
Defined.

Definition functorial_composition_data (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) :
  functor_data (precategory_binproduct_data [A, B, hsB] [B, C, hsC])
               [A, C, hsC].
Proof.
  exists (λ FG, functor_composite (pr1 FG) (pr2 FG)).
  intros F G αβ.
  exact (# (post_composition_functor _ _ _ hsB hsC (pr2 F)) (pr1 αβ) · # (pre_composition_functor _ _ _ hsB hsC (pr1 G)) (pr2 αβ)).
Defined.

Lemma is_functor_functorial_composition_data (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) : is_functor (functorial_composition_data A B C hsB hsC).
Proof.
  split.
  - red. intros FG.
    unfold functorial_composition_data.
    unfold functor_on_morphisms.
    unfold pr2.
    change (# (post_composition_functor _ _ _ hsB hsC (pr2 FG)) (identity (pr1 FG)) ·
              # (pre_composition_functor _ _ _ hsB hsC (pr1 FG)) (identity (pr2 FG)) =
              identity _).
    do 2 rewrite functor_id.
    apply id_left.
  - red. intros FG1 FG2 FG3 αβ1 αβ2.
    induction αβ1 as [α1 β1].
    induction αβ2 as [α2 β2].
    unfold functorial_composition_data.
    unfold functor_on_morphisms.
    unfold pr2.
    change (# (post_composition_functor _ _ _ hsB hsC (pr2 FG1)) (α1 · α2) ·
              # (pre_composition_functor _ _ _ hsB hsC (pr1 FG3)) (β1 · β2) =
              # (post_composition_functor _ _ _ hsB hsC (pr2 FG1)) α1 ·
               # (pre_composition_functor _ _ _ hsB hsC (pr1 FG2)) β1 ·
              (# (post_composition_functor _ _ _ hsB hsC (pr2 FG2)) α2 ·
                 # (pre_composition_functor _ _ _ hsB hsC (pr1 FG3)) β2)).
    repeat rewrite functor_comp.
    repeat rewrite <- assoc.
    apply maponpaths.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    (* we need the interchange between the two variants of presenting horcomp already here *)
    apply (nat_trans_eq hsC).
    intro a.
    cbn.
    apply nat_trans_ax.
Qed.

Definition functorial_composition {A B C : precategory} (hsB: has_homsets B) (hsC: has_homsets C) :
  functor (precategory_binproduct [A, B, hsB] [B, C, hsC]) [A, C, hsC].
Proof.
  exists (functorial_composition_data A B C hsB hsC).
  apply is_functor_functorial_composition_data.
Defined.

Goal ∏ (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C)
      (F G : precategory_binproduct_data [A, B, hsB] [B, C, hsC])
      (αβ : precategory_binproduct_data [A, B, hsB] [B, C, hsC] ⟦ F, G ⟧),
  # (functorial_composition hsB hsC) αβ =
    # (post_composition_functor _ _ _ hsB hsC (pr2 F)) (pr1 αβ) ·
      # (pre_composition_functor _ _ _ hsB hsC (pr1 G)) (pr2 αβ).
Proof.
  intros.
  apply idpath.
Qed.

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
  # (functorial_composition hsD hsE) (f,, g:precategory_binproduct [C, D, hsD] [D, E, hsE] ⟦(F,,G), (F',,G')⟧) =
  # (pre_composition_functor _ _ _ hsD hsE F) g · # (post_composition_functor _ _ _ hsD hsE G') f.
Proof.
  apply (nat_trans_eq hsE).
  intro c.
  cbn.
  apply nat_trans_ax.
Qed.

Lemma functorial_composition_post_pre (C D E: precategory) (hsD : has_homsets D) (hsE : has_homsets E)
      (F F' : [C, D, hsD]) (G G' : [D, E, hsE]) (f: [C, D, hsD]⟦F, F'⟧) (g: [D, E, hsE]⟦G, G'⟧) :
  # (functorial_composition hsD hsE) (f,, g:precategory_binproduct [C, D, hsD] [D, E, hsE] ⟦(F,,G), (F',,G')⟧) =
  # (post_composition_functor _ _ _ hsD hsE G) f · # (pre_composition_functor _ _ _ hsD hsE F') g.
Proof.
  apply idpath.
Defined. (* this seems justified not to be ended with Qed *)

Corollary functorial_composition_legacy_ok {A B C : precategory} (hsB: has_homsets B) (hsC: has_homsets C):
  functorial_composition_legacy A B C hsB hsC = functorial_composition(A:=A) hsB hsC.
Proof.
  apply functor_eq; try apply (functor_category_has_homsets A C hsC).
  cbn.
  use functor_data_eq.
  - intro FG. apply idpath.
  - intros FG1 FG2 αβ.
    cbn.
    apply (horcomp_post_pre _ _ (C,,hsC)).
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

(** [α_functors] itself is natural *)
Section associativity.

  Context {C D E F: precategory} (hsD: has_homsets D) (hsE: has_homsets E)  (hsF: has_homsets F).

  Definition assoc_left_gen :
    precategory_binproduct(precategory_binproduct [C, D, hsD] [D, E, hsE]) [E, F, hsF] ⟶ [C, F, hsF] :=
    functor_composite (pair_functor (functorial_composition(A:=C) hsD hsE) (functor_identity _))
                      (functorial_composition hsE hsF).

  Definition assoc_right_gen :
    precategory_binproduct(precategory_binproduct [C, D, hsD] [D, E, hsE]) [E, F, hsF] ⟶ [C, F, hsF] :=
    functor_composite (precategory_binproduct_unassoc _ _ _)
            (functor_composite (pair_functor (functor_identity _) (functorial_composition hsE hsF)) (functorial_composition hsD hsF)).

Local Lemma is_nat_trans_a_functors: is_nat_trans assoc_left_gen assoc_right_gen
  (λ F : (C ⟶ D × D ⟶ E) × E ⟶ F, α_functors (pr1 (pr1 F)) (pr2 (pr1 F)) (pr2 F)).
Proof.
  intros f f' m.
  (* unfold α_functors.
  etrans; [ use id_right |].
  apply pathsinv0.
  etrans; [ use id_left |]. *)
  apply (nat_trans_eq hsF).
  intro c. cbn.
  rewrite id_right.
  rewrite id_left.
  etrans.
  { apply cancel_postcomposition. apply functor_comp. }
  rewrite assoc.
  apply idpath.
Qed.

  Definition associativity_as_nat_z_iso: nat_z_iso assoc_left_gen assoc_right_gen.
  Proof.
    exists (_,, is_nat_trans_a_functors).
    intro f1f2f3.
    apply α_functors_pointwise_is_z_iso.
  Defined.

End associativity.

Section leftunit.

  Context {C D: precategory} (hsC: has_homsets C) (hsD: has_homsets D).

  Definition lunit_left_gen : [C, D, hsD] ⟶ [C, D, hsD] := pre_composition_functor _ _ _ hsC hsD (functor_identity C).

  Local Lemma is_nat_trans_l_functors: is_nat_trans lunit_left_gen (functor_identity [C, D, hsD]) (@λ_functors C D).
Proof.
  intros F F' m.
  apply (nat_trans_eq hsD).
  intro c. cbn.
  rewrite id_left.
  apply id_right.
Qed.

  Definition left_unit_as_nat_z_iso: nat_z_iso lunit_left_gen (functor_identity [C, D, hsD]).
  Proof.
    use make_nat_z_iso.
    + use make_nat_trans.
      * intro F. apply λ_functors.
      * apply is_nat_trans_l_functors.
    + intro F. cbn.
      use nat_trafo_z_iso_if_pointwise_z_iso.
      intro c.
      use tpair.
      * exact (identity (pr1 F c)).
      * abstract ( apply Isos.is_inverse_in_precat_identity ).
  Defined.

End leftunit.
