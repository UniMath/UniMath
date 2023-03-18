(** the constituents of the bicategory of categories without using the package [Bicategories];
    all is expressed with reference to the functor categories

this is useful for developments that are inspired by bicategorical insights but that are spelt out
in elementary form, so as to avoid dependency on the package [Bicategories], in particular used
in examples of whiskered monoidal categories and actegories and in the package [SubstitutionSystems]

author: Ralph Matthes 2023
*)

Require Import UniMath.Foundations.PartD.


Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.


Definition id1_CAT (C : category) : [C, C] := functor_identity C.

(** the data of a [prebicat_2_id_comp_struct] *)
Definition id2_CAT {C D : category} (F : [C, D]) : [C, D]⟦F, F⟧ := nat_trans_id (F : functor _ _).

Definition lunitor_CAT {C D : category} (F : [C, D])
  : [C, D]⟦functor_compose (id1_CAT C) F, F⟧
  := nat_trans_id (F : functor _ _).

Definition runitor_CAT {C D : category} (F : [C, D])
  : [C, D]⟦functor_compose F (id1_CAT D), F⟧
  := nat_trans_id (F : functor _ _).

Definition linvunitor_CAT {C D : category} (F : [C, D])
  : [C, D]⟦F, functor_compose (id1_CAT C) F⟧
  := nat_trans_id (F : functor _ _).

Definition rinvunitor_CAT {C D : category} (F : [C, D])
  : [C, D]⟦F, functor_compose F (id1_CAT D)⟧
  := nat_trans_id (F : functor _ _).

Definition lassociator_CAT {C D E F : category} (X : [C, D]) (Y : [D, E]) (Z : [E, F]) :
    [C, F] ⟦functor_compose X (functor_compose Y Z), functor_compose (functor_compose X Y) Z⟧
    := nat_trans_id (functor_composite X (functor_composite Y Z)).

Definition rassociator_CAT {C D E F : category} (X : [C, D]) (Y : [D, E]) (Z : [E, F]) :
    [C, F] ⟦functor_compose (functor_compose X Y) Z, functor_compose X (functor_compose Y Z)⟧
    := nat_trans_id (functor_composite (functor_composite X Y) Z).

Definition vcomp2_CAT {C D : category} {F G H : [C, D]} : [C,D]⟦F, G⟧ -> [C,D]⟦G, H⟧ -> [C,D]⟦F, H⟧.
Proof.
  intros α β. exact (nat_trans_comp _ _ _ α β).
Defined.

Definition lwhisker_CAT {C D E : category} (F : [C, D]) {G1 G2 : [D, E]}
  : [D, E]⟦G1, G2⟧ -> [C, E]⟦functor_compose F G1, functor_compose F G2⟧.
Proof.
  intro α. exact (pre_whisker (F : functor _ _) α).
Defined.

Definition rwhisker_CAT {C D E : category} {F1 F2 : [C, D]} (G : [D, E])
  : [C, D]⟦F1, F2⟧ -> [C, E]⟦functor_compose F1 G, functor_compose F2 G⟧.
Proof.
  intro α. exact (post_whisker α (G : functor _ _)).
Defined.

(** the proofs required in [prebicat_laws] *)

Lemma id2_left_CAT {C D : category} {F G : [C, D]} (α : [C, D]⟦F, G⟧) :
  id2_CAT F · α = α.
Proof.
  apply id_left.
Qed.

Lemma id2_right_CAT {C D : category} {F G : [C, D]} (α : [C, D]⟦F, G⟧) :
  α · id2_CAT G = α.
Proof.
  apply id_right.
Qed.

Lemma vassocr_CAT {C D : category} {F G H K : [C, D]}
  (α : [C, D]⟦F, G⟧) (β : [C, D]⟦G, H⟧)(γ : [C, D]⟦H, K⟧) :
  α · (β · γ) = (α · β) · γ.
Proof.
  apply assoc.
Qed.

Lemma lwhisker_id2_CAT {C D E : category} (F : [C, D]) (G : [D, E]) :
  lwhisker_CAT F (id2_CAT G) = id2_CAT _.
Proof.
  apply pre_whisker_identity.
Qed.

Lemma id2_rwhisker_CAT {C D E : category} (F : [C, D]) (G : [D, E]) :
  rwhisker_CAT G (id2_CAT F) = id2_CAT _.
Proof.
  apply post_whisker_identity.
Qed.

Lemma lwhisker_vcomp_CAT {C D E : category} (F : [C, D]) (G H I : [D, E])
  (α : [D, E]⟦G, H⟧) (β : [D, E]⟦H, I⟧) :
  lwhisker_CAT F α · lwhisker_CAT F β = lwhisker_CAT F (α · β).
Proof.
  apply pathsinv0, pre_whisker_composition.
Qed.

Lemma rwhisker_vcomp_CAT {C D E : category} (F G H : [C, D]) (I : [D, E])
  (α : [C, D]⟦F, G⟧) (β : [C, D]⟦G, H⟧) :
  rwhisker_CAT I α · rwhisker_CAT I β = rwhisker_CAT I (α · β).
Proof.
  apply pathsinv0, post_whisker_composition.
Qed.

Lemma vcomp_lunitor_CAT {C D : category} {F G : [C, D]} (α : [C, D]⟦F, G⟧) :
  lwhisker_CAT (id1_CAT C) α · lunitor_CAT G = lunitor_CAT F · α.
Proof.
  apply (nat_trans_eq D); intro c.
  rewrite id_left; apply id_right.
Qed.

Lemma vcomp_runitor_CAT {C D : category} {F G : [C, D]} (α : [C, D]⟦F, G⟧) :
  rwhisker_CAT (id1_CAT D) α · runitor_CAT G = runitor_CAT F · α.
Proof.
  apply (nat_trans_eq D); intro c.
  cbn.
  rewrite id_left. apply id_right.
Qed.

Lemma lwhisker_lwhisker_CAT {A B C D : category} {F : [A, B]} {G : [B, C]} {H I : [C, D]}
  (α : [C, D]⟦H, I⟧) :
  lwhisker_CAT F (lwhisker_CAT G α) · lassociator_CAT _ _ _ =
    lassociator_CAT _ _ _ · lwhisker_CAT (functor_compose F G) α.
Proof.
  apply (nat_trans_eq D); intro c.
  cbn.
  rewrite id_left; apply id_right.
Qed.

Lemma rwhisker_lwhisker_CAT {A B C D : category} {F : [A, B]} {G H : [B, C]} {I : [C, D]}
  (α : [B, C]⟦G, H⟧) :
  lwhisker_CAT F (rwhisker_CAT I α) · lassociator_CAT _ _ _ =
    lassociator_CAT _ _ _ · rwhisker_CAT I (lwhisker_CAT F α).
Proof.
  apply (nat_trans_eq D); intro c.
  cbn.
  rewrite id_left; apply id_right.
Qed.

Lemma rwhisker_rwhisker_CAT {A B C D : category} {F G : [A, B]} {H : [B, C]} {I : [C, D]}
  (α : [A, B]⟦F, G⟧) :
  lassociator_CAT _ _ _ ·  rwhisker_CAT I (rwhisker_CAT H α) =
    rwhisker_CAT (functor_compose H I) α · lassociator_CAT _ _ _.
Proof.
  apply (nat_trans_eq D); intro c.
  cbn.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Lemma vcomp_whisker_CAT {A B C : category} {F G : [A, B]} {H I : [B, C]}
  (α : [A, B]⟦F, G⟧) (β : [B, C]⟦H, I⟧) :
  rwhisker_CAT H α · lwhisker_CAT G β = lwhisker_CAT F β · rwhisker_CAT I α.
Proof.
  apply (nat_trans_eq C); intro c.
  apply (pr2 β).
Qed.

Lemma lunitor_linvunitor_CAT {C D : category} (F : [C, D]) :
  lunitor_CAT F · linvunitor_CAT _ = id2_CAT _.
Proof.
  apply (nat_trans_eq D); intro c.
  apply id_right.
Qed.

Lemma linvunitor_lunitor_CAT {C D : category} (F : [C, D]) :
  linvunitor_CAT F · lunitor_CAT _ = id2_CAT _.
Proof.
  apply (nat_trans_eq D); intro c.
  apply id_right.
Qed.

Lemma runitor_rinvunitor_CAT {C D : category} (F : [C, D]) :
  runitor_CAT F · rinvunitor_CAT _ = id2_CAT _.
Proof.
  apply (nat_trans_eq D); intro c.
  apply id_right.
Qed.

Lemma rinvunitor_runitor_CAT {C D : category} (F : [C, D]) :
  rinvunitor_CAT F · runitor_CAT _ = id2_CAT _.
Proof.
  apply (nat_trans_eq D); intro c.
  apply id_right.
Qed.

Lemma lassociator_rassociator_CAT {C D E F : category} (X : [C, D]) (Y : [D, E]) (Z : [E, F]) :
  lassociator_CAT X Y Z · rassociator_CAT _ _ _ = id2_CAT _.
Proof.
  apply (nat_trans_eq F); intro c.
  apply id_right.
Qed.

Lemma rassociator_lassociator_CAT {C D E F : category} (X : [C, D]) (Y : [D, E]) (Z : [E, F]) :
  rassociator_CAT X Y Z · lassociator_CAT _ _ _ = id2_CAT _.
Proof.
  apply (nat_trans_eq F); intro c.
  apply id_right.
Qed.

(* [id1_CAT B] is needed in the following formulation, an underscore is not accepted *)
Lemma runitor_rwhisker_CAT {A B C : category} (F : [A, B]) (G : [B, C]) :
  lassociator_CAT F (id1_CAT B) G · (rwhisker_CAT G (runitor_CAT F)) =
    lwhisker_CAT F (lunitor_CAT G).
Proof.
  apply (nat_trans_eq C); intro c.
  cbn.
  rewrite id_left.
  apply functor_id.
Qed.

Lemma lassociator_lassociator_CAT {A B C D E : category}
  (F : [A, B]) (G : [B, C]) (H : [C, D]) (I : [D, E]) :
  lwhisker_CAT F (lassociator_CAT G H I) · lassociator_CAT _ (functor_compose G H)  _ ·
    (rwhisker_CAT I (lassociator_CAT _ _ _)) =
    lassociator_CAT F G (functor_compose H I) · lassociator_CAT (functor_compose F G) _ _.
Proof.
  apply (nat_trans_eq E); intro c.
  cbn.
  do 3 rewrite id_left.
  apply functor_id.
Qed.

(** now for convenience *)
Lemma lunitor_CAT_pointwise_is_z_iso {C D : category} (F : [C, D]) :
  is_z_isomorphism (lunitor_CAT F).
Proof.
  exists (linvunitor_CAT F).
  split.
  - apply lunitor_linvunitor_CAT.
  - apply linvunitor_lunitor_CAT.
Defined.

Lemma runitor_CAT_pointwise_is_z_iso {C D : category} (F : [C, D]) :
  is_z_isomorphism (runitor_CAT F).
Proof.
  exists (rinvunitor_CAT F).
  split.
  - apply runitor_rinvunitor_CAT.
  - apply rinvunitor_runitor_CAT.
Defined.

Definition lassociator_CAT_pointwise_is_z_iso {C D E F : category} (X : functor C D)(Y : functor D E)(Z : functor E F) :
  is_z_isomorphism (lassociator_CAT X Y Z).
Proof.
  exists (rassociator_CAT X Y Z).
  split.
  - apply lassociator_rassociator_CAT.
  - apply rassociator_lassociator_CAT.
Defined.

(** laws that are instances of derivable rules in bicategories; here, we just prove them directly *)

Lemma lwhisker_lwhisker_rassociator_CAT {A B C D : category} {F : [A, B]} {G : [B, C]} {H I : [C, D]}
  (α : [C, D]⟦H, I⟧) :
   rassociator_CAT _ _ _ · lwhisker_CAT F (lwhisker_CAT G α) =
    lwhisker_CAT (functor_compose F G) α · rassociator_CAT _ _ _ .
Proof.
  apply (nat_trans_eq D); intro c.
  cbn.
  rewrite id_right; apply id_left.
Qed.

Lemma rwhisker_lwhisker_rassociator_CAT {A B C D : category} {F : [A, B]} {G H : [B, C]} {I : [C, D]}
  (α : [B, C]⟦G, H⟧) :
  rassociator_CAT _ _ _ · lwhisker_CAT F (rwhisker_CAT I α) =
    rwhisker_CAT I (lwhisker_CAT F α) · rassociator_CAT _ _ _.
Proof.
  apply (nat_trans_eq D); intro c.
  cbn.
  rewrite id_right; apply id_left.
Qed.

Lemma rwhisker_rwhisker_alt_CAT {A B C D : category} {F : [B, A]} {G : [C, B]} {H I : [D, C]}
  (α : [D, C]⟦H, I⟧) :
  rwhisker_CAT F (rwhisker_CAT G α) · rassociator_CAT _ _ _ =
    rassociator_CAT _ _ _ · rwhisker_CAT (functor_compose G F) α.
Proof.
  apply (nat_trans_eq A); intro d.
  cbn.
  rewrite id_left; apply id_right.
Qed.

Lemma lunitor_lwhisker_CAT {A B C : category} (F : [A, B]) (G : [B, C]) :
  rassociator_CAT F (id1_CAT B) G · (lwhisker_CAT F (lunitor_CAT G)) =
    rwhisker_CAT G (runitor_CAT F).
Proof.
  apply (nat_trans_eq C); intro c.
  cbn.
  rewrite id_left.
  apply pathsinv0, functor_id.
Qed.

Lemma rassociator_rassociator_CAT {A B C D E : category}
  (F : [A, B]) (G : [B, C]) (H : [C, D]) (I : [D, E]) :
  rwhisker_CAT I (rassociator_CAT F G H) · rassociator_CAT _ (functor_compose G H)  _ ·
    (lwhisker_CAT F (rassociator_CAT _ _ _)) =
    rassociator_CAT (functor_compose F G) H I · rassociator_CAT F G (functor_compose H I).
Proof.
  apply (nat_trans_eq E); intro c.
  cbn.
  do 3 rewrite id_right.
  apply functor_id.
Qed.
