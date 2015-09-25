Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functor_categories.
Require Import UnicodeNotations.
Require Import UniMath.RezkCompletion.whiskering.
Require Import UniMath.RezkCompletion.equivalences.
Require Import SubstSystems.Auxiliary.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G ∙ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).


Section HomSetIso_from_Adjunction.

Variables C D : precategory.
Variable F : functor C D.
Variable H : is_left_adjoint F.

Let G := right_adjoint H.
Let η := eta_from_left_adjoint H.
Let ε := eps_from_left_adjoint H.

Definition φ_adj {A : C} {B : D} : F A ⇒ B → A ⇒ G B 
  := λ f : F A ⇒ B, η _ ;; #G f.

Definition φ_adj_inv {A : C} {B : D} : A ⇒ G B → F A ⇒ B
  := λ g : A ⇒ G B, #F g ;; ε _ .

Lemma φ_adj_after_φ_adj_inv {A : C} {B : D} (g : A ⇒ G B) 
  : φ_adj (φ_adj_inv g) = g.
Proof.
  unfold φ_adj.
  unfold φ_adj_inv.
  assert (X':=triangle_id_right_ad _ _ _ H).
  rewrite functor_comp.
  rewrite assoc.
  assert (X2 := nat_trans_ax η). simpl in X2.
  rewrite <- X2; clear X2.
  rewrite <- assoc.
  pathvia (g ;; identity _).
  - apply maponpaths.
    apply X'.
  - apply id_right.
Qed.

Lemma φ_adj_inv_after_φ_adj {A : C} {B : D} (f : F A ⇒ B)
  : φ_adj_inv (φ_adj f) = f.
Proof.
  unfold φ_adj, φ_adj_inv.
  rewrite functor_comp.
  assert (X2 := nat_trans_ax ε); simpl in *.
  rewrite <- assoc.
  rewrite X2; clear X2.
  rewrite assoc.
  pathvia (identity _ ;; f).
  - apply cancel_postcomposition.
    apply triangle_id_left_ad.
  - apply id_left.
Qed.  

Definition adjunction_hom_weq (A : C) (B : D) : F A ⇒ B ≃ A ⇒ G B.
Proof.
  exists φ_adj.
  apply (gradth _ φ_adj_inv).
  - apply φ_adj_inv_after_φ_adj.
  - apply φ_adj_after_φ_adj_inv.
Defined.


Lemma φ_adj_natural_precomp (A : C) (B : D) (f : F A ⇒ B) (X : C) (h : X ⇒ A)
  : φ_adj (#F h ;; f) = h ;; φ_adj f.
Proof.
  unfold φ_adj.
  rewrite functor_comp.
  set (T:=nat_trans_ax η); simpl in T.
  rewrite assoc.
  rewrite <- T.
  apply pathsinv0, assoc.
Qed.

Lemma φ_adj_natural_postcomp (A : C) (B : D) (f : F A ⇒ B) (Y : D) (k : B ⇒ Y)
  : φ_adj (f ;; k) = φ_adj f ;; #G k.
Proof.
  unfold φ_adj.
  rewrite <- assoc.
  apply maponpaths.
  apply (functor_comp G).
Qed.

Lemma φ_adj_inv_natural_precomp (A : C) (B : D) (g : A ⇒ G B) (X : C) (h : X ⇒ A)
  : φ_adj_inv (h ;; g) = #F h ;; φ_adj_inv g.
Proof.
  unfold φ_adj_inv.
  rewrite functor_comp.
  apply pathsinv0, assoc.
Qed.

Lemma φ_adj_inv_natural_postcomp (A : C) (B : D) (g : A ⇒ G B) (Y : D) (k : B ⇒ Y)
  : φ_adj_inv (g ;; #G k) = φ_adj_inv g ;; k.
Proof.
  unfold φ_adj_inv.
  rewrite functor_comp.
  set (T:=nat_trans_ax ε); simpl in T.
  rewrite <- assoc.
  rewrite T.
  apply assoc.
Qed.

End HomSetIso_from_Adjunction.







