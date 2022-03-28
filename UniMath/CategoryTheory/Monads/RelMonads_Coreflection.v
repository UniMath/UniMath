(** **********************************************************

Contents:

- Given a coreflection F -| G : C -> D, and a monad
  relative to J : A -> C, construct a monad
  relative to FJ : A -> D
- The postcomposition map extends to monad morphisms

Benedikt Ahrens, October 2018

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monads.RelativeMonads.

Local Open Scope cat.


(** * Postcomposition of a relative monad with a coreflection *)

Section RMonad_transfer.

Context {A C D : category}
        (J : functor A C)
        (F : functor C D)
        (G : functor D C)
        (eta : nat_trans (functor_identity C) (functor_composite F G))
        (eps : nat_trans (functor_composite G F) (functor_identity D))
        (H : form_adjunction F G eta eps).

Let R : are_adjoints F G := ((eta,, eps) ,, H).
Let NHW : (natural_hom_weq F G) := nathomweq_from_adj R.

Let φ {X Y} (f : F X --> Y) : X --> G Y := hom_weq NHW f.
Let φinv {X Y} (g : X --> G Y) : F X --> Y := invweq (hom_weq NHW) g.

Hypothesis corefl : ∏ c : C, is_iso (eta c).
Let ηinv (X : C)  : G (F X) --> X := inv_from_iso (make_iso (eta X) (corefl X )).

Let ηinv_is_natural : is_nat_trans (F ∙ G) (functor_identity _ ) (fun X => ηinv X).
Proof. use is_nat_trans_inv_from_pointwise_inv. apply C. Qed.

Section RelMonad_transfer_object.

Variable (T : RelMonad_data J).

(** The new relative monad is given, on objects, by applying
   the coreflection
*)

Definition RelMonad_composed_data : RelMonad_data (J ∙ F).
Proof.
  repeat use tpair.
  - exact (λ a, F (T a)).
  - cbn. intro a. exact (#F (r_eta T _ )).
  - cbn. intros a b f.
    exact (φinv (r_bind T (φ f · ηinv _ ) · eta _ )).
Defined.

Notation "'σ'" := (r_bind T).
Notation "'v'" := (r_eta T).
Notation "'φ'" := (φ_adj R).
Notation "'φ-1'" := (φ_adj_inv R).

(** ** Proof of the monad axioms of the composed data *)

Variable (TH : RelMonad_axioms T).

Definition RelMonad_composed_axioms : RelMonad_axioms RelMonad_composed_data.
Proof.
  repeat split; intros; cbn.
  - etrans.
    apply (inv_natural_precomp NHW).
    cbn.
    rewrite <- (id_right (# F (v c))).
    etrans.
    apply maponpaths_2.
    apply maponpaths.
    apply maponpaths.
    apply maponpaths_2.
    apply (hom_natural_precomp NHW).
    cbn.
    rewrite φ_adj_identity. cbn.
    rewrite <- assoc.
    set (RT := iso_inv_after_iso (make_iso (eta _ ) (corefl (T c)))).
    cbn in RT. simpl in RT.
    etrans.
    apply maponpaths_2.
    apply maponpaths.     apply maponpaths.     apply maponpaths.
    apply RT.
    rewrite id_right.
    etrans.
    apply maponpaths. apply φ_adj_inv_unit.
    rewrite id_right.
    etrans.
    apply maponpaths.
    apply r_bind_r_eta. apply TH.
    apply functor_id.

  -  apply pathsinv0.
     etrans. 2: apply  (inv_natural_precomp NHW).
     rewrite assoc.
     apply pathsinv0.
     etrans. apply maponpaths.
     apply maponpaths_2.
     apply r_eta_r_bind; apply TH.
     etrans. apply maponpaths. rewrite <- assoc. apply maponpaths.
     apply iso_after_iso_inv.
     rewrite id_right.
     apply (homotinvweqweq (hom_weq NHW )).

  - etrans.
    apply maponpaths. apply (inv_natural_precomp NHW). cbn.
    etrans. apply maponpaths. apply maponpaths.
    apply φ_adj_inv_unit. rewrite id_right.

    etrans. apply maponpaths_2. apply (inv_natural_precomp NHW). cbn.
    etrans. apply maponpaths_2. apply maponpaths.
    apply φ_adj_inv_unit. rewrite id_right.
    etrans.
    apply pathsinv0. apply functor_comp.

    etrans.
    apply maponpaths. apply r_bind_r_bind. apply TH.

    apply pathsinv0.
    etrans.
    apply (inv_natural_precomp NHW). cbn.
    etrans. apply maponpaths.
    apply φ_adj_inv_unit. rewrite id_right.

    etrans. apply maponpaths. apply maponpaths.
    apply maponpaths_2. apply maponpaths.
    apply maponpaths.
    etrans.
    apply (inv_natural_precomp NHW). cbn.
    apply maponpaths.     apply φ_adj_inv_unit. rewrite id_right.

    apply maponpaths.
    apply maponpaths.

    etrans.
    apply maponpaths_2.
    apply (hom_natural_postcomp NHW).
    cbn.

    etrans.
    etrans. apply (!assoc _ _ _ ).
    apply maponpaths.
    apply ηinv_is_natural.
    cbn.
    apply assoc.
Qed.

End RelMonad_transfer_object.

Definition RelMonad_composed (T : RelMonad J) : RelMonad (J ∙ F)
    := RelMonad_composed_data T,, RelMonad_composed_axioms _ T.

(** ** Postcomposition of a monad morphism with a coreflection *)

Section RelMonad_transfer_morphism.

Context {T T' : RelMonad J}
        (f : RelMonadMor T T').

Notation "'σ'" := (r_bind _).
Notation "'v'" := (r_eta _).
Notation "'φ'" := (φ_adj R).
Notation "'φ-1'" := (φ_adj_inv R).


Definition RelMonadMor_composed_data
  : RelMonadMor_data (RelMonad_composed T) (RelMonad_composed T')
  := λ a, (#F (RelMonadMor_map f a)).

Lemma RelMonadMor_composed_axioms : RelMonadMor_axioms RelMonadMor_composed_data.
Proof.
  repeat split; cbn; intros.
  - unfold RelMonadMor_composed_data. cbn.
    etrans. apply (!functor_comp _ _ _ ).
    apply maponpaths. apply r_eta_α. apply f.
  - unfold RelMonadMor_composed_data. cbn.
    etrans. apply pathsinv0. apply (inv_natural_precomp NHW). cbn.
    rewrite assoc.
    etrans.
    apply (inv_natural_precomp NHW). cbn.
    etrans. apply maponpaths.
    apply φ_adj_inv_unit. rewrite id_right.
    rewrite functor_comp.

    apply pathsinv0.
    etrans. apply maponpaths_2. apply (inv_natural_precomp NHW). cbn.

    etrans. apply maponpaths_2. apply maponpaths.
    apply φ_adj_inv_unit. rewrite id_right.

    etrans. apply (!functor_comp _ _ _ ).
    etrans. apply maponpaths. apply (!(α_r_bind f) _ _ _ ).
    cbn.

    apply pathsinv0.
    etrans. apply (!functor_comp _ _ _ ).
    apply maponpaths.
    apply maponpaths. apply maponpaths.
    etrans. apply maponpaths_2. apply φ_adj_natural_postcomp.

    etrans. apply (!assoc _ _ _ ).

    etrans. apply maponpaths. apply ηinv_is_natural.
    apply assoc.
Qed.

Definition RelMonadMor_composed : RelMonadMor (RelMonad_composed T) (RelMonad_composed T')
  := RelMonadMor_composed_data ,, RelMonadMor_composed_axioms.

End RelMonad_transfer_morphism.

(** ** Postcomposing a monad with the right adjoint of a coreflection *)

Section RelMonad_transfer_radj_object.

Variable (T : RelMonad_data (J ∙ F)).

Definition RelMonad_composed_radj_data : RelMonad_data J.
Proof.
  repeat use tpair.
  - exact (λ a, G (T a)).
  - cbn. intro a. exact (φ (r_eta T _ )).
  - cbn. intros a b f.
    exact (#G (r_bind T (φ_adj_inv R f))).
Defined.

Notation "'σ'" := (r_bind T).
Notation "'v'" := (r_eta T).
Notation "'φ'" := (φ_adj R).
Notation "'φ-1'" := (φ_adj_inv R).

Variable (TH : RelMonad_axioms T).

Definition RelMonad_composed_radj_axioms : RelMonad_axioms RelMonad_composed_radj_data.
Proof.
  repeat split; intros; cbn.
  - etrans.
    do 2 apply maponpaths.
    apply φ_adj_inv_after_φ_adj.
    etrans. apply maponpaths. apply r_bind_r_eta. apply TH.
    apply functor_id.
  - etrans. apply pathsinv0. apply φ_adj_natural_postcomp.
    etrans. apply maponpaths. apply (r_eta_r_bind TH).
    apply φ_adj_after_φ_adj_inv.
  - etrans. apply (!functor_comp _ _ _ ).
    apply maponpaths.
    etrans. apply (r_bind_r_bind TH).
    apply maponpaths.
    apply pathsinv0. apply (φ_adj_inv_natural_postcomp R).
Defined.

End RelMonad_transfer_radj_object.

Definition RelMonad_composed_radj (T : RelMonad (J ∙ F)) : RelMonad J
    := RelMonad_composed_radj_data T,, RelMonad_composed_radj_axioms _ T.

(** ** Postcomposing a monad morphism with the right adjoint of a coreflection *)

Section RelMonad_transfer_radj_morphism.

Context {T T' : RelMonad (J ∙ F)}
        (f : RelMonadMor T T').

Notation "'σ'" := (r_bind _).
Notation "'v'" := (r_eta _).
Notation "'φ'" := (φ_adj R).
Notation "'φ-1'" := (φ_adj_inv R).


Definition RelMonadMor_composed_radj_data
  : RelMonadMor_data (RelMonad_composed_radj T) (RelMonad_composed_radj T')
  := λ a, (#G (RelMonadMor_map f a)).

Lemma RelMonadMor_composed_radj_axioms : RelMonadMor_axioms RelMonadMor_composed_radj_data.
Proof.
  repeat split; cbn; intros.
  - unfold RelMonadMor_composed_radj_data. cbn.
    etrans. apply pathsinv0, φ_adj_natural_postcomp .
    apply maponpaths. apply (r_eta_α f).
  - unfold RelMonadMor_composed_radj_data. cbn.
    etrans. apply (!functor_comp _ _ _ ).
    etrans. 2: { apply functor_comp. } apply maponpaths.
    etrans. apply maponpaths. apply maponpaths. apply (φ_adj_inv_natural_postcomp R).
    apply (α_r_bind f).
Qed.

Definition RelMonadMor_composed_radj : RelMonadMor (RelMonad_composed_radj T) (RelMonad_composed_radj T')
  := RelMonadMor_composed_radj_data ,, RelMonadMor_composed_radj_axioms.

End RelMonad_transfer_radj_morphism.

End RMonad_transfer.
