(** **********************************************************

Contents:

- Given a coreflection F -| G : C -> D, and a monad
  relative to J : A -> C, construct a monad
  relative to FJ : A -> D

Benedikt Ahrens, October 2018

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.Monads.RelativeMonads.

Local Open Scope cat.

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
Let ηinv (X : C)  : G (F X) --> X := inv_from_iso (isopair (eta X) (corefl X )).

Let ηinv_is_natural : is_nat_trans (G □ F) (functor_identity _ ) (fun X => ηinv X).
Proof. use is_nat_trans_inv_from_pointwise_inv. apply C. Qed.

Variable (T : RelMonad_data J).

Definition Foo : RelMonad_data (F □ J).
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

Variable (TH : RelMonad_axioms T).

Definition Bar : RelMonad_axioms Foo.
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
    set (RT := iso_inv_after_iso (isopair (eta _ ) (corefl (T c)))).
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

End RMonad_transfer.