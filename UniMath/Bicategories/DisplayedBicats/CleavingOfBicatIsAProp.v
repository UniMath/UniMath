Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Opposite.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.StrictPseudoFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.EquivalenceBetweenCartesians.

Local Open Scope cat.

Section DispLocallyUnivalent.
  Context {B : bicat}
          (D : disp_bicat B)
          {x y : B}
          {f : x --> y}
          {xx : D x}
          {yy : D y}
          (ff₁ ff₂ : xx -->[ f ] yy).

  Definition disp_inv2cell_to_disp_iso
    : disp_invertible_2cell (id2_invertible_2cell f) ff₁ ff₂
      →
      @iso_disp _ (disp_hom xx yy) _ _ (identity_iso _) ff₁ ff₂.
  Proof.
    intro α.
    simple refine (@make_iso_disp _ (disp_hom xx yy) _ _ _ _ _ _ _).
    - exact (pr1 α).
    - simple refine (_ ,, _ ,, _).
      + exact (disp_inv_cell α).
      + abstract
          (refine (disp_vcomp_linv α @ _) ; cbn ;
           apply maponpaths_2 ;
           apply cellset_property).
      + abstract
          (refine (disp_vcomp_rinv α @ _) ; cbn ;
           apply maponpaths_2 ;
           apply cellset_property).
  Defined.

  Definition disp_iso_to_disp_inv2cell
    : @iso_disp _ (disp_hom xx yy) _ _ (identity_iso _) ff₁ ff₂
      →
      disp_invertible_2cell (id2_invertible_2cell f) ff₁ ff₂.
  Proof.
    intro α.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (pr1 α).
    - exact (inv_mor_disp_from_iso α).
    - abstract
        (cbn ;
         refine (pr222 α @ _) ;
         apply maponpaths_2 ;
         apply cellset_property).
    - abstract
        (cbn ;
         refine (pr122 α @ _) ;
         apply maponpaths_2 ;
         apply cellset_property).
  Defined.

  Definition disp_inv2cell_weq_disp_iso
    : disp_invertible_2cell (id2_invertible_2cell f) ff₁ ff₂
      ≃
      @iso_disp _ (disp_hom xx yy) _ _ (identity_iso _) ff₁ ff₂.
  Proof.
    use make_weq.
    - exact disp_inv2cell_to_disp_iso.
    - use gradth.
      + exact disp_iso_to_disp_inv2cell.
      + abstract
          (intro α ;
           use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
           apply idpath).
      + abstract
          (intro α ;
           use subtypePath ; [ intro ; apply isaprop_is_iso_disp | ] ;
           apply idpath).
  Defined.
End DispLocallyUnivalent.

Definition is_univalent_disp_disp_hom
           {B : bicat}
           (D : disp_bicat B)
           (HD : disp_univalent_2_1 D)
           {x y : B}
           (xx : D x)
           (yy : D y)
  : is_univalent_disp (disp_hom xx yy).
Proof.
  intros f g p ff gg.
  induction p.
  use weqhomot.
  - exact (disp_inv2cell_weq_disp_iso D _ _
           ∘ make_weq _ (HD x y f f (idpath _) xx yy ff gg))%weq.
  - abstract
      (intro p ;
       induction p ;
       use subtypePath ; [ intro ; apply isaprop_is_iso_disp | ] ;
       apply idpath).
Defined.

Definition isaprop_local_cleaving
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (D : disp_bicat B)
           (HD : disp_univalent_2_1 D)
  : isaprop (local_cleaving D).
Proof.
  use (isofhlevelweqb 1 (local_fib_weq_local_cleaving D)).
  use impred ; intro x.
  use impred ; intro y.
  use impred ; intro xx.
  use impred ; intro yy.
  use (@isaprop_cleaving (univ_hom HB x y)).
  use is_univalent_disp_disp_hom.
  exact HD.
Defined.

Definition isaprop_local_opcleaving
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (D : disp_bicat B)
           (HD : disp_univalent_2_1 D)
  : isaprop (local_opcleaving D).
Proof.
  use (isofhlevelweqb 1 (local_opfib_weq_local_opcleaving D)).
  unfold local_opfib.
  use impred ; intro x.
  use impred ; intro y.
  use impred ; intro xx.
  use impred ; intro yy.
  use (isofhlevelweqb 1 (opcleaving_weq_cleaving _)).
  use (@isaprop_cleaving (op_unicat (univ_hom HB x y))).
Admitted.

Definition eq_cartesian_lift
           {B : bicat}
           (D : disp_bicat B)
           {x y : B}
           {yy : D y}
           {f : x --> y}
           (ℓ₁ ℓ₂ : ∑ (xx : D x) (ff : xx -->[ f ] yy), cartesian_1cell D ff)
           (p₁ : pr1 ℓ₁ = pr1 ℓ₂)
           (p₂ : transportf (λ z, z -->[ f ] yy) p₁ (pr12 ℓ₁) = pr12 ℓ₂)
  : ℓ₁ = ℓ₂.
Proof.
  induction ℓ₁ as [ xx₁ [ ff₁ Hff₁ ]].
  induction ℓ₂ as [ xx₂ [ ff₂ Hff₂ ]].
  cbn in *.
  induction p₁ ; cbn in *.
  induction p₂ ; cbn in *.
  do 2 apply maponpaths.
  unfold cartesian_1cell in Hff₁.
Admitted.

(*
Definition eq_cartesian_lift_from_iso
           {B : bicat}
           (D : disp_bicat B)
           {x y : B}
           {yy : D y}
           {f : x --> y}
           (ℓ₁ ℓ₂ : ∑ (xx : D x) (ff : xx -->[ f ] yy), cartesian_1cell D ff)
           (p₁ : pr1 ℓ₁ = pr1 ℓ₂)
           (p₂ : transportf (λ z, z -->[ f ] yy) p₁ (pr12 ℓ₁) = pr12 ℓ₂)
  : ℓ₁ = ℓ₂.
*)

Definition isaprop_global_cleaving
           {B : bicat}
           (HB : is_univalent_2 B)
           (D : disp_bicat B)
           (HD : disp_univalent_2 D)
  : isaprop (global_cleaving D).
Proof.
  use impred ; intro x.
  use impred ; intro y.
  use impred ; intro xx.
  use impred ; intro f.
  use invproofirrelevance.
  intros ℓ₁ ℓ₂.
  use total2_paths_f.
  - admit.
  - use total2_paths_f.
    +
