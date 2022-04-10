(* ******************************************************************************* *)
(** * Pseudofunctors on bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

    Modified by: Dan Frumin, Niels van der Weide
    Based on https://github.com/nmvdw/groupoids
 ********************************************************************************* *)

(** * Pseudo functors. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.

Local Open Scope bicategory_scope.
Local Open Scope cat.

(* ----------------------------------------------------------------------------------- *)
(** ** Pseudo-functors                                                                 *)
(* ----------------------------------------------------------------------------------- *)

Definition psfunctor
           (C D : bicat)
  : UU
  := psfunctor_bicat C D.

Definition make_psfunctor_data
           {C D : bicat}
           (F₀ : C → D)
           (F₁ : ∏ {a b : C}, C⟦a,b⟧ → D⟦F₀ a, F₀ b⟧)
           (F₂ : ∏ {a b : C} {f g : C⟦a,b⟧}, f ==> g → F₁ f ==> F₁ g)
           (Fid : ∏ (a : C), identity (F₀ a) ==> F₁ (identity a))
           (Fcomp : (∏ (a b c : C) (f : a --> b) (g : b --> c),
                     F₁ f · F₁ g ==> F₁ (f · g)))
  : psfunctor_data C D.
Proof.
  exact ((F₀ ,, F₁) ,, (F₂ ,, Fid ,, Fcomp)).
Defined.

Definition make_psfunctor
           {C D : bicat}
           (F : psfunctor_data C D)
           (HF : psfunctor_laws F)
           (Fcells : invertible_cells F)
  : psfunctor C D
  := (F ,, (HF ,, Fcells)).

Coercion psfunctor_to_psfunctor_data
         {C D : bicat}
         (F : psfunctor C D)
  : psfunctor_data C D
  := pr1 F.

Definition psfunctor_on_cells
           {C D : bicat}
           (F : psfunctor C D)
           {a b : C}
           {f g : a --> b}
           (x : f ==> g)
  : #F f ==> #F g
  := pr12 (pr1 F) a b f g x.

Definition psfunctor_id
           {C D : bicat}
           (F : psfunctor C D)
           (a : C)
  : invertible_2cell (identity (F a)) (#F (identity a)).
Proof.
  refine (pr122 (pr1 F) a ,, _).
  apply F.
Defined.

Definition psfunctor_comp
           {C D : bicat}
           (F : psfunctor C D)
           {a b c : C}
           (f : a --> b)
           (g : b --> c)
  : invertible_2cell (#F f · #F g) (#F (f · g)).
Proof.
  refine (pr222 (pr1 F) a b c f g ,, _).
  apply F.
Defined.

Local Notation "'##'" := (psfunctor_on_cells).

Section Projection.
  Context {C D : bicat}.
  Variable (F : psfunctor C D).

  Definition psfunctor_id2
    : ∏ {a b : C} (f : a --> b), ##F (id2 f) = id2 (#F f)
    := pr1(pr12 F).

  Definition psfunctor_vcomp
    : ∏ {a b : C} {f g h : C⟦a, b⟧} (η : f ==> g) (φ : g ==> h),
      ##F (η • φ) = ##F η • ##F φ
    := pr12(pr12 F).

  Definition psfunctor_lunitor
    : ∏ {a b : C} (f : C⟦a, b⟧),
      lunitor (#F f)
      =
      (psfunctor_id F a ▹ #F f)
        • psfunctor_comp F (identity a) f
        • ##F (lunitor f)
    := pr122(pr12 F).

  Definition psfunctor_runitor
    : ∏ {a b : C} (f : C⟦a, b⟧),
      runitor (#F f)
      =
      (#F f ◃ psfunctor_id F b)
        • psfunctor_comp F f (identity b)
        • ##F (runitor f)
    := pr1(pr222(pr12 F)).

  Definition psfunctor_lassociator
    : ∏ {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧) ,
      (#F f ◃ psfunctor_comp F g h)
        • psfunctor_comp F f (g · h)
        • ##F (lassociator f g h)
      =
      (lassociator (#F f) (#F g) (#F h))
        • (psfunctor_comp F f g ▹ #F h)
        • psfunctor_comp F (f · g) h
    := pr12(pr222(pr12 F)).

  Definition psfunctor_lwhisker
    : ∏ {a b c : C} (f : C⟦a, b⟧) {g₁ g₂ : C⟦b, c⟧} (η : g₁ ==> g₂),
      psfunctor_comp F f g₁ • ##F (f ◃ η)
      =
      #F f ◃ ##F η • psfunctor_comp F f g₂
    := pr122(pr222(pr12 F)).

  Definition psfunctor_rwhisker
    : ∏ {a b c : C} {f₁ f₂ : C⟦a, b⟧} (g : C⟦b, c⟧) (η : f₁ ==> f₂),
      psfunctor_comp F f₁ g • ##F (η ▹ g)
      =
      ##F η ▹ #F g • psfunctor_comp F f₂ g
    := pr222(pr222(pr12 F)).
End Projection.

(** Isos are preserved *)
Definition psfunctor_is_iso
           {C D : bicat}
           (F : psfunctor C D)
           {a b : C}
           {f g : C⟦a,b⟧}
           (α : invertible_2cell f g)
  : is_invertible_2cell (##F α).
Proof.
  use tpair.
  - exact (##F (α^-1)).
  - split ; cbn
    ; rewrite <- psfunctor_vcomp, <- psfunctor_id2 ; apply maponpaths.
    + apply vcomp_rinv.
    + apply vcomp_linv.
Defined.

Section PseudoFunctorDerivedLaws.
  Context {C D : bicat}.
  Variable (F : psfunctor C D).

  Definition psfunctor_linvunitor
             {a b : C}
             (f : C⟦a, b⟧)
  : ##F (linvunitor f)
    =
    (linvunitor (#F f))
      • ((psfunctor_id F a) ▹ #F f)
      • (psfunctor_comp F _ _).
  Proof.
    rewrite !vassocl.
    cbn.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    use vcomp_move_R_Mp.
    {
      refine (psfunctor_is_iso F (linvunitor f ,, _)).
      is_iso.
    }
    cbn.
    rewrite psfunctor_lunitor ; cbn.
    rewrite <- !vassocr.
    reflexivity.
  Qed.

  Definition psfunctor_rinvunitor
             {a b : C}
             (f : C⟦a, b⟧)
    : ##F (rinvunitor f)
      =
      (rinvunitor (#F f))
        • (#F f ◃ psfunctor_id F b)
        • psfunctor_comp F _ _.
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    use vcomp_move_R_Mp.
    {
      refine (psfunctor_is_iso F (rinvunitor f ,, _)).
      is_iso.
    }
    cbn.
    rewrite psfunctor_runitor ; cbn.
    rewrite <- !vassocr.
    reflexivity.
  Qed.

  Definition psfunctor_rassociator
             {a b c d : C}
             (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
    : (psfunctor_comp F f g ▹ #F h)
        • psfunctor_comp F (f · g) h
        • ##F (rassociator f g h)
      =
      (rassociator (#F f) (#F g) (#F h))
        • (#F f ◃ psfunctor_comp F g h)
        • psfunctor_comp F f (g · h).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    use vcomp_move_R_Mp.
    { refine (psfunctor_is_iso F (rassociator f g h ,, _)).
      is_iso.
    }
    cbn.
    symmetry.
    exact (psfunctor_lassociator F f g h).
  Qed.

  Definition psfunctor_comp_natural
             {a b c : C}
             {g₁ g₂ : C⟦b,c⟧} {f₁ f₂ : C⟦a,b⟧}
             (ηg : g₁ ==> g₂) (ηf : f₁ ==> f₂)
    : psfunctor_comp F f₁ g₁ • ##F (ηf ⋆ ηg)
      =
      (##F ηf) ⋆ (##F ηg) • psfunctor_comp F f₂ g₂.
  Proof.
    unfold hcomp.
    rewrite !psfunctor_vcomp.
    rewrite !vassocr.
    rewrite !psfunctor_rwhisker.
    rewrite !vassocl.
    rewrite psfunctor_lwhisker.
    reflexivity.
  Qed.

  Definition psfunctor_F_lunitor
             {a b : C}
             (f : C⟦a, b⟧)
    : ##F (lunitor f)
      =
      ((psfunctor_comp F (identity a) f)^-1)
        • ((psfunctor_id F a)^-1 ▹ #F f)
        • lunitor (#F f).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    exact (!(psfunctor_lunitor F f)).
  Qed.

  Definition psfunctor_F_runitor
             {a b : C}
             (f : C⟦a,b⟧)
    : ##F (runitor f)
      =
      ((psfunctor_comp F f (identity b))^-1)
        • (#F f ◃ (psfunctor_id F b)^-1)
        • runitor (#F f).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    exact (!(psfunctor_runitor F f)).
  Qed.

  Definition psfunctor_lassociator_alt
             {a b c d : C}
             (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
    : (psfunctor_comp F f (g · h))
        • ##F (lassociator _ _ _)
        • (psfunctor_comp F (f · g) h)^-1
        • ((psfunctor_comp F f g)^-1 ▹ #F h)
        • rassociator _ _ _
      =
      #F f ◃ (psfunctor_comp F g h)^-1.
  Proof.
    use vcomp_move_R_Mp.
    { is_iso. }
    use vcomp_move_R_Mp.
    { is_iso. }
    use vcomp_move_R_Mp.
    { is_iso. }
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    apply (psfunctor_lassociator F f g h).
  Qed.
End PseudoFunctorDerivedLaws.

Section PseudoFunctorLocalFunctor.
  Context {B C : bicat}.
  Variable (F : psfunctor B C)
           (X Y : B).

  Definition Fmor_data
    : functor_data (hom X Y) (hom (F X) (F Y)).
  Proof.
    use make_functor_data.
    - exact (λ f, #F f).
    - exact (λ _ _ α, ##F α).
  Defined.

  Definition Fmor_is_functor
    : is_functor Fmor_data.
  Proof.
    split.
    - intros f.
      exact (psfunctor_id2 F f).
    - intros f g h α β.
      exact (psfunctor_vcomp F α β).
  Defined.

  Definition Fmor
    : hom X Y ⟶ hom (F X) (F Y).
  Proof.
    use make_functor.
    - exact Fmor_data.
    - exact Fmor_is_functor.
  Defined.

  Definition Fmor_univ
             (B_is_univalent_2_1 : is_univalent_2_1 B)
             (C_is_univalent_2_1 : is_univalent_2_1 C)
    : (univ_hom B_is_univalent_2_1 X Y)
        ⟶
        univ_hom C_is_univalent_2_1 (F X) (F Y).
  Proof.
    exact Fmor.
  Defined.

End PseudoFunctorLocalFunctor.

Section ExtendPseudoFunctor.
  Context {C D : bicat}
          (HD : is_univalent_2 D)
          (F : psfunctor C D)
          (G : ob C → ob D)
          (η : ∏ (a : C), adjoint_equivalence (F a) (G a)).


  Definition extend_psfunctor : psfunctor C D.
  Proof.
    cbn.
    pose (adjequiv_base_adjequiv_tot (ps_base_is_univalent_2_0 C D HD) (adjequiv_ps_base C D F G η) (pr211 F)) as m.
    induction m as [m1 m2].
    pose (adjequiv_base_adjequiv_tot (map1cells_is_univalent_2_0 C D HD) m2 (pr21 F)) as n.
    induction n as [n1 n2].
    pose (adjequiv_base_adjequiv_tot (psfunctor_data_is_univalent_2_0 C D HD) n2 (pr2 F)) as p.
    exact (_ ,, pr1 p).
  Defined.

End ExtendPseudoFunctor.

Definition psfunctor_preserves_adjequiv
           {C D : bicat}
           (HC : is_univalent_2_0 C)
           (HD : is_univalent_2_1 D)
           (F : psfunctor C D)
           (a b : C)
           (f : adjoint_equivalence a b)
  : left_adjoint_equivalence (#F f)
  := J_2_0 HC
           (λ a b f, left_adjoint_equivalence (#F (pr1 f)))
           (λ a0,
            left_adjequiv_invertible_2cell
              HD _ _
              (psfunctor_id F a0)
              (pr2 (internal_adjoint_equivalence_identity (F a0))))
           f.

Definition psfunctor_preserves_adjequiv'
           {C D : bicat}
           (F : psfunctor C D)
           {a b : C}
           {f : a --> b}
           (Hf : left_adjoint_equivalence f)
  : left_adjoint_equivalence (#F f).
Proof.
  use equiv_to_adjequiv.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
  - exact (#F (left_adjoint_right_adjoint Hf)).
  - exact (psfunctor_id F _
           • ##F (left_equivalence_unit_iso Hf)
           • (psfunctor_comp F _ _)^-1).
  - exact (psfunctor_comp F _ _
           • ##F (left_adjoint_counit Hf)
           • (psfunctor_id F _)^-1).
  - cbn.
    is_iso.
    + apply psfunctor_id.
    + exact (psfunctor_is_iso F (left_equivalence_unit_iso Hf)).
  - cbn.
    is_iso.
    + apply psfunctor_comp.
    + exact (psfunctor_is_iso F (left_equivalence_counit_iso Hf)).
Defined.


Definition local_equivalence
           {B₁ B₂ : bicat}
           (B₁_is_univalent_2_1 : is_univalent_2_1 B₁)
           (B₂_is_univalent_2_1 : is_univalent_2_1 B₂)
           (F : psfunctor B₁ B₂)
  : UU
  := ∏ (x y : B₁),
     @left_adjoint_equivalence
       bicat_of_univ_cats
       _ _
       (Fmor_univ
          F x y
          B₁_is_univalent_2_1
          B₂_is_univalent_2_1).

Definition essentially_surjective
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
  : hProp
  := ∀ (y : B₂), ∃ (x : B₁), adjoint_equivalence (F x) y.

Definition weak_equivalence
           {B₁ B₂ : bicat}
           (B₁_is_univalent_2_1 : is_univalent_2_1 B₁)
           (B₂_is_univalent_2_1 : is_univalent_2_1 B₂)
           (F : psfunctor B₁ B₂)
  : UU
  := local_equivalence
       B₁_is_univalent_2_1
       B₂_is_univalent_2_1
       F
     × essentially_surjective F.

Module Notations.
  Notation "'##'" := (psfunctor_on_cells).
End Notations.
