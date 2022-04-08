(* ******************************************************************************* *)
(** * Bicategory of 1-categories

    Benedikt Ahrens, Marco Maggesi

    February 2018

a variant by Ralph Matthes in 2021 without asking for univalence of the object

 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.


(*
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.HorizontalComposition.
*)
Local Open Scope cat.

Definition cat_prebicat_nouniv_data
  : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact category.
  - exact (λ C D, functor C D).
  - exact (λ _ _ F G, nat_trans F G).
  - exact (λ C, functor_identity C).
  - exact (λ _ _ _ F G, functor_composite F G).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ _ _ _ α β, nat_trans_comp _ _ _ α β).
  - exact (λ _ _ _ F _ _ α, pre_whisker F α).
  - exact (λ _ _ _ _ _ H α, post_whisker α H).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ _ _ _ _ _, nat_trans_id _).
  - exact (λ _ _ _ _ _ _ _, nat_trans_id _).
Defined.

Lemma cat_prebicat_nouniv_laws : prebicat_laws cat_prebicat_nouniv_data.
Proof.
  repeat split; cbn.
  - intros C D F G η.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F G η.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_right.
  - intros C D F₁ F₂ F₃ F₄ α β γ.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply assoc.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply C₃.
    intro; apply idpath.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    apply functor_id.
  - intros C₁ C₂ C₃ F G₁ G₂ G₃ α β.
    apply nat_trans_eq; try apply C₃.
    intro; apply idpath.
  - intros C₁ C₂ C₃ F₁ F₂ F₃ G α β.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    exact (!(functor_comp G _ _)).
  - intros C D F G α.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    rewrite id_left, id_right.
    apply idpath.
  - intros C D F G α.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    rewrite id_left, id_right.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G H₁ H₂ α.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    rewrite id_left, id_right.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G₁ G₂ H α.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    rewrite id_left, id_right.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ G H α.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    rewrite id_left, id_right.
    apply idpath.
  - intros C₁ C₂ C₃ F₁ F₂ G₁ H₂ α β.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    exact ((nat_trans_ax β _ _ _)).
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    exact (id_left _ @ functor_id G _).
  - intros C₁ C₂ C₃ C₄ C₅ F₁ F₂ F₃ F₄.
    apply nat_trans_eq; try apply C₅.
    intros ; cbn.
    rewrite !id_left.
    exact (functor_id F₄ _).
Qed.

Definition prebicat_of_cats : prebicat := _ ,, cat_prebicat_nouniv_laws.

Lemma isaset_cells_prebicat_of_cats : isaset_cells prebicat_of_cats.
Proof.
  intros a b f g.
  apply isaset_nat_trans.
  apply homset_property.
Defined.

Definition bicat_of_cats : bicat
  := (prebicat_of_cats ,, isaset_cells_prebicat_of_cats).

Definition is_invertible_2cell_to_is_nat_iso
           {C D : bicat_of_cats}
           {F G : C --> D}
           (η : F ==> G)
  : is_invertible_2cell η → is_nat_iso η.
Proof.
  intros Hη X.
  use is_iso_qinv.
  - apply (Hη^-1).
  - abstract
      (split ; cbn ;
       [ exact (nat_trans_eq_pointwise (vcomp_rinv Hη) X)
       | exact (nat_trans_eq_pointwise (vcomp_linv Hη) X) ]).
Defined.

Definition invertible_2cell_to_nat_iso
           {C D : bicat_of_cats}
           (F G : C --> D)
  : invertible_2cell F G → nat_iso F G.
Proof.
  intros η.
  use make_nat_iso.
  - exact (cell_from_invertible_2cell η).
  - apply is_invertible_2cell_to_is_nat_iso.
    apply η.
Defined.

Definition is_nat_iso_to_is_invertible_2cell
           {C D : bicat_of_cats}
           {F G : C --> D}
           (η : F ==> G)
  : is_nat_iso η → is_invertible_2cell η.
Proof.
  intros Hη.
  use tpair.
  - apply (nat_iso_inv (η ,, Hη)).
  - abstract
      (split ;
       [ apply nat_trans_eq ; [ apply homset_property | ] ;
         intros x ; cbn ;
         exact (iso_inv_after_iso (pr1 η x ,, _))
       | apply nat_trans_eq ; [ apply homset_property | ] ;
         intros x ; cbn ;
         exact (iso_after_iso_inv (pr1 η x ,, _)) ]).
Defined.

Definition nat_iso_to_invertible_2cell
           {C D : bicat_of_cats}
           (F G : C --> D)
  : nat_iso F G → invertible_2cell F G.
Proof.
  intros η.
  use tpair.
  - apply η.
  - apply is_nat_iso_to_is_invertible_2cell.
    apply η.
Defined.

Definition invertible_2cell_is_nat_iso
           {C D : bicat_of_cats}
           (F G : C --> D)
  : nat_iso F G ≃ invertible_2cell F G.
Proof.
  use make_weq.
  - exact (nat_iso_to_invertible_2cell F G).
  - use isweq_iso.
    + exact (invertible_2cell_to_nat_iso F G).
    + intros X.
      use subtypePath.
      * intro.
        apply isaprop_is_nat_iso.
      * apply idpath.
    + intros X.
      use subtypePath.
      * intro.
        apply isaprop_is_invertible_2cell.
      * apply idpath.
Defined.

Local Definition CAT : bicat := bicat_of_cats.

Local Definition lwhisker := @lwhisker CAT.

Local Lemma pre_whisker_as_lwhisker (A B C: category) (F: A ⟶ B)(G H: B ⟶ C)(γ: G ⟹ H):
  pre_whisker F γ = lwhisker A B C F G H γ.
Proof.
  apply idpath.
Qed.

Local Definition rwhisker := @rwhisker CAT.

Local Lemma post_whisker_as_rwhisker (B C D: category) (G H: B ⟶ C) (γ: G ⟹ H) (K: C ⟶ D):
  post_whisker γ K = rwhisker B C D G H K γ.
Proof.
  apply idpath.
Qed.

Local Definition hcomp := @hcomp CAT.
Local Definition hcomp' := @hcomp' CAT.

(** demonstrates the mismatch: [horcomp] only corresponds to [hcomp'] *)
Local Lemma horcomp_as_hcomp'_pointwise (C D E : category) (F F' : C ⟶ D) (G G' : D ⟶ E) (α : F ⟹ F') (β: G ⟹ G'):
  horcomp α β = hcomp' C D E F F' G G' α β.
Proof.
  apply (nat_trans_eq (homset_property E)).
  intro c.
  apply idpath.
Qed.

Local Definition hcomp_functor_data := @hcomp_functor_data CAT.
Local Definition hcomp_functor := @hcomp_functor CAT.

(** no more mismatch when using [functorial_composition] *)
Local Lemma functorial_composition_as_hcomp_functor (A B C : category):
  functorial_composition_data A B C = hcomp_functor_data A B C.
Proof.
  apply idpath.
Qed.

(** as a corollary: *)
Local Lemma functorial_composition_as_hcomp_functor_datawise (A B C : category):
  functorial_composition A B C = hcomp_functor A B C.
Proof.
  use functor_eq.
  - apply functor_category_has_homsets.
  - apply functorial_composition_as_hcomp_functor.
Qed.

Local Definition hcomp_vcomp := @hcomp_vcomp CAT.

(** here, we obtain the result by inheriting from the abstract bicategorical development *)
Lemma interchange_functorial_composition (A B C: category) (F1 G1 H1: A ⟶ B) (F2 G2 H2: B ⟶ C)
  (α1 : F1 ⟹ G1) (α2: F2 ⟹ G2) (β1: G1 ⟹ H1) (β2: G2 ⟹ H2):
  # (functorial_composition A B C)
    (catbinprodmor ((α1:(functor_category A B)⟦F1,G1⟧) · β1)
                      ((α2:(functor_category B C)⟦F2,G2⟧) · β2)) =
    # (functorial_composition A B C)
      (catbinprodmor(C:=functor_category A B)(D:=functor_category B C) α1 α2) ·
      # (functorial_composition A B C)
      (catbinprodmor(C:=functor_category A B)(D:=functor_category B C) β1 β2).
Proof.
  exact (hcomp_vcomp A B C F1 G1 H1 F2 G2 H2 α1 α2 β1 β2).
Qed.
