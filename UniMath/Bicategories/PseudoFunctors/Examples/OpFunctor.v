(* ******************************************************************************* *)
(** The opposite of a category as a pseudofunctor
 ********************************************************************************* *)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.

Local Open Scope cat.


Definition TODO {A : UU} : A.
Admitted.

Definition functor_identity_op
           (C : category)
  : functor_identity (C^op)
    ⟹
    functor_opp (functor_identity C).
Proof.
  use make_nat_trans.
  - exact (λ x, identity x).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition functor_comp_op
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₂ ⟶ C₃)
  : functor_opp F ∙ functor_opp G ⟹ functor_opp (F ∙ G).
Proof.
  use make_nat_trans.
  - exact (λ x, identity _).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Local Notation "∁" := bicat_of_univ_cats.

Definition op_psfunctor_data : psfunctor_data (op2_bicat ∁) ∁.
Proof.
  use make_psfunctor_data.
  - exact (λ C, op_unicat C).
  - exact (λ _ _ f, functor_opp f).
  - exact (λ _ _ _ _ x, op_nt x).
  - exact (λ C, functor_identity_op _).
  - exact (λ _ _ _ F G, functor_comp_op F G).
Defined.

Definition op_psfunctor_laws : psfunctor_laws op_psfunctor_data.
Proof.
  repeat split.
  - intros C D F. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat D) )|].
    intro. apply idpath.
  - intros C D F G H α β ; cbn in *.
    apply nat_trans_eq ; [apply (homset_property (op_cat D) )|].
    intro x ; cbn in *.
    apply idpath.
  - intros C D F. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat D) )|].
    intro. cbn. apply pathsinv0.
    rewrite !id_left.
    apply functor_id.
  - intros C D F. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat D) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros C1 C2 C3 C4 F G H. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat C4) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite !id_right.
    rewrite functor_id.
    apply idpath.
  - intros C1 C2 C3  F G H alpha. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat C3) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite id_right.
    apply idpath.
  - intros C1 C2 C3 F1 F2 F3 α ; cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat C3) )|].
    intros x ; cbn.
    rewrite id_left, id_right.
    apply idpath.
Qed.

Definition op_psfunctor_invertible_cells
  : invertible_cells op_psfunctor_data.
Proof.
  split.
  - intro C.
    use is_nat_iso_to_is_invertible_2cell.
    intro.
    apply identity_is_iso.
  - intros C₁ C₂ C₃ F G.
    use is_nat_iso_to_is_invertible_2cell.
    intro.
    apply identity_is_iso.
Defined.

Definition op_psfunctor : psfunctor (op2_bicat ∁) ∁.
Proof.
  use make_psfunctor.
  - exact op_psfunctor_data.
  - exact op_psfunctor_laws.
  - exact op_psfunctor_invertible_cells.
Defined.
