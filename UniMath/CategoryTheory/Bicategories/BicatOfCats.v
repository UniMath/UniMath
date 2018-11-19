(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.OpCellBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctor.


Open Scope cat.
Open Scope mor_disp_scope.


Definition cat_precat_ob_mor : precategory_ob_mor.
Proof.
  exists category.
  intros C D. exact (functor C D).
Defined.

Definition cat_precategory_data : precategory_data.
Proof.
  exists cat_precat_ob_mor.
  use tpair.
  - intro C. cbn in C. exact (functor_identity C).
  - cbn. intros a b c f g.
    exact (functor_composite f g).
Defined.

Definition cat_prebicat_1_id_comp_cells : prebicat_1_id_comp_cells.
Proof.
  exists cat_precategory_data.
  intros a b f g. cbn in *. exact (nat_trans f g).
Defined.

Definition cat_prebicat_data : prebicat_data.
Proof.
  exists cat_prebicat_1_id_comp_cells.
  repeat (use tpair); cbn.
  - intros a b f. exact (nat_trans_id f).
  - intros a b f. exact (nat_trans_id f).
  - intros a b f. exact (nat_trans_id f).
  - intros a b f. exact (nat_trans_id f).
  - intros a b f. exact (nat_trans_id f).
  - intros a b c d f g h. exact (nat_trans_id _).
  - intros a b c d f g h. exact (nat_trans_id _).
  - intros a b f g h x y. exact (nat_trans_comp _ _ _ x y).
  - intros a b c f g1 g2 x. exact (pre_whisker f x).
  - intros a b c f1 f2 g x. exact (post_whisker x g).
Defined.

Definition cat_prebicat_laws : prebicat_laws cat_prebicat_data.
Proof.
  repeat split; cbn.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply id_right.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply assoc.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply functor_id.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite (functor_comp i). apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite (nat_trans_ax y ). apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite (functor_id g). apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    repeat rewrite id_left. apply functor_id.
Defined.

Definition prebicat_of_cats : prebicat := _ ,, cat_prebicat_laws.

Lemma isaset_cells_prebicat_of_cats : isaset_cells prebicat_of_cats.
Proof.
  intros a b f g.
  apply isaset_nat_trans.
  apply homset_property.
Qed.

Definition bicat_of_cats : bicat
  := (prebicat_of_cats,, isaset_cells_prebicat_of_cats).



(** * The pseudofunctor op on the bicategory of categories *)

Local Notation "∁" := bicat_of_cats.

Definition op_functor_data : functor_data (op2_prebicat ∁) ∁.
Proof.
  use tpair.
  - exact (λ c, op_cat c).
  - intros c d f. exact (functor_opp f).
Defined.

Definition op_psfunctor_ob_mor_cell : psfunctor_ob_mor_cell (op2_prebicat ∁) ∁.
Proof.
  exists op_functor_data.
  intros a b f g x.
  cbn in *.
  apply (op_nt x).
Defined.

Definition op_psfunctor_cell_data : psfunctor_cell_data op_psfunctor_ob_mor_cell.
Proof.
  split; cbn.
  - intro C.
    use tpair.
    + cbn. use tpair.
      * cbn. intro. apply identity.
      * intros a b f.
        cbn in *.
        etrans. { apply id_left. } apply (! id_right _ ).
    + cbn.
      use tpair.
      * {  use tpair.
           - cbn. intro. apply identity.
           - intros a b f.
             cbn in *.
             etrans. { apply id_left. } apply (! id_right _ ).
        }
      * { split.
          - apply nat_trans_eq. apply homset_property.
            cbn. intro. apply id_left.
          - apply nat_trans_eq. apply homset_property.
            cbn. intro. apply id_left.
        }
  - intros C D E F G.
    use tpair.
    + cbn. use tpair.
      * cbn. intro. apply identity.
      * intros a b f.
        cbn in *.
        etrans. { apply id_left. } apply (! id_right _ ).
    + cbn.
      use tpair.
      * {  use tpair.
           - cbn. intro. apply identity.
           - intros a b f.
             cbn in *.
             etrans. { apply id_left. } apply (! id_right _ ).
        }
      * { split.
          - apply nat_trans_eq. apply homset_property.
            cbn. intro. apply id_left.
          - apply nat_trans_eq. apply homset_property.
            cbn. intro. apply id_left.
        }
Defined.

Definition op_psfunctor_data : psfunctor_data (op2_prebicat ∁) ∁
  := _ ,, op_psfunctor_cell_data.

Definition op_psfunctor_laws : psfunctor_laws op_psfunctor_data.
Proof.
  repeat split.
  - intros C D F. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat D) )|].
    intro. apply idpath.
  - intros C D F. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat D) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite id_right. apply functor_id.
  - intros C D F. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat D) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros C D F. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat D) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite id_right. apply functor_id.
  - intros C D F. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat D) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros C1 C2 C3 C4 F G H. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat C4) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite id_right.
    rewrite id_left. rewrite id_left.
    apply functor_id.
  - intros C1 C2 C3 C4 F G H. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat C4) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite id_right.
    rewrite id_left. rewrite id_right.
    apply functor_id.
  - intros C1 C2  F G H alpha beta. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat C2) )|].
    intro. cbn. apply idpath.
  - intros C1 C2 C3 F G1 G2 alpha. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat C3) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite id_right.
    apply idpath.
  - intros C1 C2 C3  F G H alpha. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat C3) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite id_right.
    apply idpath.
Qed.

Definition op_psfunctor : psfunctor (op2_prebicat ∁) ∁ := _ ,, op_psfunctor_laws.
