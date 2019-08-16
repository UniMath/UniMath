(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

 Displayed bicategory of displayed structures on 1-categories.
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Definition disp_prebicat_of_disp_cats_cat_data : disp_cat_data bicat_of_cats.
Proof.
  use tpair.
  - use tpair.
    + exact (λ C : univalent_category, disp_cat C).
    + intros C C' D D' F.
      exact (disp_functor F D D').
  - use tpair; cbn.
    + intros C D.
      apply disp_functor_identity.
    + cbn. intros C C' C'' F F' D D' D'' G G'.
      apply (disp_functor_composite G G').
Defined.

Definition disp_prebicat_of_disp_cats_1_id_comp_cells
  : disp_prebicat_1_id_comp_cells bicat_of_cats.
Proof.
  exists disp_prebicat_of_disp_cats_cat_data.
  cbn. intros C C' F F' a D D' G G'. cbn in *.
  apply (disp_nat_trans a G G').
Defined.

Definition disp_prebicat_of_disp_cats_data : disp_prebicat_data bicat_of_cats.
Proof.
  exists disp_prebicat_of_disp_cats_1_id_comp_cells.
  repeat split.
  - intros ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id F').
  - intros ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id F').
  - intros ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id F').
  - intros ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id F').
  - intros ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id F').
  - intros ? ? ? ? ? ? ? ? ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id (disp_functor_composite_data (disp_functor_composite ff gg) F')).
  - intros ? ? ? ? ? ? ? ? ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id (disp_functor_composite_data (disp_functor_composite ff gg) F')).
  - intros C D ? ? ? ? ? ? ? ? ? ? rr ss ; cbn in *.
    exact (@disp_nat_trans_comp C _ _ _ _ _ _ _ _ _ _ _ rr ss).
  - intros C₁ C₂ C₃ ? ? ? ? ? ? ? ? ? ? rr ; cbn in *.
    use tpair.
    + cbn. red. intros A AA.
      cbn.
      apply rr.
    + red. cbn. intros A B F AA BB FF.
      pose (RR := @disp_nat_trans_ax _ _ _ _ _ _ _ _ _ rr).
      etrans.
      * apply RR.
      * apply maponpaths_2. apply uip.
        apply C₃.
  - intros C₁ C₂ C₃ ? ? ? ? ? ? ? ? ? ? rr.
    use tpair.
    + cbn. red. intros A AA.
      cbn.
      apply disp_functor_on_morphisms.
      apply rr.
    + red. cbn. intros A B F AA BB FF.
      etrans.
      apply pathsinv0.
      apply (@disp_functor_comp_var (pr1 C₂ ,, _) (pr1 C₃ ,, _)).
      etrans.
      2: { apply maponpaths.
           apply (@disp_functor_comp_var (pr1 C₂ ,, _) (pr1 C₃ ,, _)). }
      apply pathsinv0.
      etrans.
      apply transport_f_f.
      etrans.
      * apply maponpaths.
        apply maponpaths.
        pose (RR := @disp_nat_trans_ax_var _ _ _ _ _ _ _ _ _ rr).
        apply RR.
      * etrans.
        apply maponpaths.
        apply (@disp_functor_transportf (pr1 C₂ ,, _) (pr1 C₃ ,, _)).
        etrans.
        apply transport_f_f.
        apply maponpaths_2. apply uip. apply C₃.
Defined.

Lemma DispBicatOfDispCats_laws : disp_prebicat_laws disp_prebicat_of_disp_cats_data.
Proof.
  repeat split ; red
  ; try (intros C₁ C₂ ; cbn in C₁, C₂ ; intros
         ; apply (@disp_nat_trans_eq (pr1 C₁ ,, _) (pr1 C₂ ,, _))
         ; intros ; apply pathsinv0; unfold transportb)
  ; try (intros C₁ C₂ C₃ ; cbn in C₁, C₂, C₃ ; intros
         ; apply (@disp_nat_trans_eq (pr1 C₁ ,, _) (pr1 C₃ ,, _))
         ; intros ; apply pathsinv0; unfold transportb)
  ; try (intros C₁ C₂ C₃ C₄ ; cbn in C₁, C₂, C₃, C₄ ; intros
         ; apply (@disp_nat_trans_eq (pr1 C₁ ,, _) (pr1 C₄ ,, _))
         ; intros ; apply pathsinv0; unfold transportb)
  ; try (intros C₁ C₂ C₃ C₄ C₅ ; cbn in C₁, C₂, C₃, C₄, C₅ ; intros
         ; apply (@disp_nat_trans_eq (pr1 C₁ ,, _) (pr1 C₅ ,, _))
         ; intros ; apply pathsinv0; unfold transportb).
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
    etrans; [
      apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    apply pathsinv0.
    etrans. apply id_left_disp.
    apply pathsinv0; unfold transportb.
    apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    apply pathsinv0.
    etrans. apply id_right_disp.
    apply pathsinv0; unfold transportb.
    apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    apply pathsinv0.
    etrans. apply assoc_disp.
    apply pathsinv0; unfold transportb.
    apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    apply transportf_set. apply homset_property.
  - cbn in C₁, C₂, C₃.
    match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    apply pathsinv0.
    etrans.
    { apply (@disp_functor_id C₂). }
    unfold transportb.
    apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    apply transportf_set. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    etrans.
    {
      apply maponpaths.
      apply (@disp_functor_comp C₂ C₃).
    }
    etrans. apply transport_f_f.
    apply transportf_set. apply C₃.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    etrans.
    {
      apply maponpaths.
      apply (@id_left_disp C₂).
    }
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply (@id_right_disp C₂).
    unfold transportb. apply maponpaths_2. apply homset_property.
      - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    etrans. apply maponpaths. apply (@id_left_disp C₂).
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply (@id_right_disp C₂).
    unfold transportb. apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    etrans.
    {
      apply maponpaths.
      apply (@id_left_disp C₄).
    }
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply (@id_right_disp C₄).
    unfold transportb. apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    etrans. apply maponpaths. apply (@id_left_disp C₄).
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply (@id_right_disp C₄).
    unfold transportb. apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    etrans. apply maponpaths. apply (@id_right_disp C₄).
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply (@id_left_disp C₄).
    unfold transportb. apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    set (RR := @disp_nat_trans_ax_var _ _ _ _ _ _ _ _ _ φφ).
    etrans. apply maponpaths. apply RR.
    etrans. apply transport_f_f.
    apply transportf_set. apply C₃.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    apply pathsinv0.
    etrans. apply (@id_right_disp C₂).
    unfold transportb. apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    apply pathsinv0.
    etrans. apply (@id_right_disp C₂).
    unfold transportb. apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    apply pathsinv0.
    etrans. apply (@id_right_disp C₂).
    unfold transportb. apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    apply pathsinv0.
    etrans. apply (@id_right_disp C₂).
    unfold transportb. apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    apply pathsinv0.
    etrans. apply (@id_right_disp C₄).
    unfold transportb. apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    apply pathsinv0.
    etrans. apply (@id_right_disp C₄).
    unfold transportb. apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    apply pathsinv0.
    etrans. apply (@id_left_disp C₃).
    etrans. apply maponpaths. apply (@disp_functor_id C₂).
    etrans. apply transport_f_f.
    apply maponpaths_2. apply homset_property.
  - match goal with |[ |-  (_ (_ ?E _ ))  _ _  = _ ] => set (XYZ := E) end;
      etrans; [
        apply (disp_nat_trans_transportf _ _ _ _ _ _ _ _  XYZ) | ].
    cbn.
    apply pathsinv0.
    etrans. apply (@assoc_disp_var C₅).
    etrans. apply maponpaths. apply (@id_left_disp C₅).
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply (@id_left_disp C₅).
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply (@disp_functor_id C₄).
    etrans. apply transport_f_f.

    apply pathsinv0.
    etrans. apply maponpaths. apply (@id_left_disp C₅).
    etrans. apply transport_f_f.
    apply maponpaths_2. apply C₅.
Qed.


Definition DispBicatOfDispCats : disp_prebicat bicat_of_cats := _ ,, DispBicatOfDispCats_laws.