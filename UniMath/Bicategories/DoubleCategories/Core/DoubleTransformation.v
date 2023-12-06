(**********************************************************************************

 Double Transformations

 We define double transformations between lax double functors. In addition, we give
 some examples of these, namely the examples that are needed to construct the
 bicategory of double categories.

 Contents
 1. Preservation of the identity
 2. Preservation of composition
 3. Examples of double transformations

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleFunctor.

Local Open Scope cat.

(** * 1. Preservation of the identity *)
Definition double_nat_trans_hor_id
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {F G : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           {GG : twosided_disp_functor G G D₁ D₂}
           {τ : F ⟹ G}
           (ττ : twosided_disp_nat_trans τ τ FF GG)
           {I₁ : hor_id D₁}
           {I₂ : hor_id D₂}
           (FI : double_functor_hor_id FF I₁ I₂)
           (GI : double_functor_hor_id GG I₁ I₂)
  : UU
  := ∏ (x : C₁),
     functor_double_id_cell FI x ;;2 ττ x x (double_id I₁ x)
     =
     transportb_disp_mor2
       (id_left _ @ !(id_right _))
       (id_left _ @ !(id_right _))
       (double_id_mor I₂ (τ x) ;;2 functor_double_id_cell GI x).

Proposition isaprop_double_nat_trans_hor_id
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F G : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {GG : twosided_disp_functor G G D₁ D₂}
            {τ : F ⟹ G}
            (ττ : twosided_disp_nat_trans τ τ FF GG)
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            (FI : double_functor_hor_id FF I₁ I₂)
            (GI : double_functor_hor_id GG I₁ I₂)
  : isaprop (double_nat_trans_hor_id ττ FI GI).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

(** * 2. Preservation of composition *)
Definition double_nat_trans_hor_comp
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {F G : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           {GG : twosided_disp_functor G G D₁ D₂}
           {τ : F ⟹ G}
           (ττ : twosided_disp_nat_trans τ τ FF GG)
           {Cm₁ : hor_comp D₁}
           {Cm₂ : hor_comp D₂}
           (FC : double_functor_hor_comp FF Cm₁ Cm₂)
           (GC : double_functor_hor_comp GG Cm₁ Cm₂)
  : UU
  := ∏ (x y z : C₁)
       (h : D₁ x y)
       (k : D₁ y z),
     functor_double_comp_cell FC h k
     ;;2
     ττ _ _ (double_hor_comp Cm₁ h k)
     =
     transportb_disp_mor2
       (id_left _ @ !(id_right _))
       (id_left _ @ !(id_right _))
       (double_hor_comp_mor Cm₂ (ττ _ _ h) (ττ _ _ k)
        ;;2
        functor_double_comp_cell GC h k).

Proposition isaprop_double_nat_trans_hor_comp
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F G : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {GG : twosided_disp_functor G G D₁ D₂}
            {τ : F ⟹ G}
            (ττ : twosided_disp_nat_trans τ τ FF GG)
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            (FC : double_functor_hor_comp FF Cm₁ Cm₂)
            (GC : double_functor_hor_comp GG Cm₁ Cm₂)
  : isaprop (double_nat_trans_hor_comp ττ FC GC).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

(** * 3. Examples of double transformations *)
Proposition id_twosided_disp_nat_trans_hor_id
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            (FI : double_functor_hor_id FF I₁ I₂)
  : double_nat_trans_hor_id (id_twosided_disp_nat_trans FF) FI FI.
Proof.
  intros x ; cbn.
  rewrite double_id_mor_id.
  rewrite id_two_disp_left.
  rewrite id_two_disp_right.
  rewrite transport_b_b_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition comp_twosided_disp_nat_trans_hor_id
            {C₁ C₂ : category}
            {F F' F'' : C₁ ⟶ C₂}
            {τ : F ⟹ F'}
            {τ' : F' ⟹ F''}
            {D : twosided_disp_cat C₁ C₁}
            {D' : twosided_disp_cat C₂ C₂}
            {FF : twosided_disp_functor F F D D'}
            {FF' : twosided_disp_functor F' F' D D'}
            {FF'' : twosided_disp_functor F'' F'' D D'}
            {ττ : twosided_disp_nat_trans τ τ FF FF'}
            {ττ' : twosided_disp_nat_trans τ' τ' FF' FF''}
            {I : hor_id D}
            {I' : hor_id D'}
            {FFI : double_functor_hor_id FF I I'}
            {FFI' : double_functor_hor_id FF' I I'}
            {FFI'' : double_functor_hor_id FF'' I I'}
            (ττI : double_nat_trans_hor_id ττ FFI FFI')
            (ττI' : double_nat_trans_hor_id ττ' FFI' FFI'')
  : double_nat_trans_hor_id
      (comp_twosided_disp_nat_trans ττ ττ')
      FFI
      FFI''.
Proof.
  intros x ; cbn.
  etrans.
  {
    rewrite assoc_two_disp.
    rewrite (ττI x).
    rewrite two_disp_pre_whisker_b.
    rewrite transport_b_b_disp_mor2.
    rewrite assoc_two_disp_alt.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite (ττI' x).
    rewrite two_disp_post_whisker_b.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    apply idpath.
  }
  refine (!_).
  rewrite double_id_mor_id_comp.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition pre_whisker_twosided_disp_nat_trans_hor_id
            {C₁ C₂ C₃ : category}
            {F : C₁ ⟶ C₂}
            {G G' : C₂ ⟶ C₃}
            {τ : G ⟹ G'}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {FF : twosided_disp_functor F F D₁ D₂}
            {GG : twosided_disp_functor G G D₂ D₃}
            {GG' : twosided_disp_functor G' G' D₂ D₃}
            {ττ : twosided_disp_nat_trans τ τ GG GG'}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            {I₃ : hor_id D₃}
            (FFI : double_functor_hor_id FF I₁ I₂)
            {GGI : double_functor_hor_id GG I₂ I₃}
            {GGI' : double_functor_hor_id GG' I₂ I₃}
            (ττI : double_nat_trans_hor_id ττ GGI GGI')
  : double_nat_trans_hor_id
      (pre_whisker_twosided_disp_nat_trans FF ττ)
      (comp_hor_id FFI GGI)
      (comp_hor_id FFI GGI').
Proof.
  intros x ; cbn.
  etrans.
  {
    rewrite two_disp_pre_whisker_f.
    rewrite assoc_two_disp_alt.
    rewrite transport_f_f_disp_mor2.
    rewrite (pr2 ττ).
    rewrite two_disp_post_whisker_b.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (ττI (F x)).
    }
    rewrite two_disp_pre_whisker_b.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp_alt.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    rewrite two_disp_post_whisker_f.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    apply idpath.
  }
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition post_whisker_twosided_disp_nat_trans_hor_id
            {C₁ C₂ C₃ : category}
            {F F' : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {τ : F ⟹ F'}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {FF : twosided_disp_functor F F D₁ D₂}
            {FF' : twosided_disp_functor F' F' D₁ D₂}
            {GG : twosided_disp_functor G G D₂ D₃}
            {ττ : twosided_disp_nat_trans τ τ FF FF'}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            {I₃ : hor_id D₃}
            {FFI : double_functor_hor_id FF I₁ I₂}
            {FFI' : double_functor_hor_id FF' I₁ I₂}
            (GGI : double_functor_hor_id GG I₂ I₃)
            (ττI : double_nat_trans_hor_id ττ FFI FFI')
  : double_nat_trans_hor_id
      (post_whisker_twosided_disp_nat_trans GG ττ)
      (comp_hor_id FFI GGI)
      (comp_hor_id FFI' GGI).
Proof.
  intros x ; cbn.
  etrans.
  {
    rewrite two_disp_pre_whisker_f.
    rewrite assoc_two_disp_alt.
    rewrite transport_f_f_disp_mor2.
    rewrite twosided_disp_functor_comp_alt.
    rewrite two_disp_post_whisker_f.
    rewrite transport_f_f_disp_mor2.
    rewrite (ττI x).
    rewrite transportb_twosided_disp_functor.
    rewrite two_disp_post_whisker_b.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite twosided_disp_functor_comp.
    rewrite two_disp_post_whisker_b.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    unfold transportb.
    rewrite two_disp_post_whisker_f.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (functor_double_id_eq GGI (τ x)).
    }
    rewrite two_disp_pre_whisker_b.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    apply idpath.
  }
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition lunitor_twosided_disp_nat_trans_hor_id
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            (FI : double_functor_hor_id FF I₁ I₂)
  : double_nat_trans_hor_id
      (id_twosided_disp_nat_trans _)
      (comp_hor_id (identity_hor_id _) FI)
      FI.
Proof.
  intros x ; cbn.
  rewrite double_id_mor_id.
  rewrite id_two_disp_left.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_right.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite twosided_disp_functor_id.
  rewrite two_disp_post_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite id_two_disp_right.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition runitor_twosided_disp_nat_trans_hor_id
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            (FI : double_functor_hor_id FF I₁ I₂)
  : double_nat_trans_hor_id
      (id_twosided_disp_nat_trans _)
      (comp_hor_id FI (identity_hor_id _))
      FI.
Proof.
  intros x ; cbn.
  rewrite double_id_mor_id.
  rewrite id_two_disp_left.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite id_two_disp_right.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite id_two_disp_left.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition linvunitor_twosided_disp_nat_trans_hor_id
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            (FI : double_functor_hor_id FF I₁ I₂)
  : double_nat_trans_hor_id
      (id_twosided_disp_nat_trans _)
      FI
      (comp_hor_id (identity_hor_id _) FI).
Proof.
  intros x ; cbn.
  rewrite double_id_mor_id.
  rewrite id_two_disp_left.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_right.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite twosided_disp_functor_id.
  rewrite two_disp_post_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite id_two_disp_right.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition rinvunitor_twosided_disp_nat_trans_hor_id
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            (FI : double_functor_hor_id FF I₁ I₂)
  : double_nat_trans_hor_id
      (id_twosided_disp_nat_trans _)
      FI
      (comp_hor_id FI (identity_hor_id _)).
Proof.
  intros x ; cbn.
  rewrite double_id_mor_id.
  rewrite id_two_disp_left.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite id_two_disp_right.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite id_two_disp_left.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition rassociator_twosided_disp_nat_trans_hor_id
            {C₁ C₂ C₃ C₄ : category}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {H : C₃ ⟶ C₄}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {D₄ : twosided_disp_cat C₄ C₄}
            {FF : twosided_disp_functor F F D₁ D₂}
            {GG : twosided_disp_functor G G D₂ D₃}
            {HH : twosided_disp_functor H H D₃ D₄}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            {I₃ : hor_id D₃}
            {I₄ : hor_id D₄}
            (FI : double_functor_hor_id FF I₁ I₂)
            (GI : double_functor_hor_id GG I₂ I₃)
            (HI : double_functor_hor_id HH I₃ I₄)
  : double_nat_trans_hor_id
      (id_twosided_disp_nat_trans
         (comp_twosided_disp_functor
            _
            (comp_twosided_disp_functor _ _)))
      (comp_hor_id (comp_hor_id FI GI) HI)
      (comp_hor_id FI (comp_hor_id GI HI)).
Proof.
  intros x ; cbn.
  rewrite transportf_twosided_disp_functor.
  rewrite !two_disp_post_whisker_f.
  rewrite !two_disp_pre_whisker_f.
  rewrite !two_disp_post_whisker_f.
  unfold transportb_disp_mor2.
  rewrite !transport_f_f_disp_mor2.
  rewrite id_two_disp_right.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite double_id_mor_id.
  rewrite id_two_disp_left.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite twosided_disp_functor_comp.
  unfold transportb_disp_mor2.
  rewrite !two_disp_post_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition lassociator_twosided_disp_nat_trans_hor_id
            {C₁ C₂ C₃ C₄ : category}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {H : C₃ ⟶ C₄}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {D₄ : twosided_disp_cat C₄ C₄}
            {FF : twosided_disp_functor F F D₁ D₂}
            {GG : twosided_disp_functor G G D₂ D₃}
            {HH : twosided_disp_functor H H D₃ D₄}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            {I₃ : hor_id D₃}
            {I₄ : hor_id D₄}
            (FI : double_functor_hor_id FF I₁ I₂)
            (GI : double_functor_hor_id GG I₂ I₃)
            (HI : double_functor_hor_id HH I₃ I₄)
  : double_nat_trans_hor_id
      (id_twosided_disp_nat_trans
         (comp_twosided_disp_functor
            _
            (comp_twosided_disp_functor _ _)))
      (comp_hor_id FI (comp_hor_id GI HI))
      (comp_hor_id (comp_hor_id FI GI) HI).
Proof.
  intros x ; cbn.
  rewrite transportf_twosided_disp_functor.
  rewrite !two_disp_post_whisker_f.
  rewrite !two_disp_pre_whisker_f.
  unfold transportb_disp_mor2.
  rewrite !transport_f_f_disp_mor2.
  rewrite id_two_disp_right.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite double_id_mor_id.
  rewrite id_two_disp_left.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite twosided_disp_functor_comp.
  unfold transportb_disp_mor2.
  rewrite !two_disp_post_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition id_twosided_disp_nat_trans_hor_comp
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            (FC : double_functor_hor_comp FF Cm₁ Cm₂)
  : double_nat_trans_hor_comp (id_twosided_disp_nat_trans FF) FC FC.
Proof.
  intros x y z h k ; cbn.
  rewrite double_hor_comp_mor_id.
  rewrite id_two_disp_left.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_right.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition comp_twosided_disp_nat_trans_hor_comp
            {C₁ C₂ : category}
            {F F' F'' : C₁ ⟶ C₂}
            {τ : F ⟹ F'}
            {τ' : F' ⟹ F''}
            {D : twosided_disp_cat C₁ C₁}
            {D' : twosided_disp_cat C₂ C₂}
            {FF : twosided_disp_functor F F D D'}
            {FF' : twosided_disp_functor F' F' D D'}
            {FF'' : twosided_disp_functor F'' F'' D D'}
            {ττ : twosided_disp_nat_trans τ τ FF FF'}
            {ττ' : twosided_disp_nat_trans τ' τ' FF' FF''}
            {Cm : hor_comp D}
            {Cm' : hor_comp D'}
            {FFC : double_functor_hor_comp FF Cm Cm'}
            {FFC' : double_functor_hor_comp FF' Cm Cm'}
            {FFC'' : double_functor_hor_comp FF'' Cm Cm'}
            (ττC : double_nat_trans_hor_comp ττ FFC FFC')
            (ττC' : double_nat_trans_hor_comp ττ' FFC' FFC'')
  : double_nat_trans_hor_comp
      (comp_twosided_disp_nat_trans ττ ττ')
      FFC
      FFC''.
Proof.
  intros x y z h k ; cbn.
  rewrite assoc_two_disp.
  rewrite (ττC x).
  rewrite two_disp_pre_whisker_b.
  rewrite transport_b_b_disp_mor2.
  rewrite assoc_two_disp_alt.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  unfold transportb.
  rewrite (ττC' x).
  rewrite two_disp_post_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite double_hor_comp_mor_comp.
  rewrite assoc_two_disp_alt.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition pre_whisker_twosided_disp_nat_trans_hor_comp
            {C₁ C₂ C₃ : category}
            {F : C₁ ⟶ C₂}
            {G G' : C₂ ⟶ C₃}
            {τ : G ⟹ G'}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {FF : twosided_disp_functor F F D₁ D₂}
            {GG : twosided_disp_functor G G D₂ D₃}
            {GG' : twosided_disp_functor G' G' D₂ D₃}
            {ττ : twosided_disp_nat_trans τ τ GG GG'}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {Cm₃ : hor_comp D₃}
            (FFC : double_functor_hor_comp FF Cm₁ Cm₂)
            {GGC : double_functor_hor_comp GG Cm₂ Cm₃}
            {GGC' : double_functor_hor_comp GG' Cm₂ Cm₃}
            (ττC : double_nat_trans_hor_comp ττ GGC GGC')
  : double_nat_trans_hor_comp
      (pre_whisker_twosided_disp_nat_trans FF ττ)
      (comp_hor_comp FFC GGC)
      (comp_hor_comp FFC GGC').
Proof.
  intros x y z h k ; cbn.
  rewrite two_disp_pre_whisker_b.
  rewrite two_disp_post_whisker_b.
  rewrite transport_b_b_disp_mor2.
  rewrite assoc_two_disp_alt.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite (pr2 ττ).
  rewrite two_disp_post_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite ττC.
  rewrite two_disp_pre_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp_alt.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition post_whisker_twosided_disp_nat_trans_hor_comp
            {C₁ C₂ C₃ : category}
            {F F' : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {τ : F ⟹ F'}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {FF : twosided_disp_functor F F D₁ D₂}
            {FF' : twosided_disp_functor F' F' D₁ D₂}
            {GG : twosided_disp_functor G G D₂ D₃}
            {ττ : twosided_disp_nat_trans τ τ FF FF'}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {Cm₃ : hor_comp D₃}
            {FFC : double_functor_hor_comp FF Cm₁ Cm₂}
            {FFC' : double_functor_hor_comp FF' Cm₁ Cm₂}
            (GGC : double_functor_hor_comp GG Cm₂ Cm₃)
            (ττC : double_nat_trans_hor_comp ττ FFC FFC')
  : double_nat_trans_hor_comp
      (post_whisker_twosided_disp_nat_trans GG ττ)
      (comp_hor_comp FFC GGC)
      (comp_hor_comp FFC' GGC).
Proof.
  intros x y z h k ; cbn.
  rewrite two_disp_pre_whisker_b.
  rewrite assoc_two_disp_alt.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite twosided_disp_functor_comp_alt.
  rewrite two_disp_post_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite (ττC x y z h k).
  rewrite transportb_twosided_disp_functor.
  rewrite two_disp_post_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite twosided_disp_functor_comp.
  rewrite two_disp_post_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite two_disp_post_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite (functor_double_comp_eq GGC _ _).
  unfold transportb_disp_mor2.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition lunitor_twosided_disp_nat_trans_hor_comp
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            (FI : double_functor_hor_comp FF Cm₁ Cm₂)
  : double_nat_trans_hor_comp
      (id_twosided_disp_nat_trans _)
      (comp_hor_comp (identity_hor_comp _) FI)
      FI.
Proof.
  intros x y z h k ; cbn.
  rewrite double_hor_comp_mor_id.
  rewrite two_disp_pre_whisker_b.
  rewrite id_two_disp_right.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_left.
  rewrite transport_b_b_disp_mor2.
  rewrite twosided_disp_functor_id.
  rewrite two_disp_post_whisker_b.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_right.
  rewrite transport_b_b_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition runitor_twosided_disp_nat_trans_hor_comp
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            (FC : double_functor_hor_comp FF Cm₁ Cm₂)
  : double_nat_trans_hor_comp
      (id_twosided_disp_nat_trans _)
      (comp_hor_comp FC (identity_hor_comp _))
      FC.
Proof.
  intros x y z h k ; cbn.
  rewrite double_hor_comp_mor_id.
  rewrite two_disp_pre_whisker_b.
  rewrite id_two_disp_right.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_left.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_left.
  rewrite transport_b_b_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition linvunitor_twosided_disp_nat_trans_hor_comp
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            (FC : double_functor_hor_comp FF Cm₁ Cm₂)
  : double_nat_trans_hor_comp
      (id_twosided_disp_nat_trans _)
      FC
      (comp_hor_comp (identity_hor_comp _) FC).
Proof.
  intros x y z h k ; cbn.
  rewrite double_hor_comp_mor_id.
  rewrite two_disp_post_whisker_b.
  rewrite id_two_disp_right.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_left.
  rewrite transport_b_b_disp_mor2.
  rewrite twosided_disp_functor_id.
  rewrite two_disp_post_whisker_b.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_right.
  rewrite transport_b_b_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition rinvunitor_twosided_disp_nat_trans_hor_comp
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            (FC : double_functor_hor_comp FF Cm₁ Cm₂)
  : double_nat_trans_hor_comp
      (id_twosided_disp_nat_trans _)
      FC
      (comp_hor_comp FC (identity_hor_comp _)).
Proof.
  intros x y z h k ; cbn.
  rewrite double_hor_comp_mor_id.
  rewrite two_disp_post_whisker_b.
  rewrite id_two_disp_right.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_left.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_left.
  rewrite transport_b_b_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition rassociator_twosided_disp_nat_trans_hor_comp
            {C₁ C₂ C₃ C₄ : category}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {H : C₃ ⟶ C₄}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {D₄ : twosided_disp_cat C₄ C₄}
            {FF : twosided_disp_functor F F D₁ D₂}
            {GG : twosided_disp_functor G G D₂ D₃}
            {HH : twosided_disp_functor H H D₃ D₄}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {Cm₃ : hor_comp D₃}
            {Cm₄ : hor_comp D₄}
            (FC : double_functor_hor_comp FF Cm₁ Cm₂)
            (GC : double_functor_hor_comp GG Cm₂ Cm₃)
            (HC : double_functor_hor_comp HH Cm₃ Cm₄)
  : double_nat_trans_hor_comp
      (id_twosided_disp_nat_trans
         (comp_twosided_disp_functor
            _
            (comp_twosided_disp_functor _ _)))
      (comp_hor_comp (comp_hor_comp FC GC) HC)
      (comp_hor_comp FC (comp_hor_comp GC HC)).
Proof.
  intros x y z h k ; cbn.
  rewrite transportb_twosided_disp_functor.
  rewrite two_disp_post_whisker_b.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_right.
  rewrite transport_b_b_disp_mor2.
  rewrite two_disp_post_whisker_b.
  rewrite two_disp_pre_whisker_b.
  rewrite two_disp_post_whisker_b.
  rewrite !transport_b_b_disp_mor2.
  rewrite double_hor_comp_mor_id.
  rewrite id_two_disp_left.
  rewrite transport_b_b_disp_mor2.
  rewrite twosided_disp_functor_comp.
  rewrite two_disp_post_whisker_b.
  rewrite transport_b_b_disp_mor2.
  rewrite assoc_two_disp.
  rewrite transport_b_b_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition lassociator_twosided_disp_nat_trans_hor_comp
            {C₁ C₂ C₃ C₄ : category}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {H : C₃ ⟶ C₄}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {D₄ : twosided_disp_cat C₄ C₄}
            {FF : twosided_disp_functor F F D₁ D₂}
            {GG : twosided_disp_functor G G D₂ D₃}
            {HH : twosided_disp_functor H H D₃ D₄}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {Cm₃ : hor_comp D₃}
            {Cm₄ : hor_comp D₄}
            (FC : double_functor_hor_comp FF Cm₁ Cm₂)
            (GC : double_functor_hor_comp GG Cm₂ Cm₃)
            (HC : double_functor_hor_comp HH Cm₃ Cm₄)
  : double_nat_trans_hor_comp
      (id_twosided_disp_nat_trans
         (comp_twosided_disp_functor
            _
            (comp_twosided_disp_functor _ _)))
      (comp_hor_comp FC (comp_hor_comp GC HC))
      (comp_hor_comp (comp_hor_comp FC GC) HC).
Proof.
  intros x y z h k ; cbn.
  rewrite transportb_twosided_disp_functor.
  rewrite two_disp_post_whisker_b.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_right.
  rewrite transport_b_b_disp_mor2.
  rewrite two_disp_post_whisker_b.
  rewrite two_disp_pre_whisker_b.
  rewrite two_disp_post_whisker_b.
  rewrite !transport_b_b_disp_mor2.
  rewrite double_hor_comp_mor_id.
  rewrite id_two_disp_left.
  rewrite transport_b_b_disp_mor2.
  rewrite twosided_disp_functor_comp.
  rewrite two_disp_post_whisker_b.
  rewrite transport_b_b_disp_mor2.
  rewrite assoc_two_disp.
  rewrite transport_b_b_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.
