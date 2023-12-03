Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.TwoCategories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Comma.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCatsLaws.
Import DoubleCatsLaws.TransportSquare.

Local Open Scope cat.
Local Open Scope double_cat.

Section Und.
  Context (C : double_cat).

  Definition underlying_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact C.
    - exact (λ x y, x -->v y).
  Defined.

  Definition underlying_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact underlying_precategory_ob_mor.
    - exact (λ x, identity_v x).
    - exact (λ x y z v w, v ·v w).
  Defined.

  Proposition underlying_precategory_laws
    : is_precategory underlying_precategory_data.
  Proof.
    use is_precategory_one_assoc_to_two.
    repeat split ; cbn.
    - intros x y v.
      apply id_v_left.
    - intros x y v.
      apply id_v_right.
    - intros w x y z v₁ v₂ v₃.
      apply assocl_v.
  Defined.

  Definition underlying_two_cat_data
    : two_cat_data.
  Proof.
    use make_two_cat_data.
    - exact underlying_precategory_data.
    - exact (λ x y v₁ v₂, square v₁ v₂ (identity_h x) (identity_h y)).
    - exact (λ x y f, id_h_square f).
    - cbn.
      refine (λ x y v₁ v₂ v₃ s₁ s₂, _).
      refine (transportf_square
                (id_v_right _ @ id_v_left _)
                (id_v_right _ @ id_v_left _)
                (linvunitor_h _ ⋆v s₁ ⋆h s₂ ⋆v lunitor_h _)).
    - exact (λ x y z v w₁ w₂ s, id_h_square v ⋆v s).
    - exact (λ x y z v₁ v₂ w s, s ⋆v id_h_square w).
  Defined.

  Definition underlying_two_cat_category
    : two_cat_category.
  Proof.
    use make_two_cat_category.
    - exact underlying_two_cat_data.
    - exact underlying_precategory_laws.
    - intros x y.
      apply isaset_ver_mor.
  Defined.

  Proposition idto2mor_underlying_two_cat
              {x y : C}
              {v₁ v₂ : x -->v y}
              (p : v₁ = v₂)
    : idto2mor (C := underlying_two_cat_data) p
      =
      transportf_square
        (idpath _)
        p
        (id_h_square v₁).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  (** We prove associativity for 2-cells with a series of lemmata *)
  Section Assoc.
    Context {x y : C}
            {v₁ v₂ v₃ v₄ : x -->v y}
            (s₁ : square v₁ v₂ (identity_h x) (identity_h y))
            (s₂ : square v₂ v₃ (identity_h x) (identity_h y))
            (s₃ : square v₃ v₄ (identity_h x) (identity_h y)).

    Local Lemma assoc_step_1
                p q
      : lassociator_h _ _ _
        ⋆v (s₁ ⋆h s₂) ⋆h s₃
        ⋆v rassociator_h _ _ _
        =
        transportf_square
          p
          q
          (s₁ ⋆h (s₂ ⋆h s₃)).
    Proof.
      rewrite <- lassociator_square'.
      rewrite transportf_square_prewhisker.
      rewrite <- square_assoc_v'.
      rewrite transportf_f_square.
      rewrite lassociator_rassociator_h.
      unfold transportb_square.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      rewrite square_id_right_v.
      unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    Qed.

    Local Lemma assoc_step_2
                p q
      : id_v_square _ ⋆h linvunitor_h _
        ⋆v (lassociator_h _ _ _
        ⋆v ((s₁ ⋆h s₂) ⋆h s₃
        ⋆v (rassociator_h _ _ _
        ⋆v id_v_square _ ⋆h lunitor_h _)))
        =
        transportf_square
          p
          q
          ((id_v_square _ ⋆h linvunitor_h _)
           ⋆v s₁ ⋆h (s₂ ⋆h s₃)
           ⋆v id_v_square _ ⋆h lunitor_h _).
    Proof.
      etrans.
      {
        apply maponpaths.
        rewrite !square_assoc_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        apply maponpaths.
        apply maponpaths_2.
        use assoc_step_1.
        - rewrite id_v_right.
          exact (!(id_v_left _)).
        - rewrite id_v_right.
          exact (!(id_v_left _)).
      }
      rewrite transportf_square_prewhisker.
      rewrite !transportf_square_postwhisker.
      rewrite transportf_f_square.
      rewrite !square_assoc_v.
      unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    Qed.

    Lemma assoc_step_3
          p q
      : linvunitor_h _ ⋆h id_v_square _
        ⋆v ((s₁ ⋆h s₂) ⋆h s₃
        ⋆v lunitor_h _ ⋆h id_v_square _)
        =
        transportf_square
          p
          q
          (id_v_square _ ⋆h linvunitor_h _
           ⋆v (lassociator_h _ _ _
           ⋆v ((s₁ ⋆h s₂) ⋆h s₃
           ⋆v (rassociator_h _ _ _
           ⋆v id_v_square _ ⋆h lunitor_h _)))).
    Proof.
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths.
        apply double_triangle_alt.
      }
      unfold transportb_square.
      rewrite !transportf_square_postwhisker.
      rewrite transportf_f_square.
      rewrite runitor_h_lunitor_h.
      rewrite !square_assoc_v.
      unfold transportb_square.
      rewrite !transportf_f_square.
      rewrite double_triangle_alt_inv.
      unfold transportb_square.
      rewrite !transportf_square_prewhisker.
      rewrite !transportf_f_square.
      use transportf_square_eq.
      rewrite linvunitor_h_rinvunitor_h.
      apply idpath.
    Qed.

    Lemma assoc_step_4
      : linvunitor_h _ ⋆h id_v_square _
        ⋆v ((s₁ ⋆h s₂) ⋆h s₃
        ⋆v lunitor_h _ ⋆h id_v_square _)
        =
        (linvunitor_h (identity_h x)
         ⋆v ((s₁ ⋆h s₂)
         ⋆v lunitor_h (identity_h y)))
        ⋆h (id_v_square _ ⋆v (s₃ ⋆v id_v_square _)).
    Proof.
      rewrite <- !comp_h_square_comp.
      apply idpath.
    Qed.

    Lemma assoc_step_5
          (p₁ : (identity_v x ·v v₁) ·v identity_v y = v₁)
          (p₃ : (identity_v x ·v v₃) ·v identity_v y = v₃)
          (p₄ : identity_v x ·v (v₄ ·v identity_v y) = v₄)
      : (transportf_square
           p₁
           p₃
           (linvunitor_h (identity_h x)
            ⋆v s₁ ⋆h s₂
            ⋆v lunitor_h (identity_h y)))
        ⋆h s₃
        =
        transportf_square
          (assocl_v _ _ _ @ p₁)
          p₄
          ((linvunitor_h (identity_h x)
            ⋆v ((s₁ ⋆h s₂)
            ⋆v lunitor_h (identity_h y)))
           ⋆h (id_v_square _ ⋆v (s₃ ⋆v id_v_square _))).
    Proof.
      rewrite square_id_left_v, square_id_right_v.
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite square_assoc_v.
      unfold transportb_square.
      rewrite !transportf_hcomp_l.
      rewrite !transportf_f_square.
      refine (!_).
      rewrite transportf_hcomp_r.
      rewrite transportf_f_square.
      use transportf_square_eq.
      use eq_hcomp_square.
      - refine (!_ @ !(id_v_right _)).
        apply id_v_left.
      - use transportf_square_eq.
        apply idpath.
      - rewrite transportf_f_square.
        rewrite transportf_square_id.
        apply idpath.
    Qed.

    Proposition underlying_two_cat_assoc
                (p₁ : (identity_v x ·v v₁) ·v identity_v y = v₁)
                (p₂ : (identity_v x ·v v₂) ·v identity_v y = v₂)
                (p₃ : (identity_v x ·v v₃) ·v identity_v y = v₃)
                (p₄ : (identity_v x ·v v₄) ·v identity_v y = v₄)
      : s₁
        ⋆h
        transportf_square
          p₂
          p₄
          (linvunitor_h (identity_h x) ⋆v s₂ ⋆h s₃ ⋆v lunitor_h (identity_h y))
        =
        (transportf_square
           p₁
           p₃
           (linvunitor_h (identity_h x) ⋆v s₁ ⋆h s₂ ⋆v lunitor_h (identity_h y)))
        ⋆h
        s₃.
    Proof.
      refine (!_).
      etrans.
      {
        use assoc_step_5.
        refine (id_v_left _ @ _).
        apply id_v_right.
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply assoc_step_4.
      }
      etrans.
      {
        apply maponpaths.
        use assoc_step_3.
        - do 2 refine (id_v_left _ @ _).
          rewrite !id_v_right.
          exact (!(id_v_left _)).
        - do 2 refine (id_v_left _ @ _).
          rewrite !id_v_right.
          exact (!(id_v_left _)).
      }
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        use assoc_step_2.
        - rewrite !id_v_right.
          refine (!_).
          apply id_v_left.
        - rewrite !id_v_right.
          refine (!_).
          apply id_v_left.
      }
      rewrite transportf_f_square.
      rewrite <- !comp_h_square_comp.
      rewrite square_id_left_v.
      rewrite square_id_right_v.
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite transportf_hcomp_l.
      rewrite !transportf_hcomp_r.
      rewrite transportf_square_id.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply maponpaths_2.
      use transportf_square_eq.
      apply idpath.
    Qed.
  End Assoc.

  Proposition underlying_two_cat_laws
    : two_cat_laws underlying_two_cat_category.
  Proof.
    repeat split ; cbn.
    - intros x y v₁ v₂ s.
      rewrite <- square_assoc_v'.
      rewrite transportf_f_square.
      rewrite lunitor_square.
      unfold transportb_square.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite linvunitor_lunitor_h.
      unfold transportb_square.
      rewrite transportf_square_prewhisker.
      rewrite transportf_f_square.
      rewrite square_id_left_v.
      unfold transportb_square.
      rewrite transportf_f_square.
      apply transportf_square_id.
    - intros x y v₁ v₂ s.
      rewrite <- square_assoc_v'.
      rewrite transportf_f_square.
      rewrite lunitor_h_runitor_h.
      rewrite runitor_square.
      unfold transportb_square.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite runitor_h_lunitor_h.
      rewrite linvunitor_lunitor_h.
      unfold transportb_square.
      rewrite transportf_square_prewhisker.
      rewrite transportf_f_square.
      rewrite square_id_left_v.
      unfold transportb_square.
      rewrite transportf_f_square.
      apply transportf_square_id.
    - intros x y v₁ v₂ v₃ v₄ s₁ s₂ s₃.
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply underlying_two_cat_assoc.
    - intros x y z v₁ v₂.
      rewrite id_h_square_comp.
      apply idpath.
    - intros x y z v₁ v₂.
      rewrite id_h_square_comp.
      apply idpath.
    - intros x y z v w₁ w₂ w₃ s₁ s₂.
      rewrite transportf_square_postwhisker.
      rewrite comp_h_square_comp.
      etrans.
      {
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite linvunitor_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        apply idpath.
      }
      rewrite <- square_assoc_v'.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros x y z v w₁ w₂ w₃ s₁ s₂.
      rewrite transportf_square_prewhisker.
      rewrite comp_h_square_comp.
      rewrite <- square_assoc_v'.
      rewrite transportf_f_square.
      rewrite <- square_assoc_v'.
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      rewrite lunitor_square.
      unfold transportb_square.
      rewrite !transportf_square_postwhisker.
      rewrite transportf_f_square.
      rewrite <- square_assoc_v'.
      rewrite transportf_f_square.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply square_assoc_v'.
      }
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros x y z v w₁ w₂ w₃ s₁ s₂.
      rewrite !comp_h_square_comp.
      etrans.
      {
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite <- square_assoc_v'.
        rewrite transportf_square_postwhisker.
        rewrite transportf_f_square.
        rewrite lunitor_square.
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite transportf_f_square.
        etrans.
        {
          do 2 apply maponpaths.
          apply square_assoc_v.
        }
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite transportf_f_square.
        rewrite lunitor_h_runitor_h.
        rewrite runitor_square.
        unfold transportb_square.
        rewrite transportf_square_prewhisker.
        rewrite transportf_square_postwhisker.
        rewrite transportf_f_square.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply square_assoc_v.
        }
        unfold transportb_square.
        rewrite transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite runitor_h_lunitor_h.
        rewrite linvunitor_lunitor_h.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite <- square_assoc_v'.
        rewrite transportf_square_postwhisker.
        rewrite transportf_f_square.
        rewrite lunitor_h_runitor_h.
        rewrite runitor_square.
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite transportf_f_square.
        etrans.
        {
          do 2 apply maponpaths.
          apply square_assoc_v.
        }
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite transportf_f_square.
        rewrite runitor_h_lunitor_h.
        rewrite lunitor_square.
        unfold transportb_square.
        rewrite transportf_square_prewhisker.
        rewrite transportf_square_postwhisker.
        rewrite transportf_f_square.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply square_assoc_v.
        }
        unfold transportb_square.
        rewrite transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite linvunitor_lunitor_h.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        apply idpath.
      }
      use transportf_square_eq.
      apply idpath.
    - intros x y v₁ v₂ s.
      rewrite !idto2mor_underlying_two_cat.
      etrans.
      {
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite transportf_hcomp_r.
        rewrite transportf_square_prewhisker.
        rewrite transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite lunitor_h_runitor_h.
        rewrite runitor_square.
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite !transportf_f_square.
        rewrite runitor_h_lunitor_h.
        rewrite linvunitor_lunitor_h.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        rewrite id_h_square_id.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite transportf_hcomp_l.
        rewrite transportf_square_prewhisker.
        rewrite transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite lunitor_square.
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite !transportf_f_square.
        rewrite linvunitor_lunitor_h.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        apply idpath.
      }
      use transportf_square_eq.
      apply idpath.
    - intros x y v₁ v₂ s.
      rewrite !idto2mor_underlying_two_cat.
      etrans.
      {
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite transportf_hcomp_r.
        rewrite transportf_square_prewhisker.
        rewrite transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite lunitor_h_runitor_h.
        rewrite runitor_square.
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite !transportf_f_square.
        rewrite runitor_h_lunitor_h.
        rewrite linvunitor_lunitor_h.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        rewrite id_h_square_id.
        rewrite square_id_right_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite transportf_hcomp_l.
        rewrite transportf_square_prewhisker.
        rewrite transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite lunitor_square.
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite !transportf_f_square.
        rewrite linvunitor_lunitor_h.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        apply idpath.
      }
      use transportf_square_eq.
      apply idpath.
    - intros x₁ x₂ x₃ x₄ u v w₁ w₂ s.
      rewrite !idto2mor_underlying_two_cat.
      etrans.
      {
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite transportf_hcomp_r.
        rewrite transportf_square_prewhisker.
        rewrite transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite lunitor_h_runitor_h.
        rewrite runitor_square.
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite !transportf_f_square.
        rewrite runitor_h_lunitor_h.
        rewrite linvunitor_lunitor_h.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite transportf_hcomp_l.
        rewrite transportf_square_prewhisker.
        rewrite transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite lunitor_square.
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite !transportf_f_square.
        rewrite linvunitor_lunitor_h.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        rewrite id_h_square_comp.
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        apply idpath.
      }
      use transportf_square_eq.
      apply idpath.
    - intros x₁ x₂ x₃ x₄ u v₁ v₂ w s.
      rewrite !idto2mor_underlying_two_cat.
      etrans.
      {
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite transportf_hcomp_r.
        rewrite transportf_square_prewhisker.
        rewrite transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite lunitor_h_runitor_h.
        rewrite runitor_square.
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite !transportf_f_square.
        rewrite runitor_h_lunitor_h.
        rewrite linvunitor_lunitor_h.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite transportf_hcomp_l.
        rewrite transportf_square_prewhisker.
        rewrite transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite lunitor_square.
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite !transportf_f_square.
        rewrite linvunitor_lunitor_h.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        apply idpath.
      }
      use transportf_square_eq.
      apply idpath.
    - intros x₁ x₂ x₃ x₄ u₁ u₂ v w s.
      rewrite !idto2mor_underlying_two_cat.
      etrans.
      {
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite transportf_hcomp_l.
        rewrite transportf_square_prewhisker.
        rewrite transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite lunitor_square.
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite !transportf_f_square.
        rewrite linvunitor_lunitor_h.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite <- square_assoc_v'.
        rewrite transportf_f_square.
        rewrite transportf_hcomp_r.
        rewrite transportf_square_prewhisker.
        rewrite transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite lunitor_h_runitor_h.
        rewrite runitor_square.
        unfold transportb_square.
        rewrite !transportf_square_postwhisker.
        rewrite !transportf_f_square.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite !transportf_f_square.
        rewrite runitor_h_lunitor_h.
        rewrite linvunitor_lunitor_h.
        unfold transportb_square.
        rewrite !transportf_square_prewhisker.
        rewrite transportf_f_square.
        rewrite square_id_left_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        rewrite id_h_square_comp.
        rewrite square_assoc_v.
        unfold transportb_square.
        rewrite transportf_f_square.
        apply idpath.
      }
      use transportf_square_eq.
      apply idpath.
  Qed.

  Definition underlying_two_precat
    : two_precat.
  Proof.
    use make_two_precat.
    - exact underlying_two_cat_category.
    - exact underlying_two_cat_laws.
  Defined.

  Definition underlying_two_cat
    : two_cat.
  Proof.
    use make_two_cat.
    - exact underlying_two_precat.
    - intros x y f g.
      apply isaset_square.
  Defined.
End Und.
