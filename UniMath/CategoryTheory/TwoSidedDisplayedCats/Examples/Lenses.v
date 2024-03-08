(**********************************************************************************

 The two-sided displayed category of lenses

 Reference for lenses:
   https://ncatlab.org/nlab/show/lens+%28in+computer+science%29

 We define the two-sided displayed category of lenses.

 Contents
 1. Definition via two-sided displayed categories
 2. Discreteness and univalence
 3. Builders and accessors
 4. Identity and composition of lenses
 5. Identity and composition laws of lenses

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.FiberwiseProduct.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.DispCatOnTwoSidedDispCat.

Local Open Scope cat.

Section Lenses.
  Context (C : category)
          (prodC : BinProducts C).

  (** * 1. Definition via two-sided displayed categories *)
  Definition twosided_disp_cat_of_lenses_get_ob_mor
    : twosided_disp_cat_ob_mor C C.
  Proof.
    simple refine (_ ,, _).
    - exact (λ s v, s --> v).
    - exact (λ s₁ s₂ v₁ v₂ g₁ g₂ f₁ f₂, g₁ · f₂ = f₁ · g₂).
  Defined.

  Definition twosided_disp_cat_of_lenses_get_id_comp
    : twosided_disp_cat_id_comp
        twosided_disp_cat_of_lenses_get_ob_mor.
  Proof.
    split.
    - intros s v g ; cbn.
      rewrite id_left, id_right.
      apply idpath.
    - intros s₁ s₂ s₃ v₁ v₂ v₃ g₁ g₂ g₃ f₁ f₂ h₁ h₂ p₁ p₂ ; cbn in *.
      rewrite !assoc.
      rewrite p₁.
      rewrite !assoc'.
      rewrite p₂.
      apply idpath.
  Qed.

  Definition twosided_disp_cat_of_lenses_get_data
    : twosided_disp_cat_data C C.
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_of_lenses_get_ob_mor.
    - exact twosided_disp_cat_of_lenses_get_id_comp.
  Defined.

  Definition twosided_disp_cat_of_lenses_get_axioms
    : twosided_disp_cat_axioms twosided_disp_cat_of_lenses_get_data.
  Proof.
    repeat split ; intro ; intros.
    - apply homset_property.
    - apply homset_property.
    - apply homset_property.
    - apply isasetaprop.
      apply homset_property.
  Qed.

  Definition twosided_disp_cat_of_lenses_get
    : twosided_disp_cat C C.
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_of_lenses_get_data.
    - exact twosided_disp_cat_of_lenses_get_axioms.
  Defined.

  Definition twosided_disp_cat_of_lenses_put_ob_mor
    : twosided_disp_cat_ob_mor C C.
  Proof.
    simple refine (_ ,, _).
    - exact (λ s v, BinProductObject _ (prodC v s) --> s).
    - exact (λ s₁ s₂ v₁ v₂ g₁ g₂ f₁ f₂,
             g₁ · f₁
             =
             BinProductOfArrows _ _ _ f₂ f₁ · g₂).
  Defined.

  Definition twosided_disp_cat_of_lenses_put_id_comp
    : twosided_disp_cat_id_comp
        twosided_disp_cat_of_lenses_put_ob_mor.
  Proof.
    split.
    - intros s v g ; cbn.
      rewrite id_right.
      assert (BinProductOfArrows C (prodC v s) (prodC v s) (identity v) (identity s)
              =
              identity _)
        as p.
      {
        refine (!_).
        use BinProductArrowUnique ; rewrite id_left, id_right ; apply idpath.
      }
      rewrite p.
      rewrite id_left.
      apply idpath.
    - intros s₁ s₂ s₃ v₁ v₂ v₃ g₁ g₂ g₃ f₁ f₂ h₁ h₂ p₁ p₂ ; cbn in *.
      rewrite !assoc.
      rewrite p₁.
      rewrite !assoc'.
      rewrite p₂.
      rewrite !assoc.
      rewrite BinProductOfArrows_comp.
      apply idpath.
  Qed.

  Definition twosided_disp_cat_of_lenses_put_data
    : twosided_disp_cat_data C C.
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_of_lenses_put_ob_mor.
    - exact twosided_disp_cat_of_lenses_put_id_comp.
  Defined.

  Definition twosided_disp_cat_of_lenses_put_axioms
    : twosided_disp_cat_axioms twosided_disp_cat_of_lenses_put_data.
  Proof.
    repeat split ; intro ; intros.
    - apply homset_property.
    - apply homset_property.
    - apply homset_property.
    - apply isasetaprop.
      apply homset_property.
  Qed.

  Definition twosided_disp_cat_of_lenses_put
    : twosided_disp_cat C C.
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_cat_of_lenses_put_data.
    - exact twosided_disp_cat_of_lenses_put_axioms.
  Defined.

  Definition twosided_disp_cat_of_lawless_lenses
    : twosided_disp_cat C C
    := prod_of_twosided_disp_cat
         twosided_disp_cat_of_lenses_get
         twosided_disp_cat_of_lenses_put.

  Definition lenses_laws
             {s v : C}
             (l : twosided_disp_cat_of_lawless_lenses s v)
    : UU
    := let g := pr1 l in
       let p := pr2 l in
       (p · g = BinProductPr1 _ _)
       ×
       (BinProductArrow _ _ g (identity s) · p = identity s)
       ×
       (BinProductOfArrows
          _
          (prodC v _)
          (prodC _ _)
          (identity v)
          p
        · p
        =
        BinProductArrow
          _ _
          (BinProductPr1 _ _)
          (BinProductPr2 _ _ · BinProductPr2 _ _)
        · p).

  Proposition isaprop_lenses_laws
              {s v : C}
              (l : twosided_disp_cat_of_lawless_lenses s v)
    : isaprop (lenses_laws l).
  Proof.
    repeat (apply isapropdirprod) ; apply homset_property.
  Qed.

  Definition disp_cat_of_lenses_laws
    : disp_cat
        (total_twosided_disp_category twosided_disp_cat_of_lawless_lenses).
  Proof.
    use (disp_full_sub).
    exact (λ x, lenses_laws (pr22 x)).
  Defined.

  Definition twosided_disp_cat_of_lenses
    : twosided_disp_cat C C
    := sigma_twosided_disp_cat
         twosided_disp_cat_of_lawless_lenses
         disp_cat_of_lenses_laws.

  (** * 2. Discreteness and univalence *)
  Proposition is_strict_twosided_disp_cat_of_lenses
    : is_strict_twosided_disp_cat twosided_disp_cat_of_lenses.
  Proof.
    intros x y ; cbn.
    use isaset_total2.
    - use isasetdirprod ; apply homset_property.
    - intro.
      apply isasetaprop.
      apply isaprop_lenses_laws.
  Qed.

  Definition lenses_get_twosided_disp_cat_is_iso
    : all_disp_mor_iso twosided_disp_cat_of_lenses_get.
  Proof.
    intro ; intros.
    simple refine (_ ,, _ ,, _) ; cbn in *.
    - refine (!_).
      use z_iso_inv_on_right.
      rewrite assoc.
      use z_iso_inv_on_left ; cbn.
      exact (!fg).
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition is_univalent_lenses_get_twosided_disp_cat
    : is_univalent_twosided_disp_cat twosided_disp_cat_of_lenses_get.
  Proof.
    intros x₁ x₂ y₁ y₂ p₁ p₂ xy₁ xy₂.
    induction p₁, p₂ ; cbn.
    use isweqimplimpl.
    - intros f.
      pose (p := pr1 f) ; cbn in p.
      rewrite id_left, id_right in p.
      exact p.
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_twosided_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition discrete_lenses_get_twosided_disp_cat
    : discrete_twosided_disp_cat twosided_disp_cat_of_lenses_get.
  Proof.
    repeat split.
    - intro ; intros.
      apply homset_property.
    - exact lenses_get_twosided_disp_cat_is_iso.
    - exact is_univalent_lenses_get_twosided_disp_cat.
  Qed.

  Definition lenses_put_twosided_disp_cat_is_iso
    : all_disp_mor_iso twosided_disp_cat_of_lenses_put.
  Proof.
    intro ; intros.
    simple refine (_ ,, _ ,, _) ; cbn in *.
    - refine (!_).
      use z_iso_inv_on_left ; cbn.
      rewrite !assoc'.
      rewrite fg.
      rewrite !assoc.
      refine (!(id_left _) @ _).
      apply maponpaths_2.
      rewrite BinProductOfArrows_comp.
      rewrite !z_iso_after_z_iso_inv.
      use BinProductArrowUnique ; rewrite id_left, id_right ; apply idpath.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition is_univalent_lenses_put_twosided_disp_cat
    : is_univalent_twosided_disp_cat twosided_disp_cat_of_lenses_put.
  Proof.
    intros x₁ x₂ y₁ y₂ p₁ p₂ xy₁ xy₂.
    induction p₁, p₂ ; cbn.
    use isweqimplimpl.
    - intros f.
      pose (p := pr1 f) ; cbn in p.
      rewrite id_right in p.
      refine (p @ _ @ id_left _).
      apply maponpaths_2.
      refine (!_).
      use BinProductArrowUnique ; rewrite id_left, id_right ; apply idpath.
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_twosided_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition discrete_lenses_put_twosided_disp_cat
    : discrete_twosided_disp_cat twosided_disp_cat_of_lenses_put.
  Proof.
    repeat split.
    - intro ; intros.
      apply homset_property.
    - exact lenses_put_twosided_disp_cat_is_iso.
    - exact is_univalent_lenses_put_twosided_disp_cat.
  Qed.

  Definition is_univalent_lenses_twosided_disp_cat
    : is_univalent_twosided_disp_cat twosided_disp_cat_of_lenses.
  Proof.
    use is_univalent_sigma_of_twosided_disp_cat.
    - use is_univalent_prod_of_twosided_disp_cat.
      + exact is_univalent_lenses_get_twosided_disp_cat.
      + exact is_univalent_lenses_put_twosided_disp_cat.
    - abstract
        (use disp_full_sub_univalent ;
         intro x ;
         repeat (apply isapropdirprod) ; apply homset_property).
  Defined.

  Definition discrete_lenses_twosided_disp_cat
    : discrete_twosided_disp_cat twosided_disp_cat_of_lenses.
  Proof.
    use discrete_sigma_twosided_disp_cat.
    - use discrete_prod_twosided_disp_cat.
      + exact discrete_lenses_get_twosided_disp_cat.
      + exact discrete_lenses_put_twosided_disp_cat.
    - abstract
        (use disp_full_sub_univalent ;
         intro x ;
         apply isaprop_lenses_laws).
    - intro ; intros.
      apply isapropunit.
    - abstract
        (intro ; intros ;
         simple refine (tt ,, _ ,, _) ; apply isapropunit).
  Defined.

  (** * 3. Builders and accessors *)
  Definition lens
             (s v : C)
    : UU
    := twosided_disp_cat_of_lenses s v.

  Definition lens_data
             (s v : C)
    : UU
    := s --> v × prodC v s --> s.

  Definition make_lens_data
             {s v : C}
             (get : s --> v)
             (put : prodC v s --> s)
    : lens_data s v
    := get ,, put.

  #[reversible=no] Coercion lens_to_data
           {s v : C}
           (l : lens s v)
    : lens_data s v
    := pr1 l.

  Definition lens_get
             {s v : C}
             (l : lens_data s v)
    : s --> v
    := pr1 l.

  Definition lens_put
             {s v : C}
             (l : lens_data s v)
    : prodC v s --> s
    := pr2 l.

  Proposition lens_put_get
              {s v : C}
              (l : lens s v)
    : lens_put l · lens_get l
      =
      BinProductPr1 _ _.
  Proof.
    exact (pr12 l).
  Qed.

  Proposition lens_get_put
              {s v : C}
              (l : lens s v)
    : BinProductArrow _ _ (lens_get l) (identity s) · lens_put l
      =
      identity s.
  Proof.
    exact (pr122 l).
  Qed.

  Proposition lens_put_put
              {s v : C}
              (l : lens s v)
    : BinProductOfArrows
        _
        (prodC v _)
        (prodC _ _)
        (identity v)
        (lens_put l)
      · lens_put l
      =
      BinProductArrow
        _ _
        (BinProductPr1 _ _)
        (BinProductPr2 _ _ · BinProductPr2 _ _)
      · lens_put l.
  Proof.
    exact (pr222 l).
  Qed.

  Definition make_lens
             {s v : C}
             (l : lens_data s v)
             (Hl : lenses_laws l)
    : lens s v.
  Proof.
    simple refine (_ ,, _).
    - exact l.
    - exact Hl.
  Defined.

  Proposition eq_lens
              {s v : C}
              (l₁ l₂ : lens s v)
              (p : lens_get l₁ = lens_get l₂)
              (q : lens_put l₁ = lens_put l₂)
    : l₁ = l₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_lenses_laws.
    }
    use pathsdirprod.
    - exact p.
    - exact q.
  Qed.

  Definition lens_mor
             {s₁ s₂ v₁ v₂ : C}
             (l₁ : lens s₁ v₁)
             (l₂ : lens s₂ v₂)
             (f : s₁ --> s₂)
             (g : v₁ --> v₂)
    : UU
    := l₁ -->[ f ][ g ] l₂.

  Definition make_lens_mor
             {s₁ s₂ v₁ v₂ : C}
             {l₁ : lens s₁ v₁}
             {l₂ : lens s₂ v₂}
             {f : s₁ --> s₂}
             {g : v₁ --> v₂}
             (p_get : lens_get l₁ · g = f · lens_get l₂)
             (p_put : lens_put l₁ · f
                      =
                      BinProductOfArrows C (prodC v₂ s₂) (prodC v₁ s₁) g f · lens_put l₂)
    : lens_mor l₁ l₂ f g
    := (p_get ,, p_put) ,, tt.

  Proposition lens_mor_get
              {s₁ s₂ v₁ v₂ : C}
              {l₁ : lens s₁ v₁}
              {l₂ : lens s₂ v₂}
              {f : s₁ --> s₂}
              {g : v₁ --> v₂}
              (fg : lens_mor l₁ l₂ f g)
    : lens_get l₁ · g = f · lens_get l₂.
  Proof.
    exact (pr11 fg).
  Qed.

  Proposition lens_mor_put
              {s₁ s₂ v₁ v₂ : C}
              {l₁ : lens s₁ v₁}
              {l₂ : lens s₂ v₂}
              {f : s₁ --> s₂}
              {g : v₁ --> v₂}
              (fg : lens_mor l₁ l₂ f g)
    : lens_put l₁ · f
      =
      BinProductOfArrows C (prodC v₂ s₂) (prodC v₁ s₁) g f · lens_put l₂.
  Proof.
    exact (pr21 fg).
  Qed.

  (** * 4. Identity and composition of lenses *)
  Definition identity_lens_data
             (x : C)
    : lens_data x x.
  Proof.
    use make_lens_data.
    - exact (identity x).
    - exact (BinProductPr1 _ _).
  Defined.

  Proposition identity_lens_laws
              (x : C)
    : lenses_laws (identity_lens_data x).
  Proof.
    repeat split ; cbn.
    - apply id_right.
    - apply BinProductPr1Commutes.
    - rewrite BinProductOfArrowsPr1.
      rewrite id_right.
      rewrite BinProductPr1Commutes.
      apply idpath.
  Qed.

  Definition identity_lens
             (x : C)
    : lens x x.
  Proof.
    use make_lens.
    - exact (identity_lens_data x).
    - exact (identity_lens_laws x).
  Defined.

  Proposition identity_lens_mor
              {x y : C}
              (f : x --> y)
    : lens_mor (identity_lens x) (identity_lens y) f f.
  Proof.
    use make_lens_mor ; cbn.
    - rewrite id_left, id_right.
      apply idpath.
    - rewrite BinProductOfArrowsPr1.
      apply idpath.
  Qed.

  Definition comp_lens_data
             {x y z : C}
             (l₁ : lens x y)
             (l₂ : lens y z)
    : lens_data x z.
  Proof.
    use make_lens_data.
    - exact (lens_get l₁ · lens_get l₂).
    - exact (BinProductArrow
               _ _
               (identity _)
                (BinProductPr2 _ _)
             · BinProductOfArrows
                 _
                 (prodC _ _) (prodC _ _)
                 (BinProductOfArrows
                    _
                    (prodC _ _) (prodC _ _)
                    (identity _)
                    (lens_get l₁)
                  · lens_put l₂)
                 (identity _)
             · lens_put l₁).
  Defined.

  Proposition comp_lens_laws
              {x y z : C}
              (l₁ : lens x y)
              (l₂ : lens y z)
    : lenses_laws (comp_lens_data l₁ l₂).
  Proof.
    repeat split ; cbn.
    - rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite lens_put_get.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite BinProductOfArrowsPr1.
        rewrite !assoc'.
        rewrite lens_put_get.
        apply idpath.
      }
      rewrite !assoc.
      rewrite !BinProductPr1Commutes.
      rewrite id_left.
      rewrite BinProductOfArrowsPr1.
      rewrite id_right.
      apply idpath.
    - rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite !postcompWithBinProductArrow.
        rewrite id_right.
        rewrite precompWithBinProductArrow.
        rewrite BinProductPr2Commutes.
        apply idpath.
      }
      refine (_ @ lens_get_put l₁).
      do 2 apply maponpaths_2.
      refine (_ @ id_right _).
      rewrite <- (lens_get_put l₂).
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !precompWithBinProductArrow.
      rewrite id_right.
      rewrite id_right.
      rewrite postcompWithBinProductArrow.
      rewrite id_left, id_right.
      apply idpath.
    - pose (p₁ := lens_put_get l₁).
      pose (p₂ := lens_put_put l₂).
      pose (p₃ := lens_put_put l₁).
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !postcompWithBinProductArrow.
        rewrite precompWithBinProductArrow.
        rewrite !postcompWithBinProductArrow.
        rewrite !id_left.
        rewrite !id_right.
        rewrite BinProductOfArrowsPr2.
        rewrite !assoc.
        rewrite precompWithBinProductArrow.
        apply maponpaths_2.
        rewrite BinProductOfArrows_comp.
        rewrite id_left.
        rewrite !assoc'.
        rewrite p₁.
        rewrite BinProductPr1Commutes.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(id_left _)).
        }
        rewrite <- BinProductOfArrows_comp.
        rewrite !assoc'.
        rewrite p₂.
        rewrite !assoc.
        rewrite precompWithBinProductArrow.
        rewrite BinProductOfArrowsPr1.
        rewrite id_right.
        rewrite !assoc.
        rewrite !BinProductOfArrowsPr2.
        rewrite !assoc'.
        rewrite BinProductOfArrowsPr2.
        apply idpath.
      }
      clear p₁ p₂.
      etrans.
      {
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(id_right _)).
        }
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (postcompWithBinProductArrow _ (prodC _ _) (prodC _ _)).
        }
        rewrite !assoc'.
        rewrite p₃.
        rewrite !assoc.
        rewrite precompWithBinProductArrow.
        rewrite !assoc.
        rewrite !BinProductPr1Commutes.
        rewrite !BinProductPr2Commutes.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !precompWithBinProductArrow.
      rewrite !postcompWithBinProductArrow.
      rewrite !id_right.
      rewrite !BinProductPr2Commutes.
      apply maponpaths_2.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !postcompWithBinProductArrow.
      rewrite id_right.
      apply idpath.
  Qed.

  Definition comp_lens
             {x y z : C}
             (l₁ : lens x y)
             (l₂ : lens y z)
    : lens x z.
  Proof.
    use make_lens.
    - exact (comp_lens_data l₁ l₂).
    - exact (comp_lens_laws l₁ l₂).
  Defined.

  Proposition comp_lens_mor
              {x₁ x₂ y₁ y₂ z₁ z₂ : C}
              {v₁ : x₁ --> x₂} {v₂ : y₁ --> y₂} {v₃ : z₁ --> z₂}
              {l₁ : lens x₁ y₁}
              {l₂ : lens y₁ z₁}
              {l₃ : lens x₂ y₂}
              {l₄ : lens y₂ z₂}
              (φ : lens_mor l₁ l₃ v₁ v₂)
              (ψ : lens_mor l₂ l₄ v₂ v₃)
    : lens_mor (comp_lens l₁ l₂) (comp_lens l₃ l₄) v₁ v₃.
  Proof.
    use make_lens_mor ; cbn.
    - rewrite !assoc'.
      rewrite (lens_mor_get ψ).
      rewrite !assoc.
      rewrite (lens_mor_get φ).
      apply idpath.
    - rewrite !assoc'.
      rewrite (lens_mor_put φ).
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !postcompWithBinProductArrow.
      rewrite !precompWithBinProductArrow.
      rewrite !postcompWithBinProductArrow.
      rewrite !id_right.
      rewrite BinProductOfArrowsPr2.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite (lens_mor_put ψ).
      rewrite !assoc.
      apply maponpaths_2.
      rewrite id_left.
      rewrite !BinProductOfArrows_comp.
      rewrite id_left, id_right.
      apply maponpaths.
      rewrite (lens_mor_get φ).
      apply idpath.
  Qed.

  (** * 5. Identity and composition laws of lenses *)
  Proposition lens_id_left
              {s v : C}
              (f : lens s v)
    : comp_lens (identity_lens s) f = f.
  Proof.
    use eq_lens ; cbn.
    - apply id_left.
    - rewrite !assoc'.
      rewrite BinProductOfArrowsPr1.
      rewrite !assoc.
      rewrite BinProductPr1Commutes.
      rewrite id_left.
      rewrite BinProductOfArrows_id.
      apply id_left.
  Qed.

  Proposition lens_id_right
              {s v : C}
              (f : lens s v)
    : comp_lens f (identity_lens v) = f.
  Proof.
    use eq_lens ; cbn.
    - apply id_right.
    - rewrite !assoc'.
      rewrite BinProductOfArrowsPr1.
      rewrite !assoc.
      rewrite postcompWithBinProductArrow.
      rewrite id_left, !id_right.
      refine (_ @ id_left _).
      apply maponpaths_2.
      rewrite <- BinProductOfArrows_id.
      unfold BinProductOfArrows.
      rewrite !id_right.
      apply idpath.
  Qed.

  Proposition lens_assoc
              {w x y z : C}
              (f : lens w x)
              (g : lens x y)
              (h : lens y z)
    : comp_lens f (comp_lens g h) = comp_lens (comp_lens f g) h.
  Proof.
    use eq_lens ; cbn.
    - rewrite assoc.
      apply idpath.
    - rewrite !postcompWithBinProductArrow.
      rewrite !assoc.
      rewrite !id_left, !id_right.
      apply maponpaths_2.
      rewrite !precompWithBinProductArrow.
      rewrite !BinProductOfArrowsPr2.
      rewrite BinProductPr2Commutes.
      apply maponpaths_2.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !postcompWithBinProductArrow.
      apply maponpaths_2.
      rewrite id_right.
      apply maponpaths_2.
      rewrite BinProductOfArrows_comp.
      rewrite id_right.
      apply idpath.
  Qed.
End Lenses.
