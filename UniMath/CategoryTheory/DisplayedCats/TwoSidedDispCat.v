Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.

Section TwoSidedDispCat.
  Context {C₁ C₂ : category}.

  Definition twosided_disp_cat_ob_mor
    : UU
    := ∑ (D : C₁ → C₂ → UU),
       ∏ (x₁ x₂ : C₁)
         (y₁ y₂ : C₂),
       D x₁ y₁
       →
       D x₂ y₂
       →
       x₁ --> x₂
       →
       y₁ --> y₂
       →
       UU.

  Definition twosided_disp_cat_ob_mor_to_ob
             {D : twosided_disp_cat_ob_mor}
             (x : C₁)
             (y : C₂)
    : UU
    := pr1 D x y.

  Coercion twosided_disp_cat_ob_mor_to_ob : twosided_disp_cat_ob_mor >-> Funclass.

  Definition twosided_disp_cat_ob_mor_to_mor
             {D : twosided_disp_cat_ob_mor}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x₁ y₁)
             (xy₂ : D x₂ y₂)
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : UU
    := pr2 D x₁ x₂ y₁ y₂ xy₁ xy₂ f g.

  Local Notation "xy₁ -->[ f ][ g ] xy₂"
    := (twosided_disp_cat_ob_mor_to_mor xy₁ xy₂ f g)
         (at level 50, left associativity, xy₂ at next level).

  Definition twosided_disp_cat_id
             (D : twosided_disp_cat_ob_mor)
    : UU
    := ∏ (x : C₁)
         (y : C₂)
         (xy : D x y),
       xy -->[ identity x ][ identity y ] xy.

  Definition twosided_disp_cat_comp
             (D : twosided_disp_cat_ob_mor)
    : UU
    := ∏ (x₁ x₂ x₃ : C₁)
         (y₁ y₂ y₃ : C₂)
         (xy₁ : D x₁ y₁)
         (xy₂ : D x₂ y₂)
         (xy₃ : D x₃ y₃)
         (f₁ : x₁ --> x₂)
         (f₂ : x₂ --> x₃)
         (g₁ : y₁ --> y₂)
         (g₂ : y₂ --> y₃),
       xy₁ -->[ f₁ ][ g₁ ] xy₂
       →
       xy₂ -->[ f₂ ][ g₂ ] xy₃
       →
       xy₁ -->[ f₁ · f₂ ][ g₁ · g₂ ] xy₃.

  Definition twosided_disp_cat_id_comp
             (D : twosided_disp_cat_ob_mor)
    : UU
    := twosided_disp_cat_id D × twosided_disp_cat_comp D.

  Definition twosided_disp_cat_data
    : UU
    := ∑ (D : twosided_disp_cat_ob_mor),
       twosided_disp_cat_id_comp D.

  Coercion twosided_disp_cat_data_to_twosided_disp_cat_ob_mor
           (D : twosided_disp_cat_data)
    : twosided_disp_cat_ob_mor
    := pr1 D.

  Definition id_two_disp
             {D : twosided_disp_cat_data}
             {x : C₁}
             {y : C₂}
             (xy : D x y)
    : xy -->[ identity x ][ identity y ] xy
    := pr12 D x y xy.

  Definition comp_two_disp
             {D : twosided_disp_cat_data}
             {x₁ x₂ x₃ : C₁}
             {y₁ y₂ y₃ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {xy₃ : D x₃ y₃}
             {f₁ : x₁ --> x₂}
             {f₂ : x₂ --> x₃}
             {g₁ : y₁ --> y₂}
             {g₂ : y₂ --> y₃}
             (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
    : xy₁ -->[ f₁ · f₂ ][ g₁ · g₂ ] xy₃
    := pr22 D _ _ _ _ _ _ _ _ _ _ _ _ _ fg₁ fg₂.

  Local Notation "fg₁ ;;2 fg₂"
    := (comp_two_disp fg₁ fg₂)
         (at level 50, left associativity, format "fg₁  ;;2  fg₂").

  Definition id_two_disp_left_law
             (D : twosided_disp_cat_data)
    : UU
    := ∏ (x₁ x₂ : C₁)
         (y₁ y₂ : C₂)
         (xy₁ : D x₁ y₁)
         (xy₂ : D x₂ y₂)
         (f : x₁ --> x₂)
         (g : y₁ --> y₂)
         (fg : xy₁ -->[ f ][ g ] xy₂),
       id_two_disp xy₁ ;;2 fg
       =
       transportb
         (λ z, _ -->[ z ][ _] _)
         (id_left _)
         (transportb
            (λ z, _ -->[ _ ][ z ] _)
            (id_left _)
            fg).

  Definition id_two_disp_right_law
             (D : twosided_disp_cat_data)
    : UU
    := ∏ (x₁ x₂ : C₁)
         (y₁ y₂ : C₂)
         (xy₁ : D x₁ y₁)
         (xy₂ : D x₂ y₂)
         (f : x₁ --> x₂)
         (g : y₁ --> y₂)
         (fg : xy₁ -->[ f ][ g ] xy₂),
       fg ;;2 id_two_disp xy₂
       =
       transportb
         (λ z, _ -->[ z ][ _] _)
         (id_right _)
         (transportb
            (λ z, _ -->[ _ ][ z ] _)
            (id_right _)
            fg).

  Definition assoc_two_disp_law
             (D : twosided_disp_cat_data)
    : UU
    := ∏ (x₁ x₂ x₃ x₄ : C₁)
         (y₁ y₂ y₃ y₄ : C₂)
         (xy₁ : D x₁ y₁)
         (xy₂ : D x₂ y₂)
         (xy₃ : D x₃ y₃)
         (xy₄ : D x₄ y₄)
         (f₁ : x₁ --> x₂)
         (f₂ : x₂ --> x₃)
         (f₃ : x₃ --> x₄)
         (g₁ : y₁ --> y₂)
         (g₂ : y₂ --> y₃)
         (g₃ : y₃ --> y₄)
         (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
         (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
         (fg₃ : xy₃ -->[ f₃ ][ g₃ ] xy₄),
       (fg₁ ;;2 (fg₂ ;;2 fg₃))
       =
       transportb
         (λ z, _ -->[ z ][ _] _)
         (assoc _ _ _)
         (transportb
            (λ z, _ -->[ _ ][ z ] _)
            (assoc _ _ _)
            ((fg₁ ;;2 fg₂) ;;2 fg₃)).

  Definition isaset_disp_mor_law
             (D : twosided_disp_cat_data)
    : UU
    := ∏ (x₁ x₂ : C₁)
         (y₁ y₂ : C₂)
         (xy₁ : D x₁ y₁)
         (xy₂ : D x₂ y₂)
         (f : x₁ --> x₂)
         (g : y₁ --> y₂),
       isaset (xy₁ -->[ f ][ g ] xy₂).

  Definition twosided_disp_cat_axioms
             (D : twosided_disp_cat_data)
    : UU
    := id_two_disp_left_law D
       ×
       id_two_disp_right_law D
       ×
       assoc_two_disp_law D
       ×
       isaset_disp_mor_law D.

  Definition isaprop_twosided_disp_cat_axioms
             (D : twosided_disp_cat_data)
    : isaprop (twosided_disp_cat_axioms D).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    repeat (use pathsdirprod).
    - do 9 (use funextsec ; intro).
      apply (pr222 φ₂).
    - do 9 (use funextsec ; intro).
      apply (pr222 φ₂).
    - do 21 (use funextsec ; intro).
      apply (pr222 φ₂).
    - do 8 (use funextsec ; intro).
      apply isapropisaset.
  Qed.

  Definition twosided_disp_cat
    : UU
    := ∑ (D : twosided_disp_cat_data),
       twosided_disp_cat_axioms D.

  Coercion twosided_disp_cat_to_twosided_disp_cat_data
           (D : twosided_disp_cat)
    : twosided_disp_cat_data
    := pr1 D.

  Definition id_two_disp_left
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : id_two_disp xy₁ ;;2 fg
      =
      transportb
        (λ z, _ -->[ z ][ _] _)
        (id_left _)
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (id_left _)
           fg).
  Proof.
    exact (pr12 D _ _ _ _ _ _ _ _ fg).
  Qed.

  Definition id_two_disp_right
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : fg ;;2 id_two_disp xy₂
      =
      transportb
        (λ z, _ -->[ z ][ _] _)
        (id_right _)
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (id_right _)
           fg).
  Proof.
    exact (pr122 D _ _ _ _ _ _ _ _ fg).
  Qed.

  Definition assoc_two_disp
             {D : twosided_disp_cat}
             {x₁ x₂ x₃ x₄ : C₁}
             {y₁ y₂ y₃ y₄ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {xy₃ : D x₃ y₃}
             {xy₄ : D x₄ y₄}
             {f₁ : x₁ --> x₂}
             {f₂ : x₂ --> x₃}
             {f₃ : x₃ --> x₄}
             {g₁ : y₁ --> y₂}
             {g₂ : y₂ --> y₃}
             {g₃ : y₃ --> y₄}
             (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
             (fg₃ : xy₃ -->[ f₃ ][ g₃ ] xy₄)
    : (fg₁ ;;2 (fg₂ ;;2 fg₃))
      =
      transportb
        (λ z, _ -->[ z ][ _] _)
        (assoc _ _ _)
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (assoc _ _ _)
           ((fg₁ ;;2 fg₂) ;;2 fg₃)).
  Proof.
    exact (pr1 (pr222 D) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fg₁ fg₂ fg₃).
  Qed.

  Definition isaset_disp_mor
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x₁ y₁)
             (xy₂ : D x₂ y₂)
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : isaset (xy₁ -->[ f ][ g ] xy₂).
  Proof.
    exact (pr2 (pr222 D) _ _ _ _ xy₁ xy₂ f g).
  Qed.
End TwoSidedDispCat.

Arguments twosided_disp_cat_ob_mor _ _ : clear implicits.
Arguments twosided_disp_cat_data _ _ : clear implicits.
Arguments twosided_disp_cat _ _ : clear implicits.

Notation "xy₁ -->[ f ][ g ] xy₂"
  := (twosided_disp_cat_ob_mor_to_mor xy₁ xy₂ f g)
       (at level 50, left associativity, xy₂ at next level) : cat.

Notation "fg₁ ;;2 fg₂"
  := (comp_two_disp fg₁ fg₂)
       (at level 50, left associativity, format "fg₁  ;;2  fg₂") : cat.

Definition total2_paths_2_b
           {X Y : UU}
           (Z : X → Y → UU)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           {y₁ y₂ : Y}
           (q : y₁ = y₂)
           {z₁ : Z x₁ y₁}
           {z₂ : Z x₂ y₂}
           (r : z₁
                =
                transportb
                  (λ w, Z w _)
                  p
                  (transportb
                     (λ w, Z _ w)
                     q
                     z₂))
  : (x₁ ,, y₁ ,, z₁ : ∑ (x : X) (y : Y), Z x y)
    =
    (x₂ ,, y₂ ,, z₂ : ∑ (x : X) (y : Y), Z x y).
Proof.
  induction p, q ; cbn in *.
  induction r.
  apply idpath.
Qed.

Definition transportb_dirprodeq
           {X Y : UU}
           (Z : X → Y → UU)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           {y₁ y₂ : Y}
           (q : y₁ = y₂)
           (z : Z x₂ y₂)
  : transportb
      (λ (w : X × Y), Z (pr1 w) (pr2 w))
      (dirprodeq _ _ (x₁ ,, y₁) (x₂ ,, y₂) p q)
      z
    =
    transportb
      (λ w, Z w _)
      p
      (transportb
         (λ w, Z _ w)
         q
         z).
Proof.
  induction p, q.
  apply idpath.
Defined.

Definition transportb_dirprodeq'
           {X Y : UU}
           (Z : X × Y → UU)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           {y₁ y₂ : Y}
           (q : y₁ = y₂)
           (z : Z (x₂ ,, y₂))
  : transportb
      (λ (w : X × Y), Z w)
      (dirprodeq _ _ (x₁ ,, y₁) (x₂ ,, y₂) p q)
      z
    =
    transportb
      (λ w, Z (w ,, _))
      p
      (transportb
         (λ w, Z (_ ,, w))
         q
         z).
Proof.
  induction p, q.
  apply idpath.
Defined.

Definition is_iso_twosided_disp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {xy₁ : D x₁ y₁}
           {xy₂ : D x₂ y₂}
           {f : x₁ --> x₂}
           {g : y₁ --> y₂}
           (Hf : is_iso f)
           (Hg : is_iso g)
           (fg : xy₁ -->[ f ][ g ] xy₂)
  : UU
  := ∑ (gf : xy₂
               -->[ inv_from_iso (make_iso f Hf) ][ inv_from_iso (make_iso g Hg) ]
               xy₁),
     (fg ;;2 gf
      =
      transportb
        (λ z, _ -->[ z ][ _ ] _)
        (iso_inv_after_iso (make_iso f Hf))
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (iso_inv_after_iso (make_iso g Hg))
           (id_two_disp _)))
     ×
     (gf ;;2 fg
      =
      transportb
        (λ z, _ -->[ z ][ _ ] _)
        (iso_after_iso_inv (make_iso f Hf))
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (iso_after_iso_inv (make_iso g Hg))
           (id_two_disp _))).

Definition all_disp_mor_iso
           {C₁ C₂ : category}
           (D : twosided_disp_cat C₁ C₂)
  : UU
  := ∏ (x₁ x₂ : C₁)
       (y₁ y₂ : C₂)
       (xy₁ : D x₁ y₁)
       (xy₂ : D x₂ y₂)
       (f : x₁ --> x₂)
       (g : y₁ --> y₂)
       (Hf : is_iso f)
       (Hg : is_iso g)
       (fg : xy₁ -->[ f ][ g ] xy₂),
     is_iso_twosided_disp Hf Hg fg.

Section TotalOfTwoSidedDispCat.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂).

  Definition total_twosided_disp_precategory_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (∑ (x : C₁) (y : C₂), D x y).
    - exact (λ xy₁ xy₂,
             ∑ (f : pr1 xy₁ --> pr1 xy₂)
               (g : pr12 xy₁ --> pr12 xy₂),
             pr22 xy₁ -->[ f ][ g ] pr22 xy₂).
  Defined.

  Definition total_twosided_disp_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact total_twosided_disp_precategory_ob_mor.
    - exact (λ xy,
             identity (pr1 xy)
             ,,
             identity (pr12 xy)
             ,,
             id_two_disp (pr22 xy)).
    - exact (λ xy₁ xy₂ xy₃ fg₁ fg₂,
             pr1 fg₁ · pr1 fg₂
             ,,
             pr12 fg₁ · pr12 fg₂
             ,,
             pr22 fg₁ ;;2 pr22 fg₂).
  Defined.

  Definition total_twosided_disp_is_precategory
    : is_precategory total_twosided_disp_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros xy₁ xy₂ fg.
      use total2_paths_2_b.
      + apply id_left.
      + apply id_left.
      + apply id_two_disp_left.
    - intros xy₁ xy₂ fg.
      use total2_paths_2_b.
      + apply id_right.
      + apply id_right.
      + apply id_two_disp_right.
    - intros xy₁ xy₂ xy₃ xy₄ fg₁ fg₂ fg₃.
      use total2_paths_2_b.
      + apply assoc.
      + apply assoc.
      + apply assoc_two_disp.
  Qed.

  Definition total_twosided_disp_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact total_twosided_disp_precategory_data.
    - exact total_twosided_disp_is_precategory.
  Defined.

  Definition has_homsets_total_twosided_disp_category
    : has_homsets total_twosided_disp_precategory_ob_mor.
  Proof.
    intros xy₁ xy₂.
    apply isaset_total2.
    - apply homset_property.
    - intro.
      apply isaset_total2.
      + apply homset_property.
      + intro.
        apply isaset_disp_mor.
  Defined.

  Definition total_twosided_disp_category
    : category.
  Proof.
    use make_category.
    - exact total_twosided_disp_precategory.
    - exact has_homsets_total_twosided_disp_category.
  Defined.

  Definition twosided_disp_category_pr1_data
    : functor_data total_twosided_disp_category C₁.
  Proof.
    use make_functor_data.
    - exact (λ xy, pr1 xy).
    - exact (λ xy₁ xy₂ fg, pr1 fg).
  Defined.

  Definition twosided_disp_category_pr1_is_functor
    : is_functor twosided_disp_category_pr1_data.
  Proof.
    refine (_ ,, _) ; intro ; intros ; cbn.
    - apply idpath.
    - apply idpath.
  Qed.

  Definition twosided_disp_category_pr1
    : total_twosided_disp_category ⟶ C₁.
  Proof.
    use make_functor.
    - exact twosided_disp_category_pr1_data.
    - exact twosided_disp_category_pr1_is_functor.
  Defined.

  Definition twosided_disp_category_pr2_data
    : functor_data total_twosided_disp_category C₂.
  Proof.
    use make_functor_data.
    - exact (λ xy, pr12 xy).
    - exact (λ xy₁ xy₂ fg, pr12 fg).
  Defined.

  Definition twosided_disp_category_pr2_is_functor
    : is_functor twosided_disp_category_pr2_data.
  Proof.
    refine (_ ,, _) ; intro ; intros ; cbn.
    - apply idpath.
    - apply idpath.
  Qed.

  Definition twosided_disp_category_pr2
    : total_twosided_disp_category ⟶ C₂.
  Proof.
    use make_functor.
    - exact twosided_disp_category_pr2_data.
    - exact twosided_disp_category_pr2_is_functor.
  Defined.
End TotalOfTwoSidedDispCat.

Section ArrowTwoSidedDispCat.
  Context (C : category).

  Definition arrow_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C C.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, x --> y).
    - exact (λ x₁ x₂ y₁ y₂ h₁ h₂ f g, f · h₂ = h₁ · g).
  Defined.

  Definition arrow_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp arrow_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - intros x y xy ; cbn.
      rewrite id_left, id_right.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ f₂ g₁ g₂ p q ; cbn in *.
      rewrite assoc'.
      rewrite q.
      rewrite !assoc.
      apply maponpaths_2.
      exact p.
  Qed.

  Definition arrow_twosided_disp_cat_data
    : twosided_disp_cat_data C C.
  Proof.
    simple refine (_ ,, _).
    - exact arrow_twosided_disp_cat_ob_mor.
    - exact arrow_twosided_disp_cat_id_comp.
  Defined.

  Definition isaprop_arrow_twosided_mor
             {x₁ x₂ : C}
             {y₁ y₂ : C}
             (xy₁ : arrow_twosided_disp_cat_data x₁ y₁)
             (xy₂ : arrow_twosided_disp_cat_data x₂ y₂)
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : isaprop (xy₁ -->[ f ][ g ] xy₂).
  Proof.
    apply homset_property.
  Qed.

  Definition arrow_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms arrow_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply isaprop_arrow_twosided_mor.
    - intro ; intros.
      apply isaprop_arrow_twosided_mor.
    - intro ; intros.
      apply isaprop_arrow_twosided_mor.
    - intro ; intros.
      apply isasetaprop.
      apply isaprop_arrow_twosided_mor.
  Qed.

  Definition arrow_twosided_disp_cat
    : twosided_disp_cat C C.
  Proof.
    simple refine (_ ,, _).
    - exact arrow_twosided_disp_cat_data.
    - exact arrow_twosided_disp_cat_axioms.
  Defined.

  Definition arrow_twosided_disp_cat_is_iso
    : all_disp_mor_iso arrow_twosided_disp_cat.
  Proof.
    intro ; intros.
    simple refine (_ ,, _ ,, _) ; cbn in *.
    - use iso_inv_on_right.
      rewrite assoc.
      use iso_inv_on_left ; cbn.
      exact fg.
    - apply isaprop_arrow_twosided_mor.
    - apply isaprop_arrow_twosided_mor.
  Qed.
End ArrowTwoSidedDispCat.

Section CommaTwoSidedDispCat.
  Context {C₁ C₂ C₃ : category}
          (F : C₁ ⟶ C₃)
          (G : C₂ ⟶ C₃).

  Definition comma_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, F x --> G y).
    - exact (λ x₁ x₂ y₁ y₂ h₁ h₂ f g, #F f · h₂ = h₁ · #G g).
  Defined.

  Definition comma_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp comma_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - intros x y xy ; cbn.
      rewrite !functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ h₁ h₂ h₃ f₁ f₂ g₁ g₂ hh₁ hh₂ ; cbn in *.
      rewrite !functor_comp.
      rewrite !assoc'.
      rewrite hh₂.
      rewrite !assoc.
      apply maponpaths_2.
      exact hh₁.
  Qed.

  Definition comma_twosided_disp_cat_data
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact comma_twosided_disp_cat_ob_mor.
    - exact comma_twosided_disp_cat_id_comp.
  Defined.

  Definition isaprop_comma_twosided_mor
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : comma_twosided_disp_cat_data x₁ y₁)
             (xy₂ : comma_twosided_disp_cat_data x₂ y₂)
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : isaprop (xy₁ -->[ f ][ g ] xy₂).
  Proof.
    apply homset_property.
  Qed.

  Definition comma_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms comma_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply isaprop_comma_twosided_mor.
    - intro ; intros.
      apply isaprop_comma_twosided_mor.
    - intro ; intros.
      apply isaprop_comma_twosided_mor.
    - intro ; intros.
      apply isasetaprop.
      apply isaprop_comma_twosided_mor.
  Qed.

  Definition comma_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact comma_twosided_disp_cat_data.
    - exact comma_twosided_disp_cat_axioms.
  Defined.

  Definition comma_twosided_disp_cat_is_iso
    : all_disp_mor_iso comma_twosided_disp_cat.
  Proof.
    intro ; intros.
    simple refine (_ ,, _ ,, _) ; cbn in *.
    - rewrite !functor_on_inv_from_iso.
      use iso_inv_on_right.
      rewrite assoc.
      use iso_inv_on_left ; cbn.
      exact fg.
    - apply isaprop_comma_twosided_mor.
    - apply isaprop_comma_twosided_mor.
  Qed.
End CommaTwoSidedDispCat.

Section IsoCommaTwoSidedDispCat.
  Context {C₁ C₂ C₃ : category}
          (F : C₁ ⟶ C₃)
          (G : C₂ ⟶ C₃).

  Definition iso_comma_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, iso (F x) (G y)).
    - exact (λ x₁ x₂ y₁ y₂ h₁ h₂ f g, #F f · h₂ = h₁ · #G g).
  Defined.

  Definition iso_comma_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp iso_comma_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - intros x y xy ; cbn.
      rewrite !functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ h₁ h₂ h₃ f₁ f₂ g₁ g₂ hh₁ hh₂ ; cbn in *.
      rewrite !functor_comp.
      rewrite !assoc'.
      rewrite hh₂.
      rewrite !assoc.
      apply maponpaths_2.
      exact hh₁.
  Qed.

  Definition iso_comma_twosided_disp_cat_data
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact iso_comma_twosided_disp_cat_ob_mor.
    - exact iso_comma_twosided_disp_cat_id_comp.
  Defined.

  Definition isaprop_iso_comma_twosided_mor
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : iso_comma_twosided_disp_cat_data x₁ y₁)
             (xy₂ : iso_comma_twosided_disp_cat_data x₂ y₂)
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : isaprop (xy₁ -->[ f ][ g ] xy₂).
  Proof.
    apply homset_property.
  Qed.

  Definition iso_comma_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms iso_comma_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply isaprop_iso_comma_twosided_mor.
    - intro ; intros.
      apply isaprop_iso_comma_twosided_mor.
    - intro ; intros.
      apply isaprop_iso_comma_twosided_mor.
    - intro ; intros.
      apply isasetaprop.
      apply isaprop_iso_comma_twosided_mor.
  Qed.

  Definition iso_comma_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact iso_comma_twosided_disp_cat_data.
    - exact iso_comma_twosided_disp_cat_axioms.
  Defined.

  Definition iso_comma_twosided_disp_cat_is_iso
    : all_disp_mor_iso iso_comma_twosided_disp_cat.
  Proof.
    intro ; intros.
    simple refine (_ ,, _ ,, _) ; cbn in *.
    - rewrite !functor_on_inv_from_iso.
      use iso_inv_on_right.
      rewrite assoc.
      use iso_inv_on_left ; cbn.
      exact fg.
    - apply isaprop_iso_comma_twosided_mor.
    - apply isaprop_iso_comma_twosided_mor.
  Qed.
End IsoCommaTwoSidedDispCat.

Section TwoSidedDispCatVersusDispCat.
  Context (C₁ C₂ : category).

  Definition twosided_disp_cat_to_disp_cat_ob_mor
             (D : twosided_disp_cat C₁ C₂)
    : disp_cat_ob_mor (category_binproduct C₁ C₂).
  Proof.
    simple refine (_ ,, _).
    - exact (λ xy, D (pr1 xy) (pr2 xy)).
    - exact (λ xy₁ xy₂ z₁ z₂ fg, z₁ -->[ pr1 fg ][ pr2 fg ] z₂).
  Defined.

  Definition twosided_disp_cat_to_disp_cat_id_comp
             (D : twosided_disp_cat C₁ C₂)
    : disp_cat_id_comp
        (category_binproduct C₁ C₂)
        (twosided_disp_cat_to_disp_cat_ob_mor D).
  Proof.
    simple refine (_ ,, _).
    - exact (λ xy z, id_two_disp z).
    - exact (λ xy₁ xy₂ xy₃ fg₁ fg₂ z₁ z₂ z₃ h₁ h₂,
             h₁ ;;2 h₂).
  Defined.

  Definition twosided_disp_cat_to_disp_cat_data
             (D : twosided_disp_cat C₁ C₂)
    : disp_cat_data (category_binproduct C₁ C₂).
  Proof.
    simple refine (_ ,, _).
    - exact (twosided_disp_cat_to_disp_cat_ob_mor D).
    - exact (twosided_disp_cat_to_disp_cat_id_comp D).
  Defined.

  Definition twosided_disp_cat_to_disp_cat_axioms
             (D : twosided_disp_cat C₁ C₂)
    : disp_cat_axioms
        (category_binproduct C₁ C₂)
        (twosided_disp_cat_to_disp_cat_data D).
  Proof.
    repeat split.
    - intros x y f g xx yy ; cbn in *.
      refine (id_two_disp_left _ @ _).
      refine (!_).
      apply transportb_dirprodeq.
    - intros x y f g xx yy ; cbn in *.
      refine (id_two_disp_right _ @ _).
      refine (!_).
      apply transportb_dirprodeq.
    - intros w x y z f g h ww xx yy zz ff gg hh ; cbn in *.
      refine (assoc_two_disp _ _ _ @ _).
      refine (!_).
      apply transportb_dirprodeq.
    - intros x y f xx yy ; cbn in *.
      apply isaset_disp_mor.
  Qed.

  Definition twosided_disp_cat_to_disp_cat
             (D : twosided_disp_cat C₁ C₂)
    : disp_cat (category_binproduct C₁ C₂).
  Proof.
    simple refine (_ ,, _).
    - exact (twosided_disp_cat_to_disp_cat_data D).
    - exact (twosided_disp_cat_to_disp_cat_axioms D).
  Defined.

  Definition disp_cat_to_twosided_disp_cat_ob_mor
             (D : disp_cat (category_binproduct C₁ C₂))
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, D (x ,, y)).
    - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g, xy₁ -->[ f ,, g ] xy₂).
  Defined.

  Definition disp_cat_to_twosided_disp_cat_id_comp
             (D : disp_cat (category_binproduct C₁ C₂))
    : twosided_disp_cat_id_comp
        (disp_cat_to_twosided_disp_cat_ob_mor D).
  Proof.
    split.
    - exact (λ x y xy, id_disp _).
    - refine (λ x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ f₂ g₁ g₂ fg₁ fg₂,
              _).
      cbn in *.
      exact (fg₁ ;; fg₂)%mor_disp.
  Defined.

  Definition disp_cat_to_twosided_disp_cat_data
             (D : disp_cat (category_binproduct C₁ C₂))
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (disp_cat_to_twosided_disp_cat_ob_mor D).
    - exact (disp_cat_to_twosided_disp_cat_id_comp D).
  Defined.

  Definition disp_cat_to_twosided_disp_cat_axioms
             (D : disp_cat (category_binproduct C₁ C₂))
    : twosided_disp_cat_axioms (disp_cat_to_twosided_disp_cat_data D).
  Proof.
    repeat split.
    - intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg ; cbn in *.
      refine (id_left_disp fg @ _).
      apply transportb_dirprodeq'.
    - intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg ; cbn in *.
      refine (id_right_disp fg @ _).
      apply transportb_dirprodeq'.
    - intros x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ xy₁ xy₂ xy₃ xy₄ f₁ f₂ f₃ g₁ g₂ g₃ fg₁ fg₂ fg₃.
      cbn in *.
      refine (assoc_disp fg₁ fg₂ fg₃ @ _).
      apply transportb_dirprodeq'.
    - intro ; intros.
      apply D.
  Qed.

  Definition disp_cat_to_twosided_disp_cat
             (D : disp_cat (category_binproduct C₁ C₂))
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (disp_cat_to_twosided_disp_cat_data D).
    - exact (disp_cat_to_twosided_disp_cat_axioms D).
  Defined.

  Definition two_sided_disp_cat_weq_disp_cat_inv_left
             (D : twosided_disp_cat C₁ C₂)
    : disp_cat_to_twosided_disp_cat (twosided_disp_cat_to_disp_cat D)
      =
      D.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_twosided_disp_cat_axioms.
    }
    apply idpath.
  Qed.

  Definition two_sided_disp_cat_weq_disp_cat_inv_right
             (D : disp_cat (category_binproduct C₁ C₂))
    : twosided_disp_cat_to_disp_cat (disp_cat_to_twosided_disp_cat D)
      =
      D.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_disp_cat_axioms.
    }
    apply idpath.
  Qed.

  Definition two_sided_disp_cat_weq_disp_cat
    : twosided_disp_cat C₁ C₂ ≃ disp_cat (category_binproduct C₁ C₂).
  Proof.
    use make_weq.
    - exact twosided_disp_cat_to_disp_cat.
    - use gradth.
      + exact disp_cat_to_twosided_disp_cat.
      + exact two_sided_disp_cat_weq_disp_cat_inv_left.
      + exact two_sided_disp_cat_weq_disp_cat_inv_right.
  Defined.
End TwoSidedDispCatVersusDispCat.

Section TwoSidedFibration.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂).

  Definition twosided_opcartesian
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : UU
    := ∏ (x₃ : C₁)
         (y₃ : C₂)
         (xy₃ : D x₃ y₃)
         (f' : x₂ --> x₃)
         (g' : y₂ --> y₃)
         (fg' : xy₁ -->[ f · f' ][ g · g' ] xy₃),
       ∃! (ℓ : xy₂ -->[ f' ][ g' ] xy₃),
       fg ;;2 ℓ = fg'.

  Definition twosided_opcartesian_factorisation
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             {fg : xy₁ -->[ f ][ g ] xy₂}
             (H : twosided_opcartesian fg)
             {x₃ : C₁}
             {y₃ : C₂}
             {xy₃ : D x₃ y₃}
             {f' : x₂ --> x₃}
             {g' : y₂ --> y₃}
             (fg' : xy₁ -->[ f · f' ][ g · g' ] xy₃)
    : xy₂ -->[ f' ][ g' ] xy₃
    := pr11 (H _ _ _ _ _ fg').

  Definition twosided_opcartesian_factorisation_commutes
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             {fg : xy₁ -->[ f ][ g ] xy₂}
             (H : twosided_opcartesian fg)
             {x₃ : C₁}
             {y₃ : C₂}
             {xy₃ : D x₃ y₃}
             {f' : x₂ --> x₃}
             {g' : y₂ --> y₃}
             (fg' : xy₁ -->[ f · f' ][ g · g' ] xy₃)
    : fg ;;2 twosided_opcartesian_factorisation H fg' = fg'
    := pr21 (H _ _ _ _ _ fg').

  Definition twosided_cartesian
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : UU
    := ∏ (x₀ : C₁)
         (y₀ : C₂)
         (xy₀ : D x₀ y₀)
         (f' : x₀ --> x₁)
         (g' : y₀ --> y₁)
         (fg' : xy₀ -->[ f' · f ][ g' · g ] xy₂),
       ∃! (ℓ : xy₀ -->[ f' ][ g' ] xy₁),
       ℓ ;;2 fg = fg'.

  Definition twosided_cartesian_factorisation
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             {fg : xy₁ -->[ f ][ g ] xy₂}
             (H : twosided_cartesian fg)
             {x₀ : C₁}
             {y₀ : C₂}
             {xy₀ : D x₀ y₀}
             {f' : x₀ --> x₁}
             {g' : y₀ --> y₁}
             (fg' : xy₀ -->[ f' · f ][ g' · g ] xy₂)
    : xy₀ -->[ f' ][ g' ] xy₁
    := pr11 (H _ _ _ _ _ fg').

  Definition twosided_cartesian_factorisation_commutes
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             {fg : xy₁ -->[ f ][ g ] xy₂}
             (H : twosided_cartesian fg)
             {x₀ : C₁}
             {y₀ : C₂}
             {xy₀ : D x₀ y₀}
             {f' : x₀ --> x₁}
             {g' : y₀ --> y₁}
             (fg' : xy₀ -->[ f' · f ][ g' · g ] xy₂)
    : twosided_cartesian_factorisation H fg' ;;2 fg = fg'
    := pr21 (H _ _ _ _ _ fg').

  Definition twosided_opcleaving
    : UU
    := ∏ (x : C₁)
         (y₁ y₂ : C₂)
         (xy₁ : D x y₁)
         (g : y₁ --> y₂),
       ∑ (xy₂ : D x y₂)
         (ℓ : xy₁ -->[ identity _ ][ g ] xy₂),
       twosided_opcartesian ℓ.

  Definition twosided_opcleaving_ob
             (H : twosided_opcleaving)
             {x : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x y₁)
             (g : y₁ --> y₂)
    : D x y₂
    := pr1 (H x y₁ y₂ xy₁ g).

  Definition twosided_opcleaving_mor
             (H : twosided_opcleaving)
             {x : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x y₁)
             (g : y₁ --> y₂)
    : xy₁ -->[ identity _ ][ g ] twosided_opcleaving_ob H xy₁ g
    := pr12 (H x y₁ y₂ xy₁ g).

  Definition twosided_opcleaving_opcartesian
             (H : twosided_opcleaving)
             {x : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x y₁)
             (g : y₁ --> y₂)
    : twosided_opcartesian (twosided_opcleaving_mor H xy₁ g)
    := pr22 (H x y₁ y₂ xy₁ g).

  Definition twosided_cleaving
    : UU
    := ∏ (x₁ x₂ : C₁)
         (y : C₂)
         (xy₂ : D x₂ y)
         (f : x₁ --> x₂),
       ∑ (xy₁ : D x₁ y)
         (ℓ : xy₁ -->[ f ][ identity _ ] xy₂),
       twosided_cartesian ℓ.

  Definition twosided_cleaving_ob
             (H : twosided_cleaving)
             {x₁ x₂ : C₁}
             {y : C₂}
             (xy₂ : D x₂ y)
             (f : x₁ --> x₂)
    : D x₁ y
    := pr1 (H x₁ x₂ y xy₂ f).

  Definition twosided_cleaving_mor
             (H : twosided_cleaving)
             {x₁ x₂ : C₁}
             {y : C₂}
             (xy₂ : D x₂ y)
             (f : x₁ --> x₂)
    : twosided_cleaving_ob H xy₂ f -->[ f ][ identity _ ] xy₂
    := pr12 (H x₁ x₂ y xy₂ f).

  Definition twosided_cleaving_cartesian
             (H : twosided_cleaving)
             {x₁ x₂ : C₁}
             {y : C₂}
             (xy₂ : D x₂ y)
             (f : x₁ --> x₂)
    : twosided_cartesian (twosided_cleaving_mor H xy₂ f)
    := pr22 (H x₁ x₂ y xy₂ f).

  Definition twosided_commute
             (H₁ : twosided_opcleaving)
             (H₂ : twosided_cleaving)
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (xy : D x₂ y₁)
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : twosided_opcleaving_ob H₁ (twosided_cleaving_ob H₂ xy f) g
      -->[ identity _ ][ identity _ ]
      twosided_cleaving_ob H₂ (twosided_opcleaving_ob H₁ xy g) f.
  Proof.
    use (twosided_opcartesian_factorisation
           (twosided_opcleaving_opcartesian H₁ _ g)).
    use (twosided_cartesian_factorisation
           (twosided_cleaving_cartesian H₂ _ f)).
    refine (transportb
              (λ z, _ -->[ z ][ _ ] _)
              _
              (transportb
                 (λ z, _ -->[ _ ][ z ] _)
                 _
                 (twosided_cleaving_mor H₂ xy f ;;2 twosided_opcleaving_mor H₁ xy g))).
    - abstract
        (rewrite !id_left, !id_right ;
         apply idpath).
    - abstract
        (rewrite !id_left, !id_right ;
         apply idpath).
  Defined.

  Definition is_iso_twosided_commute
             (H₁ : twosided_opcleaving)
             (H₂ : twosided_cleaving)
    : UU
    := ∏ (x₁ x₂ : C₁)
         (y₁ y₂ : C₂)
         (xy : D x₂ y₁)
         (f : x₁ --> x₂)
         (g : y₁ --> y₂),
       is_iso_twosided_disp
         (identity_is_iso _ _)
         (identity_is_iso _ _)
         (twosided_commute H₁ H₂ xy f g).

  Definition twosided_fibration
    : UU
    := ∑ (H₁ : twosided_opcleaving)
         (H₂ : twosided_cleaving),
       is_iso_twosided_commute H₁ H₂.
End TwoSidedFibration.

Section ArrowTwoSidedFibration.
  Context (C : category).

  Definition arrow_twosided_opcleaving
    : twosided_opcleaving (arrow_twosided_disp_cat C).
  Proof.
    intros x₁ x₂ x₃ f g ; cbn in *.
    simple refine (f · g ,, _ ,, _) ; cbn.
    - apply id_left.
    - intros x₄ x₅ h k l p.
      use iscontraprop1.
      + use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isaset_disp_mor.
        }
        apply isaprop_arrow_twosided_mor.
      + simple refine (_ ,, _).
        * cbn in *.
          rewrite id_left, assoc in p.
          exact p.
        * apply isaprop_arrow_twosided_mor.
  Qed.

  Definition arrow_twosided_cleaving
    : twosided_cleaving (arrow_twosided_disp_cat C).
  Proof.
    intros x₁ x₂ x₃ f g ; cbn in *.
    simple refine (g · f ,, _ ,, _) ; cbn.
    - rewrite id_right.
      apply idpath.
    - intros x₄ x₅ h k l p.
      use iscontraprop1.
      + use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isaset_disp_mor.
        }
        apply isaprop_arrow_twosided_mor.
      + cbn in *.
        simple refine (_ ,, _).
        * rewrite id_right, assoc' in p.
          exact p.
        * apply isaprop_arrow_twosided_mor.
  Qed.

  Definition arrow_twosided_fibration
    : twosided_fibration (arrow_twosided_disp_cat C).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact arrow_twosided_opcleaving.
    - exact arrow_twosided_cleaving.
    - intro ; intros.
      apply arrow_twosided_disp_cat_is_iso.
  Defined.
End ArrowTwoSidedFibration.

Section CommaTwoSidedFibration.
  Context {C₁ C₂ C₃ : category}
          (F : C₁ ⟶ C₃)
          (G : C₂ ⟶ C₃).

  Definition comma_twosided_opcleaving
    : twosided_opcleaving (comma_twosided_disp_cat F G).
  Proof.
    intros x₁ x₂ x₃ f g ; cbn in *.
    simple refine (f · #G g ,, _ ,, _) ; cbn.
    - rewrite functor_id.
      rewrite id_left.
      apply idpath.
    - intros x₄ x₅ h k l p.
      use iscontraprop1.
      + use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isaset_disp_mor.
        }
        apply isaprop_comma_twosided_mor.
      + cbn in *.
        simple refine (_ ,, _).
        * rewrite id_left, functor_comp, assoc in p.
          exact p.
        * apply isaprop_comma_twosided_mor.
  Qed.

  Definition comma_twosided_cleaving
    : twosided_cleaving (comma_twosided_disp_cat F G).
  Proof.
    intros x₁ x₂ x₃ f g ; cbn in *.
    simple refine (#F g · f ,, _ ,, _) ; cbn.
    - rewrite functor_id.
      rewrite id_right.
      apply idpath.
    - intros x₄ x₅ h k l p.
      use iscontraprop1.
      + use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isaset_disp_mor.
        }
        apply isaprop_comma_twosided_mor.
      + cbn in *.
        simple refine (_ ,, _).
        * rewrite id_right, functor_comp, assoc' in p.
          exact p.
        * apply isaprop_comma_twosided_mor.
  Qed.

  Definition comma_twosided_fibration
    : twosided_fibration (comma_twosided_disp_cat F G).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact comma_twosided_opcleaving.
    - exact comma_twosided_cleaving.
    - intro ; intros.
      apply comma_twosided_disp_cat_is_iso.
  Defined.
End CommaTwoSidedFibration.
