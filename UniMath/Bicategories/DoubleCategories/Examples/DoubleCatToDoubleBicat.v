(*****************************************************************************************

 Pseudo double category to Verity double bicategory

 Every pseudo double category `C` gives rise to a Verity double bicategory. This Verity
 double bicategory is defined as follows:
 - Objects: objects in `C`
 - Horizontal 1-cells: vertical morphisms in `C`
 - Horizontal 2-cells: equalities of vertical morphisms
 - Vertical 1-cells: horizontal morphisms in `C`
 - Vertical 2-cells: globular squares in `C`
 - Squares: squares in `C`
 Note that the horizontal and vertical morphisms get swapped in this construction. For
 Verity double bicategories, this does not matter, because their definition is symmetric.
 The reason why this swap is desired, is because for Verity double bicategories and for
 pseudo double categories, a different convention is used regarding which morphisms are
 called horizontal and which ones are called vertical. For Verity double bicategories,
 the PhD thesis of Verity is followed, whereas for pseudo double categories, the book on
 2-dimensional categories by Johnson and Yau is followed.

 Another thing that is worth noticing, is that vertical 2-cells correspond to
 squares in this Verity double bicategory. However, the same cannot be said for the
 horizontal 2-cells. For example, we could consider the pseudo double category whose
 objects are strict categories, vertical morphisms are categories, horizontal morphisms
 are profunctors, and whose squares are given by natural transformations. Equalities of
 functors between strict categories do not correspond to squares whose horizontal sides
 are identity profunctors.

 Contents
 1. The vertical bicategory
 2. The whiskering operations
 3. The laws of the Verity double bicategory
 4. The Verity double bicategory coming from a pseudo double category
 5. The univalence of this Verity double bicategory
 6. Companions and conjoints

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.DiscreteBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.Core.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.DerivedLaws.TransportLaws.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.
Require Import UniMath.Bicategories.DoubleCategories.Underlying.HorizontalBicategory.

Local Open Scope cat.
Local Open Scope double_cat.

Section DoubleCatToDoubleBicat.
  Context (C : double_cat).

  Let ℍ : bicat := horizontal_bicat C. (* \bH *)

  (** * 1. The vertical bicategory *)
  Definition double_cat_to_twosided_disp_cat_data
    : twosided_disp_cat_data C C.
  Proof.
    simple refine ((_ ,, _) ,, (_ ,, _)).
    - exact (λ x y, x -->h y).
    - exact (λ _ _ _ _ h k v w, square v w h k).
    - exact (λ x y h, id_v_square h).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂, s₁ ⋆v s₂).
  Defined.

  Definition double_cat_to_ver_sq_bicat
    : ver_sq_bicat.
  Proof.
    use make_ver_sq_bicat.
    - exact (cat_to_bicat C).
    - exact double_cat_to_twosided_disp_cat_data.
  Defined.

  Definition double_cat_to_ver_sq_bicat_ver_id_comp
    : ver_sq_bicat_ver_id_comp double_cat_to_ver_sq_bicat.
  Proof.
    split.
    - split.
      + exact (λ x, identity_h x).
      + exact (λ _ _ _ h k, h ·h k).
    - exact (λ (x y : ℍ) (h k : x --> y), h ==> k).
  Defined.

  Definition double_cat_to_ver_sq_bicat_id_comp_cells
    : ver_sq_bicat_id_comp_cells double_cat_to_ver_sq_bicat_ver_id_comp.
  Proof.
    repeat split.
    - exact (λ (x y : ℍ) (f : x --> y), id2 f).
    - exact (λ (x y : ℍ) (f : x --> y), lunitor f).
    - exact (λ (x y : ℍ) (f : x --> y), runitor f).
    - exact (λ (x y : ℍ) (f : x --> y), linvunitor f).
    - exact (λ (x y : ℍ) (f : x --> y), rinvunitor f).
    - exact (λ (w x y z : ℍ) (f : w --> x) (g : x --> y) (h : y --> z), rassociator f g h).
    - exact (λ (w x y z : ℍ) (f : w --> x) (g : x --> y) (h : y --> z), lassociator f g h).
    - exact (λ (x y : ℍ) (f g h : x --> y) (τ : f ==> g) (θ : g ==> h), τ • θ).
    - exact (λ (x y z : ℍ) (f : x --> y) (g₁ g₂ : y --> z) (τ : g₁ ==> g₂), f ◃ τ).
    - exact (λ (x y z : ℍ) (f₁ f₂ : x --> y) (g : y --> z) (τ : f₁ ==> f₂), τ ▹ g).
  Defined.

  (** Note: the next definition is transparent so that the vertical bicategory
      of this Verity double bicategory is definitionally equal to the horizontal
      bicategory of the pseudo double category *)
  Proposition double_cat_to_ver_sq_bicat_prebicat_laws
    : ver_sq_bicat_prebicat_laws double_cat_to_ver_sq_bicat_id_comp_cells.
  Proof.
    exact (pr21 ℍ).
  Defined.

  Definition double_cat_to_ver_bicat_sq_bicat
    : ver_bicat_sq_bicat.
  Proof.
    use make_ver_bicat_sq_bicat.
    - exact double_cat_to_ver_sq_bicat.
    - exact double_cat_to_ver_sq_bicat_ver_id_comp.
    - exact double_cat_to_ver_sq_bicat_id_comp_cells.
    - exact double_cat_to_ver_sq_bicat_prebicat_laws.
    - intros x y f g.
      apply (cellset_property (C := ℍ)).
  Defined.

  Definition double_cat_to_ver_bicat_sq_bicat_ver_id_comp_sq
    : ver_bicat_sq_bicat_ver_id_comp_sq
        double_cat_to_ver_bicat_sq_bicat.
  Proof.
    split.
    - exact (λ x y f, id_h_square f).
    - exact (λ x₁ x₂ x₃ y₁ y₂ y₃ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂, s₁ ⋆h s₂).
  Defined.

  Definition double_cat_to_ver_bicat_sq_bicat_ver_id_comp
    : ver_bicat_sq_bicat_ver_id_comp.
  Proof.
    use make_ver_bicat_sq_bicat_ver_id_comp.
    - exact double_cat_to_ver_bicat_sq_bicat.
    - exact double_cat_to_ver_bicat_sq_bicat_ver_id_comp_sq.
  Defined.

  (** * 2. The whiskering operations *)
  Definition double_cat_to_double_bicat_whiskering
    : double_bicat_whiskering double_cat_to_ver_bicat_sq_bicat_ver_id_comp.
  Proof.
    repeat split.
    - exact (λ (w x y z : C)
               (v₁ : w -->v x) (v₂ : y -->v z)
               (h₁ h₁' : w -->h y) (h₂ : x -->h z)
               (s₁ : square (identity_v w) (identity_v y) h₁ h₁')
               (s₂ : square v₁ v₂ h₁' h₂),
             transportf_square
               (id_v_left _)
               (id_v_left _)
               (s₁ ⋆v s₂)).
    - exact (λ (w x y z : C)
               (v₁ : w -->v x) (v₂ : y -->v z)
               (h₁ : w -->h y) (h₂ h₂' : x -->h z)
               (s₁ : square (identity_v _) (identity_v _) h₂ h₂')
               (s₂ : square v₁ v₂ h₁ h₂),
             transportf_square
               (id_v_right _)
               (id_v_right _)
               (s₂ ⋆v s₁)).
    - exact (λ (w x y z : C)
               (v₁ v₁' : w -->v x) (v₂ : y -->v z)
               (h₁ : w -->h y) (h₂ : x -->h z)
               (p : v₁ = v₁')
               (s : square v₁' v₂ h₁ h₂),
             transportf_square
               (!p)
               (idpath _)
               s).
    - exact (λ (w x y z : C)
               (v₁ : w -->v x) (v₂ v₂' : y -->v z)
               (h₁ : w -->h y) (h₂ : x -->h z)
               (p : v₂ = v₂')
               (s : square v₁ v₂ h₁ h₂),
             transportf_square
               (idpath _)
               p
               s).
  Defined.

  Definition double_cat_to_ver_bicat_sq_id_comp_whisker
    : ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_ver_bicat_sq_id_comp_whisker.
    - exact double_cat_to_ver_bicat_sq_bicat_ver_id_comp.
    - exact double_cat_to_double_bicat_whiskering.
  Defined.

  (** * 3. The laws of the Verity double bicategory *)
  Proposition double_cat_to_whisker_square_bicat_law
    : whisker_square_bicat_law double_cat_to_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split.
    - intros w x y z v₁ v₂ h₁ h₂ s ; cbn in *.
      etrans.
      {
        apply maponpaths.
        apply square_id_left_v.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      apply transportf_square_id.
    - intros w x y z v₁ v₂ h₁ h₁' h₁'' h₂ s₁ s₂ s₃.
      cbn in *.
      rewrite transportf_square_prewhisker.
      rewrite transportf_square_postwhisker.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite !transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros w x y z v₁ v₂ h₁ h₂ s ; cbn in *.
      etrans.
      {
        apply maponpaths.
        apply square_id_right_v.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      apply transportf_square_id.
    - intros w x y z v₁ v₂ h₁ h₂ h₂' h₂'' s₁ s₂ s₃.
      cbn in *.
      rewrite transportf_square_prewhisker.
      rewrite transportf_square_postwhisker.
      etrans.
      {
        do 2 apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite !transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros w x y z v₁ v₂ h₁ h₂ s.
      cbn in *.
      apply transportf_square_id.
    - intros w x y z v₁ v₁' v₁'' v₂ h₁ h₂ p q s.
      cbn in *.
      induction p, q ; cbn.
      apply transportf_square_id.
    - intros w x y z v₁ v₂ h₁ h₂ s.
      cbn -[transportf_square] in *.
      apply transportf_square_id.
    - intros w x y z v₁ v₂ v₂' v₂'' h₁ h₂ p q s.
      cbn -[transportf_square] in *.
      induction p, q.
      cbn -[transportf_square].
      apply transportf_square_id.
    - intros w x y z v₁ v₁' v₂ v₂' h₁ h₂ p q s.
      cbn -[transportf_square] in *.
      induction p, q.
      rewrite !transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros w x y z v₁ v₁' v₂ h₁ h₁' h₂ p s₁ s₂.
      cbn in *.
      induction p.
      cbn.
      use transportf_square_eq.
      apply idpath.
    - intros w x y z v₁ v₁' v₂ h₁ h₂ h₂' p s₁ s₂.
      cbn in *.
      induction p ; cbn.
      use transportf_square_eq.
      apply idpath.
    - intros w x y z v₁ v₂ v₂' h₁ h₁' h₂ p s₁ s₂.
      cbn in *.
      induction p ; cbn.
      use transportf_square_eq.
      apply idpath.
    - intros w x y z v₁ v₂ v₂' h₁ h₂ h₂' p s₁ s₂.
      cbn in *.
      induction p ; cbn.
      use transportf_square_eq.
      apply idpath.
    - intros w x y z v₁ v₂ h₁ h₁' h₂ h₂' s₁ s₂ s₃.
      cbn in *.
      rewrite transportf_square_prewhisker.
      rewrite transportf_square_postwhisker.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite !transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros x y h k s.
      cbn in *.
      etrans.
      {
        apply maponpaths.
        apply square_id_right_v.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply square_id_left_v.
      }
      unfold transportb_square.
      rewrite !transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros x y h k p.
      cbn in *.
      induction p ; cbn.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₁' v₂ v₃ h₁ h₂ k₁ k₂ p s₁ s₂.
      cbn in *.
      induction p ; cbn.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ v₃' h₁ h₂ k₁ k₂ p s₁ s₂.
      cbn in *.
      induction p ; cbn.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₂' v₃ h₁ h₂ k₁ k₂ p s₁ s₂.
      cbn in *.
      induction p ; cbn.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ v₁ v₂ w₁ w₂ h₁ h₁' h₂ h₃ s₁ s₂ s₃.
      cbn in *.
      rewrite transportf_square_prewhisker.
      etrans.
      {
        apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite !transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ v₁ v₂ w₁ w₂ h₁ h₂ h₃ h₃' s₁ s₂ s₃.
      cbn in *.
      rewrite transportf_square_postwhisker.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite !transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ v₁ v₂ w₁ w₂ h₁ h₂ h₂' h₃ s₁ s₂ s₃.
      cbn in *.
      rewrite transportf_square_prewhisker.
      rewrite transportf_square_postwhisker.
      etrans.
      {
        apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite !transportf_f_square.
      use transportf_square_eq.
      apply idpath.
  Qed.

  Proposition double_cat_to_double_bicat_id_comp_square_laws
    : double_bicat_id_comp_square_laws double_cat_to_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split.
    - intro ; intros ; cbn.
      refine (!_).
      apply comp_h_square_comp.
    - intros ; cbn.
      refine (!_).
      apply id_h_square_id.
    - intros ; cbn.
      apply comp_h_square_id.
    - intros ; cbn.
      refine (!_).
      apply id_h_square_comp.
  Qed.

  Proposition double_cat_to_double_bicat_cylinder_laws
    : double_bicat_cylinder_laws double_cat_to_ver_bicat_sq_id_comp_whisker.
  Proof.
    repeat split.
    - intros ; cbn -[transportf_square].
      etrans.
      {
        apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros ; cbn -[transportf_square].
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply lassociator_square'.
      }
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros ; cbn -[transportf_square].
      etrans.
      {
        apply maponpaths.
        apply square_id_left_v.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros ; cbn -[transportf_square].
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply lunitor_square.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros ; cbn -[transportf_square].
      etrans.
      {
        apply maponpaths.
        apply square_id_right_v.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros ; cbn -[transportf_square].
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply runitor_square.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      use transportf_square_eq.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₁' h₂ h₂' k₁ k₁' k₂ k₂'.
      intros s₁ s₁' s₂ s₂' s₃ s₃' s₄ s₄' p q.
      cbn in *.
      pose (maponpaths (transportb_square (id_v_left v₁) (id_v_left v₂)) p) as p'.
      rewrite transportbf_square in p'.
      unfold transportb_square in p'.
      rewrite transportf_f_square in p'.
      clear p.
      pose (maponpaths (transportb_square (id_v_left v₂) (id_v_left v₃)) q) as q'.
      rewrite transportbf_square in q'.
      unfold transportb_square in q'.
      rewrite transportf_f_square in q'.
      clear q.
      rewrite transportf_square_prewhisker.
      rewrite transportf_square_postwhisker.
      rewrite !transportf_f_square.
      rewrite <- !comp_h_square_comp.
      rewrite !square_id_left_v.
      rewrite !square_id_right_v.
      unfold transportb_square.
      rewrite !transportf_square_prewhisker.
      rewrite !transportf_square_postwhisker.
      rewrite p', q'.
      rewrite !transportf_f_square.
      etrans.
      {
        rewrite transportf_hcomp_l.
        rewrite !transportf_f_square.
        cbn.
        rewrite transportf_hcomp_r.
        rewrite !transportf_f_square.
        cbn -[transportf_square].
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite transportf_hcomp_l.
        rewrite !transportf_f_square.
        cbn.
        rewrite transportf_hcomp_r.
        rewrite !transportf_f_square.
        apply idpath.
      }
      use transportf_square_eq.
      apply maponpaths_2.
      use transportf_square_eq.
      apply idpath.
    - intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₁' h₂ h₂' k₁ k₁' k₂ k₂'.
      intros p p' q q' s₁ s₁' s₂ s₂' r r'.
      cbn -[transportf_square] in *.
      induction p, p', q, q'.
      cbn in r, r'.
      induction r, r'.
      use transportf_square_eq.
      apply idpath.
  Qed.

  Proposition double_cat_to_double_bicat_laws
    : double_bicat_laws double_cat_to_ver_bicat_sq_id_comp_whisker.
  Proof.
    use make_double_bicat_laws.
    - exact double_cat_to_whisker_square_bicat_law.
    - exact double_cat_to_double_bicat_id_comp_square_laws.
    - exact double_cat_to_double_bicat_cylinder_laws.
    - intro ; intros.
      apply isaset_square.
  Qed.

  (** * 4. The Verity double bicategory coming from a pseudo double category *)
  Definition double_cat_to_verity_double_bicat
    : verity_double_bicat.
  Proof.
    use make_verity_double_bicat.
    - exact double_cat_to_ver_bicat_sq_id_comp_whisker.
    - exact double_cat_to_double_bicat_laws.
  Defined.

  Definition double_cat_vertically_saturated
    : vertically_saturated
        double_cat_to_verity_double_bicat.
  Proof.
    refine (λ (x y : C) (h₁ h₂ : x -->h y), _).
    use isweq_iso.
    - exact (idfun _).
    - abstract
        (intros s ; cbn ;
         refine (maponpaths (transportf_square _ _) (square_id_right_v _) @ _) ;
         unfold transportb_square ;
         rewrite transportf_f_square ;
         apply transportf_square_id).
    - abstract
        (intros s ; cbn ;
         refine (maponpaths (transportf_square _ _) (square_id_right_v _) @ _) ;
         unfold transportb_square ;
         rewrite transportf_f_square ;
         apply transportf_square_id).
  Defined.

  Definition double_cat_horizontal_cells_are_squares
             (H : ver_weq_square C)
    : horizontally_saturated
        double_cat_to_verity_double_bicat.
  Proof.
    refine (λ (x y : C) (v₁ v₂ : x -->v y), _).
    use isweqimplimpl.
    - cbn.
      intros s.
      exact (invmap (make_weq _ (H x y v₁ v₂)) s).
    - apply homset_property.
    - apply isaprop_square_ver_weq_square.
      exact H.
  Defined.

  Definition is_weak_double_cat_double_cat
             (H : ver_weq_square C)
    : is_weak_double_cat
        double_cat_to_verity_double_bicat.
  Proof.
    split.
    - exact double_cat_vertically_saturated.
    - exact (double_cat_horizontal_cells_are_squares H).
  Defined.
End DoubleCatToDoubleBicat.

(** * 5. The univalence of this Verity double bicategory *)
Definition locally_univalent_double_cat_to_verity_double_bicat
           (C : univalent_double_cat)
  : locally_univalent_verity_double_bicat
      (double_cat_to_verity_double_bicat C).
Proof.
  split.
  - apply is_univalent_2_1_cat_to_bicat.
  - exact (is_univalent_2_1_horizontal_bicat C).
Defined.

Definition hor_globally_univalent_double_cat_to_verity_double_bicat
           (C : univalent_double_cat)
  : hor_globally_univalent
      (double_cat_to_verity_double_bicat C).
Proof.
  use is_univalent_2_0_cat_to_bicat.
  exact (is_univalent_vertical_cat C).
Defined.

Definition gregarious_univalent_double_cat_to_verity_double_bicat
           (C : univalent_double_cat)
  : gregarious_univalent
      (double_cat_to_verity_double_bicat C).
Proof.
  use hor_globally_univalent_to_gregarious_univalent.
  - exact (locally_univalent_double_cat_to_verity_double_bicat C).
  - exact (hor_globally_univalent_double_cat_to_verity_double_bicat C).
  - exact (double_cat_vertically_saturated C).
Defined.

(** * 6. Companions and conjoints *)
Definition double_cat_to_verity_double_bicat_are_companions
           {C : double_cat}
           {x y : C}
           (h : x -->h y)
           (v : x -->v y)
  : double_cat_are_companions h v
    ≃
    are_companions
      (B := double_cat_to_verity_double_bicat C)
      v h.
Proof.
  use weqfibtototal.
  intro φ.
  use weqfibtototal.
  intro ψ.
  use weqimplimpl.
  - abstract
      (intros p ;
       induction p as [ p₁ p₂ ] ;
       refine (p₁ ,, _) ;
       refine (_ @ p₂) ;
       cbn -[transportf_square] ;
       do 2 use transportf_square_eq ;
       apply idpath).
  - abstract
      (cbn -[transportf_square] ;
       intros p ;
       induction p as [ p₁ p₂ ] ;
       refine (p₁ ,, _) ;
       refine (_ @ p₂) ;
       do 2 use transportf_square_eq ;
       apply idpath).
  - abstract (apply isapropdirprod ; apply isaset_square).
  - abstract (apply isapropdirprod ; apply isaset_square).
Defined.

Definition all_companions_double_cat_to_verity_double_bicat
           {C : double_cat}
           (H : all_companions_double_cat C)
  : all_companions (double_cat_to_verity_double_bicat C).
Proof.
  intros x y v.
  simple refine (_ ,, _).
  - exact (pr1 (H x y v)).
  - use double_cat_to_verity_double_bicat_are_companions.
    exact (pr2 (H x y v)).
Defined.

Definition double_cat_to_verity_double_bicat_are_conjoints
           {C : double_cat}
           {x y : C}
           (h : y -->h x)
           (v : x -->v y)
  : double_cat_are_conjoints h v
    ≃
    are_conjoints
      (B := double_cat_to_verity_double_bicat C)
      v h.
Proof.
  use weqfibtototal.
  intro φ.
  use weqfibtototal.
  intro ψ.
  use weqimplimpl.
  - abstract
      (intros p ;
       induction p as [ p₁ p₂ ] ;
       refine (p₁ ,, _) ;
       refine (_ @ p₂) ;
       cbn -[transportf_square] ;
       do 2 use transportf_square_eq ;
       apply idpath).
  - abstract
      (cbn -[transportf_square] ;
       intros p ;
       induction p as [ p₁ p₂ ] ;
       refine (p₁ ,, _) ;
       refine (_ @ p₂) ;
       do 2 use transportf_square_eq ;
       apply idpath).
  - abstract (apply isapropdirprod ; apply isaset_square).
  - abstract (apply isapropdirprod ; apply isaset_square).
Defined.

Definition all_conjoints_double_cat_to_verity_double_bicat
           {C : double_cat}
           (H : all_conjoints_double_cat C)
  : all_conjoints (double_cat_to_verity_double_bicat C).
Proof.
  intros x y v.
  simple refine (_ ,, _).
  - exact (pr1 (H x y v)).
  - use double_cat_to_verity_double_bicat_are_conjoints.
    exact (pr2 (H x y v)).
Defined.
