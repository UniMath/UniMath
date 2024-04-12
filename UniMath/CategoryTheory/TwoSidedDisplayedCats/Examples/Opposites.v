(***********************************************************************************************

 Opposites of 2-sided displayed categories

 In this file, we define two opposites of 2-sided displayed categories. They are inspired by
 double categories. More specifically, given a double category `C`, we can form a vertical
 opposite where we reverse the vertical morphisms and a horizontal opposite where we reverse the
 horizontal morphisms. To construct these double categories, we first construct the corresponding
 operations on the level of 2-sided displayed categories.

 For 2-sided displayed categories, we can interpret these operations as follows. Suppose that we
 have a 2-sided displayed category `D` over `C₁` and `C₂`. Then we can form a 2-sided displayed
 category over `C₁^op` and `C₂^op` ([ver_op_twosided_disp_cat]), and this corresponds to the
 vertical opposite of double categories. In addition, if we have a 2-sided displayed category `D`
 over `C₁` and `C₂`, then we also have a 2-sided displayed category over `C₂` and `C₂`, which is
 given in [hor_op_twosided_disp_cat]. This corresponds to the horizontal opposite of double
 categories.

 Contents
 1. The vertical opposite
 1.1. The construction of the 2-sided displayed category
 1.2. Isos in the vertical opposite
 1.3. The univalence of the vertical opposite
 2. The horizontal opposite
 2.1. The construction of the 2-sided displayed category
 2.2. Isos in the horizontal opposite
 2.3. The univalence of the horizontal opposite

 ***********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.

Local Open Scope cat.

(** * 1. The vertical opposite *)
Section VerOpposite.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂).

  (** * 1.1. The construction of the 2-sided displayed category *)
  Definition ver_op_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor (C₁^op) (C₂^op).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, D x y).
    - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g, xy₂ -->[ f ][ g ] xy₁).
  Defined.

  Definition ver_op_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp ver_op_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - exact (λ (x : C₁) (y : C₂) (xy : D x y), id_two_disp xy).
    - exact (λ (x₁ x₂ x₃ : C₁)
               (y₁ y₂ y₃ : C₂)
               (xy₁ : D x₁ y₁)
               (xy₂ : D x₂ y₂)
               (xy₃ : D x₃ y₃)
               (f₁ : x₂ --> x₁) (f₂ : x₃ --> x₂)
               (g₁ : y₂ --> y₁) (g₂ : y₃ --> y₂)
               (fg₁ : xy₂ -->[ f₁ ][ g₁ ] xy₁)
               (fg₂ : xy₃ -->[ f₂ ][ g₂ ] xy₂),
             fg₂ ;;2 fg₁).
  Defined.

  Definition ver_op_twosided_disp_cat_data
    : twosided_disp_cat_data (C₁^op) (C₂^op).
  Proof.
    simple refine (_ ,, _).
    - exact ver_op_twosided_disp_cat_ob_mor.
    - exact ver_op_twosided_disp_cat_id_comp.
  Defined.

  Proposition ver_op_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms ver_op_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros ; cbn in *.
      apply (id_two_disp_right (D := D)).
    - intro ; intros ; cbn in *.
      apply (id_two_disp_left (D := D)).
    - intro ; intros ; cbn in *.
      refine (assoc_two_disp_alt (D := D) _ _ _ @ _).
      unfold transportb_disp_mor2.
      use transportf_disp_mor2_eq.
      apply idpath.
    - intro ; intros.
      apply isaset_disp_mor.
  Qed.

  Definition ver_op_twosided_disp_cat
    : twosided_disp_cat (C₁^op) (C₂^op).
  Proof.
    simple refine (_ ,, _).
    - exact ver_op_twosided_disp_cat_data.
    - exact ver_op_twosided_disp_cat_axioms.
  Defined.

  (** * 1.2. Isos in the vertical opposite *)
  Definition to_iso_ver_op_twosided_disp_cat
             {x : C₁}
             {y : C₂}
             {xy₁ xy₂ : D x y}
             (fg : xy₁ -->[ identity _ ][ identity _ ] xy₂)
             (Hfg : is_iso_twosided_disp
                      (D := D)
                      (identity_is_z_iso _) (identity_is_z_iso _)
                      fg)
    : is_iso_twosided_disp
        (D := ver_op_twosided_disp_cat)
        (identity_is_z_iso _)
        (identity_is_z_iso _)
        fg.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (iso_inv_twosided_disp Hfg).
    - abstract
        (refine (iso_after_inv_twosided_disp Hfg @ _) ;
         use transportb_disp_mor2_eq ;
         apply idpath).
    - abstract
        (refine (inv_after_iso_twosided_disp Hfg @ _) ;
         use transportb_disp_mor2_eq ;
         apply idpath).
  Defined.

  Definition from_iso_ver_op_twosided_disp_cat
             {x : C₁}
             {y : C₂}
             {xy₁ xy₂ : D x y}
             (fg : xy₁ -->[ identity _ ][ identity _ ] xy₂)
             (Hfg : is_iso_twosided_disp
                      (D := ver_op_twosided_disp_cat)
                      (identity_is_z_iso _)
                      (identity_is_z_iso _)
                      fg)
    : is_iso_twosided_disp
        (D := D)
        (identity_is_z_iso _) (identity_is_z_iso _)
        fg.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (iso_inv_twosided_disp Hfg).
    - abstract
        (refine (iso_after_inv_twosided_disp Hfg @ _) ;
         use transportb_disp_mor2_eq ;
         apply idpath).
    - abstract
        (refine (inv_after_iso_twosided_disp Hfg @ _) ;
         use transportb_disp_mor2_eq ;
         apply idpath).
  Defined.

  Definition iso_ver_op_twosided_disp_cat_weq
             {x : C₁}
             {y : C₂}
             (xy₁ xy₂ : D x y)
    : iso_twosided_disp (D := D) (identity_z_iso _) (identity_z_iso _) xy₁ xy₂
      ≃
      iso_twosided_disp
        (D := ver_op_twosided_disp_cat)
        (identity_z_iso _) (identity_z_iso _)
        xy₂ xy₁.
  Proof.
    use weqfibtototal.
    intros fg.
    use weqimplimpl.
    - apply to_iso_ver_op_twosided_disp_cat.
    - apply from_iso_ver_op_twosided_disp_cat.
    - apply isaprop_is_iso_twosided_disp.
    - apply isaprop_is_iso_twosided_disp.
  Defined.

  (** * 1.3. The univalence of the vertical opposite *)
  Definition is_univalent_ver_op_twosided_disp_cat
             (H : is_univalent_twosided_disp_cat D)
    : is_univalent_twosided_disp_cat ver_op_twosided_disp_cat.
  Proof.
    intros x x' y y' p q xy xy'.
    induction p, q ; cbn.
    use weqhomot.
    - exact (iso_ver_op_twosided_disp_cat_weq _ _
             ∘ make_weq _ (H x x y y (idpath _) (idpath _) xy' xy)
             ∘ weqpathsinv0 _ _)%weq.
    - intros p.
      use subtypePath.
      {
        intro.
        apply isaprop_is_iso_twosided_disp.
      }
      induction p.
      cbn.
      apply idpath.
  Qed.

  Proposition is_strict_ver_op_twosided_disp_cat
              (H : is_strict_twosided_disp_cat D)
    : is_strict_twosided_disp_cat ver_op_twosided_disp_cat.
  Proof.
    intros x y.
    apply H.
  Qed.
End VerOpposite.

(** * 2. The horizontal opposite *)
Section HorOpposite.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂).

  (** * 2.1. The construction of the 2-sided displayed category *)
  Definition hor_op_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₂ C₁.
  Proof.
    simple refine (_ ,, _).
    - exact (λ y x, D x y).
    - exact (λ y₁ y₂ x₁ x₂ xy₁ xy₂ g f, xy₁ -->[ f ][ g ] xy₂).
  Defined.

  Definition hor_op_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp hor_op_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - exact (λ y x xy, id_two_disp xy).
    - exact (λ y₁ y₂ y₃ x₁ x₂ x₃ xy₁ xy₂ xy₃ g₁ g₂ f₁ f₂ fg₁ fg₂, fg₁ ;;2 fg₂).
  Defined.

  Definition hor_op_twosided_disp_cat_data
    : twosided_disp_cat_data C₂ C₁.
  Proof.
    simple refine (_ ,, _).
    - exact hor_op_twosided_disp_cat_ob_mor.
    - exact hor_op_twosided_disp_cat_id_comp.
  Defined.

  Proposition transportf_disp_mor2_hor_op
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {xy₁ : D x₁ y₁}
              {xy₂ : D x₂ y₂}
              {f f' : x₁ --> x₂}
              (p : f = f')
              {g g' : y₁ --> y₂}
              (q : g = g')
              (fg : xy₁ -->[ f ][ g ] xy₂)
    : transportf_disp_mor2
        (D := hor_op_twosided_disp_cat_data)
        q
        p
        fg
      =
      transportf_disp_mor2
        (D := D)
        p
        q
        fg.
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Proposition transportb_disp_mor2_hor_op
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {xy₁ : D x₁ y₁}
              {xy₂ : D x₂ y₂}
              {f f' : x₁ --> x₂}
              (p : f' = f)
              {g g' : y₁ --> y₂}
              (q : g' = g)
              (fg : xy₁ -->[ f ][ g ] xy₂)
    : transportb_disp_mor2
        (D := hor_op_twosided_disp_cat_data)
        q
        p
        fg
      =
      transportb_disp_mor2
        (D := D)
        p
        q
        fg.
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Proposition hor_op_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms hor_op_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros ; cbn.
      refine (id_two_disp_left _ @ !_).
      apply transportb_disp_mor2_hor_op.
    - intro ; intros ; cbn.
      refine (id_two_disp_right _ @ !_).
      apply transportb_disp_mor2_hor_op.
    - intro ; intros ; cbn.
      refine (assoc_two_disp _ _ _ @ !_).
      apply transportb_disp_mor2_hor_op.
    - intro ; intros.
      apply isaset_disp_mor.
  Qed.

  Definition hor_op_twosided_disp_cat
    : twosided_disp_cat C₂ C₁.
  Proof.
    simple refine (_ ,, _).
    - exact hor_op_twosided_disp_cat_data.
    - exact hor_op_twosided_disp_cat_axioms.
  Defined.

  (** * 2.2. Isos in the horizontal opposite *)
  Definition to_iso_hor_op_twosided_disp_cat
             {x : C₁}
             {y : C₂}
             {xy₁ xy₂ : D x y}
             (fg : xy₁ -->[ identity _ ][ identity _ ] xy₂)
             (Hfg : is_iso_twosided_disp
                      (D := D)
                      (identity_is_z_iso _) (identity_is_z_iso _)
                      fg)
    : is_iso_twosided_disp
        (D := hor_op_twosided_disp_cat)
        (identity_is_z_iso y)
        (identity_is_z_iso x)
        fg.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (iso_inv_twosided_disp Hfg).
    - abstract
        (refine (inv_after_iso_twosided_disp Hfg @ _) ;
         refine (_ @ !(transportb_disp_mor2_hor_op _ _ _)) ;
         use transportb_disp_mor2_eq ;
         apply idpath).
    - abstract
        (refine (iso_after_inv_twosided_disp Hfg @ _) ;
         refine (_ @ !(transportb_disp_mor2_hor_op _ _ _)) ;
         use transportb_disp_mor2_eq ;
         apply idpath).
  Defined.

  Definition from_iso_hor_op_twosided_disp_cat
             {x : C₁}
             {y : C₂}
             {xy₁ xy₂ : D x y}
             (fg : xy₁ -->[ identity _ ][ identity _ ] xy₂)
             (Hfg : is_iso_twosided_disp
                      (D := hor_op_twosided_disp_cat)
                      (identity_is_z_iso y)
                      (identity_is_z_iso x)
                      fg)
    : is_iso_twosided_disp
        (D := D)
        (identity_is_z_iso _) (identity_is_z_iso _)
        fg.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (iso_inv_twosided_disp Hfg).
    - abstract
        (refine (inv_after_iso_twosided_disp Hfg @ _) ;
         refine (transportb_disp_mor2_hor_op _ _ _ @ _) ;
         use transportb_disp_mor2_eq ;
         apply idpath).
    - abstract
        (refine (iso_after_inv_twosided_disp Hfg @ _) ;
         refine (transportb_disp_mor2_hor_op _ _ _ @ _) ;
         use transportb_disp_mor2_eq ;
         apply idpath).
  Defined.

  Definition iso_hor_op_twosided_disp_cat_weq
             {x : C₁}
             {y : C₂}
             (xy₁ xy₂ : D x y)
    : iso_twosided_disp (D := D) (identity_z_iso _) (identity_z_iso _) xy₁ xy₂
      ≃
      iso_twosided_disp
        (D := hor_op_twosided_disp_cat)
        (identity_z_iso _) (identity_z_iso _)
        xy₁ xy₂.
  Proof.
    use weqfibtototal.
    intros fg.
    use weqimplimpl.
    - apply to_iso_hor_op_twosided_disp_cat.
    - apply from_iso_hor_op_twosided_disp_cat.
    - apply isaprop_is_iso_twosided_disp.
    - apply isaprop_is_iso_twosided_disp.
  Defined.

  (** * 2.3. The univalence of the horizontal opposite *)
  Definition is_univalent_hor_op_twosided_disp_cat
             (H : is_univalent_twosided_disp_cat D)
    : is_univalent_twosided_disp_cat hor_op_twosided_disp_cat.
  Proof.
    intros y y' x x' p q xy xy'.
    induction p, q ; cbn.
    use weqhomot.
    - exact (iso_hor_op_twosided_disp_cat_weq _ _
             ∘ make_weq _ (H x x y y (idpath _) (idpath _) xy xy'))%weq.
    - intros p.
      use subtypePath.
      {
        intro.
        apply isaprop_is_iso_twosided_disp.
      }
      induction p.
      cbn.
      apply idpath.
  Qed.

  Proposition is_strict_hor_op_twosided_disp_cat
              (H : is_strict_twosided_disp_cat D)
    : is_strict_twosided_disp_cat hor_op_twosided_disp_cat.
  Proof.
    intros x y.
    apply H.
  Qed.
End HorOpposite.
