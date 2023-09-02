(**********************************************************************************

 The fiberwise product of two-sided displayed categories

 If we have two two-sided displayed categories over the same `C₁` and `C₂`, then
 we can form their product to obtain a new two-sided displayed category over `C₁`
 and `C₂`.

 Contents
 1. The definition
 2. Isomorphisms
 3. Univalence and discreteness

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.

Local Open Scope cat.

Definition transportf_dirprod_fam
           {X : UU}
           {Y₁ Y₂ : X → UU}
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           (y : Y₁ x₁ × Y₂ x₁)
  : transportf
      (λ x, Y₁ x × Y₂ x)
      p
      y
    =
    transportf Y₁ p (pr1 y) ,, transportf Y₂ p (pr2 y).
Proof.
  induction p.
  apply idpath.
Defined.

Section FiberwiseProduct.
  Context {C₁ C₂ : category}
          (D₁ D₂ : twosided_disp_cat C₁ C₂).

  (**
   1. The definition
   *)
  Definition prod_of_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, D₁ x y × D₂ x y).
    - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g,
             pr1 xy₁ -->[ f ][ g ] pr1 xy₂
             ×
             pr2 xy₁ -->[ f ][ g ] pr2 xy₂).
  Defined.

  Definition prod_of_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp prod_of_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y xy, id_two_disp (pr1 xy) ,, id_two_disp (pr2 xy)).
    - exact (λ x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ f₂ g₁ g₂ fg₁ fg₂,
             (pr1 fg₁ ;;2 pr1 fg₂) ,, (pr2 fg₁ ;;2 pr2 fg₂)).
  Defined.

  Definition prod_of_twosided_disp_cat_data
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact prod_of_twosided_disp_cat_ob_mor.
    - exact prod_of_twosided_disp_cat_id_comp.
  Defined.

  Definition prod_of_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms prod_of_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros ; cbn.
      unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn.
      rewrite transportf_dirprod_fam.
      rewrite transportf_dirprod_fam.
      use dirprod_paths ; apply id_two_disp_left.
    - intro ; intros ; cbn.
      unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn.
      rewrite transportf_dirprod_fam.
      rewrite transportf_dirprod_fam.
      use dirprod_paths ; apply id_two_disp_right.
    - intro ; intros ; cbn.
      unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn.
      rewrite transportf_dirprod_fam.
      rewrite transportf_dirprod_fam.
      use dirprod_paths ; apply assoc_two_disp.
    - intro ; intros.
      apply isasetdirprod ; apply isaset_disp_mor.
  Qed.

  Definition prod_of_twosided_disp_cat
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact prod_of_twosided_disp_cat_data.
    - exact prod_of_twosided_disp_cat_axioms.
  Defined.

  (**
   2. Isomorphisms
   *)
  Definition make_is_iso_prod_of_twosided_disp_cat
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {f : x₁ --> x₂}
             (Hf : is_z_isomorphism f)
             {g : y₁ --> y₂}
             (Hg : is_z_isomorphism g)
             {xy₁₁ : D₁ x₁ y₁}
             {xy₁₂ : D₂ x₁ y₁}
             {xy₂₁ : D₁ x₂ y₂}
             {xy₂₂ : D₂ x₂ y₂}
             (fg₁ : xy₁₁ -->[ f ][ g ] xy₂₁)
             (Hfg₁ : is_iso_twosided_disp Hf Hg fg₁)
             (fg₂ : xy₁₂ -->[ f ][ g ] xy₂₂)
             (Hfg₂ : is_iso_twosided_disp Hf Hg fg₂)
    : @is_iso_twosided_disp
        _ _
        prod_of_twosided_disp_cat
        _ _ _ _
        (xy₁₁ ,, xy₁₂)
        (xy₂₁ ,, xy₂₂)
        f g
        Hf Hg
        (fg₁ ,, fg₂).
  Proof.
    simple refine ((_ ,, _) ,, _ ,, _).
    - exact (pr1 Hfg₁).
    - exact (pr1 Hfg₂).
    - abstract
        (cbn ;
         unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn ;
         rewrite !transportf_dirprod_fam ;
         use pathsdirprod ;
         [ apply Hfg₁
         | apply Hfg₂ ]).
    - abstract
        (cbn ;
         unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn ;
         rewrite !transportf_dirprod_fam ;
         use pathsdirprod ;
         [ apply Hfg₁
         | apply Hfg₂ ]).
  Defined.

  Definition isaprop_disp_twosided_mor_prod_of_twosided_disp_cat
             (HD₁ : isaprop_disp_twosided_mor D₁)
             (HD₂ : isaprop_disp_twosided_mor D₂)
    : isaprop_disp_twosided_mor prod_of_twosided_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg fg'.
    apply pathsdirprod.
    - apply HD₁.
    - apply HD₂.
  Qed.

  Definition make_iso_prod_of_twosided_disp_cat
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {f : z_iso x₁ x₂}
             {g : z_iso y₁ y₂}
             {xy₁₁ : D₁ x₁ y₁}
             {xy₁₂ : D₂ x₁ y₁}
             {xy₂₁ : D₁ x₂ y₂}
             {xy₂₂ : D₂ x₂ y₂}
             (fg : iso_twosided_disp f g xy₁₁ xy₂₁
                   ×
                   iso_twosided_disp f g xy₁₂ xy₂₂)
    : @iso_twosided_disp
        _ _
        prod_of_twosided_disp_cat
        _ _ _ _
        f g
        (xy₁₁ ,, xy₁₂)
        (xy₂₁ ,, xy₂₂).
  Proof.
    simple refine ((_ ,, _) ,, _).
    - exact (pr11 fg).
    - exact (pr12 fg).
    - use make_is_iso_prod_of_twosided_disp_cat.
      + exact (pr21 fg).
      + exact (pr22 fg).
  Defined.

  Definition iso_prod_of_twosided_disp_cat_pr1
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {f : z_iso x₁ x₂}
             {g : z_iso y₁ y₂}
             {xy₁₁ : D₁ x₁ y₁}
             {xy₁₂ : D₂ x₁ y₁}
             {xy₂₁ : D₁ x₂ y₂}
             {xy₂₂ : D₂ x₂ y₂}
             (fg : @iso_twosided_disp
                     _ _
                     prod_of_twosided_disp_cat
                     _ _ _ _
                     f g
                     (xy₁₁ ,, xy₁₂)
                     (xy₂₁ ,, xy₂₂))
    : iso_twosided_disp f g xy₁₁ xy₂₁.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (pr11 fg).
    - exact (pr112 fg).
    - abstract
        (refine (maponpaths dirprod_pr1 (pr122 fg) @ _) ; cbn ;
         unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn ;
         rewrite !transportf_dirprod_fam ;
         apply idpath).
    - abstract
        (refine (maponpaths dirprod_pr1 (pr222 fg) @ _) ; cbn ;
         unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn ;
         rewrite !transportf_dirprod_fam ;
         apply idpath).
  Defined.

  Definition iso_prod_of_twosided_disp_cat_pr2
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {f : z_iso x₁ x₂}
             {g : z_iso y₁ y₂}
             {xy₁₁ : D₁ x₁ y₁}
             {xy₁₂ : D₂ x₁ y₁}
             {xy₂₁ : D₁ x₂ y₂}
             {xy₂₂ : D₂ x₂ y₂}
             (fg : @iso_twosided_disp
                     _ _
                     prod_of_twosided_disp_cat
                     _ _ _ _
                     f g
                     (xy₁₁ ,, xy₁₂)
                     (xy₂₁ ,, xy₂₂))
    : iso_twosided_disp f g xy₁₂ xy₂₂.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (pr21 fg).
    - exact (pr212 fg).
    - abstract
        (refine (maponpaths dirprod_pr2 (pr122 fg) @ _) ; cbn ;
         unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn ;
         rewrite !transportf_dirprod_fam ;
         apply idpath).
    - abstract
        (refine (maponpaths dirprod_pr2 (pr222 fg) @ _) ; cbn ;
         unfold transportb_disp_mor2, transportf_disp_mor2 ; cbn ;
         rewrite !transportf_dirprod_fam ;
         apply idpath).
  Defined.

  Definition from_iso_prod_of_twosided_disp_cat
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {f : z_iso x₁ x₂}
             {g : z_iso y₁ y₂}
             {xy₁₁ : D₁ x₁ y₁}
             {xy₁₂ : D₂ x₁ y₁}
             {xy₂₁ : D₁ x₂ y₂}
             {xy₂₂ : D₂ x₂ y₂}
             (fg : @iso_twosided_disp
                     _ _
                     prod_of_twosided_disp_cat
                     _ _ _ _
                     f g
                     (xy₁₁ ,, xy₁₂)
                     (xy₂₁ ,, xy₂₂))
    : iso_twosided_disp f g xy₁₁ xy₂₁
      ×
      iso_twosided_disp f g xy₁₂ xy₂₂
    := iso_prod_of_twosided_disp_cat_pr1 fg
       ,,
       iso_prod_of_twosided_disp_cat_pr2 fg.

  Definition weq_iso_prod_of_twosided_disp_cat
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {f : z_iso x₁ x₂}
             {g : z_iso y₁ y₂}
             (xy₁₁ : D₁ x₁ y₁)
             (xy₁₂ : D₂ x₁ y₁)
             (xy₂₁ : D₁ x₂ y₂)
             (xy₂₂ : D₂ x₂ y₂)
    :(iso_twosided_disp f g xy₁₁ xy₂₁
      ×
      iso_twosided_disp f g xy₁₂ xy₂₂)
     ≃
     @iso_twosided_disp
        _ _
        prod_of_twosided_disp_cat
        _ _ _ _
        f g
        (xy₁₁ ,, xy₁₂)
        (xy₂₁ ,, xy₂₂).
  Proof.
    use weq_iso.
    - exact make_iso_prod_of_twosided_disp_cat.
    - exact from_iso_prod_of_twosided_disp_cat.
    - abstract
        (intro fg ;
         use pathsdirprod ;
         (use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath)).
    - abstract
        (intro fg ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
  Defined.

  (**
   3. Univalence and discreteness
   *)
  Definition prod_twosided_disp_cat_all_disp_mor_iso
             (HD₁ : all_disp_mor_iso D₁)
             (HD₂ : all_disp_mor_iso D₂)
    : all_disp_mor_iso prod_of_twosided_disp_cat.
  Proof.
    intro ; intros.
    use make_is_iso_prod_of_twosided_disp_cat.
    - apply HD₁.
    - apply HD₂.
  Defined.

  Definition is_univalent_prod_of_twosided_disp_cat
             (HD₁ : is_univalent_twosided_disp_cat D₁)
             (HD₂ : is_univalent_twosided_disp_cat D₂)
    : is_univalent_twosided_disp_cat prod_of_twosided_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ p₁ p₂ xy₁ xy₂.
    induction p₁, p₂ ; cbn.
    use weqhomot.
    - exact (weq_iso_prod_of_twosided_disp_cat _ _ _ _
             ∘ weqdirprodf
                 (_ ,, HD₁ x₁ x₁ y₁ y₁ (idpath _) (idpath _) _ _)
                 (_ ,, HD₂ x₁ x₁ y₁ y₁ (idpath _) (idpath _) _ _)
             ∘ pathsdirprodweq)%weq.
    - abstract
        (intro p ;
         induction p ; cbn ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_twosided_disp | ] ;
         apply idpath).
  Defined.

  Definition discrete_prod_twosided_disp_cat
             (HD₁ : discrete_twosided_disp_cat D₁)
             (HD₂ : discrete_twosided_disp_cat D₂)
    : discrete_twosided_disp_cat prod_of_twosided_disp_cat.
  Proof.
    repeat split.
    - use isaprop_disp_twosided_mor_prod_of_twosided_disp_cat.
      + apply HD₁.
      + apply HD₂.
    - use prod_twosided_disp_cat_all_disp_mor_iso.
      + apply HD₁.
      + apply HD₂.
    - use is_univalent_prod_of_twosided_disp_cat.
      + apply HD₁.
      + apply HD₂.
  Qed.
End FiberwiseProduct.
