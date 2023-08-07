(**********************************************************************************

 The displayed bicategory of two-sided displayed categories

 In this file, we define the bicategory of two-sided displayed categories. The
 displayed objects over a univalent category `C` are univalent two-sided displayed
 categories from `C` to `C`. The displayed 1-cells and 2-cells are defined
 analogously, but with functors and natural transformations instead.

 We also prove that this displayed bicategory is univalent. For that, we use the
 following idea:
 - We already know that the displayed bicategory of displayed categories is
   univalent.
 - We have an isomorphism from the displayed bicategory of two-sided displayed
   categories to the displayed bicategory of displayed categories.
 - Isomorphisms of displayed bicategories transport univalence.
 Note that this isomorphism lies over the diagonal pseudofunctor, because a
 two-sided displayed category over `C` is the same as a displayed category over
 `C × C`.

 Contents
 1. The displayed bicategory of two-sided displayed categories
 2. A pseudofunctor into displayed categories
 3. This pseudofunctor is an isomorphism
 4. The univalence

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.UnivalenceTechniques.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.CatDiag.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

Local Open Scope cat.

(**
 1. The displayed bicategory of two-sided displayed categories
 *)
Definition disp_cat_ob_mor_twosided_disp_cat
  : disp_cat_ob_mor bicat_of_univ_cats.
Proof.
  simple refine (_ ,, _).
  - exact (λ (C : univalent_category), univalent_twosided_disp_cat C C).
  - exact (λ (C₁ C₂ : univalent_category)
             (D₁ : univalent_twosided_disp_cat C₁ C₁)
             (D₂ : univalent_twosided_disp_cat C₂ C₂)
             (F : C₁ ⟶ C₂),
           twosided_disp_functor F F D₁ D₂).
Defined.

Definition disp_cat_id_comp_twosided_disp_cat
  : disp_cat_id_comp bicat_of_univ_cats disp_cat_ob_mor_twosided_disp_cat.
Proof.
  simple refine (_ ,, _).
  - exact (λ C D, twosided_disp_functor_identity _).
  - exact (λ C₁ C₂ C₃ F G D₁ D₂ D₃ FF GG, comp_twosided_disp_functor FF GG).
Defined.

Definition disp_cat_data_twosided_disp_cat
  : disp_cat_data bicat_of_univ_cats.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_twosided_disp_cat.
  - exact disp_cat_id_comp_twosided_disp_cat.
Defined.

Definition disp_prebicat_1_id_comp_twosided_disp_cat
  : disp_prebicat_1_id_comp_cells bicat_of_univ_cats.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_twosided_disp_cat.
  - exact (λ C₁ C₂ F G τ D₁ D₂ FF GG, twosided_disp_nat_trans τ τ (pr1 FF) (pr1 GG)).
Defined.

Definition disp_prebicat_ops_twosided_disp_cat
  : disp_prebicat_ops disp_prebicat_1_id_comp_twosided_disp_cat.
Proof.
  repeat split.
  - exact (λ C₁ C₂ F D₁ D₂ FF,
           id_twosided_disp_nat_trans FF).
  - exact (λ C₁ C₂ F D₁ D₂ FF,
           id_twosided_disp_nat_trans FF).
  - exact (λ C₁ C₂ F D₁ D₂ FF,
           id_twosided_disp_nat_trans FF).
  - exact (λ C₁ C₂ F D₁ D₂ FF,
           id_twosided_disp_nat_trans FF).
  - exact (λ C₁ C₂ F D₁ D₂ FF,
           id_twosided_disp_nat_trans FF).
  - exact (λ C₁ C₂ C₃ C₄ F G H D₁ D₂ D₃ D₄ FF GG HH,
           id_twosided_disp_nat_trans
             (comp_twosided_disp_functor
                FF
                (comp_twosided_disp_functor GG HH))).
  - exact (λ C₁ C₂ C₃ C₄ F G H D₁ D₂ D₃ D₄ FF GG HH,
           id_twosided_disp_nat_trans
             (comp_twosided_disp_functor
                (comp_twosided_disp_functor FF GG)
                HH)).
  - exact (λ C₁ C₂ F G H τ θ D₁ D₂ FF GG HH ττ θθ,
           comp_twosided_disp_nat_trans ττ θθ).
  - exact (λ C₁ C₂ C₃ F G₁ G₂ τ D₁ D₂ D₃ FF GG₁ GG₂ ττ,
           pre_whisker_twosided_disp_nat_trans FF ττ).
  - exact (λ C₁ C₂ C₃ F₁ F₂ G τ D₁ D₂ D₃ FF₁ FF₂ GG ττ,
           post_whisker_twosided_disp_nat_trans GG ττ).
Defined.

Definition disp_prebicat_data_twosided_disp_cat
  : disp_prebicat_data bicat_of_univ_cats.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_1_id_comp_twosided_disp_cat.
  - exact disp_prebicat_ops_twosided_disp_cat.
Defined.

Proposition transportb_prebicat_twosided_disp_cat
            {C₁ C₂ : bicat_of_univ_cats}
            {F G : C₁ --> C₂}
            {τ θ : F ==> G}
            (p : τ = θ)
            {D₁ : disp_prebicat_data_twosided_disp_cat C₁}
            {D₂ : disp_prebicat_data_twosided_disp_cat C₂}
            {FF : D₁ -->[ F ] D₂}
            {GG : D₁ -->[ G ] D₂}
            (θθ : FF ==>[ θ ] GG)
            (x y : pr11 C₁)
            (xy : pr11 D₁ x y)
  : pr1 (transportb (λ z, FF ==>[ z ] GG) p θθ) x y xy
    =
    transportb
      (λ z, _ -->[ z ][ _ ] _)
      (maponpaths (λ n, pr1 n x) p)
      (transportb
         (λ z, _ -->[ _ ][ z ] _)
         (maponpaths (λ n, pr1 n y) p)
         (pr1 θθ x y xy)).
Proof.
  induction p.
  cbn.
  apply idpath.
Qed.

Proposition disp_prebicat_laws_twosided_disp_cat
  : disp_prebicat_laws disp_prebicat_data_twosided_disp_cat.
Proof.
  repeat split ;
  intro ; intros ;
  use eq_twosided_disp_nat_trans ;
  intros ;
  refine (_ @ !(transportb_prebicat_twosided_disp_cat _ _ _ _ _)) ; cbn.
  - rewrite id_two_disp_left.
    rewrite !twosided_prod_transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_right.
    rewrite !twosided_prod_transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite assoc_two_disp.
    rewrite !twosided_prod_transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite !twosided_prod_transportb.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (_ @ idpath (idpath _)).
      apply isaset_dirprod ; apply homset_property.
    }
    apply idpath.
  - rewrite twosided_disp_functor_id.
    rewrite !twosided_prod_transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite !twosided_prod_transportb.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (_ @ idpath (idpath _)).
      apply isaset_dirprod ; apply homset_property.
    }
    apply idpath.
  - rewrite twosided_disp_functor_comp_alt.
    rewrite twosided_prod_transport.
    rewrite !twosided_prod_transportb.
    unfold transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_left, id_two_disp_right.
    rewrite !twosided_prod_transportb.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_left, id_two_disp_right.
    rewrite !twosided_prod_transportb.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_left, id_two_disp_right.
    rewrite !twosided_prod_transportb.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_left, id_two_disp_right.
    rewrite !twosided_prod_transportb.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_left, id_two_disp_right.
    rewrite !twosided_prod_transportb.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite (pr2 φφ).
    rewrite !twosided_prod_transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_left.
    rewrite !twosided_prod_transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_left.
    rewrite !twosided_prod_transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_left.
    rewrite !twosided_prod_transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_left.
    rewrite !twosided_prod_transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_left.
    rewrite !twosided_prod_transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_left.
    rewrite !twosided_prod_transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - rewrite id_two_disp_left.
    rewrite twosided_disp_functor_id.
    rewrite !twosided_prod_transportb.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  - etrans.
    {
      rewrite id_two_disp_left.
      unfold transportb.
      rewrite two_disp_pre_whisker_left.
      rewrite two_disp_pre_whisker_right.
      rewrite twosided_prod_transport.
      rewrite id_two_disp_left.
      unfold transportb.
      rewrite twosided_prod_transport.
      rewrite transport_f_f.
      rewrite twosided_disp_functor_id.
      unfold transportb.
      rewrite twosided_prod_transport.
      rewrite transport_f_f.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      unfold transportb.
      rewrite twosided_prod_transport.
      rewrite id_two_disp_left.
      unfold transportb.
      rewrite twosided_prod_transport.
      rewrite transport_f_f.
      apply idpath.
    }
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
Qed.

Definition disp_prebicat_twosided_disp_cat
  : disp_prebicat bicat_of_univ_cats.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_data_twosided_disp_cat.
  - exact disp_prebicat_laws_twosided_disp_cat.
Defined.

Definition disp_bicat_twosided_disp_cat
  : disp_bicat bicat_of_univ_cats.
Proof.
  refine (disp_prebicat_twosided_disp_cat ,, _).
  intros C₁ C₂ F G τ D₁ D₂ FF GG.
  apply isaset_twosided_disp_nat_trans.
Defined.

Definition bicat_twosided_disp_cat
  : bicat
  := total_bicat disp_bicat_twosided_disp_cat.

(**
 2. A pseudofunctor into displayed categories
 *)
Definition twosided_disp_cat_to_disp_cat_psfunctor_id
           {C : category}
           (D : twosided_disp_cat C C)
  : disp_nat_trans
      (nat_trans_id (functor_identity _))
      (disp_functor_identity (twosided_disp_cat_to_disp_cat C C (pr1 D)))
      (two_sided_disp_functor_to_disp_functor (twosided_disp_functor_identity D)).
Proof.
  refine ((λ x xx, id_disp _) ,, _).
  abstract
    (intros x y f xx yy ff ; cbn ;
     rewrite id_two_disp_right ;
     rewrite id_two_disp_left ;
     rewrite <- !transportb_dirprodeq ;
     rewrite transport_b_b ;
     apply maponpaths_2 ;
     apply isasetdirprod ; apply homset_property).
Defined.

Definition twosided_disp_cat_to_disp_cat_psfunctor_comp
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {D₃ : twosided_disp_cat C₃ C₃}
           (FF : twosided_disp_functor F F D₁ D₂)
           (GG : twosided_disp_functor G G D₂ D₃)
  : disp_nat_trans
      (nat_trans_id _)
      (disp_functor_composite
         (two_sided_disp_functor_to_disp_functor FF)
         (two_sided_disp_functor_to_disp_functor GG))
      (two_sided_disp_functor_to_disp_functor
         (comp_twosided_disp_functor FF GG)).
Proof.
  refine ((λ x xx, id_disp _) ,, _).
  abstract
    (intros x y f xx yy ff ; cbn ;
     rewrite id_two_disp_right ;
     rewrite id_two_disp_left ;
     rewrite <- !transportb_dirprodeq ;
     rewrite transport_b_b ;
     apply maponpaths_2 ;
     apply isasetdirprod ; apply homset_property).
Defined.

Definition twosided_disp_cat_to_disp_cat_psfunctor_data
  : disp_psfunctor_data
      disp_bicat_twosided_disp_cat
      disp_bicat_of_univ_disp_cats
      diag_univ_cat.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact (λ C D, univalent_twosided_disp_cat_weq_univalent_disp_cat _ _ D).
  - exact (λ C₁ C₂ F D₁ D₂ FF, two_sided_disp_functor_to_disp_functor FF).
  - exact (λ C₁ C₂ F G τ D₁ D₂ FF GG ττ, twosided_disp_nat_trans_to_disp_nat_trans ττ).
  - intros C D.
    refine (twosided_disp_cat_to_disp_cat_psfunctor_id (pr1 D) ,, _).
    simple refine (_ ,, _ ,, _).
    + refine ((λ x xx, id_disp _) ,, _).
      abstract
        (intros x y f xx yy ff ; cbn ;
         rewrite id_two_disp_right ;
         rewrite id_two_disp_left ;
         rewrite <- !transportb_dirprodeq ;
         rewrite transport_b_b ;
         apply maponpaths_2 ;
         apply isasetdirprod ; apply homset_property).
    + abstract
        (use disp_nat_trans_eq ;
         intros x xx ;
         unfold transportb ;
         refine (_ @ !(disp_nat_trans_transportf _ _ _ _ _ _ _ _ _ _)) ; cbn ;
         rewrite id_two_disp_left ;
         rewrite <- transportb_dirprodeq ;
         unfold transportb ;
         apply maponpaths_2 ;
         apply isasetdirprod ; apply homset_property).
    + abstract
        (use disp_nat_trans_eq ;
         intros x xx ;
         unfold transportb ;
         refine (_ @ !(disp_nat_trans_transportf _ _ _ _ _ _ _ _ _ _)) ; cbn ;
         rewrite id_two_disp_left ;
         rewrite <- transportb_dirprodeq ;
         unfold transportb ;
         apply maponpaths_2 ;
         apply isasetdirprod ; apply homset_property).
  - intros C₁ C₂ C₃ F G D₁ D₂ D₃ FF GG.
    refine (twosided_disp_cat_to_disp_cat_psfunctor_comp FF GG ,, _).
    simple refine (_ ,, _ ,, _).
    + refine ((λ x xx, id_disp _) ,, _).
      abstract
        (intros x y f xx yy ff ; cbn ;
         rewrite id_two_disp_right ;
         rewrite id_two_disp_left ;
         rewrite <- !transportb_dirprodeq ;
         rewrite transport_b_b ;
         apply maponpaths_2 ;
         apply isasetdirprod ; apply homset_property).
    + abstract
        (use disp_nat_trans_eq ;
         intros x xx ;
         unfold transportb ;
         refine (_ @ !(disp_nat_trans_transportf _ _ _ _ _ _ _ _ _ _)) ; cbn ;
         rewrite id_two_disp_left ;
         rewrite <- transportb_dirprodeq ;
         unfold transportb ;
         apply maponpaths_2 ;
         apply isasetdirprod ; apply homset_property).
    + abstract
        (use disp_nat_trans_eq ;
         intros x xx ;
         unfold transportb ;
         refine (_ @ !(disp_nat_trans_transportf _ _ _ _ _ _ _ _ _ _)) ; cbn ;
         rewrite id_two_disp_left ;
         rewrite <- transportb_dirprodeq ;
         unfold transportb ;
         apply maponpaths_2 ;
         apply isasetdirprod ; apply homset_property).
Defined.

Proposition twosided_disp_cat_to_disp_cat_psfunctor_laws
  : is_disp_psfunctor
      disp_bicat_twosided_disp_cat
      disp_bicat_of_univ_disp_cats
      diag_univ_cat
      twosided_disp_cat_to_disp_cat_psfunctor_data.
Proof.
  repeat split.
  - intros C₁ C₂ F D₁ D₂ FF.
    use disp_nat_trans_eq.
    intros x xx.
    unfold transportb.
    refine (!_).
    etrans.
    {
      apply disp_nat_trans_transportf.
    }
    cbn.
    rewrite transportf_set.
    + apply idpath.
    + apply isasetdirprod ; apply homset_property.
  - intros C₁ C₂ F₁ F₂ F₃ τ θ D₁ D₂ FF₁ FF₂ FF₃ ττ θθ.
    use disp_nat_trans_eq.
    intros x xx.
    unfold transportb.
    refine (!_).
    etrans.
    {
      apply disp_nat_trans_transportf.
    }
    cbn.
    rewrite transportf_set.
    + apply idpath.
    + apply isasetdirprod ; apply homset_property.
  - intros C₁ C₂ F D₁ D₂ FF.
    use disp_nat_trans_eq.
    intros x xx.
    unfold transportb.
    refine (!_).
    etrans.
    {
      apply disp_nat_trans_transportf.
    }
    cbn.
    do 2 (rewrite id_two_disp_right ; rewrite <- transportb_dirprodeq).
    rewrite twosided_disp_functor_id.
    rewrite <- transportb_dirprodeq.
    unfold transportb.
    rewrite !transport_f_f.
    rewrite transportf_set.
    + apply idpath.
    + apply isasetdirprod ; apply homset_property.
  - intros C₁ C₂ F D₁ D₂ FF.
    use disp_nat_trans_eq.
    intros x xx.
    unfold transportb.
    refine (!_).
    etrans.
    {
      apply disp_nat_trans_transportf.
    }
    cbn.
    do 2 (rewrite id_two_disp_right ; rewrite <- transportb_dirprodeq).
    unfold transportb.
    rewrite !transport_f_f.
    rewrite transportf_set.
    + apply idpath.
    + apply isasetdirprod ; apply homset_property.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ D₁ D₂ D₃ D₄ FF₁ FF₂ FF₃.
    use disp_nat_trans_eq.
    intros x xx.
    unfold transportb.
    refine (!_).
    etrans.
    {
      apply disp_nat_trans_transportf.
    }
    cbn.
    rewrite twosided_disp_functor_id.
    rewrite <- transportb_dirprodeq.
    do 3 (rewrite id_two_disp_right ; rewrite <- transportb_dirprodeq).
    rewrite id_two_disp_left ; rewrite <- transportb_dirprodeq.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply isasetdirprod ; apply homset_property.
  - intros C₁ C₂ C₃ F G₁ G₂ θ D₁ D₂ D₃ FF₁ GG₁ GG₂ θθ.
    use disp_nat_trans_eq.
    intros x xx.
    unfold transportb.
    refine (!_).
    etrans.
    {
      apply disp_nat_trans_transportf.
    }
    cbn.
    rewrite id_two_disp_right ; rewrite <- transportb_dirprodeq.
    rewrite id_two_disp_left ; rewrite <- transportb_dirprodeq.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply isasetdirprod ; apply homset_property.
  - intros C₁ C₂ C₃ F₁ F₂ G τ D₁ D₂ D₃ FF₁ FF₂ GG ττ.
    use disp_nat_trans_eq.
    intros x xx.
    unfold transportb.
    refine (!_).
    etrans.
    {
      apply disp_nat_trans_transportf.
    }
    cbn.
    rewrite id_two_disp_right ; rewrite <- transportb_dirprodeq.
    rewrite id_two_disp_left ; rewrite <- transportb_dirprodeq.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply isasetdirprod ; apply homset_property.
Qed.

Definition twosided_disp_cat_to_disp_cat_psfunctor
  : disp_psfunctor
      disp_bicat_twosided_disp_cat
      disp_bicat_of_univ_disp_cats
      diag_univ_cat.
Proof.
  simple refine (_ ,, _).
  - exact twosided_disp_cat_to_disp_cat_psfunctor_data.
  - exact twosided_disp_cat_to_disp_cat_psfunctor_laws.
Defined.

(**
 3. This pseudofunctor is an isomorphism
 *)
Proposition twosided_disp_cat_to_disp_cat_psfunctor_iso
  : disp_psfunctor_iso twosided_disp_cat_to_disp_cat_psfunctor.
Proof.
  repeat split.
  - intro C.
    exact (pr2 (univalent_twosided_disp_cat_weq_univalent_disp_cat _ _)).
  - intros C₁ C₂ F D₁ D₂.
    exact (pr2 (two_sided_disp_functor_weq_disp_functor F F (pr1 D₁) (pr1 D₂))).
  - intros C₁ C₂ F G τ D₁ D₂ FF GG.
    exact (pr2 (twosided_disp_nat_trans_weq_disp_nat_trans τ τ FF GG)).
Defined.

(**
 4. The univalence
 *)
Definition disp_univalent_2_disp_bicat_twosided_disp_cat
  : disp_univalent_2 disp_bicat_twosided_disp_cat.
Proof.
  use (disp_univalent_2_along_iso
         twosided_disp_cat_to_disp_cat_psfunctor).
  - exact twosided_disp_cat_to_disp_cat_psfunctor_iso.
  - exact disp_univalent_2_1_disp_bicat_of_univ_disp_cat.
  - exact univalent_cat_is_univalent_2_1.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_0_disp_bicat_of_univ_disp_cat.
Defined.

Definition is_univalent_2_1_bicat_twosided_disp_cat
  : is_univalent_2_1 bicat_twosided_disp_cat.
Proof.
  use total_is_univalent_2_1.
  - exact univalent_cat_is_univalent_2_1.
  - exact (pr2 disp_univalent_2_disp_bicat_twosided_disp_cat).
Defined.

Definition is_univalent_2_0_bicat_twosided_disp_cat
  : is_univalent_2_0 bicat_twosided_disp_cat.
Proof.
  use total_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_0.
  - exact (pr1 disp_univalent_2_disp_bicat_twosided_disp_cat).
Defined.

Definition is_univalent_2_bicat_twosided_disp_cat
  : is_univalent_2 bicat_twosided_disp_cat.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_twosided_disp_cat.
  - exact univalent_cat_is_univalent_2.
Defined.
