(******************************************************************************************

 The displayed category of strict 2-sided displayed categories

 In this file, we define the displayed category of strict 2-sided displayed categories over
 the category of strict categories. The objects over a strict category `C` are strict
 2-sided displayed categories over `C` and `C`, and the morphisms over a functor `F` are
 2-sided displayed functors over `F` and `F`.

 In essence, this proof is nothing more than a more complicated, convoluted, and technical
 version of the proof that the category of strict categories is univalent. The extra work
 comes mainly from the fact that we are looking at 2-sided displayed categories instead of
 categories.

 Contents
 1. The data of the displayed category of 2-sided displayed categories
 2. Transport lemmas for this displayed category
 3. The laws
 4. The displayed category of strict 2-sided displayed categories
 5. The proof that it is univalent
 5.1. Characterization of the isomorphisms
 5.2. The actual proof of univalence

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedCatEq.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.DispFunctorPair.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TransportLaws.

Local Open Scope cat.

(** * 1. The data of the displayed category of 2-sided displayed categories *)
Definition disp_cat_ob_mor_of_strict_twosided_disp_cat
  : disp_cat_ob_mor cat_of_setcategory.
Proof.
  simple refine (_ ,, _).
  - exact (λ (C : setcategory), strict_twosided_disp_cat C C).
  - exact (λ (C₁ C₂ : setcategory) D₁ D₂ (F : C₁ ⟶ C₂),
           twosided_disp_functor F F D₁ D₂).
Defined.

Definition disp_cat_id_comp_of_strict_twosided_disp_cat
  : disp_cat_id_comp
      cat_of_setcategory
      disp_cat_ob_mor_of_strict_twosided_disp_cat.
Proof.
  split.
  - exact (λ (C : setcategory) (D : strict_twosided_disp_cat C C),
           twosided_disp_functor_identity D).
  - exact (λ (C₁ C₂ C₃ : setcategory)
             (F : C₁ ⟶ C₂)
             (G : C₂ ⟶ C₃)
             (D₁ : strict_twosided_disp_cat C₁ C₁)
             (D₂ : strict_twosided_disp_cat C₂ C₂)
             (D₃ : strict_twosided_disp_cat C₃ C₃)
             (FF : twosided_disp_functor F F D₁ D₂)
             (GG : twosided_disp_functor G G D₂ D₃),
           comp_twosided_disp_functor FF GG).
Defined.

Definition disp_cat_data_of_strict_twosided_disp_cat
  : disp_cat_data cat_of_setcategory.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_of_strict_twosided_disp_cat.
  - exact disp_cat_id_comp_of_strict_twosided_disp_cat.
Defined.

(** * 2. Transport lemmas for this displayed category *)
Proposition transportb_disp_cat_of_strict_twosided_disp_cat_ob_help
            {C₁ C₂ : category}
            (D₁ : twosided_disp_cat C₁ C₁)
            (D₂ : twosided_disp_cat C₂ C₂)
            {F G : C₁ ⟶ C₂}
            (p : F = G)
            (GG : twosided_disp_functor G G D₁ D₂)
            {x y : C₁}
            (xy : D₁ x y)
  : (transportb
       (λ H, twosided_disp_functor H H D₁ D₂)
       p
       GG)
      x
      y
      xy
    =
    transportb_disp_ob2
      (path_functor_ob p _)
      (path_functor_ob p _)
      (GG x y xy).
Proof.
  induction p ; cbn.
  apply idpath.
Defined.

Proposition transportb_disp_cat_of_strict_twosided_disp_cat_ob
            {C₁ C₂ : setcategory}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            (FD : functor_data C₁ C₂)
            (HF₁ HF₂ : is_functor FD)
            (F := make_functor FD HF₁)
            (G := make_functor FD HF₂)
            (p : F = G)
            (GG : twosided_disp_functor G G D₁ D₂)
            {x y : C₁}
            (xy : D₁ x y)
  : (transportb
       (λ H, twosided_disp_functor H H D₁ D₂)
       p
       GG)
      x
      y
      xy
    =
    GG x y xy.
Proof.
  etrans.
  {
    apply transportb_disp_cat_of_strict_twosided_disp_cat_ob_help.
  }
  assert (path_functor_ob p x = idpath _) as r₁.
  {
    apply isaset_ob.
  }
  assert (path_functor_ob p y = idpath _) as r₂.
  {
    apply isaset_ob.
  }
  rewrite r₁, r₂.
  cbn.
  apply idpath.
Qed.

Proposition transportb_disp_cat_of_strict_twosided_disp_cat_mor_path
            {C₁ C₂ : setcategory}
            {F G : C₁ ⟶ C₂}
            (p : F = G)
            {x₁ x₂ : C₁}
            (f : x₁ --> x₂)
  : idtoiso (idpath (F x₁))
    · idtoiso (path_functor_ob p x₁)
    · # G f
    · idtoiso (! path_functor_ob p x₂)
    · idtoiso (idpath (F x₂))
    =
    # F f.
Proof.
  induction p ; cbn.
  rewrite !id_left.
  rewrite !id_right.
  apply idpath.
Qed.

Proposition transportb_disp_cat_of_strict_twosided_disp_cat_mor_help
            {C₁ C₂ : setcategory}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F G : C₁ ⟶ C₂}
            (p : F = G)
            (GG : twosided_disp_functor G G D₁ D₂)
            {x₁ x₂ y₁ y₂ : C₁}
            {f : x₁ --> x₂}
            {g : y₁ --> y₂}
            {xy₁ : D₁ x₁ y₁}
            {xy₂ : D₁ x₂ y₂}
            (fg : xy₁ -->[ f ][ g ] xy₂)
  : #2 (transportb
          (λ H, twosided_disp_functor H H D₁ D₂)
          p
          GG)
      fg
    =
    transportf_disp_mor2
      (transportb_disp_cat_of_strict_twosided_disp_cat_mor_path p f)
      (transportb_disp_cat_of_strict_twosided_disp_cat_mor_path p g)
      (idtoiso_twosided_disp
         (idpath _) (idpath _)
         (transportb_disp_cat_of_strict_twosided_disp_cat_ob_help D₁ D₂ p GG xy₁)
       ;;2 transportb_disp_ob2_mor _ _ _
       ;;2 #2 GG fg
       ;;2 transportb_disp_ob2_inv _ _ _
       ;;2 idtoiso_twosided_disp
             (idpath _) (idpath _)
             (!transportb_disp_cat_of_strict_twosided_disp_cat_ob_help D₁ D₂ p GG xy₂)).
Proof.
  induction p ; cbn.
  rewrite !(id_two_disp_left (D := D₂)).
  rewrite !(id_two_disp_right (D := D₂)).
  unfold transportb_disp_mor2.
  rewrite (two_disp_pre_whisker_f (D := D₂)).
  rewrite !(id_two_disp_left (D := D₂)).
  unfold transportb_disp_mor2.
  rewrite !transport_f_f_disp_mor2.
  refine (!_).
  apply transportf_disp_mor2_idpath.
Qed.

Proposition transportb_disp_cat_of_strict_twosided_disp_cat_mor
            {C₁ C₂ : setcategory}
            {D₁ : strict_twosided_disp_cat C₁ C₁}
            {D₂ : strict_twosided_disp_cat C₂ C₂}
            (FD : functor_data C₁ C₂)
            (HF₁ HF₂ : is_functor FD)
            (F := make_functor FD HF₁)
            (G := make_functor FD HF₂)
            (p : F = G)
            (GG : twosided_disp_functor G G D₁ D₂)
            {x₁ x₂ y₁ y₂ : C₁}
            {f : x₁ --> x₂}
            {g : y₁ --> y₂}
            {xy₁ : D₁ x₁ y₁}
            {xy₂ : D₁ x₂ y₂}
            (fg : xy₁ -->[ f ][ g ] xy₂)
  : #2 (transportb
          (λ H, twosided_disp_functor H H D₁ D₂)
          p
          GG)
       fg
    =
    transportf_disp_mor2
      (id_right _ @ id_left _)
      (id_right _ @ id_left _)
      (idtoiso_twosided_disp
         (idpath _) (idpath _)
         (transportb_disp_cat_of_strict_twosided_disp_cat_ob F HF₁ HF₂ p GG xy₁)
       ;;2 #2 GG fg
       ;;2 idtoiso_twosided_disp
             (idpath _) (idpath _)
             (!(transportb_disp_cat_of_strict_twosided_disp_cat_ob F HF₁ HF₂ p GG xy₂))).
Proof.
  rewrite transportb_disp_cat_of_strict_twosided_disp_cat_mor_help.
  unfold transportb_disp_ob2_mor, transportb_disp_ob2_inv.
  etrans.
  {
    apply maponpaths.
    do 3 apply maponpaths_2.
    apply idtoiso_twosided_disp_concat_strict.
  }
  unfold transportb_disp_mor2.
  rewrite !two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp_alt.
  rewrite transport_f_f_disp_mor2.
  etrans.
  {
    do 2 apply maponpaths.
    apply idtoiso_twosided_disp_concat_strict.
  }
  unfold transportb_disp_mor2.
  rewrite !two_disp_post_whisker_f.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idtoiso_twosided_disp_triple_concat.
Qed.

(** * 3. The laws *)
Proposition disp_cat_axioms_of_strict_twosided_disp_cat
  : disp_cat_axioms
      cat_of_setcategory
      disp_cat_data_of_strict_twosided_disp_cat.
Proof.
  repeat split.
  - cbn ; intros C₁ C₂ F D₁ D₂ FF.
    use eq_twosided_disp_functor.
    + intros x y xy ; cbn.
      exact (!(transportb_disp_cat_of_strict_twosided_disp_cat_ob _ _ _ _ _ _)).
    + intros x₁ x₂ f y₁ y₂ g xy₁ xy₂ fg ; cbn -[idtoiso_twosided_disp].
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply transportb_disp_cat_of_strict_twosided_disp_cat_mor.
      }
      cbn -[idtoiso_twosided_disp].
      rewrite (two_disp_post_whisker_f (D := D₂)).
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply (assoc_two_disp (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (assoc_two_disp (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        apply (idtoiso_twosided_disp_concat (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite !two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      rewrite idtoiso_twosided_disp_identity.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (id_two_disp_left (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
  - cbn ; intros C₁ C₂ F D₁ D₂ FF.
    use eq_twosided_disp_functor.
    + intros x y xy ; cbn.
      exact (!(transportb_disp_cat_of_strict_twosided_disp_cat_ob
                 F _ _
                 (@id_right cat_of_setcategory _ _ F)
                 FF
                 xy)).
    + intros x₁ x₂ f y₁ y₂ g xy₁ xy₂ fg ; cbn -[idtoiso_twosided_disp].
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply (transportb_disp_cat_of_strict_twosided_disp_cat_mor
                 _
                 _ _
                 (id_right (C := cat_of_setcategory) F)).
      }
      cbn -[idtoiso_twosided_disp].
      rewrite (two_disp_post_whisker_f (D := D₂)).
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply (assoc_two_disp (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (assoc_two_disp (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        apply (idtoiso_twosided_disp_concat (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite !two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      rewrite idtoiso_twosided_disp_identity.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (id_two_disp_left (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
  - cbn ; intros C₁ C₂ C₃ C₄ F G H D₁ D₂ D₃ D₄ FF GG HH.
    use eq_twosided_disp_functor.
    + intros x y xy ; cbn.
      exact (!(transportb_disp_cat_of_strict_twosided_disp_cat_ob
                 _ _ _
                 (@assoc cat_of_setcategory _ _ _ _ F G H)
                 (comp_twosided_disp_functor (comp_twosided_disp_functor FF GG) HH)
                 xy)).
    + intros x₁ x₂ f y₁ y₂ g xy₁ xy₂ fg.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply (transportb_disp_cat_of_strict_twosided_disp_cat_mor
                 _
                 _ _
                 (assoc (C := cat_of_setcategory) F G H)).
      }
      cbn -[idtoiso_twosided_disp].
      rewrite (two_disp_post_whisker_f (D := D₄)).
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply (assoc_two_disp (D := D₄)).
      }
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (assoc_two_disp (D := D₄)).
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        apply (idtoiso_twosided_disp_concat (D := D₄)).
      }
      unfold transportb_disp_mor2.
      rewrite !two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      rewrite idtoiso_twosided_disp_identity.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (id_two_disp_left (D := D₄)).
      }
      unfold transportb_disp_mor2.
      rewrite two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
  - intros.
    apply isaset_twosided_disp_functor.
Qed.

(** * 4. The displayed category of strict 2-sided displayed categories *)
Definition disp_cat_of_strict_twosided_disp_cat
  : disp_cat cat_of_setcategory.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_of_strict_twosided_disp_cat.
  - exact disp_cat_axioms_of_strict_twosided_disp_cat.
Defined.

Definition cat_of_strict_twosided_disp_cat
  : category
  := total_category disp_cat_of_strict_twosided_disp_cat.

(** * 5. The proof that it is univalent *)
Definition path_twosided_disp_functor_ob
           {C₁ C₂ C₁' C₂' : category}
           {F : C₁ ⟶ C₁'}
           {G : C₂ ⟶ C₂'}
           {D : twosided_disp_cat C₁ C₂}
           {D' : twosided_disp_cat C₁' C₂'}
           {FG FG' : twosided_disp_functor F G D D'}
           (p : FG = FG')
           {x : C₁}
           {y : C₂}
           (xy : D x y)
  : FG x y xy = FG' x y xy.
Proof.
  induction p ; cbn.
  apply idpath.
Defined.

Definition path_twosided_disp_functor_mor
           {C₁ C₂ C₁' C₂' : category}
           {F : C₁ ⟶ C₁'}
           {G : C₂ ⟶ C₂'}
           {D : twosided_disp_cat C₁ C₂}
           {D' : twosided_disp_cat C₁' C₂'}
           {FG FG' : twosided_disp_functor F G D D'}
           (p : FG = FG')
           {x₁ x₂ : C₁}
           {f : x₁ --> x₂}
           {y₁ y₂ : C₂}
           {g : y₁ --> y₂}
           {xy₁ : D x₁ y₁}
           {xy₂ : D x₂ y₂}
           (fg : xy₁ -->[ f ][ g ] xy₂)
  : #2 FG fg
    =
    transportf_disp_mor2
      (id_right _ @ id_left _)
      (id_right _ @ id_left _)
      (idtoiso_twosided_disp
         (idpath _) (idpath _)
         (path_twosided_disp_functor_ob p xy₁)
       ;;2 #2 FG' fg
       ;;2 idtoiso_twosided_disp
             (idpath _) (idpath _)
             (!(path_twosided_disp_functor_ob p xy₂))).
Proof.
  induction p ; cbn.
  rewrite id_two_disp_right.
  rewrite id_two_disp_left.
  unfold transportb_disp_mor2.
  rewrite !transport_f_f_disp_mor2.
  refine (!_).
  apply transportf_disp_mor2_idpath.
Qed.

Section StrictTwosidedDispCatIso.
  Context {C : setcategory}
          {D₁ D₂ : strict_twosided_disp_cat C C}
          (F : disp_functor
                 (functor_identity _)
                 (twosided_disp_cat_to_disp_cat C C D₁)
                 (twosided_disp_cat_to_disp_cat C C D₂)).

  (** ** 5.1. Characterization of the isomorphisms *)
  Section FromIso.
    Context (HF : is_z_iso_disp
                    (D := disp_cat_of_strict_twosided_disp_cat)
                    (@identity_z_iso cat_of_setcategory C)
                    (disp_functor_to_two_sided_disp_functor
                       (disp_functor_over_pair F))).

    Let G : twosided_disp_functor (functor_identity _) (functor_identity _) D₂ D₁
      := inv_mor_disp_from_z_iso HF.

    Lemma two_sided_disp_cat_iso_path_ob
          {x y : C}
          (xy : D₁ x y)
      : G x y (F (x ,, y) xy) = xy.
    Proof.
      pose (path_twosided_disp_functor_ob
              (inv_mor_after_z_iso_disp HF)
              xy)
        as p.
      cbn in p.
      refine (p @ _).
      apply (transportb_disp_cat_of_strict_twosided_disp_cat_ob
               (functor_identity _)).
    Qed.

    Lemma two_sided_disp_cat_iso_path_ob_alt
          {x y : C}
          (xy : D₂ x y)
      : F (x ,, y) (G x y xy) = xy.
    Proof.
      pose (path_twosided_disp_functor_ob
              (z_iso_disp_after_inv_mor HF)
              xy)
        as p.
      cbn in p.
      refine (p @ _).
      apply (transportb_disp_cat_of_strict_twosided_disp_cat_ob
               (functor_identity _)).
    Qed.

    (**
     Note the following: in the upcoming lemmas, we frequently
     pose an extra argument (see `fg'` below). The reason to
     do that, is to help the type checker of Coq type check
     the expression. The only thing that happens in the argument
     `fg'`, is that we provide extra type information.
     *)
    Lemma two_sided_disp_cat_iso_path_mor
          {x₁ x₂ y₁ y₂ : C}
          (xx := (x₁ ,, y₁) : category_binproduct C C)
          (yy := (x₂ ,, y₂) : category_binproduct C C)
          {f : x₁ --> x₂}
          {g : y₁ --> y₂}
          {xy₁ : D₁ x₁ y₁}
          {xy₂ : D₁ x₂ y₂}
          (fg : xy₁ -->[ f ][ g ] xy₂)
          (fg' := fg : @mor_disp
                         _
                         (twosided_disp_cat_to_disp_cat C C D₁)
                         xx yy
                         xy₁ xy₂
                         (f ,, g))
      : #2 G (♯ F fg')%mor_disp
        =
        transportf_disp_mor2
          (id_right _ @ id_left _)
          (id_right _ @ id_left _)
          (idtoiso_twosided_disp
             (idpath _) (idpath _)
             (two_sided_disp_cat_iso_path_ob xy₁)
           ;;2 fg
           ;;2 idtoiso_twosided_disp
                 (idpath _) (idpath _)
                 (!(two_sided_disp_cat_iso_path_ob xy₂))).
    Proof.
      etrans.
      {
        apply (path_twosided_disp_functor_mor (inv_mor_after_z_iso_disp HF)).
      }
      cbn -[idtoiso_twosided_disp].
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        apply (transportb_disp_cat_of_strict_twosided_disp_cat_mor
                 _
                 _ _
                 (id_left (C := cat_of_setcategory) (functor_identity C))).
      }
      cbn -[idtoiso_twosided_disp].
      rewrite (two_disp_post_whisker_f (D := D₁)).
      rewrite (two_disp_pre_whisker_f (D := D₁)).
      rewrite transport_f_f_disp_mor2.
      rewrite !(assoc_two_disp_alt (D := D₁)).
      rewrite !two_disp_post_whisker_f.
      rewrite !transport_f_f_disp_mor2.
      etrans.
      {
        do 4 apply maponpaths.
        apply (idtoiso_twosided_disp_concat (D := D₁)).
      }
      unfold transportb_disp_mor2.
      rewrite !two_disp_post_whisker_f.
      rewrite transport_f_f_disp_mor2.
      rewrite !(assoc_two_disp (D := D₁)).
      unfold transportb_disp_mor2.
      rewrite !transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        apply (idtoiso_twosided_disp_concat (D := D₁)).
      }
      unfold transportb_disp_mor2.
      rewrite !two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      use transportf_disp_mor2_eq.
      use idtoiso_twosided_disp_triple_concat.
    Qed.

    Lemma two_sided_disp_cat_iso_path_mor_alt
          {x₁ x₂ y₁ y₂ : C}
          (xx := (x₁ ,, y₁) : category_binproduct C C)
          (yy := (x₂ ,, y₂) : category_binproduct C C)
          {f : x₁ --> x₂}
          {g : y₁ --> y₂}
          (h := (f ,, g) : xx --> yy)
          {xy₁ : D₂ x₁ y₁}
          {xy₂ : D₂ x₂ y₂}
          (fg : xy₁ -->[ f ][ g ] xy₂)
          (fg' := #2 G fg : @mor_disp
                               _
                               (twosided_disp_cat_to_disp_cat C C D₁)
                               xx yy
                               (G x₁ y₁ xy₁) (G x₂ y₂ xy₂)
                               h)
      : (♯F fg'
         =
         transportf_disp_mor2
           (id_right _ @ id_left (pr1 h))
           (id_right _ @ id_left (pr2 h))
           (idtoiso_twosided_disp
              (idpath _)
              (idpath _)
              (two_sided_disp_cat_iso_path_ob_alt xy₁)
            ;;2 fg
            ;;2 idtoiso_twosided_disp
                  (idpath _)
                  (idpath _)
                  (!(two_sided_disp_cat_iso_path_ob_alt xy₂))))%mor_disp.
    Proof.
      etrans.
      {
        apply (path_twosided_disp_functor_mor (z_iso_disp_after_inv_mor HF)).
      }
      cbn -[idtoiso_twosided_disp].
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        apply (transportb_disp_cat_of_strict_twosided_disp_cat_mor
                 _
                 _ _
                 (id_left (C := cat_of_setcategory) (functor_identity C))).
      }
      cbn -[idtoiso_twosided_disp].
      rewrite (two_disp_post_whisker_f (D := D₂)).
      rewrite (two_disp_pre_whisker_f (D := D₂)).
      rewrite transport_f_f_disp_mor2.
      rewrite !(assoc_two_disp_alt (D := D₂)).
      rewrite !two_disp_post_whisker_f.
      rewrite !transport_f_f_disp_mor2.
      etrans.
      {
        do 4 apply maponpaths.
        apply (idtoiso_twosided_disp_concat (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite !two_disp_post_whisker_f.
      rewrite transport_f_f_disp_mor2.
      rewrite !(assoc_two_disp (D := D₂)).
      unfold transportb_disp_mor2.
      rewrite !transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        apply (idtoiso_twosided_disp_concat (D := D₂)).
      }
      unfold transportb_disp_mor2.
      rewrite !two_disp_pre_whisker_f.
      rewrite transport_f_f_disp_mor2.
      use transportf_disp_mor2_eq.
      use idtoiso_twosided_disp_triple_concat.
    Qed.

    Lemma disp_functor_comp_two_disp
          {x₁ x₂ x₃ y₁ y₂ y₃ : C}
          (xx := (x₁ ,, y₁) : category_binproduct C C)
          (yy := (x₂ ,, y₂) : category_binproduct C C)
          (zz := (x₃ ,, y₃) : category_binproduct C C)
          {f₁ : x₁ --> x₂} {f₂ : x₂ --> x₃}
          {g₁ : y₁ --> y₂} {g₂ : y₂ --> y₃}
          {xy₁ : D₁ x₁ y₁}
          {xy₂ : D₁ x₂ y₂}
          {xy₃ : D₁ x₃ y₃}
          (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
          (fg₁' := fg₁ : @mor_disp
                            _
                            (twosided_disp_cat_to_disp_cat C C D₁)
                            xx yy
                            xy₁ xy₂
                            (f₁ ,, g₁))
          (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
          (fg₂' := fg₂ : @mor_disp
                            _
                            (twosided_disp_cat_to_disp_cat C C D₁)
                            yy zz
                            xy₂ xy₃
                            (f₂ ,, g₂))
          (h := fg₁ ;;2 fg₂ : @mor_disp
                                 _
                                 (twosided_disp_cat_to_disp_cat C C D₁)
                                 xx zz
                                 xy₁ xy₃
                                 (f₁ · f₂ ,, g₁ · g₂))
      : (♯ F h
         =
         ♯F fg₁' ;;2 ♯F fg₂')%mor_disp.
    Proof.
      exact (disp_functor_comp F fg₁' fg₂').
    Qed.

    Lemma disp_functor_transportf_disp_mor2
          {x₁ x₂ y₁ y₂ : C}
          (xx := (x₁ ,, y₁) : category_binproduct C C)
          (yy := (x₂ ,, y₂) : category_binproduct C C)
          {f f' : x₁ --> x₂}
          {g g' : y₁ --> y₂}
          (p : f = f')
          (q : g = g')
          {xy₁ : D₁ x₁ y₁}
          {xy₂ : D₁ x₂ y₂}
          (fg : xy₁ -->[ f ][ g ] xy₂)
          (fg' := fg : @mor_disp
                          _
                          (twosided_disp_cat_to_disp_cat C C D₁)
                          xx yy
                          xy₁ xy₂
                          (f ,, g))
          (φ := transportf_disp_mor2 p q fg' : @mor_disp
                                                  _
                                                  (twosided_disp_cat_to_disp_cat C C D₁)
                                                  xx yy
                                                  xy₁ xy₂
                                                  (f' ,, g'))
      : (♯F φ
         =
         transportf_disp_mor2
           p
           q
           (♯F fg'))%mor_disp.
    Proof.
      induction p, q.
      refine (!_).
      apply transportf_disp_mor2_idpath.
    Qed.

    Lemma disp_functor_idtoiso_twosided_disp
          {x y : C}
          (xx := x ,, y : category_binproduct C C)
          {xy₁ xy₂ : D₁ x y}
          (p : xy₁ = xy₂)
          (f := idtoiso_twosided_disp
                  (idpath x) (idpath y)
                  p : xy₁ -->[ identity _ ][ identity _ ] xy₂)
          (φ := f : @mor_disp
                      _
                      (twosided_disp_cat_to_disp_cat C C D₁)
                      xx xx
                      xy₁ xy₂
                      (identity _ ,, identity _))
          (ψ := idtoiso_twosided_disp
                  (idpath _)
                  (idpath _)
                  (maponpaths (F xx) p)
             : F xx xy₁ -->[ identity _ ][ identity _ ] F xx xy₂)
      : (♯F φ = ψ)%mor_disp.
    Proof.
      induction p ; cbn.
      exact (disp_functor_id F (x := xx) xy₁).
    Qed.

    Proposition is_z_iso_disp_strict_twosided_disp_cat_to_ff
      : disp_functor_ff F.
    Proof.
      intros x y xx yy f.
      use isweq_iso.
      - exact (λ ff,
               transportf_disp_mor2
                 (id_right _ @ id_left _)
                 (id_right _ @ id_left _)
                 (idtoiso_twosided_disp
                    (idpath _) (idpath _)
                    (!(two_sided_disp_cat_iso_path_ob _))
                  ;;2 #2 G ff
                  ;;2 idtoiso_twosided_disp
                        (idpath _) (idpath _)
                        (two_sided_disp_cat_iso_path_ob _))).
      - intro ff ; cbn -[idtoiso_twosided_disp].
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          exact (two_sided_disp_cat_iso_path_mor ff).
        }
        rewrite (two_disp_post_whisker_f (D := D₁)).
        rewrite (two_disp_pre_whisker_f (D := D₁)).
        rewrite transport_f_f_disp_mor2.
        rewrite !assoc_two_disp_alt.
        rewrite !two_disp_post_whisker_f.
        rewrite !transport_f_f_disp_mor2.
        etrans.
        {
          do 4 apply maponpaths.
          apply (idtoiso_twosided_disp_concat (D := D₁)).
        }
        rewrite pathsinv0l.
        unfold transportb_disp_mor2.
        rewrite !two_disp_post_whisker_f.
        rewrite !transport_f_f_disp_mor2.
        etrans.
        {
          do 3 apply maponpaths.
          apply (id_two_disp_right (D := D₁)).
        }
        unfold transportb_disp_mor2.
        rewrite !two_disp_post_whisker_f.
        rewrite !transport_f_f_disp_mor2.
        rewrite assoc_two_disp.
        unfold transportb_disp_mor2.
        rewrite !transport_f_f_disp_mor2.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply (idtoiso_twosided_disp_concat (D := D₁)).
        }
        unfold transportb_disp_mor2.
        rewrite two_disp_pre_whisker_f.
        rewrite !transport_f_f_disp_mor2.
        rewrite pathsinv0l.
        etrans.
        {
          apply maponpaths.
          apply (id_two_disp_left (D := D₁)).
        }
        unfold transportb_disp_mor2.
        rewrite !transport_f_f_disp_mor2.
        apply transportf_disp_mor2_idpath.
      - intro ff ; cbn -[idtoiso_twosided_disp].
        rewrite disp_functor_transportf_disp_mor2.
        rewrite !disp_functor_comp_two_disp.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          apply two_sided_disp_cat_iso_path_mor_alt.
        }
        cbn -[idtoiso_twosided_disp].
        rewrite (two_disp_post_whisker_f (D := D₂)).
        rewrite (two_disp_pre_whisker_f (D := D₂)).
        rewrite transport_f_f_disp_mor2.
        etrans.
        {
          apply maponpaths.
          apply maponpaths.
          apply disp_functor_idtoiso_twosided_disp.
        }
        etrans.
        {
          apply maponpaths.
          do 2 apply maponpaths_2.
          apply disp_functor_idtoiso_twosided_disp.
        }
        rewrite !(assoc_two_disp_alt (D := D₂)).
        rewrite !two_disp_post_whisker_f.
        rewrite !transport_f_f_disp_mor2.
        etrans.
        {
          do 4 apply maponpaths.
          apply (idtoiso_twosided_disp_concat (D := D₂)).
        }
        unfold transportb_disp_mor2.
        rewrite !two_disp_post_whisker_f.
        rewrite !transport_f_f_disp_mor2.
        rewrite !(assoc_two_disp (D := D₂)).
        unfold transportb_disp_mor2.
        rewrite !transport_f_f_disp_mor2.
        etrans.
        {
          apply maponpaths.
          do 2 apply maponpaths_2.
          apply (idtoiso_twosided_disp_concat (D := D₂)).
        }
        unfold transportb_disp_mor2.
        rewrite !two_disp_pre_whisker_f.
        rewrite !transport_f_f_disp_mor2.
        rewrite !idtoiso_twosided_disp_identity.
        etrans.
        {
          apply maponpaths.
          apply (id_two_disp_right (D := D₂)).
        }
        etrans.
        {
          do 2 apply maponpaths.
          apply (id_two_disp_left (D := D₂)).
        }
        unfold transportb_disp_mor2.
        rewrite !transport_f_f_disp_mor2.
        apply transportf_disp_mor2_idpath.
    Qed.

    Proposition is_z_iso_disp_strict_twosided_disp_cat_to_ob_weq
                (x : C × C)
      : isweq (F x).
    Proof.
      use isweq_iso.
      - exact (λ xx, G _ _ xx).
      - intro xx ; cbn.
        apply two_sided_disp_cat_iso_path_ob.
      - intro xx ; cbn.
        pose (path_twosided_disp_functor_ob
                (z_iso_disp_after_inv_mor HF)
                xx)
          as p.
        cbn in p.
        refine (p @ _).
        apply (transportb_disp_cat_of_strict_twosided_disp_cat_ob
                 (functor_identity _)).
    Qed.
  End FromIso.

  Section ToIso.
    Context (HF_ff : disp_functor_ff F)
            (HF_weq : ∏ (x : C × C), isweq (F x)).

    Let φ₀ : ∏ (x y : C), D₁ x y ≃ D₂ x y
      := λ x y, make_weq _ (HF_weq (x ,, y)).

    Let φ₁ : ∏ {x₁ x₂ y₁ y₂ : C}
               (xy₁ : D₁ x₁ y₁) (xy₂ : D₁ x₂ y₂)
               (f : x₁ --> x₂) (g : y₁ --> y₂),
             xy₁ -->[ f ][ g] xy₂ ≃ F (x₁,, y₁) xy₁ -->[ f ][ g] F (x₂,, y₂) xy₂
      := λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g,
         make_weq _ (HF_ff (x₁ ,, y₁) (x₂ ,, y₂) xy₁ xy₂ (f ,, g)).

    Definition to_is_z_iso_disp_strict_twosided_disp_cat_inv_data
      : twosided_disp_functor_data
          (functor_identity C) (functor_identity C)
          D₂ D₁.
    Proof.
      simple refine (_ ,, _).
      - exact (λ x y xy, invmap (φ₀ x y) xy).
      - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg,
               invmap
                 (φ₁ (invmap (φ₀ x₁ y₁) xy₁) (invmap (φ₀ x₂ y₂) xy₂) f g)
                 (transportf_disp_mor2
                    (id_right _ @ id_left _)
                    (id_right _ @ id_left _)
                    (idtoiso_twosided_disp
                       (idpath _) (idpath _)
                       (homotweqinvweq (φ₀ x₁ y₁) _)
                     ;;2 fg
                     ;;2 idtoiso_twosided_disp
                           (idpath _) (idpath _)
                           (!(homotweqinvweq (φ₀ x₂ y₂)) _)))).
    Defined.

    Proposition to_is_z_iso_disp_strict_twosided_disp_cat_inv_laws
      : twosided_disp_functor_laws
          (functor_identity C) (functor_identity C)
          D₂ D₁
          to_is_z_iso_disp_strict_twosided_disp_cat_inv_data.
    Proof.
      split.
      - intros x y xy ; cbn -[idtoiso_twosided_disp].
        use (invmaponpathsweq (φ₁ _ _ _ _)).
        etrans.
        {
          apply homotweqinvweq.
        }
        cbn -[idtoiso_twosided_disp].
        rewrite (id_two_disp_right (D := D₂)).
        unfold transportb_disp_mor2.
        rewrite (two_disp_pre_whisker_f (D := D₂)).
        rewrite transport_f_f_disp_mor2.
        etrans.
        {
          apply maponpaths.
          apply (idtoiso_twosided_disp_concat (D := D₂)).
        }
        unfold transportb_disp_mor2.
        rewrite transport_f_f_disp_mor2.
        rewrite pathsinv0r.
        cbn.
        refine (!_).
        etrans.
        {
          exact (@disp_functor_id _ _ _ _ _ F (_ ,, _) (invmap (φ₀ x y) xy)).
        }
        cbn.
        refine (!_).
        apply transportf_disp_mor2_idpath.
      - intros x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ g₁ fg₁ f₂ g₂ fg₂.
        cbn -[idtoiso_twosided_disp].
        use (invmaponpathsweq (φ₁ _ _ _ _)).
        etrans.
        {
          apply homotweqinvweq.
        }
        cbn -[idtoiso_twosided_disp].
        refine (!_).
        etrans.
        {
          apply disp_functor_comp_two_disp.
        }
        etrans.
        {
          apply maponpaths.
          apply (homotweqinvweq (φ₁ _ _ _ _)).
        }
        etrans.
        {
          apply maponpaths_2.
          apply (homotweqinvweq (φ₁ _ _ _ _)).
        }
        rewrite two_disp_pre_whisker_f.
        rewrite two_disp_post_whisker_f.
        rewrite transport_f_f_disp_mor2.
        rewrite !(assoc_two_disp_alt (D := D₂)).
        rewrite !two_disp_post_whisker_f.
        rewrite !transport_f_f_disp_mor2.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !(assoc_two_disp (D := D₂)).
          do 2 apply maponpaths.
          do 2 apply maponpaths_2.
          apply (idtoiso_twosided_disp_concat (D := D₂)).
        }
        rewrite pathsinv0l.
        unfold transportb_disp_mor2.
        rewrite !two_disp_pre_whisker_f.
        rewrite !two_disp_post_whisker_f.
        rewrite !transport_f_f_disp_mor2.
        etrans.
        {
          do 3 apply maponpaths.
          apply maponpaths_2.
          apply id_two_disp_left.
        }
        unfold transportb_disp_mor2.
        rewrite !two_disp_pre_whisker_f.
        rewrite !two_disp_post_whisker_f.
        rewrite !transport_f_f_disp_mor2.
        apply transportf_disp_mor2_eq.
        apply idpath.
    Qed.

    Definition to_is_z_iso_disp_strict_twosided_disp_cat_inv
      : twosided_disp_functor
          (functor_identity C) (functor_identity C)
          D₂ D₁.
    Proof.
      simple refine (_ ,, _).
      - exact to_is_z_iso_disp_strict_twosided_disp_cat_inv_data.
      - exact to_is_z_iso_disp_strict_twosided_disp_cat_inv_laws.
    Defined.

    Let G := to_is_z_iso_disp_strict_twosided_disp_cat_inv.

    Local Arguments idtoiso_twosided_disp {_ _ _ _ _ _ _ _ _ _ _ _}.

    Proposition to_is_z_iso_disp_strict_twosided_disp_cat_laws
      : is_disp_inverse
          (D := disp_cat_of_strict_twosided_disp_cat)
          (identity_z_iso _)
          (disp_functor_to_two_sided_disp_functor (disp_functor_over_pair F))
          G.
    Proof.
      split.
      - use eq_twosided_disp_functor.
        + abstract
            (intros x y xy ; cbn ;
             refine (homotweqinvweq (φ₀ x y) _ @ _) ;
             refine (!_) ;
             apply (transportb_disp_cat_of_strict_twosided_disp_cat_ob
                      (functor_identity _))).
        + intros x₁ x₂ f y₁ y₂ g xy₁ xy₂ fg.
          cbn -[idtoiso_twosided_disp].
          etrans.
          {
            apply maponpaths_2.
            apply (homotweqinvweq (φ₁ (invmap (φ₀ x₁ y₁) xy₁) (invmap (φ₀ x₂ y₂) xy₂) f g)).
          }
          rewrite (two_disp_pre_whisker_f (D := D₂)).
          rewrite !(assoc_two_disp_alt (D := D₂)).
          rewrite !transport_f_f_disp_mor2.
          etrans.
          {
            do 3 apply maponpaths.
            apply (idtoiso_twosided_disp_concat (D := D₂)).
          }
          unfold transportb_disp_mor2.
          rewrite !two_disp_post_whisker_f.
          rewrite transport_f_f_disp_mor2.
          refine (!_).
          etrans.
          {
            do 2 apply maponpaths.
            apply (transportb_disp_cat_of_strict_twosided_disp_cat_mor
                     (functor_identity _)).
          }
          cbn -[idtoiso_twosided_disp].
          rewrite (two_disp_post_whisker_f (D := D₂)).
          rewrite transport_f_f_disp_mor2.
          rewrite !(assoc_two_disp (D := D₂)).
          unfold transportb_disp_mor2.
          rewrite two_disp_pre_whisker_f.
          rewrite !transport_f_f_disp_mor2.
          etrans.
          {
            apply maponpaths.
            do 2 apply maponpaths_2.
            apply (idtoiso_twosided_disp_concat (D := D₂)).
          }
          unfold transportb_disp_mor2.
          rewrite !two_disp_pre_whisker_f.
          rewrite !transport_f_f_disp_mor2.
          use transportf_disp_mor2_eq.
          use idtoiso_twosided_disp_triple_concat.
      - use eq_twosided_disp_functor.
        + intros x y xy ; cbn.
          refine (homotinvweqweq (φ₀ x y) _ @ _).
          refine (!_).
          apply (transportb_disp_cat_of_strict_twosided_disp_cat_ob
                   (functor_identity _)).
        + intros x₁ x₂ f y₁ y₂ g xy₁ xy₂ fg.
          use (invmaponpathsweq (φ₁ _ _ _ _)).
          cbn -[idtoiso_twosided_disp].
          rewrite !disp_functor_transportf_disp_mor2.
          etrans.
          {
            apply disp_functor_comp_two_disp.
          }
          etrans.
          {
            apply maponpaths_2.
            apply (homotweqinvweq (φ₁ _ _ _ _)).
          }
          refine (!_).
          etrans.
          {
            apply maponpaths.
            apply disp_functor_comp_two_disp.
          }
          etrans.
          {
            do 3 apply maponpaths.
            apply (transportb_disp_cat_of_strict_twosided_disp_cat_mor
                     _
                     _ _
                     (id_left (C := cat_of_setcategory) (functor_identity C))).
          }
          cbn -[idtoiso_twosided_disp].
          rewrite disp_functor_transportf_disp_mor2.
          rewrite (two_disp_pre_whisker_f (D := D₂)).
          rewrite (two_disp_post_whisker_f (D := D₂)).
          rewrite transport_f_f_disp_mor2.
          etrans.
          {
            do 2 apply maponpaths.
            etrans.
            {
              apply disp_functor_comp_two_disp.
            }
            apply maponpaths_2.
            apply disp_functor_comp_two_disp.
          }
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              apply disp_functor_idtoiso_twosided_disp.
            }
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply disp_functor_idtoiso_twosided_disp.
            }
            do 2 apply maponpaths_2.
            apply disp_functor_idtoiso_twosided_disp.
          }
          refine (!_).
          etrans.
          {
            do 2 apply maponpaths.
            apply disp_functor_idtoiso_twosided_disp.
          }
          rewrite !(assoc_two_disp_alt (D := D₂)).
          rewrite !transport_f_f_disp_mor2.
          etrans.
          {
            do 3 apply maponpaths.
            apply (idtoiso_twosided_disp_concat (D := D₂)).
          }
          unfold transportb_disp_mor2.
          rewrite !two_disp_post_whisker_f.
          rewrite transport_f_f_disp_mor2.
          refine (!_).
          rewrite !(assoc_two_disp (D := D₂)).
          unfold transportb_disp_mor2.
          rewrite !two_disp_pre_whisker_f.
          rewrite !transport_f_f_disp_mor2.
          etrans.
          {
            apply maponpaths.
            do 2 apply maponpaths_2.
            apply (idtoiso_twosided_disp_concat (D := D₂)).
          }
          unfold transportb_disp_mor2.
          rewrite !two_disp_pre_whisker_f.
          rewrite transport_f_f_disp_mor2.
          use transportf_disp_mor2_eq.
          use idtoiso_twosided_disp_triple_concat.
    Qed.

    Definition to_is_z_iso_disp_strict_twosided_disp_cat
      : is_z_iso_disp
          (D := disp_cat_of_strict_twosided_disp_cat)
          (@identity_z_iso cat_of_setcategory C)
          (disp_functor_to_two_sided_disp_functor (disp_functor_over_pair F)).
    Proof.
      simple refine (_ ,, _).
      - exact G.
      - exact to_is_z_iso_disp_strict_twosided_disp_cat_laws.
    Defined.
  End ToIso.

  Proposition is_z_iso_disp_strict_twosided_disp_cat_weq
    : (∏ (x : C × C), isweq (F x)) × disp_functor_ff F
      ≃
      is_z_iso_disp
        (D := disp_cat_of_strict_twosided_disp_cat)
        (@identity_z_iso cat_of_setcategory C)
        (disp_functor_to_two_sided_disp_functor (disp_functor_over_pair F)).
  Proof.
    use weqimplimpl.
    - intros HF.
      induction HF as [ HF_weq HF_ff ].
      exact (to_is_z_iso_disp_strict_twosided_disp_cat HF_ff HF_weq).
    - intros HF.
      split.
      + exact (is_z_iso_disp_strict_twosided_disp_cat_to_ob_weq HF).
      + exact (is_z_iso_disp_strict_twosided_disp_cat_to_ff HF).
    - use isapropdirprod.
      + use impred ; intro.
        apply isapropisweq.
      + apply isaprop_disp_functor_ff.
    - apply isaprop_is_z_iso_disp.
  Qed.
End StrictTwosidedDispCatIso.

(** ** 5.2. The actual proof of univalence *)
Proposition is_univalent_disp_disp_cat_of_strict_twosided_disp_cat
  : is_univalent_disp disp_cat_of_strict_twosided_disp_cat.
Proof.
  use is_univalent_disp_from_fibers.
  intros C D₁ D₂.
  cbn in C, D₁, D₂.
  use weqhomot.
  - refine (_ ∘ path_sigma_hprop _ _ _ (isaprop_is_strict_twosided_disp_cat _))%weq.
    refine (_ ∘ make_weq _ (isweqmaponpaths (two_sided_disp_cat_weq_disp_cat C C) D₁ D₂))%weq.
    refine (_ ∘ disp_cat_eq _ _)%weq.
    use weqtotal2.
    + exact (invweq
               (two_sided_disp_functor_weq_disp_functor
                  (functor_identity C)
                  (functor_identity C) D₁ D₂)
             ∘ disp_functor_over_pair_weq _ _)%weq.
    + intro F.
      apply is_z_iso_disp_strict_twosided_disp_cat_weq.
  - intro p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_z_iso_disp.
    }
    use subtypePath.
    {
      intro.
      apply isaprop_twosided_disp_functor_laws.
    }
    apply idpath.
Qed.

Proposition is_univalent_cat_of_strict_twosided_disp_cat
  : is_univalent cat_of_strict_twosided_disp_cat.
Proof.
  use is_univalent_total_category.
  - exact is_univalent_cat_of_setcategory.
  - exact is_univalent_disp_disp_cat_of_strict_twosided_disp_cat.
Qed.
