(*********************************************************************************

 The category of pseudo double setcategories

 In this file, we define the category of pseudo double setcategories. Pseudo double
 setcategories are given by:
 - A set of objects
 - A set of vertical morphisms
 - A set of horizontal morphisms
 - A set of squares
 Unitality and associativity of vertical composition holds strictly, while these
 laws only hold weakly (i.e., up to invertible globular squares) for horizontal
 morphisms. Note that we require the objects, vertical morphisms, and horizontal
 morphisms to form a set, and that we require no further univalent condition.

 We also show that this category is univalent. More concretely, pseudo double
 setcategories satisfy a univalence principle that is given by isomorphisms of
 strict double functors between pseudo double categories. Note the contrast with
 the univalence principle of univalent pseudo double categories, which identifies
 them up to equivalence of lax double functor. As such, there are two differences:
 - For pseudo double setcategories, we require that the horizontal identity and
   composition is preserved strictly, while for univalent pseudo double categories,
   we only require that up to invertible 2-cell.
 - For pseudo double setcategories, we look at isomorphisms, whereas for univalent
   pseudo double categories, we look at adjoint equivalences.

 Content
 1. Preliminary definitions
 2. Displayed category that adds the left unitor
 3. Displayed category that adds the right unitor
 4. Displayed category that adds the associator
 5. Displayed category that adds the unitors and associator
 6. The category of pseudo double setcategories

 *********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.StrictTwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TransportLaws.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Basics.StrictDoubleCatBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.CatOfStrictDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleFunctor.

Local Open Scope cat.

(** * 1. Preliminary definitions *)
Definition preserves_hor_id_to_double_functor
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {I₁ : hor_id D₁}
           {I₂ : hor_id D₂}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           (HFF : preserves_hor_id I₁ I₂ FF)
  : double_functor_hor_id FF I₁ I₂.
Proof.
  use make_double_functor_hor_id.
  - exact (λ x, idtoiso_twosided_disp (idpath _) (idpath _) (!(HFF x))).
  - abstract
      (intros x y f ; cbn -[idtoiso_twosided_disp] ;
       refine (!_) ;
       refine (maponpaths
                 (λ z, transportf_disp_mor2 _ _ z)
                 (!(is_natural_preserves_hor_id_alt' HFF f))
               @ _) ;
       unfold transportb_disp_mor2 ;
       rewrite transport_f_f_disp_mor2 ;
       apply transportf_disp_mor2_idpath).
Defined.

Definition preserves_hor_comp_to_double_functor
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {Cm₁ : hor_comp D₁}
           {Cm₂ : hor_comp D₂}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           (HFF : preserves_hor_comp Cm₁ Cm₂ FF)
  : double_functor_hor_comp FF Cm₁ Cm₂.
Proof.
  use make_double_functor_hor_comp.
  - exact (λ x y z f g, idtoiso_twosided_disp (idpath _) (idpath _) (!(HFF x y z f g))).
  - abstract
      (intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂ ;
       cbn -[idtoiso_twosided_disp] ;
       refine (!(is_natural_preserves_hor_comp_alt' HFF s₁ s₂) @ _) ;
       use transportf_disp_mor2_eq ;
       apply idpath).
Defined.

(** * 2. Displayed category that adds the left unitor *)
Definition disp_cat_of_lunitor_ob_mor
  : disp_cat_ob_mor cat_of_strict_twosided_disp_cat_hor_id_comp.
Proof.
  simple refine (_ ,, _).
  - exact (λ C, double_cat_lunitor (pr12 C) (pr22 C)).
  - exact (λ CD₁ CD₂ l₁ l₂ FF,
           double_functor_lunitor
             l₁ l₂
             (preserves_hor_id_to_double_functor (pr12 FF))
             (preserves_hor_comp_to_double_functor (pr22 FF))).
Defined.

Definition disp_cat_of_lunitor_id_comp
  : disp_cat_id_comp
      cat_of_strict_twosided_disp_cat_hor_id_comp
      disp_cat_of_lunitor_ob_mor.
Proof.
  split.
  - intros CD l ; cbn.
    refine (transportf
              (λ z, double_functor_lunitor _ _ z _)
              _
              (transportf
                 (λ z, double_functor_lunitor _ _ _ z)
                 _
                 (identity_functor_lunitor l))).
    + use subtypePath.
      {
        intro.
        apply isaprop_double_functor_hor_id_laws.
      }
      use funextsec ; intro x.
      refine (!_).
      apply idtoiso_twosided_disp_identity.
    + use subtypePath.
      {
        intro.
        apply isaprop_double_functor_hor_comp_laws.
      }
      repeat (use funextsec ; intro).
      refine (!_).
      apply idtoiso_twosided_disp_identity.
  - intros CD₁ CD₂ CD₃ FF GG l₁ l₂ l₃ HFF HGG.
    refine (transportf
              (λ z, double_functor_lunitor _ _ z _)
              _
              (transportf
                 (λ z, double_functor_lunitor _ _ _ z)
                 _
                 (comp_functor_lunitor HFF HGG))).
    + use subtypePath.
      {
        intro.
        apply isaprop_double_functor_hor_id_laws.
      }
      repeat (use funextsec ; intro).
      cbn -[idtoiso_twosided_disp].
      etrans.
      {
        do 2 apply maponpaths.
        apply (idtoiso_twosided_disp_functor' (pr21 GG)).
      }
      unfold transportb_disp_mor2.
      rewrite (two_disp_post_whisker_f (D := pr121 CD₃)).
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply (idtoiso_twosided_disp_concat (D := pr121 CD₃)).
      }
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      rewrite transportf_disp_mor2_idpath.
      do 2 apply maponpaths.
      apply is_strict_strict_twosided_disp_cat.
    + use subtypePath.
      {
        intro.
        apply isaprop_double_functor_hor_comp_laws.
      }
      repeat (use funextsec ; intro).
      cbn -[idtoiso_twosided_disp].
      etrans.
      {
        do 2 apply maponpaths.
        apply (idtoiso_twosided_disp_functor' (pr21 GG)).
      }
      unfold transportb_disp_mor2.
      rewrite (two_disp_post_whisker_f (D := pr121 CD₃)).
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply (idtoiso_twosided_disp_concat (D := pr121 CD₃)).
      }
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      rewrite transportf_disp_mor2_idpath.
      do 2 apply maponpaths.
      apply is_strict_strict_twosided_disp_cat.
Qed.

Definition disp_cat_of_lunitor_data
  : disp_cat_data cat_of_strict_twosided_disp_cat_hor_id_comp.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_of_lunitor_ob_mor.
  - exact disp_cat_of_lunitor_id_comp.
Defined.

Proposition disp_cat_of_lunitor_laws
  : disp_cat_axioms
      cat_of_strict_twosided_disp_cat_hor_id_comp
      disp_cat_of_lunitor_data.
Proof.
  repeat split.
  - intros.
    apply isaprop_double_functor_lunitor.
  - intros.
    apply isaprop_double_functor_lunitor.
  - intros.
    apply isaprop_double_functor_lunitor.
  - intros.
    apply isasetaprop.
    apply isaprop_double_functor_lunitor.
Qed.

Definition disp_cat_of_lunitor
  : disp_cat cat_of_strict_twosided_disp_cat_hor_id_comp.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_of_lunitor_data.
  - exact disp_cat_of_lunitor_laws.
Defined.

Definition is_univalent_disp_cat_of_lunitor
  : is_univalent_disp disp_cat_of_lunitor.
Proof.
  use is_univalent_disp_from_fibers.
  intros CD l₁ l₂.
  induction CD as [ [ C D ] [ I Cm ] ].
  cbn in C, D, I, Cm.
  use isweqimplimpl.
  - intros FF.
    induction FF as [ FF H ].
    use subtypePath.
    {
      intro.
      apply isaprop_double_lunitor_laws.
    }
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro f.
    use subtypePath.
    {
      intro.
      apply isaprop_is_iso_twosided_disp.
    }
    refine (_ @ !(FF x y f)) ; cbn -[idtoiso_twosided_disp].
    refine (!_).
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply (idtoiso_twosided_disp_identity (D := D)).
      }
      apply (double_hor_comp_mor_id Cm).
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (id_two_disp_left (D := D)).
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply (idtoiso_twosided_disp_identity (D := D)).
    }
    unfold transportb_disp_mor2.
    rewrite (two_disp_pre_whisker_f (D := D)).
    rewrite transport_f_f_disp_mor2.
    rewrite (id_two_disp_left (D := D)).
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    apply transportf_disp_mor2_idpath.
  - apply isaset_double_cat_lunitor.
  - use isaproptotal2.
    + intro.
      apply isaprop_is_z_iso_disp.
    + intros.
      apply isaprop_double_functor_lunitor.
Qed.

(** * 3. Displayed category that adds the right unitor *)
Definition disp_cat_of_runitor_ob_mor
  : disp_cat_ob_mor cat_of_strict_twosided_disp_cat_hor_id_comp.
Proof.
  simple refine (_ ,, _).
  - exact (λ C, double_cat_runitor (pr12 C) (pr22 C)).
  - exact (λ CD₁ CD₂ r₁ r₂ FF,
           double_functor_runitor
             r₁ r₂
             (preserves_hor_id_to_double_functor (pr12 FF))
             (preserves_hor_comp_to_double_functor (pr22 FF))).
Defined.

Definition disp_cat_of_runitor_id_comp
  : disp_cat_id_comp
      cat_of_strict_twosided_disp_cat_hor_id_comp
      disp_cat_of_runitor_ob_mor.
Proof.
  split.
  - intros CD r ; cbn.
    refine (transportf
              (λ z, double_functor_runitor _ _ z _)
              _
              (transportf
                 (λ z, double_functor_runitor _ _ _ z)
                 _
                 (identity_functor_runitor r))).
    + use subtypePath.
      {
        intro.
        apply isaprop_double_functor_hor_id_laws.
      }
      use funextsec ; intro x.
      refine (!_).
      apply idtoiso_twosided_disp_identity.
    + use subtypePath.
      {
        intro.
        apply isaprop_double_functor_hor_comp_laws.
      }
      repeat (use funextsec ; intro).
      refine (!_).
      apply idtoiso_twosided_disp_identity.
  - intros CD₁ CD₂ CD₃ FF GG r₁ r₂ r₃ HFF HGG.
    refine (transportf
              (λ z, double_functor_runitor _ _ z _)
              _
              (transportf
                 (λ z, double_functor_runitor _ _ _ z)
                 _
                 (comp_functor_runitor HFF HGG))).
    + use subtypePath.
      {
        intro.
        apply isaprop_double_functor_hor_id_laws.
      }
      repeat (use funextsec ; intro).
      cbn -[idtoiso_twosided_disp].
      etrans.
      {
        do 2 apply maponpaths.
        apply (idtoiso_twosided_disp_functor' (pr21 GG)).
      }
      unfold transportb_disp_mor2.
      rewrite (two_disp_post_whisker_f (D := pr121 CD₃)).
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply (idtoiso_twosided_disp_concat (D := pr121 CD₃)).
      }
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      rewrite transportf_disp_mor2_idpath.
      do 2 apply maponpaths.
      apply is_strict_strict_twosided_disp_cat.
    + use subtypePath.
      {
        intro.
        apply isaprop_double_functor_hor_comp_laws.
      }
      repeat (use funextsec ; intro).
      cbn -[idtoiso_twosided_disp].
      etrans.
      {
        do 2 apply maponpaths.
        apply (idtoiso_twosided_disp_functor' (pr21 GG)).
      }
      unfold transportb_disp_mor2.
      rewrite (two_disp_post_whisker_f (D := pr121 CD₃)).
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        apply (idtoiso_twosided_disp_concat (D := pr121 CD₃)).
      }
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      rewrite transportf_disp_mor2_idpath.
      do 2 apply maponpaths.
      apply is_strict_strict_twosided_disp_cat.
Qed.

Definition disp_cat_of_runitor_data
  : disp_cat_data cat_of_strict_twosided_disp_cat_hor_id_comp.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_of_runitor_ob_mor.
  - exact disp_cat_of_runitor_id_comp.
Defined.

Proposition disp_cat_of_runitor_laws
  : disp_cat_axioms
      cat_of_strict_twosided_disp_cat_hor_id_comp
      disp_cat_of_runitor_data.
Proof.
  repeat split.
  - intros.
    apply isaprop_double_functor_runitor.
  - intros.
    apply isaprop_double_functor_runitor.
  - intros.
    apply isaprop_double_functor_runitor.
  - intros.
    apply isasetaprop.
    apply isaprop_double_functor_runitor.
Qed.

Definition disp_cat_of_runitor
  : disp_cat cat_of_strict_twosided_disp_cat_hor_id_comp.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_of_runitor_data.
  - exact disp_cat_of_runitor_laws.
Defined.

Definition is_univalent_disp_cat_of_runitor
  : is_univalent_disp disp_cat_of_runitor.
Proof.
  use is_univalent_disp_from_fibers.
  intros CD r₁ r₂.
  induction CD as [ [ C D ] [ I Cm ] ].
  cbn in C, D, I, Cm.
  use isweqimplimpl.
  - intros FF.
    induction FF as [ FF H ].
    use subtypePath.
    {
      intro.
      apply isaprop_double_runitor_laws.
    }
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro f.
    use subtypePath.
    {
      intro.
      apply isaprop_is_iso_twosided_disp.
    }
    refine (_ @ !(FF x y f)) ; cbn -[idtoiso_twosided_disp].
    refine (!_).
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply (idtoiso_twosided_disp_identity (D := D)).
      }
      apply (double_hor_comp_mor_id Cm).
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (id_two_disp_left (D := D)).
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply (idtoiso_twosided_disp_identity (D := D)).
    }
    unfold transportb_disp_mor2.
    rewrite (two_disp_pre_whisker_f (D := D)).
    rewrite transport_f_f_disp_mor2.
    rewrite (id_two_disp_left (D := D)).
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    apply transportf_disp_mor2_idpath.
  - apply isaset_double_cat_runitor.
  - use isaproptotal2.
    + intro.
      apply isaprop_is_z_iso_disp.
    + intros.
      apply isaprop_double_functor_runitor.
Qed.

(** * 4. Displayed category that adds the associator *)
Definition disp_cat_of_associator_ob_mor
  : disp_cat_ob_mor cat_of_strict_twosided_disp_cat_hor_id_comp.
Proof.
  simple refine (_ ,, _).
  - exact (λ C, double_cat_associator (pr22 C)).
  - exact (λ CD₁ CD₂ a₁ a₂ FF,
           double_functor_associator
             a₁ a₂
             (preserves_hor_comp_to_double_functor (pr22 FF))).
Defined.

Definition disp_cat_of_associator_id_comp
  : disp_cat_id_comp
      cat_of_strict_twosided_disp_cat_hor_id_comp
      disp_cat_of_associator_ob_mor.
Proof.
  split.
  - intros CD a ; cbn.
    refine (transportf
              (λ z, double_functor_associator _ _ z)
              _
              (identity_functor_associator a)).
    use subtypePath.
    {
      intro.
      apply isaprop_double_functor_hor_comp_laws.
    }
    repeat (use funextsec ; intro).
    refine (!_).
    apply idtoiso_twosided_disp_identity.
  - intros CD₁ CD₂ CD₃ FF GG a₁ a₂ a₃ HFF HGG.
    refine (transportf
              (λ z, double_functor_associator _ _ z)
              _
              (comp_functor_associator HFF HGG)).
    use subtypePath.
    {
      intro.
      apply isaprop_double_functor_hor_comp_laws.
    }
    repeat (use funextsec ; intro).
    cbn -[idtoiso_twosided_disp].
    etrans.
    {
      do 2 apply maponpaths.
      apply (idtoiso_twosided_disp_functor' (pr21 GG)).
    }
    unfold transportb_disp_mor2.
    rewrite (two_disp_post_whisker_f (D := pr121 CD₃)).
    rewrite transport_f_f_disp_mor2.
    etrans.
    {
      apply maponpaths.
      apply (idtoiso_twosided_disp_concat (D := pr121 CD₃)).
    }
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite transportf_disp_mor2_idpath.
    do 2 apply maponpaths.
    apply is_strict_strict_twosided_disp_cat.
Qed.

Definition disp_cat_of_associator_data
  : disp_cat_data cat_of_strict_twosided_disp_cat_hor_id_comp.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_of_associator_ob_mor.
  - exact disp_cat_of_associator_id_comp.
Defined.

Proposition disp_cat_of_associator_laws
  : disp_cat_axioms
      cat_of_strict_twosided_disp_cat_hor_id_comp
      disp_cat_of_associator_data.
Proof.
  repeat split.
  - intros.
    apply isaprop_double_functor_associator.
  - intros.
    apply isaprop_double_functor_associator.
  - intros.
    apply isaprop_double_functor_associator.
  - intros.
    apply isasetaprop.
    apply isaprop_double_functor_associator.
Qed.

Definition disp_cat_of_associator
  : disp_cat cat_of_strict_twosided_disp_cat_hor_id_comp.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_of_associator_data.
  - exact disp_cat_of_associator_laws.
Defined.

Definition is_univalent_disp_cat_of_associator
  : is_univalent_disp disp_cat_of_associator.
Proof.
  use is_univalent_disp_from_fibers.
  intros CD a₁ a₂.
  induction CD as [ [ C D ] [ I Cm ] ].
  cbn in C, D, I, Cm.
  use isweqimplimpl.
  - intros FF.
    induction FF as [ FF H ].
    use subtypePath.
    {
      intro.
      apply isaprop_double_associator_laws.
    }
    use funextsec ; intro w.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro z.
    use funextsec ; intro f.
    use funextsec ; intro g.
    use funextsec ; intro h.
    repeat (use funextsec ; intro).
    use subtypePath.
    {
      intro.
      apply isaprop_is_iso_twosided_disp.
    }
    pose (FF w x y z f g h).
    cbn -[idtoiso_twosided_disp] in p.
    refine (_
            @ maponpaths
                (transportf_disp_mor2 (id_right _ @ id_left _) (id_right _ @ id_left _))
                (!p)
            @ _).
    + refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply (idtoiso_twosided_disp_identity (D := D)).
          }
          apply (double_hor_comp_mor_id Cm).
        }
        apply (id_two_disp_left (D := D)).
      }
      unfold transportb_disp_mor2.
      rewrite (two_disp_pre_whisker_f (D := D)).
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply (idtoiso_twosided_disp_identity (D := D)).
        }
        apply (id_two_disp_left (D := D)).
      }
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
    + etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply (idtoiso_twosided_disp_identity (D := D)).
          }
          apply (double_hor_comp_mor_id Cm).
        }
        apply (id_two_disp_right (D := D)).
      }
      unfold transportb_disp_mor2.
      rewrite (two_disp_pre_whisker_f (D := D)).
      rewrite transport_f_f_disp_mor2.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply (idtoiso_twosided_disp_identity (D := D)).
        }
        apply (id_two_disp_right (D := D)).
      }
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      apply transportf_disp_mor2_idpath.
  - apply isaset_double_cat_associator.
  - use isaproptotal2.
    + intro.
      apply isaprop_is_z_iso_disp.
    + intros.
      apply isaprop_double_functor_associator.
Qed.

(** * 5. Displayed category that adds the unitors and associator *)
Definition disp_cat_of_unitor_associator
  : disp_cat cat_of_strict_twosided_disp_cat_hor_id_comp
  := dirprod_disp_cat
       disp_cat_of_lunitor
       (dirprod_disp_cat
          disp_cat_of_runitor
          disp_cat_of_associator).

Proposition is_univalent_disp_cat_of_unitor_associator
  : is_univalent_disp disp_cat_of_unitor_associator.
Proof.
  use dirprod_disp_cat_is_univalent.
  - exact is_univalent_disp_cat_of_lunitor.
  - use dirprod_disp_cat_is_univalent.
    + exact is_univalent_disp_cat_of_runitor.
    + exact is_univalent_disp_cat_of_associator.
Qed.

Definition cat_of_unitor_associator
  : category
  := total_category disp_cat_of_unitor_associator.

Proposition is_univalent_cat_of_unitor_associator
  : is_univalent cat_of_unitor_associator.
Proof.
  use is_univalent_total_category.
  - exact is_univalent_cat_of_strict_twosided_disp_cat_hor_id_comp.
  - exact is_univalent_disp_cat_of_unitor_associator.
Qed.

(** * 6. The category of pseudo double setcategories *)
Definition disp_cat_of_pseudo_double_setcategory
  : disp_cat cat_of_unitor_associator
  := disp_full_sub
       cat_of_unitor_associator
       (λ CD,
        let l := pr12 CD in
        let r := pr122 CD in
        let a := pr222 CD in
        triangle_law l r a × pentagon_law a).

Proposition is_univalent_disp_cat_of_pseudo_double_setcategory
  : is_univalent_disp disp_cat_of_pseudo_double_setcategory.
Proof.
  use disp_full_sub_univalent.
  intro CD.
  apply isapropdirprod.
  - apply isaprop_triangle_law.
  - apply isaprop_pentagon_law.
Qed.

Definition univalent_cat_of_pseudo_double_setcategory
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (total_category disp_cat_of_pseudo_double_setcategory).
  - use is_univalent_total_category.
    + exact is_univalent_cat_of_unitor_associator.
    + exact is_univalent_disp_cat_of_pseudo_double_setcategory.
Defined.
