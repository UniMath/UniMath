(***********************************************************************

 Left Kan extensions

 In this file, we define left Kan extensions of functors. In addition,
 we construct a left adjoint to the precomposition functor. To define
 the left Kan extension, we use the pointwise formula for it, which
 defines it as a conical colimit.

 Contents
 1. Pointwise definition of the left Kan extension
 1.1. Action on objects
 1.2. Action on morphisms
 1.3. Functoriality
 1.4. Definition of the left Kan extension
 1.5. Natural transformation that witnesses commutation (the unit)
 2. Left Kan extension of natural transformations
 2.1. Extending transformations
 2.2. Naturality of unit
 3. Functoriality of assigning the left Kan extension
 4. Adjunction coming from left Kan extensions
 4.1. The left adjoint (left Kan extension)
 4.2. The unit
 4.3. The counit
 4.4. The triangles
 4.5. The adjunction

 ***********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.CommaCategories.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

(**
 1. Pointwise definition of the left Kan extension

 Note: we assume `C₁` below to be small.
 *)
Section LeftKanExtension.
  Context {C₁ C₂ D : category}
          (ColimsD : Colims D)
          (P : C₁ ⟶ C₂)
          (F : C₁ ⟶ D).

  (**
   1.1. Action on objects
   *)
  Definition lan_comma (x : C₂) : category := comma P (constant_functor unit_category _ x).
  Definition lan_pr (x : C₂) : lan_comma x ⟶ D := comma_pr1 _ _ ∙ F.
  Definition lan_colim
             (x : C₂)
    : ColimCocone (diagram_from_functor (lan_comma x) D (lan_pr x))
    := ColimsD _ (diagram_from_functor _ _ (lan_pr x)).

  Definition lan_point
             (x : C₂)
    : D
    := colim (lan_colim x).

  (**
   1.2. Action on morphisms
   *)
  Section LanMor.
    Context {x y : C₂}
            (f : x --> y).

    Definition lan_mor_cocone_ob
               (z : C₁)
               (h : P z --> x)
      : F z --> lan_point y
      := colimIn (lan_colim y) ((z ,, tt) ,, h · f).

    Definition lan_mor_forms_cocone
               {z₁ z₂ : C₁}
               (h₁ : P z₁ --> x)
               (h₂ : P z₂ --> x)
               (e : z₁ --> z₂)
               (p : h₁ = # P e · h₂)
      : # F e · lan_mor_cocone_ob z₂ h₂
        =
        lan_mor_cocone_ob z₁ h₁.
    Proof.
      refine (colimInCommutes
               (lan_colim y)
               ((z₁ ,, tt) ,, h₁ · f)
               ((z₂ ,, tt) ,, h₂ · f)
               ((e ,, idpath _) ,, _)).
      abstract
        (cbn ;
         rewrite id_right ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         exact p).
    Defined.

    Definition lan_mor
      : D ⟦ lan_point x , lan_point y ⟧.
    Proof.
      refine (colim_mor
                (lan_colim x)
                (lan_point y)
                (λ v, lan_mor_cocone_ob (pr11 v) (pr2 v))
                (λ v₁ v₂ e, lan_mor_forms_cocone (pr2 v₁) (pr2 v₂) (pr11 e) _)).
      abstract
          (exact(!(id_right _) @ pr2 e)).
    Defined.

    Definition lan_mor_colimIn
               (w : C₁)
               (h : P w --> x)
               (a : unit)
      : colimIn (lan_colim x) ((w ,, a) ,, h) · lan_mor
        =
        colimIn (lan_colim y) ((w ,, a) ,, h · f).
    Proof.
      induction a.
      unfold lan_mor.
      rewrite colim_mor_commute.
      apply idpath.
    Qed.
  End LanMor.

  Definition lan_data
    : functor_data C₂ D.
  Proof.
    use make_functor_data.
    - exact lan_point.
    - exact @lan_mor.
  Defined.

  (**
   1.3. Functoriality
   *)
  Definition lan_is_functor
    : is_functor lan_data.
  Proof.
    split.
    - intros x ; cbn.
      use colim_mor_eq.
      intros v.
      rewrite id_right.
      refine (lan_mor_colimIn (identity x) (pr11 v) (pr2 v) _ @ _).
      rewrite id_right.
      apply idpath.
    - intros x y z f g.
      cbn.
      use colim_mor_eq.
      intros v.
      rewrite !assoc.
      etrans.
      {
        apply lan_mor_colimIn.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply lan_mor_colimIn.
      }
      etrans.
      {
        apply (lan_mor_colimIn g (pr11 v) (pr2 v · f)).
      }
      rewrite !assoc'.
      apply idpath.
  Qed.

  (**
   1.4. Definition of the left Kan extension
   *)
  Definition lan
    : C₂ ⟶ D.
  Proof.
    use make_functor.
    - exact lan_data.
    - exact lan_is_functor.
  Defined.

  (**
   1.5. Natural transformation that witnesses commutation
   *)
  Definition lan_commute_data
    : nat_trans_data F (P ∙ lan)
    := λ x,
       colimIn
         (lan_colim (P x))
         ((x ,, tt) ,, identity _).

  Definition lan_commute_is_nat_trans
    : is_nat_trans F (P ∙ lan) lan_commute_data.
  Proof.
    intros x y f.
    cbn.
    refine (!_).
    etrans.
    {
      exact (lan_mor_colimIn (#P f) x (identity _) _).
    }
    rewrite id_left.
    exact (!(colimInCommutes
               (lan_colim (P y))
               ((x ,, tt) ,, #P f)
               ((y ,, tt) ,, identity _)
               ((f ,, idpath _) ,, idpath _))).
  Qed.

  Definition lan_commute
    : F ⟹ P ∙ lan.
  Proof.
    use make_nat_trans.
    - exact lan_commute_data.
    - exact lan_commute_is_nat_trans.
  Defined.
End LeftKanExtension.

(**
 2. Left Kan extension of natural transformations
 *)
Section LeftKanExtensionNatTrans.
  Context {C₁ C₂ D : category}
          (ColimsD : Colims D)
          (P : C₁ ⟶ C₂)
          {F G : C₁ ⟶ D}
          (τ : F ⟹ G).

  (**
   2.1. Extending transformations
   *)
  Definition lan_nat_trans_data_cocone_ob
             (x : C₂)
             (w : C₁)
             (h : P w --> x)
    : F w --> lan_point ColimsD P G x
    := τ w · colimIn (lan_colim ColimsD P G x) ((w ,, tt) ,, h).

  Definition lan_nat_trans_data_cocone_forms_cocone
             {x : C₂}
             {w₁ w₂ : C₁}
             {h₁ : P w₁ --> x}
             {h₂ : P w₂ --> x}
             {e : w₁ --> w₂}
             (p : h₁ · identity _ = #P e · h₂)
    : # F e · lan_nat_trans_data_cocone_ob x w₂ h₂
      =
      lan_nat_trans_data_cocone_ob x w₁ h₁.
  Proof.
    unfold lan_nat_trans_data_cocone_ob.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      exact (nat_trans_ax τ _ _ e).
    }
    rewrite !assoc'.
    apply maponpaths.
    exact (colimInCommutes
             (lan_colim ColimsD P G x)
             ((w₁,, tt),, h₁)
             ((w₂,, tt),, h₂)
             ((e ,, idpath _) ,, p)).
  Qed.

  Definition lan_nat_trans_data
    : nat_trans_data
        (lan ColimsD P F)
        (lan ColimsD P G)
    := λ x, colim_mor (lan_colim ColimsD P F x)
              _
              (λ v, lan_nat_trans_data_cocone_ob x (pr11 v) (pr2 v))
              (λ _ _ e, lan_nat_trans_data_cocone_forms_cocone (pr2 e)).

  Definition lan_nat_trans_colimIn
             (x : C₂)
             (w : C₁)
             (h : P w --> x)
             (a : unit)
    : colimIn (lan_colim ColimsD P F x) ((w ,, a) ,, h) · lan_nat_trans_data x
      =
      τ w · colimIn (lan_colim ColimsD P G x) ((w ,, a) ,, h).
  Proof.
    unfold lan_nat_trans_data.
    induction a.
    rewrite colim_mor_commute.
    apply idpath.
  Qed.

  Definition lan_nat_trans_is_nat_trans
    : is_nat_trans _ _ lan_nat_trans_data.
  Proof.
    intros x y f ; cbn.
    use colim_mor_eq.
    intros v.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply lan_mor_colimIn.
    }
    etrans.
    {
      apply (lan_nat_trans_colimIn y (pr11 v) (pr2 v · f)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply lan_nat_trans_colimIn.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply lan_mor_colimIn.
    }
    apply idpath.
  Qed.

  Definition lan_nat_trans
    : lan ColimsD P F ⟹ lan ColimsD P G.
  Proof.
    use make_nat_trans.
    - exact lan_nat_trans_data.
    - exact lan_nat_trans_is_nat_trans.
  Defined.

  (**
   2.2. Naturality of unit
   *)
  Definition lan_commute_natural
    : nat_trans_comp
        _ _ _
        τ (lan_commute ColimsD P G)
      =
      nat_trans_comp
        _ _ _
        (lan_commute ColimsD P F) (pre_whisker P (lan_nat_trans )).
  Proof.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x ; cbn.
    unfold lan_commute_data.
    refine (!_).
    apply lan_nat_trans_colimIn.
  Qed.
End LeftKanExtensionNatTrans.

(**
 3. Functoriality of assigning the left Kan extension
 *)
Definition lan_nat_trans_id
           {C₁ C₂ D : category}
           (ColimsD : Colims D)
           (P : C₁ ⟶ C₂)
           (F : C₁ ⟶ D)
  : lan_nat_trans ColimsD P (nat_trans_id F)
    =
    nat_trans_id _.
Proof.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro x.
  use colim_mor_eq.
  intro v.
  etrans.
  {
    apply lan_nat_trans_colimIn.
  }
  exact (id_left _ @ !(id_right _)).
Qed.

Definition lan_nat_trans_comp
           {C₁ C₂ D : category}
           (ColimsD : Colims D)
           (P : C₁ ⟶ C₂)
           {F G H : C₁ ⟶ D}
           (τ₁ : F ⟹ G)
           (τ₂ : G ⟹ H)
  : lan_nat_trans ColimsD P (nat_trans_comp _ _ _ τ₁ τ₂)
    =
    nat_trans_comp _ _ _ (lan_nat_trans ColimsD P τ₁) (lan_nat_trans ColimsD P τ₂).
Proof.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro x.
  use colim_mor_eq.
  intro v.
  etrans.
  {
    apply lan_nat_trans_colimIn.
  }
  refine (_ @ assoc' _ _ _).
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply lan_nat_trans_colimIn.
  }
  refine (assoc' _ _ _ @ _).
  etrans.
  {
    apply maponpaths.
    apply lan_nat_trans_colimIn.
  }
  apply assoc.
Qed.

(**
 4. Adjunction coming from left Kan extensions
 *)
Section LeftKanExtensionAdjunction.
  Context {C₁ C₂ D : category}
          (ColimsD : Colims D)
          (P : C₁ ⟶ C₂).

  (**
   4.1. The left adjoint (left Kan extension)
   *)
  Definition lan_functor_data
    : functor_data [ C₁ , D ] [ C₂ , D ].
  Proof.
    use make_functor_data.
    - exact (λ F, lan ColimsD P F).
    - exact (λ _ _ τ, lan_nat_trans ColimsD P τ).
  Defined.

  Definition lan_functor_is_functor
    : is_functor lan_functor_data.
  Proof.
    split.
    - intro ; intros.
      apply lan_nat_trans_id.
    - intro ; intros.
      apply lan_nat_trans_comp.
  Qed.

  Definition lan_functor
    : [ C₁ , D ] ⟶ [ C₂ , D ].
  Proof.
    use make_functor.
    - exact lan_functor_data.
    - exact lan_functor_is_functor.
  Defined.

  (**
   4.2. The unit
   *)
  Definition lan_precomposition_unit
    : functor_identity _ ⟹ lan_functor ∙ pre_comp_functor P.
  Proof.
    use make_nat_trans.
    - exact (λ F, lan_commute ColimsD P F).
    - exact (λ F G τ, lan_commute_natural ColimsD P τ).
  Defined.

  (**
   4.3. The counit
   *)
  Definition lan_precomposition_counit_point
             (F : C₂ ⟶ D)
             (x : C₂)
    : lan_point ColimsD P (P ∙ F) x --> F x.
  Proof.
    use colim_mor.
    - exact (λ v, #F (pr2 v)).
    - abstract
        (intros v₁ v₂ e ;
         refine (!(functor_comp F _ _) @ maponpaths (λ z, #F z) _) ;
         exact (!(pr2 e) @ id_right _)).
  Defined.

  Definition lan_precomposition_counit_point_colimIn
             (F : C₂ ⟶ D)
             (x : C₂)
             (w : C₁)
             (f : P w --> x)
             (a : unit)
    : colimIn (lan_colim ColimsD P (P ∙ F) x) ((w ,, a) ,, f)
      · lan_precomposition_counit_point F x
      =
      #F f.
  Proof.
    etrans.
    {
      apply colim_mor_commute.
    }
    apply idpath.
  Qed.

  Definition lan_precomposition_counit_natural
             (F : C₂ ⟶ D)
             {x y : C₂}
             (f : x --> y)
    : lan_mor ColimsD P (P ∙ F) f · lan_precomposition_counit_point F y
      =
      lan_precomposition_counit_point F x · # F f.
  Proof.
    use colim_mor_eq.
    intros v.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply lan_mor_colimIn.
    }
    rewrite lan_precomposition_counit_point_colimIn.
    etrans.
    {
      apply (lan_precomposition_counit_point_colimIn F y (pr11 v) (pr2 v · f)).
    }
    apply (functor_comp F).
  Qed.

  Definition lan_precomposition_counit_data
             (F : C₂ ⟶ D)
    : lan_data ColimsD P (P ∙ F) ⟹ F.
  Proof.
    use make_nat_trans.
    - exact (lan_precomposition_counit_point F).
    - exact (@lan_precomposition_counit_natural F).
  Defined.

  Definition lan_precomposition_counit_natural_trans
             {F G : C₂ ⟶ D}
             (τ : F ⟹ G)
    : nat_trans_comp
        _ _ _
        (lan_nat_trans ColimsD P (pre_whisker P τ : P ∙ F ⟹ P ∙ G))
        (lan_precomposition_counit_data G)
      =
      nat_trans_comp
        _ _ _
        (lan_precomposition_counit_data F) τ.
  Proof.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use colim_mor_eq.
    intro v ; cbn -[comma].
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply (lan_nat_trans_colimIn
               ColimsD
               P
               (pre_whisker P τ : P ∙ F ⟹ P ∙ G)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply lan_precomposition_counit_point_colimIn.
    }
    refine (!_).
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply lan_precomposition_counit_point_colimIn.
    }
    refine (!_).
    apply (nat_trans_ax τ).
  Qed.

  Definition lan_precomposition_counit
    : pre_comp_functor P ∙ lan_functor ⟹ functor_identity _.
  Proof.
    use make_nat_trans.
    - exact lan_precomposition_counit_data.
    - exact @lan_precomposition_counit_natural_trans.
  Defined.

  (**
   4.4. The triangles
   *)
  Definition lan_precomposition_triangle_1
             (F : C₁ ⟶ D)
    : nat_trans_comp
        _ _ _
        (lan_nat_trans ColimsD P (lan_commute ColimsD P F))
        (lan_precomposition_counit_data (lan ColimsD P F))
      =
      nat_trans_id (lan_data ColimsD P F).
  Proof.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use colim_mor_eq.
    intro v ; cbn -[comma].
    refine (assoc _ _ _ @ _ @ !(id_right _)).
    etrans.
    {
      apply maponpaths_2.
      apply lan_nat_trans_colimIn.
    }
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply (lan_precomposition_counit_point_colimIn (lan ColimsD P F)).
    }
    etrans.
    {
      exact (lan_mor_colimIn ColimsD P F (pr2 v) (pr11 v) (identity _) tt).
    }
    induction v as [ v₁ v₃ ].
    induction v₁ as [ v₁ v₂ ].
    induction v₂.
    cbn.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition lan_precomposition_triangle_2
             (F : C₂ ⟶ D)
    : nat_trans_comp
        _ _ _
        (lan_commute ColimsD P (P ∙ F))
        (pre_whisker P (lan_precomposition_counit_data F))
      =
      nat_trans_id (functor_composite_data P F).
  Proof.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    cbn.
    etrans.
    {
      apply lan_precomposition_counit_point_colimIn.
    }
    apply functor_id.
  Qed.

  (**
   4.5. The adjunction
   *)
  Definition lan_precomposition_are_adjoints
    : are_adjoints lan_functor (pre_comp_functor P).
  Proof.
    simple refine ((_ ,, _) ,, (_ ,, _)).
    - exact lan_precomposition_unit.
    - exact lan_precomposition_counit.
    - exact lan_precomposition_triangle_1.
    - exact lan_precomposition_triangle_2.
  Defined.

  Definition is_right_adjoint_precomposition
    : is_right_adjoint (pre_comp_functor P)
    := lan_functor ,, lan_precomposition_are_adjoints.
End LeftKanExtensionAdjunction.
