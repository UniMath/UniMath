(**********************************************************************************

 Basics for strict double categories

 In this file, we lay down the basics notions to define strict double categories.
 In a strict double category, the identity and associativity laws hold strictly,
 so up to an equality of horizontal morphisms. We also show that the type of
 horizontal identities and the type of horizontal composition operations form
 a set if we are looking at a strict 2-sided displayed category.

 Finally, we look at when functors preserve horizontal identities/composition. The
 definitions might look a bit surprising at first. The definition of preservation
 of the identity is given in [preserves_hor_id], and it consists of two parts. The
 first part ([preserves_hor_id_data]) says that the horizontal identity is preserved
 up to equality. However, we also require that the assignment of these equalities
 give rise to a natural transformation ([isaprop_preserves_hor_id_laws]), and that
 is the second part of the definition. For the preservation of horizontal composition,
 we take the same route. THe following has to be noted here:
 - To prove that we have a univalent category of strict double categories, we need
   this naturality condition.
 - This condition is also required in the literature. See, for example, Definition
   12.3.18 in "2-Dimensional Categories" by Johnson and Yau. A strict double functor
   is a lax double functor such that the natural transformations that witness the
   preservation of identity and horizontal composition, are pointwise identities.
   As such, the same naturality condition is required there.

 Contents
 1. Laws for strict double categories
 2. Horizontal identities/composition forms a set
 3. Preservation of horizontal identities
 4. Preservation of horizontal composition
 5. The identity preserves identities and composition
 6. The composition preserves identities and composition

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TransportLaws.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCategoryBasics.

Local Open Scope cat.

(** * 1. Laws for strict double categories *)
Definition strict_double_cat_id_left
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
           (Cm : hor_comp D)
  : UU
  := ∏ (x y : C)
       (f : D x y),
     double_hor_comp Cm (double_id I x) f = f.

Definition strict_double_cat_id_right
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
           (Cm : hor_comp D)
  : UU
  := ∏ (x y : C)
       (f : D x y),
     double_hor_comp Cm f (double_id I y) = f.

Definition strict_double_cat_assoc
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp D)
  : UU
  := ∏ (w x y z : C)
       (f : D w x)
       (g : D x y)
       (h : D y z),
     double_hor_comp Cm f (double_hor_comp Cm g h)
     =
     double_hor_comp Cm (double_hor_comp Cm f g) h.

Definition strict_double_cat_laws
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
           (Cm : hor_comp D)
  : UU
  := strict_double_cat_id_left I Cm
     ×
     strict_double_cat_id_right I Cm
     ×
     strict_double_cat_assoc Cm.

Proposition isaprop_strict_double_cat_laws
            {C : category}
            {D : strict_twosided_disp_cat C C}
            (I : hor_id D)
            (Cm : hor_comp D)
  : isaprop (strict_double_cat_laws I Cm).
Proof.
  repeat (use isapropdirprod) ;
  repeat (use impred ; intro) ;
  apply is_strict_strict_twosided_disp_cat.
Qed.

(** * 2. Horizontal identities/composition forms a set *)
Proposition isaset_hor_id
            {C : category}
            (D : strict_twosided_disp_cat C C)
  : isaset (hor_id D).
Proof.
  use isaset_total2.
  - use isaset_total2.
    + use impred_isaset ; intro.
      apply is_strict_strict_twosided_disp_cat.
    + intro I.
      repeat (use impred_isaset ; intro).
      apply isaset_disp_mor.
  - intro.
    apply isasetaprop.
    apply isaprop_hor_id_laws.
Qed.

Proposition isaset_hor_comp
            {C : category}
            (D : strict_twosided_disp_cat C C)
  : isaset (hor_comp D).
Proof.
  use isaset_total2.
  - use isaset_total2.
    + repeat (use impred_isaset ; intro).
      apply is_strict_strict_twosided_disp_cat.
    + intro I.
      repeat (use impred_isaset ; intro).
      apply isaset_disp_mor.
  - intro.
    apply isasetaprop.
    apply isaprop_hor_comp_laws.
Qed.

(** * 3. Preservation of horizontal identities *)
Definition preserves_hor_id_data
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           (I₁ : hor_id D₁)
           (I₂ : hor_id D₂)
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
  : UU
  := ∏ (x : C₁),
     FF _ _ (double_id I₁ x)
     =
     double_id I₂ (F x).

Definition preserves_hor_id_laws
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {I₁ : hor_id D₁}
           {I₂ : hor_id D₂}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           (FFI : preserves_hor_id_data I₁ I₂ FF)
  : UU
  := ∏ (x y : C₁)
       (f : x --> y),
     #2 FF (double_id_mor I₁ f)
     ;;2
     idtoiso_twosided_disp (idpath _) (idpath _) (FFI y)
     =
     transportf_disp_mor2
       (id_left _ @ !(id_right _))
       (id_left _ @ !(id_right _))
       (idtoiso_twosided_disp (idpath _) (idpath _) (FFI x)
        ;;2
        double_id_mor I₂ (#F f)).

Proposition isaprop_preserves_hor_id_laws
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            (FFI : preserves_hor_id_data I₁ I₂ FF)
  : isaprop (preserves_hor_id_laws FFI).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

Definition preserves_hor_id
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           (I₁ : hor_id D₁)
           (I₂ : hor_id D₂)
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
  : UU
  := ∑ (FFI : preserves_hor_id_data I₁ I₂ FF),
     preserves_hor_id_laws FFI.

Definition make_preserves_hor_id
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           (I₁ : hor_id D₁)
           (I₂ : hor_id D₂)
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
           (FFI : preserves_hor_id_data I₁ I₂ FF)
           (HFFI : preserves_hor_id_laws FFI)
  : preserves_hor_id I₁ I₂ FF
  := FFI ,, HFFI.

Definition preserves_hor_id_to_data
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {I₁ : hor_id D₁}
           {I₂ : hor_id D₂}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           (FFI : preserves_hor_id I₁ I₂ FF)
           (x : C₁)
  : FF _ _ (double_id I₁ x)
    =
    double_id I₂ (F x)
  := pr1 FFI x.

Coercion preserves_hor_id_to_data : preserves_hor_id >-> Funclass.

Proposition is_natural_preserves_hor_id
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            (FFI : preserves_hor_id I₁ I₂ FF)
            {x y : C₁}
            (f : x --> y)
  : #2 FF (double_id_mor I₁ f)
    ;;2
    idtoiso_twosided_disp (idpath _) (idpath _) (FFI y)
    =
    transportf_disp_mor2
      (id_left _ @ !(id_right _))
      (id_left _ @ !(id_right _))
      (idtoiso_twosided_disp (idpath _) (idpath _) (FFI x)
       ;;2
       double_id_mor I₂ (#F f)).
Proof.
  exact (pr2 FFI x y f).
Qed.

Proposition isaprop_preserves_hor_id
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : strict_twosided_disp_cat C₂ C₂}
            (I₁ : hor_id D₁)
            (I₂ : hor_id D₂)
            {F : C₁ ⟶ C₂}
            (FF : twosided_disp_functor F F D₁ D₂)
  : isaprop (preserves_hor_id I₁ I₂ FF).
Proof.
  use isaproptotal2.
  - intro.
    apply isaprop_preserves_hor_id_laws.
  - intros.
    use funextsec ; intro.
    apply is_strict_strict_twosided_disp_cat.
Qed.

(** * 4. Preservation of horizontal composition *)
Definition preserves_hor_comp_data
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           (Cm₁ : hor_comp D₁)
           (Cm₂ : hor_comp D₂)
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
  : UU
  := ∏ (x y z : C₁)
       (f : D₁ x y) (g : D₁ y z),
     FF _ _ (double_hor_comp Cm₁ f g)
     =
     double_hor_comp Cm₂ (FF _ _ f) (FF _ _ g).

Definition preserves_hor_comp_laws
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {Cm₁ : hor_comp D₁}
           {Cm₂ : hor_comp D₂}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           (FFC : preserves_hor_comp_data Cm₁ Cm₂ FF)
  : UU
  := ∏ (x₁ x₂ y₁ y₂ z₁ z₂ : C₁)
       (vx : x₁ --> x₂)
       (vy : y₁ --> y₂)
       (vz : z₁ --> z₂)
       (h₁ : D₁ x₁ y₁) (k₁ : D₁ y₁ z₁)
       (h₂ : D₁ x₂ y₂) (k₂ : D₁ y₂ z₂)
       (s₁ : h₁ -->[ vx ][ vy ] h₂)
       (s₂ : k₁ -->[ vy ][ vz ] k₂),
     #2 FF (double_hor_comp_mor Cm₁ s₁ s₂)
     ;;2
     idtoiso_twosided_disp (idpath _) (idpath _) (FFC x₂ y₂ z₂ h₂ k₂)
     =
     transportf_disp_mor2
       (id_left _ @ !(id_right _))
       (id_left _ @ !(id_right _))
       (idtoiso_twosided_disp (idpath _) (idpath _) (FFC x₁ y₁ z₁ h₁ k₁)
        ;;2
        double_hor_comp_mor Cm₂ (#2 FF s₁) (#2 FF s₂)).

Proposition isaprop_preserves_hor_comp_laws
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            (FFI : preserves_hor_comp_data Cm₁ Cm₂ FF)
  : isaprop (preserves_hor_comp_laws FFI).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

Definition preserves_hor_comp
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           (Cm₁ : hor_comp D₁)
           (Cm₂ : hor_comp D₂)
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
  : UU
  := ∑ (FFC : preserves_hor_comp_data Cm₁ Cm₂ FF),
     preserves_hor_comp_laws FFC.

Definition make_preserves_hor_comp
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           (Cm₁ : hor_comp D₁)
           (Cm₂ : hor_comp D₂)
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
           (FFc : preserves_hor_comp_data Cm₁ Cm₂ FF)
           (HFFc : preserves_hor_comp_laws FFc)
  : preserves_hor_comp Cm₁ Cm₂ FF
  := FFc ,, HFFc.

Definition preserves_hor_comp_to_data
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {Cm₁ : hor_comp D₁}
           {Cm₂ : hor_comp D₂}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           (FFc : preserves_hor_comp Cm₁ Cm₂ FF)
           {x y z : C₁}
           (f : D₁ x y) (g : D₁ y z)
  : FF _ _ (double_hor_comp Cm₁ f g)
    =
    double_hor_comp Cm₂ (FF _ _ f) (FF _ _ g)
  := pr1 FFc x y z f g.

Coercion preserves_hor_comp_to_data : preserves_hor_comp >-> Funclass.

Proposition is_natural_preserves_hor_comp
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            (FFc : preserves_hor_comp Cm₁ Cm₂ FF)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C₁}
            {vx : x₁ --> x₂}
            {vy : y₁ --> y₂}
            {vz : z₁ --> z₂}
            {h₁ : D₁ x₁ y₁} {k₁ : D₁ y₁ z₁}
            {h₂ : D₁ x₂ y₂} {k₂ : D₁ y₂ z₂}
            (s₁ : h₁ -->[ vx ][ vy ] h₂)
            (s₂ : k₁ -->[ vy ][ vz ] k₂)
  : #2 FF (double_hor_comp_mor Cm₁ s₁ s₂)
    ;;2
    idtoiso_twosided_disp (idpath _) (idpath _) (FFc x₂ y₂ z₂ h₂ k₂)
    =
    transportf_disp_mor2
      (id_left _ @ !(id_right _))
      (id_left _ @ !(id_right _))
      (idtoiso_twosided_disp (idpath _) (idpath _) (FFc x₁ y₁ z₁ h₁ k₁)
       ;;2
       double_hor_comp_mor Cm₂ (#2 FF s₁) (#2 FF s₂)).
Proof.
  exact (pr2 FFc x₁ x₂ y₁ y₂ z₁ z₂ vx vy vz h₁ k₁ h₂ k₂ s₁ s₂).
Qed.

Proposition isaprop_preserves_hor_comp
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : strict_twosided_disp_cat C₂ C₂}
            (Cm₁ : hor_comp D₁)
            (Cm₂ : hor_comp D₂)
            {F : C₁ ⟶ C₂}
            (FF : twosided_disp_functor F F D₁ D₂)
  : isaprop (preserves_hor_comp Cm₁ Cm₂ FF).
Proof.
  use isaproptotal2.
  - intro.
    apply isaprop_preserves_hor_comp_laws.
  - intros.
    repeat (use funextsec ; intro).
    apply is_strict_strict_twosided_disp_cat.
Qed.

(** * 5. The identity preserves identities and composition *)
Proposition identity_preserves_hor_id_data
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
  : preserves_hor_id_data I I (twosided_disp_functor_identity D).
Proof.
  intro x ; cbn.
  apply idpath.
Defined.

Proposition identity_preserves_hor_id_laws
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
  : preserves_hor_id_laws (identity_preserves_hor_id_data I).
Proof.
  intros x y f ; cbn.
  rewrite id_two_disp_left, id_two_disp_right.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition identity_preserves_hor_id
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
  : preserves_hor_id I I (twosided_disp_functor_identity D).
Proof.
  use make_preserves_hor_id.
  - exact (identity_preserves_hor_id_data I).
  - exact (identity_preserves_hor_id_laws I).
Defined.

Proposition identity_preserves_hor_comp_data
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
  : preserves_hor_comp_data Cm Cm (twosided_disp_functor_identity D).
Proof.
  intros x y z f g.
  apply idpath.
Defined.

Proposition identity_preserves_hor_comp_laws
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
  : preserves_hor_comp_laws (identity_preserves_hor_comp_data Cm).
Proof.
  intros x₁ x₂ y₁ y₂ z₁ z₂ vx vy vz h₁ k₁ h₂ k₂ s₁ s₂ ; cbn.
  rewrite id_two_disp_left, id_two_disp_right.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition identity_preserves_hor_comp
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
  : preserves_hor_comp Cm Cm (twosided_disp_functor_identity D).
Proof.
  use make_preserves_hor_comp.
  - exact (identity_preserves_hor_comp_data Cm).
  - exact (identity_preserves_hor_comp_laws Cm).
Defined.

(** * 6. The composition preserves identities and composition *)
Proposition composition_preserves_hor_id_data
            {C₁ C₂ C₃ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            {I₃ : hor_id D₃}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {FF : twosided_disp_functor F F D₁ D₂}
            (FFI : preserves_hor_id I₁ I₂ FF)
            {GG : twosided_disp_functor G G D₂ D₃}
            (GGI : preserves_hor_id I₂ I₃ GG)
  : preserves_hor_id_data
      I₁ I₃
      (comp_twosided_disp_functor FF GG).
Proof.
  intro x ; cbn.
  refine (_ @ GGI (F x)).
  apply maponpaths.
  apply (FFI x).
Defined.

Proposition composition_preserves_hor_id_laws
            {C₁ C₂ C₃ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            {I₃ : hor_id D₃}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {FF : twosided_disp_functor F F D₁ D₂}
            (FFI : preserves_hor_id I₁ I₂ FF)
            {GG : twosided_disp_functor G G D₂ D₃}
            (GGI : preserves_hor_id I₂ I₃ GG)
  : preserves_hor_id_laws (composition_preserves_hor_id_data FFI GGI).
Proof.
  intros x y f ; cbn -[idtoiso_twosided_disp].
  unfold composition_preserves_hor_id_data.
  etrans.
  {
    apply maponpaths.
    apply idtoiso_twosided_disp_concat'.
  }
  rewrite two_disp_post_whisker_f.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite idtoiso_twosided_disp_functor.
  rewrite two_disp_post_whisker_f.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite twosided_disp_functor_comp_alt.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply maponpaths.
    apply is_natural_preserves_hor_id.
  }
  rewrite transportf_twosided_disp_functor.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite twosided_disp_functor_comp.
  unfold transportb_disp_mor2.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp_alt.
  rewrite transport_f_f_disp_mor2.
  etrans.
  {
    do 2 apply maponpaths.
    apply is_natural_preserves_hor_id.
  }
  rewrite two_disp_post_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite idtoiso_twosided_disp_functor'.
  unfold transportb_disp_mor2.
  rewrite !two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply idtoiso_twosided_disp_concat.
  }
  unfold transportb_disp_mor2.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition composition_preserves_hor_id
            {C₁ C₂ C₃ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            {I₃ : hor_id D₃}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {FF : twosided_disp_functor F F D₁ D₂}
            (FFI : preserves_hor_id I₁ I₂ FF)
            {GG : twosided_disp_functor G G D₂ D₃}
            (GGI : preserves_hor_id I₂ I₃ GG)
  : preserves_hor_id
      I₁ I₃
      (comp_twosided_disp_functor FF GG).
Proof.
  use make_preserves_hor_id.
  - exact (composition_preserves_hor_id_data FFI GGI).
  - exact (composition_preserves_hor_id_laws FFI GGI).
Defined.

Proposition composition_preserves_hor_comp_data
            {C₁ C₂ C₃ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {Cm₃ : hor_comp D₃}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {FF : twosided_disp_functor F F D₁ D₂}
            (FFc : preserves_hor_comp Cm₁ Cm₂ FF)
            {GG : twosided_disp_functor G G D₂ D₃}
            (GGc : preserves_hor_comp Cm₂ Cm₃ GG)
  : preserves_hor_comp_data
      Cm₁ Cm₃
      (comp_twosided_disp_functor FF GG).
Proof.
  intros x y z f g ; cbn.
  etrans.
  {
    apply maponpaths.
    exact (FFc x y z f g).
  }
  exact (GGc (F x) (F y) (F z) (FF x y f) (FF y z g)).
Defined.

Proposition composition_preserves_hor_comp_laws
            {C₁ C₂ C₃ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {Cm₃ : hor_comp D₃}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {FF : twosided_disp_functor F F D₁ D₂}
            (FFc : preserves_hor_comp Cm₁ Cm₂ FF)
            {GG : twosided_disp_functor G G D₂ D₃}
            (GGc : preserves_hor_comp Cm₂ Cm₃ GG)
  : preserves_hor_comp_laws (composition_preserves_hor_comp_data FFc GGc).
Proof.
  intros x₁ x₂ y₁ y₂ z₁ z₂ vx vy vz h₁ k₁ h₂ k₂ s₁ s₂.
  cbn -[idtoiso_twosided_disp].
  unfold composition_preserves_hor_comp_data.
  etrans.
  {
    apply maponpaths.
    apply idtoiso_twosided_disp_concat'.
  }
  rewrite two_disp_post_whisker_f.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite idtoiso_twosided_disp_functor.
  rewrite two_disp_post_whisker_f.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite twosided_disp_functor_comp_alt.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply maponpaths.
    apply is_natural_preserves_hor_comp.
  }
  rewrite transportf_twosided_disp_functor.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite twosided_disp_functor_comp.
  unfold transportb_disp_mor2.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp_alt.
  rewrite transport_f_f_disp_mor2.
  etrans.
  {
    do 2 apply maponpaths.
    apply is_natural_preserves_hor_comp.
  }
  rewrite two_disp_post_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite idtoiso_twosided_disp_functor'.
  unfold transportb_disp_mor2.
  rewrite !two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply idtoiso_twosided_disp_concat.
  }
  unfold transportb_disp_mor2.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

Proposition composition_preserves_hor_comp
            {C₁ C₂ C₃ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {Cm₃ : hor_comp D₃}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {FF : twosided_disp_functor F F D₁ D₂}
            (FFc : preserves_hor_comp Cm₁ Cm₂ FF)
            {GG : twosided_disp_functor G G D₂ D₃}
            (GGc : preserves_hor_comp Cm₂ Cm₃ GG)
  : preserves_hor_comp
      Cm₁ Cm₃
      (comp_twosided_disp_functor FF GG).
Proof.
  use make_preserves_hor_comp.
  - exact (composition_preserves_hor_comp_data FFc GGc).
  - exact (composition_preserves_hor_comp_laws FFc GGc).
Defined.
