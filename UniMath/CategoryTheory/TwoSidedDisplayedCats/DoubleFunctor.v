Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DoubleCategory.

Local Open Scope cat.

(**
 1. Preservation of the identity
 *)
Definition double_functor_hor_id_data
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
           (I₁ : hor_id D₁)
           (I₂ : hor_id D₂)
  : UU
  := ∏ (x : C₁),
     double_id I₂ (F x)
     -->[ identity _ ][ identity _ ]
     FF _ _ (double_id I₁ x).

Definition double_functor_hor_id_laws
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           {I₁ : hor_id D₁}
           {I₂ : hor_id D₂}
           (FI : double_functor_hor_id_data FF I₁ I₂)
  : UU
  := ∏ (x y : C₁)
       (f : x --> y),
     double_id_mor I₂ (#F f) ;;2 FI y
     =
     transportb
       (λ z, _ -->[ z ][ _ ] _)
       (id_right _ @ !(id_left _))
       (transportb
          (λ z, _ -->[ _ ][ z ] _)
          (id_right _ @ !(id_left _))
          (FI x ;;2 #2 FF (double_id_mor I₁ f))).

Definition double_functor_hor_id
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
           (I₁ : hor_id D₁)
           (I₂ : hor_id D₂)
  : UU
  := ∑ (FI : double_functor_hor_id_data FF I₁ I₂), double_functor_hor_id_laws FI.

Definition make_double_functor_hor_id
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           {I₁ : hor_id D₁}
           {I₂ : hor_id D₂}
           (FI : double_functor_hor_id_data FF I₁ I₂)
           (HFI : double_functor_hor_id_laws FI)
  : double_functor_hor_id FF I₁ I₂
  := FI ,, HFI.

Definition functor_double_id_cell
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           {I₁ : hor_id D₁}
           {I₂ : hor_id D₂}
           (IFF : double_functor_hor_id FF I₁ I₂)
           (x : C₁)
  : double_id I₂ (F x)
    -->[ identity _ ][ identity _ ]
    FF _ _ (double_id I₁ x)
  := pr1 IFF x.

Proposition functor_double_id_eq
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            (IFF : double_functor_hor_id FF I₁ I₂)
            {x y : C₁}
            (f : x --> y)
  : double_id_mor I₂ (#F f) ;;2 functor_double_id_cell IFF y
    =
    transportb
      (λ z, _ -->[ z ][ _ ] _)
      (id_right _ @ !(id_left _))
      (transportb
         (λ z, _ -->[ _ ][ z ] _)
         (id_right _ @ !(id_left _))
         (functor_double_id_cell IFF x ;;2 #2 FF (double_id_mor I₁ f))).
Proof.
  exact (pr2 IFF x y f).
Defined.

(**
 2. Preservation of composition
 *)
Definition double_functor_hor_comp_data
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
           (Cm₁ : hor_comp D₁)
           (Cm₂ : hor_comp D₂)
  : UU
  := ∏ (x y z : C₁)
       (h : D₁ x y)
       (k : D₁ y z),
     double_hor_comp Cm₂ (FF _ _ h) (FF _ _ k)
     -->[ identity _ ][ identity _ ]
     FF _ _ (double_hor_comp Cm₁ h k).

Definition double_functor_hor_comp_laws
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           {Cm₁ : hor_comp D₁}
           {Cm₂ : hor_comp D₂}
           (FC : double_functor_hor_comp_data FF Cm₁ Cm₂)
  : UU
  := ∏ (x₁ x₂ y₁ y₂ z₁ z₂ : C₁)
       (v₁ : x₁ --> x₂)
       (v₂ : y₁ --> y₂)
       (v₃ : z₁ --> z₂)
       (h₁ : D₁ x₁ y₁) (h₂ : D₁ x₂ y₂)
       (k₁ : D₁ y₁ z₁) (k₂ : D₁ y₂ z₂)
       (s₁ : h₁ -->[ v₁ ][ v₂ ] h₂)
       (s₂ : k₁ -->[ v₂ ][ v₃ ] k₂),
     double_hor_comp_mor Cm₂ (#2 FF s₁) (#2 FF s₂) ;;2 FC _ _ _ _ _
     =
     transportb
       (λ z, _ -->[ z ][ _ ] _)
       (id_right _ @ !(id_left _))
       (transportb
          (λ z, _ -->[ _ ][ z ] _)
          (id_right _ @ !(id_left _))
          (FC _ _ _ _ _ ;;2 #2 FF (double_hor_comp_mor Cm₁ s₁ s₂))).

Definition double_functor_hor_comp
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
           (Cm₁ : hor_comp D₁)
           (Cm₂ : hor_comp D₂)
  : UU
  := ∑ (FC : double_functor_hor_comp_data FF Cm₁ Cm₂),
     double_functor_hor_comp_laws FC.

Definition make_double_functor_hor_comp
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           {Cm₁ : hor_comp D₁}
           {Cm₂ : hor_comp D₂}
           (FC : double_functor_hor_comp_data FF Cm₁ Cm₂)
           (HFC : double_functor_hor_comp_laws FC)
  : double_functor_hor_comp FF Cm₁ Cm₂
  := FC ,, HFC.

Definition functor_double_comp_cell
           {C₁ C₂ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           {Cm₁ : hor_comp D₁}
           {Cm₂ : hor_comp D₂}
           (CFF : double_functor_hor_comp FF Cm₁ Cm₂)
           {x y z : C₁}
           (h : D₁ x y)
           (k : D₁ y z)
  : double_hor_comp Cm₂ (FF _ _ h) (FF _ _ k)
    -->[ identity _ ][ identity _ ]
    FF _ _ (double_hor_comp Cm₁ h k)
  := pr1 CFF x y z h k.

Proposition functor_double_comp_eq
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            (FC : double_functor_hor_comp FF Cm₁ Cm₂)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C₁}
            {v₁ : x₁ --> x₂}
            {v₂ : y₁ --> y₂}
            {v₃ : z₁ --> z₂}
            {h₁ : D₁ x₁ y₁} {h₂ : D₁ x₂ y₂}
            {k₁ : D₁ y₁ z₁} {k₂ : D₁ y₂ z₂}
            (s₁ : h₁ -->[ v₁ ][ v₂ ] h₂)
            (s₂ : k₁ -->[ v₂ ][ v₃ ] k₂)
  : double_hor_comp_mor Cm₂ (#2 FF s₁) (#2 FF s₂) ;;2 functor_double_comp_cell FC _ _
    =
    transportb
      (λ z, _ -->[ z ][ _ ] _)
      (id_right _ @ !(id_left _))
      (transportb
         (λ z, _ -->[ _ ][ z ] _)
         (id_right _ @ !(id_left _))
         (functor_double_comp_cell FC _ _ ;;2 #2 FF (double_hor_comp_mor Cm₁ s₁ s₂))).
Proof.
  exact (pr2 FC x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂).
Defined.

(**
 3. Preservation of the unitors and associators
 *)
Definition double_functor_lunitor
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {I₁ : hor_id D₁}
           {Cm₁ : hor_comp D₁}
           {I₂ : hor_id D₂}
           {Cm₂ : hor_comp D₂}
           (l₁ : double_cat_lunitor I₁ Cm₁)
           (l₂ : double_cat_lunitor I₂ Cm₂)
           {FF : twosided_disp_functor F F D₁ D₂}
           (FI : double_functor_hor_id FF I₁ I₂)
           (FC : double_functor_hor_comp FF Cm₁ Cm₂)
  : UU
  := ∏ (x y : C₁)
       (f : D₁ x y),
     double_hor_comp_mor Cm₂ (functor_double_id_cell FI _) (id_two_disp _)
     ;;2
     functor_double_comp_cell FC _ _
     ;;2
     #2 FF (double_lunitor l₁ f)
     =
     transportb
       (λ z, _ -->[ _][ z ] _)
       (assoc' _ _ _ @ id_left _ @ id_left _ @ functor_id F _)
       (transportb
          (λ z, _ -->[ z ][ _ ] _)
          (assoc' _ _ _ @ id_left _ @ id_left _ @ functor_id F _)
          (double_lunitor l₂ (FF _ _ f))).

Proposition isaprop_double_functor_lunitor
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {I₁ : hor_id D₁}
            {Cm₁ : hor_comp D₁}
            {I₂ : hor_id D₂}
            {Cm₂ : hor_comp D₂}
            (l₁ : double_cat_lunitor I₁ Cm₁)
            (l₂ : double_cat_lunitor I₂ Cm₂)
            {FF : twosided_disp_functor F F D₁ D₂}
            (FI : double_functor_hor_id FF I₁ I₂)
            (FC : double_functor_hor_comp FF Cm₁ Cm₂)
  : isaprop (double_functor_lunitor l₁ l₂ FI FC).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

(**
 4. Bundled version of the definition
 *)

(**
 5. The identity double functor
 *)
Definition identity_hor_id_data
           (C : category)
           (D : twosided_disp_cat C C)
           (I : hor_id D)
  : double_functor_hor_id_data (twosided_disp_functor_identity D) I I
  := λ x, id_two_disp _.

Arguments identity_hor_id_data {C D} I /.

Proposition identity_hor_id_laws
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
  : double_functor_hor_id_laws (identity_hor_id_data I).
Proof.
  intros x y f ; cbn.
  rewrite id_two_disp_left, id_two_disp_right.
  refine (!_).
  unfold transportb.
  etrans.
  {
    apply maponpaths.
    rewrite twosided_swap_transport.
    rewrite transport_f_f.
    apply idpath.
  }
  rewrite transport_f_f.
  rewrite <- !twosided_swap_transport.
  rewrite !twosided_prod_transport_alt.
  apply maponpaths_2.
  apply isasetdirprod ; apply homset_property.
Qed.

Definition identity_hor_id
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
  : double_functor_hor_id (twosided_disp_functor_identity D) I I.
Proof.
  use make_double_functor_hor_id.
  - exact (identity_hor_id_data I).
  - exact (identity_hor_id_laws I).
Defined.

Definition identity_hor_comp_data
           (C : category)
           (D : twosided_disp_cat C C)
           (Cm : hor_comp D)
  : double_functor_hor_comp_data (twosided_disp_functor_identity D) Cm Cm
  := λ x y z h k, id_two_disp _.

Arguments identity_hor_comp_data {C D} Cm /.

Proposition identity_hor_comp_laws
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
  : double_functor_hor_comp_laws (identity_hor_comp_data Cm).
Proof.
  intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂ ; cbn.
  rewrite id_two_disp_left, id_two_disp_right.
  refine (!_).
  unfold transportb.
  etrans.
  {
    apply maponpaths.
    rewrite twosided_swap_transport.
    rewrite transport_f_f.
    apply idpath.
  }
  rewrite transport_f_f.
  rewrite <- !twosided_swap_transport.
  rewrite !twosided_prod_transport_alt.
  apply maponpaths_2.
  apply isasetdirprod ; apply homset_property.
Qed.

Definition identity_hor_comp
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp D)
  : double_functor_hor_comp (twosided_disp_functor_identity D) Cm Cm.
Proof.
  use make_double_functor_hor_comp.
  - exact (identity_hor_comp_data Cm).
  - exact (identity_hor_comp_laws Cm).
Defined.

Proposition identity_functor_lunitor
            {C : category}
            {D : twosided_disp_cat C C}
            {I : hor_id D}
            {Cm : hor_comp D}
            (l : double_cat_lunitor I Cm)
  : double_functor_lunitor l l (identity_hor_id I) (identity_hor_comp Cm).
Proof.
  intros x y f ; cbn.
  rewrite double_hor_comp_mor_id.
  rewrite id_two_disp_left.
  unfold transportb.
  rewrite two_disp_pre_whisker_left.
  rewrite two_disp_pre_whisker_right.
  rewrite twosided_prod_transport, twosided_prod_transport_alt.
  rewrite id_two_disp_left.
  unfold transportb.
  rewrite twosided_prod_transport.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply isasetdirprod ; apply homset_property.
Qed.

(**
 6. The composition of double functors
 *)
Definition comp_hor_id_data
           {C₁ C₂ C₃ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {D₃ : twosided_disp_cat C₃ C₃}
           {I₁ : hor_id D₁}
           {I₂ : hor_id D₂}
           {I₃ : hor_id D₃}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           {G : C₂ ⟶ C₃}
           {GG : twosided_disp_functor G G D₂ D₃}
           (HFF : double_functor_hor_id FF I₁ I₂)
           (HGG : double_functor_hor_id GG I₂ I₃)
  : double_functor_hor_id_data (comp_twosided_disp_functor FF GG) I₁ I₃.
Proof.
  refine (λ x,
          transportb
            (λ z, _ -->[ _][ z ] _)
            _
            (transportb
               (λ z, _ -->[ z ][ _ ] _)
               _
               (functor_double_id_cell HGG (F x)
                ;;2
                 #2 GG (functor_double_id_cell HFF x)))).
  - abstract
      (rewrite functor_id ;
       rewrite id_left ;
       apply idpath).
  - abstract
      (rewrite functor_id ;
       rewrite id_left ;
       apply idpath).
Defined.

Arguments comp_hor_id_data /.

Proposition comp_hor_id_laws
            {C₁ C₂ C₃ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            {I₃ : hor_id D₃}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {G : C₂ ⟶ C₃}
            {GG : twosided_disp_functor G G D₂ D₃}
            (HFF : double_functor_hor_id FF I₁ I₂)
            (HGG : double_functor_hor_id GG I₂ I₃)
  : double_functor_hor_id_laws (comp_hor_id_data HFF HGG).
Proof.
  intros x y f ; cbn.
  unfold transportb.
  etrans.
  {
    rewrite two_disp_post_whisker_right.
    rewrite two_disp_post_whisker_left.
    rewrite !twosided_prod_transport_alt.
    rewrite assoc_two_disp.
    unfold transportb.
    rewrite <- !twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    rewrite functor_double_id_eq.
    unfold transportb.
    rewrite two_disp_pre_whisker_left.
    rewrite two_disp_pre_whisker_right.
    rewrite <- !twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    rewrite assoc_two_disp_alt.
    unfold transportb.
    rewrite <- !twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    rewrite twosided_disp_functor_comp_alt.
    rewrite two_disp_post_whisker_left.
    rewrite two_disp_post_whisker_right.
    rewrite <- twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    rewrite functor_double_id_eq.
    rewrite transportb_twosided_disp_functor_left.
    rewrite transportb_twosided_disp_functor_right.
    unfold transportb.
    rewrite two_disp_post_whisker_left.
    rewrite two_disp_post_whisker_right.
    rewrite <- twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    rewrite twosided_disp_functor_comp.
    unfold transportb.
    rewrite two_disp_post_whisker_left.
    rewrite two_disp_post_whisker_right.
    rewrite <- twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    rewrite two_disp_pre_whisker_right.
    rewrite two_disp_pre_whisker_left.
    rewrite !twosided_prod_transport_alt.
    rewrite <- !twosided_swap_transport.
    rewrite !twosided_prod_transport_alt.
    rewrite transport_f_f.
    rewrite assoc_two_disp_alt.
    unfold transportb.
    rewrite <- !twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    apply idpath.
  }
  apply maponpaths_2.
  apply isasetdirprod ; apply homset_property.
Qed.

Definition comp_hor_id
           {C₁ C₂ C₃ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {D₃ : twosided_disp_cat C₃ C₃}
           {I₁ : hor_id D₁}
           {I₂ : hor_id D₂}
           {I₃ : hor_id D₃}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           {G : C₂ ⟶ C₃}
           {GG : twosided_disp_functor G G D₂ D₃}
           (HFF : double_functor_hor_id FF I₁ I₂)
           (HGG : double_functor_hor_id GG I₂ I₃)
  : double_functor_hor_id (comp_twosided_disp_functor FF GG) I₁ I₃.
Proof.
  use make_double_functor_hor_id.
  - exact (comp_hor_id_data HFF HGG).
  - exact (comp_hor_id_laws HFF HGG).
Defined.

Definition comp_hor_comp_data
           {C₁ C₂ C₃ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {D₃ : twosided_disp_cat C₃ C₃}
           {Cm₁ : hor_comp D₁}
           {Cm₂ : hor_comp D₂}
           {Cm₃ : hor_comp D₃}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           {G : C₂ ⟶ C₃}
           {GG : twosided_disp_functor G G D₂ D₃}
           (HFF : double_functor_hor_comp FF Cm₁ Cm₂)
           (HGG : double_functor_hor_comp GG Cm₂ Cm₃)
  : double_functor_hor_comp_data (comp_twosided_disp_functor FF GG) Cm₁ Cm₃.
Proof.
  refine (λ x y z h k,
          transportb
            (λ z, _ -->[ _][ z ] _)
            _
            (transportb
               (λ z, _ -->[ z ][ _ ] _)
               _
               (functor_double_comp_cell HGG (FF _ _ h) (FF _ _ k)
                ;;2
                 #2 GG (functor_double_comp_cell HFF h k)))).
  - abstract
      (rewrite functor_id ;
       rewrite id_left ;
       apply idpath).
  - abstract
      (rewrite functor_id ;
       rewrite id_left ;
       apply idpath).
Defined.

Arguments comp_hor_comp_data /.

Proposition comp_hor_comp_laws
            {C₁ C₂ C₃ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {Cm₃ : hor_comp D₃}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {G : C₂ ⟶ C₃}
            {GG : twosided_disp_functor G G D₂ D₃}
            (HFF : double_functor_hor_comp FF Cm₁ Cm₂)
            (HGG : double_functor_hor_comp GG Cm₂ Cm₃)
  : double_functor_hor_comp_laws (comp_hor_comp_data HFF HGG).
Proof.
  intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂ ; cbn.
  unfold transportb.
  etrans.
  {
    rewrite two_disp_post_whisker_right.
    rewrite two_disp_post_whisker_left.
    rewrite !twosided_prod_transport_alt.
    rewrite assoc_two_disp.
    unfold transportb.
    rewrite <- !twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    rewrite functor_double_comp_eq.
    unfold transportb.
    rewrite two_disp_pre_whisker_left.
    rewrite two_disp_pre_whisker_right.
    rewrite <- !twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    rewrite assoc_two_disp_alt.
    unfold transportb.
    rewrite <- !twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    rewrite twosided_disp_functor_comp_alt.
    rewrite two_disp_post_whisker_left.
    rewrite two_disp_post_whisker_right.
    rewrite <- twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    rewrite functor_double_comp_eq.
    rewrite transportb_twosided_disp_functor_left.
    rewrite transportb_twosided_disp_functor_right.
    unfold transportb.
    rewrite two_disp_post_whisker_left.
    rewrite two_disp_post_whisker_right.
    rewrite <- twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    rewrite twosided_disp_functor_comp.
    unfold transportb.
    rewrite two_disp_post_whisker_left.
    rewrite two_disp_post_whisker_right.
    rewrite <- twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    rewrite two_disp_pre_whisker_right.
    rewrite two_disp_pre_whisker_left.
    rewrite !twosided_prod_transport_alt.
    rewrite <- !twosided_swap_transport.
    rewrite !twosided_prod_transport_alt.
    rewrite transport_f_f.
    rewrite assoc_two_disp_alt.
    unfold transportb.
    rewrite <- !twosided_swap_transport.
    rewrite twosided_prod_transport_alt.
    rewrite transport_f_f.
    apply idpath.
  }
  apply maponpaths_2.
  apply isasetdirprod ; apply homset_property.
Qed.

Definition comp_hor_comp
           {C₁ C₂ C₃ : category}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {D₃ : twosided_disp_cat C₃ C₃}
           {Cm₁ : hor_comp D₁}
           {Cm₂ : hor_comp D₂}
           {Cm₃ : hor_comp D₃}
           {F : C₁ ⟶ C₂}
           {FF : twosided_disp_functor F F D₁ D₂}
           {G : C₂ ⟶ C₃}
           {GG : twosided_disp_functor G G D₂ D₃}
           (HFF : double_functor_hor_comp FF Cm₁ Cm₂)
           (HGG : double_functor_hor_comp GG Cm₂ Cm₃)
  : double_functor_hor_comp (comp_twosided_disp_functor FF GG) Cm₁ Cm₃.
Proof.
  use make_double_functor_hor_comp.
  - exact (comp_hor_comp_data HFF HGG).
  - exact (comp_hor_comp_laws HFF HGG).
Defined.

Proposition comp_functor_lunitor
            {C₁ C₂ C₃ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            {I₃ : hor_id D₃}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {Cm₃ : hor_comp D₃}
            {l₁ : double_cat_lunitor I₁ Cm₁}
            {l₂ : double_cat_lunitor I₂ Cm₂}
            {l₃ : double_cat_lunitor I₃ Cm₃}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {G : C₂ ⟶ C₃}
            {GG : twosided_disp_functor G G D₂ D₃}
            {FI : double_functor_hor_id FF I₁ I₂}
            {GI : double_functor_hor_id GG I₂ I₃}
            {FC : double_functor_hor_comp FF Cm₁ Cm₂}
            {GC : double_functor_hor_comp GG Cm₂ Cm₃}
            (Fl : double_functor_lunitor l₁ l₂ FI FC)
            (Gl : double_functor_lunitor l₂ l₃ GI GC)
  : double_functor_lunitor
      l₁ l₃
      (comp_hor_id FI GI)
      (comp_hor_comp FC GC).
Proof.
  intros x y f ; cbn.
  unfold transportb.
  rewrite two_disp_post_whisker_right.
  rewrite two_disp_post_whisker_left.
  rewrite two_disp_pre_whisker_right.
  rewrite two_disp_pre_whisker_left.
  rewrite !twosided_prod_transport_alt.

Admitted.
