(**********************************************************************************

 Basics of double functors

 We define the basic notions for double functors. Note that the double functors we
 consider are *lax* double functors. Note the direction of the squares in
 [double_functor_hor_id_data] and in [double_functor_hor_comp_data] and compare to
 definition 6.1 in 'Framed Bicategories and Monoidal Fibrations' by Shulman
 (http://www.tac.mta.ca/tac/volumes/20/18/20-18.pdf). In addition, we show that the
 identity is a double functor.

 The proof that the composition of double functors is again a double functor, is
 split over multiple files (LeftUnitor.v, RightUnitor.v, and Associator.v).

 Contents
 1. Preservation of the identity
 2. Preservation of composition
 3. Preservation of the unitors and associators
 4. The identity double functor

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.

Local Open Scope cat.

(** * 1. Preservation of the identity *)
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
     transportb_disp_mor2
       (id_right _ @ !(id_left _))
       (id_right _ @ !(id_left _))
       (FI x ;;2 #2 FF (double_id_mor I₁ f)).

Proposition isaprop_double_functor_hor_id_laws
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            (FI : double_functor_hor_id_data FF I₁ I₂)
  : isaprop (double_functor_hor_id_laws FI).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

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
    transportb_disp_mor2
      (id_right _ @ !(id_left _))
      (id_right _ @ !(id_left _))
      (functor_double_id_cell IFF x ;;2 #2 FF (double_id_mor I₁ f)).
Proof.
  exact (pr2 IFF x y f).
Qed.

(** * 2. Preservation of composition *)
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
     transportb_disp_mor2
       (id_right _ @ !(id_left _))
       (id_right _ @ !(id_left _))
       (FC _ _ _ _ _ ;;2 #2 FF (double_hor_comp_mor Cm₁ s₁ s₂)).

Proposition isaprop_double_functor_hor_comp_laws
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            (FC : double_functor_hor_comp_data FF Cm₁ Cm₂)
  : isaprop (double_functor_hor_comp_laws FC).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

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
    transportb_disp_mor2
      (id_right _ @ !(id_left _))
      (id_right _ @ !(id_left _))
      (functor_double_comp_cell FC _ _ ;;2 #2 FF (double_hor_comp_mor Cm₁ s₁ s₂)).
Proof.
  exact (pr2 FC x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂).
Qed.

Proposition functor_double_comp_eq_alt
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
  : functor_double_comp_cell FC _ _ ;;2 #2 FF (double_hor_comp_mor Cm₁ s₁ s₂)
    =
    transportf_disp_mor2
      (id_right _ @ !(id_left _))
      (id_right _ @ !(id_left _))
      (double_hor_comp_mor Cm₂ (#2 FF s₁) (#2 FF s₂) ;;2 functor_double_comp_cell FC _ _).
Proof.
  rewrite functor_double_comp_eq.
  rewrite transportfb_disp_mor2.
  apply idpath.
Qed.

Proposition functor_double_comp_eq_transport
            {C₁ C₂ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            (FC : double_functor_hor_comp FF Cm₁ Cm₂)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C₁}
            {v₁ : x₁ --> x₂} {v₁' : F x₁ --> F x₂}
            {v₂ : y₁ --> y₂} {v₂' : F y₁ --> F y₂}
            {v₃ : z₁ --> z₂} {v₃' : F z₁ --> F z₂}
            (p : #F v₁ = v₁')
            (q q' : #F v₂ = v₂')
            (r : #F v₃ = v₃')
            {h₁ : D₁ x₁ y₁} {h₂ : D₁ x₂ y₂}
            {k₁ : D₁ y₁ z₁} {k₂ : D₁ y₂ z₂}
            (s₁ : h₁ -->[ v₁ ][ v₂ ] h₂)
            (s₂ : k₁ -->[ v₂ ][ v₃ ] k₂)
  : double_hor_comp_mor
      Cm₂
      (transportf_disp_mor2 p q (#2 FF s₁))
      (transportf_disp_mor2 q' r (#2 FF s₂))
    ;;2
    functor_double_comp_cell FC _ _
    =
    transportf_disp_mor2
      (id_left _ @ p @ !(id_right _))
      (id_left _ @ r @ !(id_right _))
      (functor_double_comp_cell FC _ _ ;;2 #2 FF (double_hor_comp_mor Cm₁ s₁ s₂)).
Proof.
  induction p, q, r.
  assert (q' = idpath _) as H.
  {
    apply homset_property.
  }
  rewrite H.
  cbn.
  rewrite functor_double_comp_eq.
  unfold transportb_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.

(** * 3. Preservation of the unitors and associators *)
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
     double_lunitor l₂ (FF _ _ f)
     =
     transportf_disp_mor2
       (assoc' _ _ _ @ id_left _ @ id_left _ @ functor_id F _)
       (assoc' _ _ _ @ id_left _ @ id_left _ @ functor_id F _)
       (double_hor_comp_mor Cm₂ (functor_double_id_cell FI _) (id_two_disp _)
        ;;2
        functor_double_comp_cell FC _ _
        ;;2
        #2 FF (double_lunitor l₁ f)).

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

Definition double_functor_runitor
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {I₁ : hor_id D₁}
           {Cm₁ : hor_comp D₁}
           {I₂ : hor_id D₂}
           {Cm₂ : hor_comp D₂}
           (r₁ : double_cat_runitor I₁ Cm₁)
           (r₂ : double_cat_runitor I₂ Cm₂)
           {FF : twosided_disp_functor F F D₁ D₂}
           (FI : double_functor_hor_id FF I₁ I₂)
           (FC : double_functor_hor_comp FF Cm₁ Cm₂)
  : UU
  := ∏ (x y : C₁)
       (f : D₁ x y),
     double_runitor r₂ (FF _ _ f)
     =
     transportf_disp_mor2
       (assoc' _ _ _ @ id_left _ @ id_left _ @ functor_id F _)
       (assoc' _ _ _ @ id_left _ @ id_left _ @ functor_id F _)
       (double_hor_comp_mor Cm₂ (id_two_disp _) (functor_double_id_cell FI _)
        ;;2
        functor_double_comp_cell FC _ _
        ;;2
        #2 FF (double_runitor r₁ f)).

Proposition isaprop_double_functor_runitor
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {I₁ : hor_id D₁}
            {Cm₁ : hor_comp D₁}
            {I₂ : hor_id D₂}
            {Cm₂ : hor_comp D₂}
            (r₁ : double_cat_runitor I₁ Cm₁)
            (r₂ : double_cat_runitor I₂ Cm₂)
            {FF : twosided_disp_functor F F D₁ D₂}
            (FI : double_functor_hor_id FF I₁ I₂)
            (FC : double_functor_hor_comp FF Cm₁ Cm₂)
  : isaprop (double_functor_runitor r₁ r₂ FI FC).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

Definition double_functor_associator
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {Cm₁ : hor_comp D₁}
           {Cm₂ : hor_comp D₂}
           (a₁ : double_cat_associator Cm₁)
           (a₂ : double_cat_associator Cm₂)
           {FF : twosided_disp_functor F F D₁ D₂}
           (FC : double_functor_hor_comp FF Cm₁ Cm₂)
  : UU
  := ∏ (w x y z : C₁)
       (f : D₁ w x)
       (g : D₁ x y)
       (h : D₁ y z),
     double_associator a₂ (FF _ _ f) (FF _ _ g) (FF _ _ h)
     ;;2 double_hor_comp_mor Cm₂ (functor_double_comp_cell FC f g) (id_two_disp _)
     ;;2 functor_double_comp_cell FC (double_hor_comp Cm₁ f g) h
     =
     transportf_disp_mor2
       (maponpaths (λ q, _ · q) (functor_id F _))
       (maponpaths (λ q, _ · q) (functor_id F _))
       (double_hor_comp_mor Cm₂ (id_two_disp _) (functor_double_comp_cell FC g h)
        ;;2 functor_double_comp_cell FC f (double_hor_comp Cm₁ g h)
        ;;2 #2 FF (double_associator a₁ f g h)).

Proposition isaprop_double_functor_associator
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            (a₁ : double_cat_associator Cm₁)
            (a₂ : double_cat_associator Cm₂)
            {FF : twosided_disp_functor F F D₁ D₂}
            (FC : double_functor_hor_comp FF Cm₁ Cm₂)
  : isaprop (double_functor_associator a₁ a₂ FC).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

(** * 4. The identity double functor *)
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
  rewrite transport_b_b_disp_mor2.
  use transportb_disp_mor2_eq.
  apply idpath.
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
  rewrite transport_b_b_disp_mor2.
  use transportb_disp_mor2_eq.
  apply idpath.
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
  unfold transportb_disp_mor2.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite id_two_disp_left.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  refine (!_).
  apply transportf_disp_mor2_idpath.
Qed.

Proposition identity_functor_runitor
            {C : category}
            {D : twosided_disp_cat C C}
            {I : hor_id D}
            {Cm : hor_comp D}
            (r : double_cat_runitor I Cm)
  : double_functor_runitor r r (identity_hor_id I) (identity_hor_comp Cm).
Proof.
  intros x y f ; cbn.
  rewrite double_hor_comp_mor_id.
  rewrite id_two_disp_left.
  unfold transportb_disp_mor2.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite id_two_disp_left.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  refine (!_).
  apply transportf_disp_mor2_idpath.
Qed.

Proposition identity_functor_associator
            {C : category}
            {D : twosided_disp_cat C C}
            {Cm : hor_comp D}
            (a : double_cat_associator Cm)
  : double_functor_associator a a (identity_hor_comp Cm).
Proof.
  intros w x y z f g h ; cbn.
  rewrite id_two_disp_right.
  rewrite double_hor_comp_mor_id.
  rewrite id_two_disp_right.
  rewrite transport_b_b_disp_mor2.
  rewrite id_two_disp_right.
  rewrite double_hor_comp_mor_id.
  rewrite two_disp_pre_whisker_b.
  rewrite id_two_disp_left.
  rewrite transport_b_b_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
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
  : double_functor_hor_id_data (comp_twosided_disp_functor FF GG) I₁ I₃
  := λ x,
     transportf_disp_mor2
       (id_left _ @ functor_id _ _)
       (id_left _ @ functor_id _ _)
       (functor_double_id_cell HGG (F x)
        ;;2
        #2 GG (functor_double_id_cell HFF x)).

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
  rewrite two_disp_post_whisker_f.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite (functor_double_id_eq HGG).
  rewrite two_disp_pre_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp_alt.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite (twosided_disp_functor_comp_alt _ _ _ _ GG).
  rewrite two_disp_post_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite (functor_double_id_eq HFF).
  rewrite transportb_twosided_disp_functor.
  rewrite two_disp_post_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite (twosided_disp_functor_comp _ _ _ _ GG).
  rewrite two_disp_post_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  refine (!_).
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp_alt.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
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
          transportb_disp_mor2
            _
            _
            (functor_double_comp_cell HGG (FF _ _ h) (FF _ _ k)
             ;;2
             #2 GG (functor_double_comp_cell HFF h k))).
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
  etrans.
  {
    rewrite two_disp_post_whisker_b.
    rewrite assoc_two_disp.
    rewrite transport_b_b_disp_mor2.
    rewrite functor_double_comp_eq.
    rewrite two_disp_pre_whisker_b.
    rewrite transport_b_b_disp_mor2.
    rewrite assoc_two_disp_alt.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite twosided_disp_functor_comp_alt.
    rewrite two_disp_post_whisker_f.
    rewrite transport_f_f_disp_mor2.
    rewrite functor_double_comp_eq.
    rewrite transportb_twosided_disp_functor.
    rewrite two_disp_post_whisker_b.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite twosided_disp_functor_comp.
    rewrite two_disp_post_whisker_b.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    rewrite two_disp_pre_whisker_b.
    rewrite transport_b_b_disp_mor2.
    rewrite assoc_two_disp_alt.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    apply idpath.
  }
  use transportf_disp_mor2_eq.
  apply idpath.
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
