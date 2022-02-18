(*****************************************************************************

 Display map bicategories

 1. Subbicategories of the arrow bicategory
 2. Examples of subbicategories of the arrow bicategory
 3. Display map bicategories
 4. Examples of display map bicategories

 *****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.Morphisms.Properties.ClosedUnderPullback.
Require Import UniMath.Bicategories.Limits.Pullbacks.

Local Open Scope cat.

(**
 1. Subbicategories of the arrow bicategory
 *)
Section Subbicat.
  Context {B : bicat}
          (pred_mor : ∏ (e₁ e₂ b₁ b₂ : B)
                        (p₁ : e₁ --> b₁)
                        (p₂ : e₂ --> b₂)
                        (fe : e₁ --> e₂),
                      UU).

  Let P₁ {e₁ e₂ b₁ b₂ : B}
         (p₁ : e₁ --> b₁)
         (p₂ : e₂ --> b₂)
         (fe : e₁ --> e₂)
    : UU
    := pred_mor _ _ _ _ p₁ p₂ fe.

  Definition contains_id
    : UU
    := ∏ (e b : B)
         (p : e --> b),
       P₁ p p (id₁ _).

  Definition closed_under_comp
    : UU
    := ∏ (e₁ e₂ e₃ b₁ b₂ b₃ : B)
         (p₁ : e₁ --> b₁)
         (p₂ : e₂ --> b₂)
         (p₃ : e₃ --> b₃)
         (fe : e₁ --> e₂) (ge : e₂ --> e₃),
       P₁ p₁ p₂ fe
       →
       P₁ p₂ p₃ ge
       →
       P₁ p₁ p₃ (fe · ge).

  Definition contains_equiv_over_id
    : UU
    := ∏ (e₁ e₂ b : B)
         (p₁ : e₁ --> b)
         (p₂ : e₂ --> b)
         (fe : e₁ --> e₂),
       left_adjoint_equivalence fe
       →
       invertible_2cell p₁ (fe · p₂)
       →
       P₁ p₁ p₂ fe.

  Definition closed_under_invertible_2cell
    : UU
    := ∏ (e₁ e₂ b₁ b₂ : B)
         (p₁ : e₁ --> b₁)
         (p₂ : e₂ --> b₂)
         (fe₁ fe₂ : e₁ --> e₂)
         (α : invertible_2cell fe₁ fe₂)
         (H : P₁ p₁ p₂ fe₁),
       P₁ p₁ p₂ fe₂.
End Subbicat.

Definition arrow_subbicat
           (B : bicat)
  : UU
  := ∑ (P₀ : ∏ (x y : B), x --> y → UU)
       (P₁ : ∏ (e₁ e₂ b₁ b₂ : B)
               (p₁ : e₁ --> b₁)
               (p₂ : e₂ --> b₂)
               (fe : e₁ --> e₂),
             UU),
     contains_id P₁
     ×
     closed_under_comp P₁
     ×
     closed_under_invertible_2cell P₁.

Section Projections.
  Context {B : bicat}
          (D : arrow_subbicat B).

  Definition pred_ob
             {x y : B}
             (f : x --> y)
    : UU
    := pr1 D x y f.

  Definition pred_mor
             {e₁ e₂ b₁ b₂ : B}
             (p₁ : e₁ --> b₁)
             (p₂ : e₂ --> b₂)
             (fe : e₁ --> e₂)
    : UU
    := pr12 D e₁ e₂ b₁ b₂ p₁ p₂ fe.

  Definition id_pred_mor
             {e b : B}
             (p : e --> b)
    : pred_mor p p (id₁ e)
    := pr122 D e b p.

  Definition comp_pred_mor
             {e₁ e₂ e₃ b₁ b₂ b₃ : B}
             {p₁ : e₁ --> b₁}
             {p₂ : e₂ --> b₂}
             {p₃ : e₃ --> b₃}
             {fe : e₁ --> e₂}
             {ge : e₂ --> e₃}
             (Hfe : pred_mor p₁ p₂ fe)
             (Hge : pred_mor p₂ p₃ ge)
    : pred_mor p₁ p₃ (fe · ge)
    := pr1 (pr222 D) _ _ _ _ _ _ _ _ _ _ _ Hfe Hge.

  Definition invertible_pred_mor
             {e₁ e₂ b₁ b₂ : B}
             {p₁ : e₁ --> b₁}
             {p₂ : e₂ --> b₂}
             {fe₁ fe₂ : e₁ --> e₂}
             (α : invertible_2cell fe₁ fe₂)
             (H : pred_mor p₁ p₂ fe₁)
    : pred_mor p₁ p₂ fe₂
    := pr2 (pr222 D) _ _ _ _ _ _ _ _ α H.
End Projections.

Definition make_arrow_subbicat
           {B : bicat}
           (P₀ : ∏ (x y : B), x --> y → UU)
           (P₁ : ∏ (e₁ e₂ b₁ b₂ : B)
                   (p₁ : e₁ --> b₁)
                   (p₂ : e₂ --> b₂)
                   (fe : e₁ --> e₂),
                 UU)
           (Hid : contains_id P₁)
           (Hcomp : closed_under_comp P₁)
           (Hinv : closed_under_invertible_2cell P₁)
  : arrow_subbicat B
  := (P₀ ,, P₁ ,, Hid ,, Hcomp ,, Hinv).

Definition arrow_subbicat_contains_equiv_over_id
           {B : bicat}
           (HB : is_univalent_2 B)
           (D : arrow_subbicat B)
  : contains_equiv_over_id (λ e₁ e₂ b₁ b₂ p₁ p₂ fe, pred_mor D p₁ p₂ fe).
Proof.
  intros e₁ e₂ b p₁ p₂ fe Hfe γ.
  refine (J_2_0
            (pr1 HB)
            (λ (x₁ x₂ : B) (L : adjoint_equivalence x₁ x₂),
             ∏ (p₁ : x₁ --> b)
               (p₂ : x₂ --> b)
               (γ : invertible_2cell p₁ (pr1 L · p₂)),
             pred_mor D p₁ p₂ (pr1 L))
            _
            (fe ,, Hfe)
            p₁
            p₂
            γ).
  cbn.
  clear e₁ e₂ p₁ p₂ fe Hfe γ.
  intros e p₁ p₂ γ.
  pose (c := comp_of_invertible_2cell γ (lunitor_invertible_2cell _)).
  use (J_2_1
         (pr2 HB)
         (λ (x₁ x₂ : B)
            (f g : x₁ --> x₂)
            (γ : invertible_2cell f g),
          pred_mor D f g (id₁ _))
         _
         c).
  cbn ; intros.
  apply (id_pred_mor D).
Defined.

Definition arrow_subbicat_props
           {B : bicat}
           (D : arrow_subbicat B)
  : UU
  := (∏ (x y : B) (f : x --> y), isaprop (pred_ob D f))
     ×
     (∏ (e₁ e₂ b₁ b₂ : B)
        (p₁ : e₁ --> b₁)
        (p₂ : e₂ --> b₂)
        (fe : e₁ --> e₂),
      isaprop (pred_mor D p₁ p₂ fe)).

(**
 2. Examples of subbicategories of the arrow bicategory
 *)
Definition full_arrow_subbicat
           {B : bicat}
           (P₀ : ∏ (x y : B), x --> y → UU)
  : arrow_subbicat B.
Proof.
  use make_arrow_subbicat.
  - exact P₀.
  - exact (λ _ _ _ _ _ _ _, unit).
  - exact (λ _ _ _, tt).
  - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _, tt).
  - exact (λ _ _ _ _ _ _ _ _ _ _, tt).
Defined.

Definition full_arrow_subbicat_props
           {B : bicat}
           (P₀ : ∏ (x y : B), x --> y → UU)
           (isaprop_P₀ : ∏ (x y : B) (f : x --> y), isaprop (P₀ _ _ f))
  : arrow_subbicat_props (full_arrow_subbicat P₀).
Proof.
  split.
  - intros.
    apply isaprop_P₀.
  - intros.
    apply isapropunit.
Defined.

Definition intersection_arrow_subbicat
           {B : bicat}
           (D₁ D₂ : arrow_subbicat B)
  : arrow_subbicat B.
Proof.
  use make_arrow_subbicat.
  - exact (λ x y f, pred_ob D₁ f × pred_ob D₂ f).
  - exact (λ _ _ _ _ p₁ p₂ fe,
           pred_mor D₁ p₁ p₂ fe
           ×
           pred_mor D₂ p₁ p₂ fe).
  - intro ; intros.
    split ; apply id_pred_mor.
  - intros ? ? ? ? ? ? ? ? ? ? ? H₁ H₂.
    split.
    + exact (comp_pred_mor
               D₁
               (pr1 H₁) (pr1 H₂)).
    + exact (comp_pred_mor
               D₂
               (pr2 H₁) (pr2 H₂)).
  - intros e₁ e₂ b₁ b₂ p₁ p₂ fe₁ fe₂ α H.
    split.
    + exact (invertible_pred_mor D₁ α (pr1 H)).
    + exact (invertible_pred_mor D₂ α (pr2 H)).
Defined.

Definition intersection_arrow_subbicat_props
           {B : bicat}
           {D₁ D₂ : arrow_subbicat B}
           (HD₁ : arrow_subbicat_props D₁)
           (HD₂ : arrow_subbicat_props D₂)
  : arrow_subbicat_props (intersection_arrow_subbicat D₁ D₂).
Proof.
  split.
  - intros x y f.
    apply isapropdirprod.
    + exact (pr1 HD₁ _ _ f).
    + exact (pr1 HD₂ _ _ f).
  - intros e₁ e₂ b₁ b₂ p₁ p₂ fe.
    apply isapropdirprod.
    + exact (pr2 HD₁ _ _ _ _ p₁ p₂ fe).
    + exact (pr2 HD₂ _ _ _ _ p₁ p₂ fe).
Defined.

Definition faithful_subbicat
           (B : bicat)
  : arrow_subbicat B
  := full_arrow_subbicat (λ _ _ f, faithful_1cell f).

Definition faithful_subbicat_props
           (B : bicat)
  : arrow_subbicat_props (faithful_subbicat B).
Proof.
  use full_arrow_subbicat_props.
  intros.
  apply isaprop_faithful_1cell.
Defined.

Definition fully_faithful_subbicat
           (B : bicat)
  : arrow_subbicat B
  := full_arrow_subbicat (λ _ _ f, fully_faithful_1cell f).

Definition fully_faithful_subbicat_props
           (B : bicat)
  : arrow_subbicat_props (fully_faithful_subbicat B).
Proof.
  use full_arrow_subbicat_props.
  intros.
  apply isaprop_fully_faithful_1cell.
Defined.

Definition conservative_subbicat
           (B : bicat)
  : arrow_subbicat B
  := full_arrow_subbicat (λ _ _ f, conservative_1cell f).

Definition conservative_subbicat_props
           (B : bicat)
  : arrow_subbicat_props (conservative_subbicat B).
Proof.
  use full_arrow_subbicat_props.
  intros.
  apply isaprop_conservative_1cell.
Defined.

Definition discrete_subbicat
           (B : bicat)
  : arrow_subbicat B
  := full_arrow_subbicat (λ _ _ f, discrete_1cell f).

Definition discrete_subbicat_props
           (B : bicat)
  : arrow_subbicat_props (discrete_subbicat B).
Proof.
  use full_arrow_subbicat_props.
  intros.
  apply isaprop_discrete_1cell.
Defined.

Definition sfib_subbicat
           (B : bicat)
  : arrow_subbicat B.
Proof.
  use make_arrow_subbicat.
  - exact (λ _ _ f, internal_sfib f).
  - exact (λ _ _ _ _ p₁ p₂ fe, mor_preserves_cartesian p₁ p₂ fe).
  - intro ; intros.
    apply id_mor_preserves_cartesian.
  - intros e₁ e₂ e₃ b₁ b₂ b₃ p₁ p₂ p₃ fe ge Hf Hg.
    exact (comp_preserves_cartesian Hf Hg).
  - intros e₁ e₂ b₁ b₂ p₁ p₂ fe₁ fe₂ α H.
    exact (invertible_2cell_between_preserves_cartesian α H).
Defined.

Definition sfib_subbicat_props
           (B : bicat)
           (HB_2_1 : is_univalent_2_1 B)
  : arrow_subbicat_props (sfib_subbicat B).
Proof.
  split.
  - intros ; simpl.
    apply isaprop_internal_sfib.
    exact HB_2_1.
  - intros ; simpl.
    apply isaprop_mor_preserves_cartesian.
Defined.

Definition sopfib_subbicat
           (B : bicat)
  : arrow_subbicat B.
Proof.
  use make_arrow_subbicat.
  - exact (λ _ _ f, internal_sopfib f).
  - exact (λ _ _ _ _ p₁ p₂ fe, mor_preserves_opcartesian p₁ p₂ fe).
  - intro ; intros.
    apply id_mor_preserves_opcartesian.
  - intros e₁ e₂ e₃ b₁ b₂ b₃ p₁ p₂ p₃ fe ge Hf Hg.
    exact (comp_preserves_opcartesian Hf Hg).
  - intros e₁ e₂ b₁ b₂ p₁ p₂ fe₁ fe₂ α H.
    exact (invertible_2cell_between_preserves_opcartesian α H).
Defined.

Definition sopfib_subbicat_props
           (B : bicat)
           (HB_2_1 : is_univalent_2_1 B)
  : arrow_subbicat_props (sopfib_subbicat B).
Proof.
  split.
  - intros ; simpl.
    apply isaprop_internal_sopfib.
    exact HB_2_1.
  - intros ; simpl.
    apply isaprop_mor_preserves_opcartesian.
Defined.

Definition discrete_sfib_subbicat
           (B : bicat)
  : arrow_subbicat B
  := intersection_arrow_subbicat
       (sfib_subbicat B)
       (discrete_subbicat B).

Definition discrete_sfib_subbicat_props
           (B : bicat)
           (HB_2_1 : is_univalent_2_1 B)
  : arrow_subbicat_props (discrete_sfib_subbicat B).
Proof.
  use intersection_arrow_subbicat_props.
  - exact (sfib_subbicat_props _ HB_2_1).
  - exact (discrete_subbicat_props B).
Defined.

Definition discrete_sopfib_subbicat
           (B : bicat)
  : arrow_subbicat B
  := intersection_arrow_subbicat
       (sopfib_subbicat B)
       (discrete_subbicat B).

Definition discrete_sopfib_subbicat_props
           (B : bicat)
           (HB_2_1 : is_univalent_2_1 B)
  : arrow_subbicat_props (discrete_sopfib_subbicat B).
Proof.
  use intersection_arrow_subbicat_props.
  - exact (sopfib_subbicat_props _ HB_2_1).
  - exact (discrete_subbicat_props B).
Defined.

(**
 3. Display map bicategories
 *)
Section DispMapBicat.
  Context {B : bicat}
          (D : arrow_subbicat B).

  Definition closed_under_pb
    : UU
    := ∏ (pb x y z : B)
         (f : x --> z)
         (g : y --> z)
         (p₁ : pb --> x)
         (p₂ : pb --> y)
         (γ : invertible_2cell (p₁ · f) (p₂ · g)),
       pred_ob D f
       → has_pb_ump (make_pb_cone pb p₁ p₂ γ)
       → pred_ob D p₂ × pred_mor D p₂ f p₁.

  Definition contains_pb
    : UU
    := ∏ (x y z : B)
         (f : x --> z)
         (g : y --> z),
       pred_ob D f
       →
       ∑ (pb : B)
         (p₁ : pb --> x)
         (p₂ : pb --> y)
         (γ : invertible_2cell (p₁ · f) (p₂ · g)),
       has_pb_ump (make_pb_cone pb p₁ p₂ γ).

  Definition closed_under_pb_ump_mor
    : UU
    := ∏ (pb x y z : B)
         (f : x --> z)
         (g : y --> z)
         (p₁ : pb --> x)
         (p₂ : pb --> y)
         (γ : invertible_2cell (p₁ · f) (p₂ · g))
         (H : has_pb_ump (make_pb_cone pb p₁ p₂ γ))
         (cc c : B)
         (cp₁ : cc --> x)
         (cp₂ : cc --> c)
         (h : c --> y)
         (δ : invertible_2cell (cp₁ · f) ((cp₂ · h) · g))
         (cone := make_pb_cone cc cp₁ (cp₂ · h) δ),
       pred_ob D f
       → pred_mor D p₂ f p₁
       → pred_mor D cp₂ f cp₁
       → pred_mor D cp₂ p₂ (pb_ump_mor H cone).

  Definition contained_in_sfib
    : UU
    := ∏ (x y : B) (f : x --> y),
       pred_ob D f
       →
       internal_sfib f.

  Definition contained_in_sopfib
    : UU
    := ∏ (x y : B) (f : x --> y),
       pred_ob D f
       →
       internal_sopfib f.

  Definition contained_in_faithful
    : UU
    := ∏ (x y : B) (f : x --> y),
       pred_ob D f
       →
       faithful_1cell f.

  Definition contained_in_conservative
    : UU
    := ∏ (x y : B) (f : x --> y),
       pred_ob D f
       →
       conservative_1cell f.

  Definition contained_in_discrete
    : UU
    := ∏ (x y : B) (f : x --> y),
       pred_ob D f
       →
       discrete_1cell f.

  Definition discrete_contained_in_faithful
             (H : contained_in_discrete)
    : contained_in_faithful.
  Proof.
    intros x y f Hf.
    exact (pr1 (H x y f Hf)).
  Defined.

  Definition discrete_contained_in_conservative
             (H : contained_in_discrete)
    : contained_in_conservative.
  Proof.
    intros x y f Hf.
    exact (pr2 (H x y f Hf)).
  Defined.

  Definition pred_mor_is_mor_preserves_cartesian
    : UU
    := ∏ (e₁ e₂ b₁ b₂ : B)
         (p₁ : e₁ --> b₁)
         (p₂ : e₂ --> b₂)
         (fe : e₁ --> e₂),
       (pred_mor D p₁ p₂ fe
        →
        mor_preserves_cartesian p₁ p₂ fe)
       ×
       (mor_preserves_cartesian p₁ p₂ fe
        →
        pred_mor D p₁ p₂ fe).

  Definition pred_mor_is_mor_preserves_opcartesian
    : UU
    := ∏ (e₁ e₂ b₁ b₂ : B)
         (p₁ : e₁ --> b₁)
         (p₂ : e₂ --> b₂)
         (fe : e₁ --> e₂),
       (pred_mor D p₁ p₂ fe
        →
        mor_preserves_opcartesian p₁ p₂ fe)
       ×
       (mor_preserves_opcartesian p₁ p₂ fe
        →
        pred_mor D p₁ p₂ fe).
End DispMapBicat.

Definition disp_map_bicat
           (B : bicat)
  : UU
  := ∑ (D : arrow_subbicat B),
     closed_under_pb D
     ×
     contains_pb D
     ×
     closed_under_pb_ump_mor D.

Coercion disp_map_bicat_to_arrow_subbicat
         {B : bicat}
         (D : disp_map_bicat B)
  : arrow_subbicat B
  := pr1 D.

Section Projections.
  Context {B : bicat}
          (D : disp_map_bicat B).

  Definition pb_preserves_pred_ob
             {pb x y z : B}
             {f : x --> z}
             {g : y --> z}
             {p₁ : pb --> x}
             {p₂ : pb --> y}
             {γ : invertible_2cell (p₁ · f) (p₂ · g)}
             (Hf : pred_ob D f)
             (pb_sqr : has_pb_ump (make_pb_cone pb p₁ p₂ γ))
    : pred_ob D p₂
    := pr1 (pr12 D pb x y z f g p₁ p₂ γ Hf pb_sqr).

  Definition mor_of_pb_preserves_pred_ob
             {pb x y z : B}
             {f : x --> z}
             {g : y --> z}
             {p₁ : pb --> x}
             {p₂ : pb --> y}
             {γ : invertible_2cell (p₁ · f) (p₂ · g)}
             (Hf : pred_ob D f)
             (pb_sqr : has_pb_ump (make_pb_cone pb p₁ p₂ γ))
    : pred_mor (pr1 D) p₂ f p₁
    := pr2 (pr12 D pb x y z f g p₁ p₂ γ Hf pb_sqr).

  Definition pb_ob_of_pred_ob
             {x y z : B}
             (f : x --> z)
             (g : y --> z)
             (Hf : pred_ob D f)
    : B
    := pr1 (pr122 D x y z f g Hf).

  Definition pb_pr1_of_pred_ob
             {x y z : B}
             (f : x --> z)
             (g : y --> z)
             (Hf : pred_ob D f)
    : pb_ob_of_pred_ob f g Hf --> x
    := pr12 (pr122 D x y z f g Hf).

  Definition pb_pr2_of_pred_ob
             {x y z : B}
             (f : x --> z)
             (g : y --> z)
             (Hf : pred_ob D f)
    : pb_ob_of_pred_ob f g Hf --> y
    := pr122 (pr122 D x y z f g Hf).

  Definition pb_cell_of_pred_ob
             {x y z : B}
             (f : x --> z)
             (g : y --> z)
             (Hf : pred_ob D f)
    : invertible_2cell
        (pb_pr1_of_pred_ob f g Hf · f)
        (pb_pr2_of_pred_ob f g Hf · g)
    := pr1 (pr222 (pr122 D x y z f g Hf)).

  Definition pb_cone_of_pred_ob
             {x y z : B}
             (f : x --> z)
             (g : y --> z)
             (Hf : pred_ob D f)
    : pb_cone f g
    := make_pb_cone
         (pb_ob_of_pred_ob f g Hf)
         (pb_pr1_of_pred_ob f g Hf)
         (pb_pr2_of_pred_ob f g Hf)
         (pb_cell_of_pred_ob f g Hf).

  Definition pb_of_pred_ob_has_pb_ump
             {x y z : B}
             (f : x --> z)
             (g : y --> z)
             (Hf : pred_ob D f)
    : has_pb_ump (pb_cone_of_pred_ob f g Hf)
    := pr2 (pr222 (pr122 D x y z f g Hf)).

  Definition pred_mor_closed_under_pb_ump_mor
    : closed_under_pb_ump_mor D
    := pr222 D.
End Projections.

Definition make_disp_map_bicat
           {B : bicat}
           (D : arrow_subbicat B)
           (closed_pb : closed_under_pb D)
           (contains_pb : contains_pb D)
           (closed_pb_mor : closed_under_pb_ump_mor D)
  : disp_map_bicat B
  := (D ,, closed_pb ,, contains_pb ,, closed_pb_mor).

Definition make_disp_map_bicat_with_pb
           (B : bicat_with_pb)
           (D : arrow_subbicat B)
           (closed_pb : closed_under_pb D)
           (closed_pb_mor : closed_under_pb_ump_mor D)
  : disp_map_bicat B.
Proof.
  refine (make_disp_map_bicat D closed_pb _ closed_pb_mor).
  intros x y z f g p.
  pose (cone := pr1 (pr2 B x y z f g)).
  pose (pb_ump := pr2 (pr2 B x y z f g)).
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact cone.
  - exact (pb_cone_pr1 cone).
  - exact (pb_cone_pr2 cone).
  - exact (pb_cone_cell cone).
  - exact pb_ump.
Defined.

(**
 4. Examples of display map bicategories
 *)
Definition full_disp_map_bicat
           {B : bicat_with_pb}
           (P₀ : ∏ (x y : B), x --> y → UU)
           (closed_pb : ∏ (pb x y z : B)
                          (f : x --> z)
                          (g : y --> z)
                          (p₁ : pb --> x)
                          (p₂ : pb --> y)
                          (γ : invertible_2cell (p₁ · f) (p₂ · g)),
                        P₀ x z f
                        →
                        has_pb_ump (make_pb_cone pb p₁ p₂ γ)
                        →
                        P₀ pb y p₂)
  : disp_map_bicat B.
Proof.
  use make_disp_map_bicat_with_pb.
  - exact (full_arrow_subbicat P₀).
  - exact (λ pb x y z f g p₁ p₂ γ H₁ H₂,
           closed_pb pb x y z f g p₁ p₂ γ H₁ H₂
           ,,
           tt).
  - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, tt).
Defined.

Definition intersection_disp_map_bicat
           {B : bicat}
           (D₁ D₂ : disp_map_bicat B)
  : disp_map_bicat B.
Proof.
  use make_disp_map_bicat.
  - exact (intersection_arrow_subbicat D₁ D₂).
  - intros ? ? ? ? ? ? ? ? ? Hf pb_sqr.
    split ; split.
    + exact (pb_preserves_pred_ob D₁ (pr1 Hf) pb_sqr).
    + exact (pb_preserves_pred_ob D₂ (pr2 Hf) pb_sqr).
    + exact (mor_of_pb_preserves_pred_ob D₁ (pr1 Hf) pb_sqr).
    + exact (mor_of_pb_preserves_pred_ob D₂ (pr2 Hf) pb_sqr).
  - intros x y z f g H.
    exact (pr122 D₁ _ _ _ _ _ (pr1 H)).
  - intros ? ? ? ? ? ? ? ? ? pb_sqr ? ? ? ? ? ? ? Hf Hp₁ Hcp₁.
    split.
    + exact (pred_mor_closed_under_pb_ump_mor
               D₁
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               (pr1 Hf) (pr1 Hp₁) (pr1 Hcp₁)).
    + exact (pred_mor_closed_under_pb_ump_mor
               D₂
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               (pr2 Hf) (pr2 Hp₁) (pr2 Hcp₁)).
Defined.

Definition faithful_disp_map_bicat
           (B : bicat_with_pb)
  : disp_map_bicat B.
Proof.
  use full_disp_map_bicat.
  - exact (λ _ _ f, faithful_1cell f).
  - intros pb x y z f g p₁ p₂ γ Hf Hpb.
    exact (pb_of_faithful_1cell Hpb Hf).
Defined.

Definition fully_faithful_disp_map_bicat
           (B : bicat_with_pb)
  : disp_map_bicat B.
Proof.
  use full_disp_map_bicat.
  - exact (λ _ _ f, fully_faithful_1cell f).
  - intros pb x y z f g p₁ p₂ γ Hf Hpb.
    exact (pb_of_fully_faithful_1cell Hpb Hf).
Defined.

Definition conservative_disp_map_bicat
           (B : bicat_with_pb)
  : disp_map_bicat B.
Proof.
  use full_disp_map_bicat.
  - exact (λ _ _ f, conservative_1cell f).
  - intros pb x y z f g p₁ p₂ γ Hf Hpb.
    exact (pb_of_conservative_1cell Hpb Hf).
Defined.

Definition discrete_disp_map_bicat
           (B : bicat_with_pb)
  : disp_map_bicat B.
Proof.
  use full_disp_map_bicat.
  - exact (λ _ _ f, discrete_1cell f).
  - intros pb x y z f g p₁ p₂ γ Hf Hpb.
    exact (pb_of_discrete_1cell Hpb Hf).
Defined.

Definition sfib_disp_map_bicat
           (B : bicat_with_pb)
  : disp_map_bicat B.
Proof.
  use make_disp_map_bicat_with_pb.
  - exact (sfib_subbicat B).
  - intros pb x y z f g p₁ p₂ γ q Hpb.
    split.
    + exact (pb_of_sfib Hpb q).
    + exact (mor_preserves_cartesian_pb_pr1 Hpb q).
  - intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? H₁ H₂ H₃.
    apply mor_preserves_cartesian_pb_ump_mor.
    exact H₃.
Defined.

Definition sopfib_disp_map_bicat
           (B : bicat_with_pb)
  : disp_map_bicat B.
Proof.
  use make_disp_map_bicat_with_pb.
  - exact (sopfib_subbicat B).
  - intros pb x y z f g p₁ p₂ γ q Hpb.
    split.
    + exact (pb_of_sopfib Hpb q).
    + exact (mor_preserves_opcartesian_pb_pr1 Hpb q).
  - intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? H₁ H₂ H₃.
    apply mor_preserves_opcartesian_pb_ump_mor.
    exact H₃.
Defined.

Definition discrete_sfib_disp_map_bicat
           (B : bicat_with_pb)
  : disp_map_bicat B
  := intersection_disp_map_bicat
       (sfib_disp_map_bicat B)
       (discrete_disp_map_bicat B).

Definition discrete_sfib_disp_map_bicat_in_discrete
           (B : bicat_with_pb)
  : contained_in_discrete (discrete_sfib_disp_map_bicat B).
Proof.
  intros x y f Hf.
  exact (pr2 Hf).
Defined.

Definition discrete_sopfib_disp_map_bicat
           (B : bicat_with_pb)
  : disp_map_bicat B
  := intersection_disp_map_bicat
       (sopfib_disp_map_bicat B)
       (discrete_disp_map_bicat B).

Definition discrete_sopfib_disp_map_bicat_in_discrete
           (B : bicat_with_pb)
  : contained_in_discrete (discrete_sopfib_disp_map_bicat B).
Proof.
  intros x y f Hf.
  exact (pr2 Hf).
Defined.

(**
 5. Properties of display map bicategories
 *)
Definition is_covariant_disp_map_bicat
           {B : bicat}
           (D : disp_map_bicat B)
  : UU
  := contained_in_sopfib D
     ×
     pred_mor_is_mor_preserves_opcartesian D.

Definition is_contravariant_disp_map_bicat
           {B : bicat}
           (D : disp_map_bicat B)
  : UU
  := contained_in_sfib D
     ×
     pred_mor_is_mor_preserves_cartesian D.

Definition intersection_is_covariant
           {B : bicat}
           {D₁ D₂ : disp_map_bicat B}
           (HD₁ : is_covariant_disp_map_bicat D₁)
           (HD₂ : is_covariant_disp_map_bicat D₂)
  : is_covariant_disp_map_bicat (intersection_disp_map_bicat D₁ D₂).
Proof.
  split.
  - intros x y f Hf.
    apply HD₁.
    apply Hf.
  - intros e₁ e₂ b₁ b₂ p₁ p₂ fe.
    split.
    + intro H.
      apply HD₁.
      apply H.
    + intro H.
      split.
      * apply HD₁.
        apply H.
      * apply HD₂.
        apply H.
Defined.

Definition intersection_with_full_is_covariant
           {B : bicat_with_pb}
           (P₀ : ∏ (x y : B), x --> y → UU)
           (closed_pb : ∏ (pb x y z : B)
                          (f : x --> z)
                          (g : y --> z)
                          (p₁ : pb --> x)
                          (p₂ : pb --> y)
                          (γ : invertible_2cell (p₁ · f) (p₂ · g)),
                        P₀ x z f
                        →
                        has_pb_ump (make_pb_cone pb p₁ p₂ γ)
                        →
                        P₀ pb y p₂)
           {D : disp_map_bicat B}
           (HD : is_covariant_disp_map_bicat D)
  : is_covariant_disp_map_bicat
      (intersection_disp_map_bicat
         D
         (full_disp_map_bicat P₀ closed_pb)).
Proof.
  split.
  - intros x y f Hf.
    apply HD.
    apply Hf.
  - intros e₁ e₂ b₁ b₂ p₁ p₂ fe.
    split.
    + intro H.
      apply HD.
      apply H.
    + intro H.
      split.
      * apply HD.
        apply H.
      * exact tt.
Defined.

Definition intersection_is_contravariant
           {B : bicat}
           {D₁ D₂ : disp_map_bicat B}
           (HD₁ : is_contravariant_disp_map_bicat D₁)
           (HD₂ : is_contravariant_disp_map_bicat D₂)
  : is_contravariant_disp_map_bicat (intersection_disp_map_bicat D₁ D₂).
Proof.
  split.
  - intros x y f Hf.
    apply HD₁.
    apply Hf.
  - intros e₁ e₂ b₁ b₂ p₁ p₂ fe.
    split.
    + intro H.
      apply HD₁.
      apply H.
    + intro H.
      split.
      * apply HD₁.
        apply H.
      * apply HD₂.
        apply H.
Defined.

Definition intersection_with_full_is_contravariant
           {B : bicat_with_pb}
           (P₀ : ∏ (x y : B), x --> y → UU)
           (closed_pb : ∏ (pb x y z : B)
                          (f : x --> z)
                          (g : y --> z)
                          (p₁ : pb --> x)
                          (p₂ : pb --> y)
                          (γ : invertible_2cell (p₁ · f) (p₂ · g)),
                        P₀ x z f
                        →
                        has_pb_ump (make_pb_cone pb p₁ p₂ γ)
                        →
                        P₀ pb y p₂)
           {D : disp_map_bicat B}
           (HD : is_contravariant_disp_map_bicat D)
  : is_contravariant_disp_map_bicat
      (intersection_disp_map_bicat
         D
         (full_disp_map_bicat P₀ closed_pb)).
Proof.
  split.
  - intros x y f Hf.
    apply HD.
    apply Hf.
  - intros e₁ e₂ b₁ b₂ p₁ p₂ fe.
    split.
    + intro H.
      apply HD.
      apply H.
    + intro H.
      split.
      * apply HD.
        apply H.
      * exact tt.
Defined.

Definition sopfib_disp_map_bicat_is_covariant
           (B : bicat_with_pb)
  : is_covariant_disp_map_bicat (sopfib_disp_map_bicat B).
Proof.
  split.
  - intros ? ? ? H.
    exact H.
  - intros ? ? ? ? ? ? ?.
    split.
    + exact (λ H, H).
    + exact (λ H, H).
Defined.

Definition sfib_disp_map_bicat_is_contravariant
           (B : bicat_with_pb)
  : is_contravariant_disp_map_bicat (sfib_disp_map_bicat B).
Proof.
  split.
  - intros ? ? ? H.
    exact H.
  - intros ? ? ? ? ? ? ?.
    split.
    + exact (λ H, H).
    + exact (λ H, H).
Defined.

Definition discrete_sopfib_disp_map_bicat_is_covariant
           (B : bicat_with_pb)
  : is_covariant_disp_map_bicat (discrete_sopfib_disp_map_bicat B).
Proof.
  use intersection_with_full_is_covariant.
  split.
  - intros ? ? ? H.
    exact H.
  - intros ? ? ? ? ? ? ?.
    split.
    + exact (λ H, H).
    + exact (λ H, H).
Defined.

Definition discrete_sfib_disp_map_bicat_is_covariant
           (B : bicat_with_pb)
  : is_contravariant_disp_map_bicat (discrete_sfib_disp_map_bicat B).
Proof.
  use intersection_with_full_is_contravariant.
  split.
  - intros ? ? ? H.
    exact H.
  - intros ? ? ? ? ? ? ?.
    split.
    + exact (λ H, H).
    + exact (λ H, H).
Defined.
