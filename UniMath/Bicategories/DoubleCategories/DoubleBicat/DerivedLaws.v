(*****************************************************************************************

 Derived laws in Verity double bicategories

 This file collects laws that hold in Verity double bicategories. Some of these laws are
 reformulations of the standard laws of a Verity double bicategory. For example, the laws
 about the associators and unitors can be expressed in multiple ways depending on where
 the whiskering operations are put. Depending on the situation, some laws might be easier
 to use than others.

 Verity double bicategories have two laws that might seem peculiar: they express that
 vertical and horizontal composition preserve vertical and horizontal cylinder
 respectively. The reason why these laws might seem peculiar, is that they have a side
 condition. This also makes them more complicated to use, because every time that we want
 to rewrite using those laws, we need to prove two side conditions.

 However, we can equivalently express these two laws of Verity double category via 4 laws
 that do not have any side conditions. For the preservation of vertical cylinders, we use
 [lr_lwhisker_v_comp_square] and [lr_rwhisker_v_comp_square], while for the preservation of
 horizontal cylinders, we use [lr_uwhisker_h_comp_square] and [lr_dwhisker_h_comp_square].
 We also give versions of these laws using whiskering. These laws express how vertical and
 horizontal composition of squares interact with the whiskering operations of Verity double
 bicategories.

 We also give a composition for corners. This is needed to construct the composition of
 companion pairs.

 Contents
 1. Laws regarding the left unitor and composition
 2. Laws regarding the right unitor and composition
 3. Laws regarding the associator
 4. Laws regarding whiskering 2-cells
 5. Equality laws for whiskering
 6. Operations on globular squares
 7. Composing corners

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.

Local Open Scope cat.
Local Open Scope double_bicat.

(** * 1. Laws regarding the left unitor and composition *)
Proposition lunitor_v_comp_square'
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : id_v_square_bicat h₁ ⋆v s
    =
    linvunitor v₂ ▹s (lunitor v₁ ◃s s).
Proof.
  rewrite lunitor_v_comp_square.
  rewrite <- rwhisker_square_comp.
  rewrite lunitor_linvunitor.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition lunitor_v_comp_square''
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : lunitor v₂ ▹s (linvunitor v₁ ◃s id_v_square_bicat h₁ ⋆v s)
    =
    s.
Proof.
  rewrite lunitor_v_comp_square'.
  rewrite !rwhisker_lwhisker_square.
  rewrite <- lwhisker_square_comp.
  rewrite <- rwhisker_square_comp.
  rewrite !linvunitor_lunitor.
  rewrite lwhisker_square_id.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition lunitor_h_comp_square'
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : id_h_square_bicat v₁ ⋆h s
    =
    linvunitor h₂ ▿s (lunitor h₁ ▵s s).
Proof.
  rewrite <- lunitor_h_comp_square.
  rewrite <- dwhisker_square_comp.
  rewrite lunitor_linvunitor.
  rewrite dwhisker_square_id.
  apply idpath.
Qed.

(** * 2. Laws regarding the right unitor and composition *)
Proposition runitor_v_comp_square'
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : s ⋆v id_v_square_bicat h₂
    =
    rinvunitor v₂ ▹s (runitor v₁ ◃s s).
Proof.
  rewrite runitor_v_comp_square.
  rewrite <- rwhisker_square_comp.
  rewrite runitor_rinvunitor.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition runitor_v_comp_square''
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : runitor v₂ ▹s (rinvunitor v₁ ◃s s ⋆v id_v_square_bicat h₂)
    =
    s.
Proof.
  rewrite runitor_v_comp_square'.
  rewrite !rwhisker_lwhisker_square.
  rewrite <- lwhisker_square_comp.
  rewrite <- rwhisker_square_comp.
  rewrite !rinvunitor_runitor.
  rewrite lwhisker_square_id.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition runitor_h_comp_square'
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : s ⋆h id_h_square_bicat v₂
    =
    rinvunitor h₂ ▿s (runitor h₁ ▵s s).
Proof.
  rewrite <- runitor_h_comp_square.
  rewrite <- dwhisker_square_comp.
  rewrite runitor_rinvunitor.
  rewrite dwhisker_square_id.
  apply idpath.
Qed.

Proposition runitor_h_comp_square''
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            (s : square_double_bicat h₁ h₂ v₁ v₂)
  : runitor h₂ ▿s (rinvunitor h₁ ▵s s ⋆h id_h_square_bicat v₂)
    =
    s.
Proof.
  rewrite runitor_h_comp_square'.
  rewrite !dwhisker_uwhisker_square.
  rewrite <- uwhisker_square_comp.
  rewrite <- dwhisker_square_comp.
  rewrite !rinvunitor_runitor.
  rewrite dwhisker_square_id.
  rewrite uwhisker_square_id.
  apply idpath.
Qed.

(** * 3. Laws regarding the associator *)
Proposition lassociator_h_comp_square'
            {B : verity_double_bicat}
            {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : B}
            {h₁ : x₁ --> x₂} {h₂ : x₂ --> x₃} {h₃ : x₃ --> x₄}
            {k₁ : y₁ --> y₂} {k₂ : y₂ --> y₃} {k₃ : y₃ --> y₄}
            {v₁ : x₁ -|-> y₁} {v₂ : x₂ -|-> y₂}
            {v₃ : x₃ -|-> y₃} {v₄ : x₄ -|-> y₄}
            (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
            (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
            (s₃ : square_double_bicat h₃ k₃ v₃ v₄)
  : s₁ ⋆h (s₂ ⋆h s₃)
    =
    rassociator k₁ k₂ k₃ ▿s (lassociator h₁ h₂ h₃ ▵s s₁ ⋆h s₂ ⋆h s₃).
Proof.
  rewrite <- lassociator_h_comp_square.
  rewrite <- dwhisker_square_comp.
  rewrite lassociator_rassociator.
  rewrite dwhisker_square_id.
  apply idpath.
Qed.

Proposition lassociator_h_comp_square''
            {B : verity_double_bicat}
            {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : B}
            {h₁ : x₁ --> x₂} {h₂ : x₂ --> x₃} {h₃ : x₃ --> x₄}
            {k₁ : y₁ --> y₂} {k₂ : y₂ --> y₃} {k₃ : y₃ --> y₄}
            {v₁ : x₁ -|-> y₁} {v₂ : x₂ -|-> y₂}
            {v₃ : x₃ -|-> y₃} {v₄ : x₄ -|-> y₄}
            (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
            (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
            (s₃ : square_double_bicat h₃ k₃ v₃ v₄)
  : s₁ ⋆h s₂ ⋆h s₃
    =
    lassociator k₁ k₂ k₃ ▿s (rassociator h₁ h₂ h₃ ▵s s₁ ⋆h (s₂ ⋆h s₃)).
Proof.
  rewrite dwhisker_uwhisker_square.
  rewrite lassociator_h_comp_square.
  rewrite <- uwhisker_square_comp.
  rewrite rassociator_lassociator.
  rewrite uwhisker_square_id.
  apply idpath.
Qed.

Proposition lassociator_v_comp_square'
            {B : verity_double_bicat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : B}
            {hw : w₁ --> w₂} {hx : x₁ --> x₂}
            {hy : y₁ --> y₂} {hz : z₁ --> z₂}
            {u₁ : w₁ -|-> x₁} {u₂ : x₁ -|-> y₁} {u₃ : y₁ -|-> z₁}
            {v₁ : w₂ -|-> x₂} {v₂ : x₂ -|-> y₂} {v₃ : y₂ -|-> z₂}
            (s₁ : square_double_bicat hw hx u₁ v₁)
            (s₂ : square_double_bicat hx hy u₂ v₂)
            (s₃ : square_double_bicat hy hz u₃ v₃)
  : s₁ ⋆v s₂ ⋆v s₃
    =
    rassociator u₁ u₂ u₃ ◃s (lassociator v₁ v₂ v₃ ▹s s₁ ⋆v (s₂ ⋆v s₃)).
Proof.
  rewrite <- lassociator_v_comp_square.
  rewrite <- lwhisker_square_comp.
  rewrite rassociator_lassociator.
  rewrite lwhisker_square_id.
  apply idpath.
Qed.

Proposition lassociator_v_comp_square''
            {B : verity_double_bicat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : B}
            {hw : w₁ --> w₂} {hx : x₁ --> x₂}
            {hy : y₁ --> y₂} {hz : z₁ --> z₂}
            {u₁ : w₁ -|-> x₁} {u₂ : x₁ -|-> y₁} {u₃ : y₁ -|-> z₁}
            {v₁ : w₂ -|-> x₂} {v₂ : x₂ -|-> y₂} {v₃ : y₂ -|-> z₂}
            (s₁ : square_double_bicat hw hx u₁ v₁)
            (s₂ : square_double_bicat hx hy u₂ v₂)
            (s₃ : square_double_bicat hy hz u₃ v₃)
  : s₁ ⋆v (s₂ ⋆v s₃)
    =
    lassociator u₁ u₂ u₃ ◃s (rassociator v₁ v₂ v₃ ▹s s₁ ⋆v s₂ ⋆v s₃).
Proof.
  rewrite <- rwhisker_lwhisker_square.
  rewrite lassociator_v_comp_square.
  rewrite <- rwhisker_square_comp.
  rewrite lassociator_rassociator.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

(** * 4. Laws regarding whiskering 2-cells *)
Proposition l_lwhisker_v_comp_square
            {B : verity_double_bicat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : B}
            {h₁ : x₁ --> x₂}
            {h₂ : y₁ --> y₂}
            {h₃ : z₁ --> z₂}
            {v₁ v₁' : x₁ -|-> y₁}
            {v₂ : y₁ -|-> z₁}
            {w₁ : x₂ -|-> y₂}
            {w₂ : y₂ -|-> z₂}
            (τ : v₁' =|=> v₁)
            (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
            (s₂ : square_double_bicat h₂ h₃ v₂ w₂)
  : (τ ◃s s₁) ⋆v s₂ = (τ ▹ v₂) ◃s s₁ ⋆v s₂.
Proof.
  rewrite rwhisker_hcomp.
  refine (!_).
  etrans.
  {
    use (ver_bicat_hcomp_v_comp_square B τ (id2 v₂) (id2 _) (id2 _) (τ ◃s s₁)).
    - exact s₂.
    - rewrite rwhisker_square_id.
      apply idpath.
    - rewrite lwhisker_square_id, rwhisker_square_id.
      apply idpath.
  }
  rewrite hcomp_identity.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition r_lwhisker_v_comp_square
            {B : verity_double_bicat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : B}
            {h₁ : x₁ --> x₂}
            {h₂ : y₁ --> y₂}
            {h₃ : z₁ --> z₂}
            {v₁ : x₁ -|-> y₁}
            {v₂ v₂' : y₁ -|-> z₁}
            {w₁ : x₂ -|-> y₂}
            {w₂ : y₂ -|-> z₂}
            (τ : v₂' =|=> v₂)
            (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
            (s₂ : square_double_bicat h₂ h₃ v₂ w₂)
  : s₁ ⋆v (τ ◃s s₂) = (v₁ ◃ τ) ◃s s₁ ⋆v s₂.
Proof.
  rewrite lwhisker_hcomp.
  refine (!_).
  etrans.
  {
    use (ver_bicat_hcomp_v_comp_square B (id2 v₁) τ (id2 _) (id2 _) s₁).
    - exact (τ ◃s s₂).
    - rewrite lwhisker_square_id, rwhisker_square_id.
      apply idpath.
    - rewrite rwhisker_square_id.
      apply idpath.
  }
  rewrite hcomp_identity.
  rewrite rwhisker_square_id.
  apply idpath.
Qed.

Proposition lr_lwhisker_v_comp_square
            {B : verity_double_bicat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : B}
            {h₁ : x₁ --> x₂}
            {h₂ : y₁ --> y₂}
            {h₃ : z₁ --> z₂}
            {v₁ v₁' : x₁ -|-> y₁}
            {v₂ v₂' : y₁ -|-> z₁}
            {w₁ w₁' : x₂ -|-> y₂}
            {w₂ w₂' : y₂ -|-> z₂}
            (τ₁ : v₁' =|=> v₁)
            (τ₂ : v₂' =|=> v₂)
            (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
            (s₂ : square_double_bicat h₂ h₃ v₂ w₂)
  : (τ₁ ◃s s₁) ⋆v (τ₂ ◃s s₂) = (τ₂ ⋆⋆ τ₁) ◃s s₁ ⋆v s₂.
Proof.
  rewrite l_lwhisker_v_comp_square.
  rewrite r_lwhisker_v_comp_square.
  rewrite <- lwhisker_square_comp.
  apply idpath.
Qed.

Proposition l_rwhisker_v_comp_square
            {B : verity_double_bicat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : B}
            {h₁ : x₁ --> x₂}
            {h₂ : y₁ --> y₂}
            {h₃ : z₁ --> z₂}
            {v₁ : x₁ -|-> y₁}
            {v₂ : y₁ -|-> z₁}
            {w₁ w₁' : x₂ -|-> y₂}
            {w₂ : y₂ -|-> z₂}
            (τ : w₁ =|=> w₁')
            (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
            (s₂ : square_double_bicat h₂ h₃ v₂ w₂)
  : (τ ▹s s₁) ⋆v s₂ = (τ ▹ w₂) ▹s s₁ ⋆v s₂.
Proof.
  rewrite rwhisker_hcomp.
  refine (!_).
  etrans.
  {
    refine (!_).
    use (ver_bicat_hcomp_v_comp_square B (id2 v₁) (id2 v₂) τ (id2 w₂)).
    - exact (τ ▹s s₁).
    - exact s₂.
    - rewrite lwhisker_square_id.
      apply idpath.
    - rewrite lwhisker_square_id, rwhisker_square_id.
      apply idpath.
  }
  rewrite hcomp_identity.
  rewrite lwhisker_square_id.
  apply idpath.
Qed.

Proposition r_rwhisker_v_comp_square
            {B : verity_double_bicat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : B}
            {h₁ : x₁ --> x₂}
            {h₂ : y₁ --> y₂}
            {h₃ : z₁ --> z₂}
            {v₁ : x₁ -|-> y₁}
            {v₂ : y₁ -|-> z₁}
            {w₁ : x₂ -|-> y₂}
            {w₂ w₂' : y₂ -|-> z₂}
            (τ : w₂ =|=> w₂')
            (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
            (s₂ : square_double_bicat h₂ h₃ v₂ w₂)
  : s₁ ⋆v (τ ▹s s₂)= (w₁ ◃ τ) ▹s s₁ ⋆v s₂.
Proof.
  rewrite lwhisker_hcomp.
  refine (!_).
  etrans.
  {
    refine (!_).
    use (ver_bicat_hcomp_v_comp_square B (id2 v₁) (id2 v₂) (id2 w₁) τ).
    - exact s₁.
    - exact (τ ▹s s₂).
    - rewrite lwhisker_square_id, rwhisker_square_id.
      apply idpath.
    - rewrite lwhisker_square_id.
      apply idpath.
  }
  rewrite hcomp_identity.
  rewrite lwhisker_square_id.
  apply idpath.
Qed.

Proposition lr_rwhisker_v_comp_square
            {B : verity_double_bicat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : B}
            {h₁ : x₁ --> x₂}
            {h₂ : y₁ --> y₂}
            {h₃ : z₁ --> z₂}
            {v₁ : x₁ -|-> y₁}
            {v₂ : y₁ -|-> z₁}
            {w₁ w₁' : x₂ -|-> y₂}
            {w₂ w₂' : y₂ -|-> z₂}
            (τ₁ : w₁ =|=> w₁')
            (τ₂ : w₂ =|=> w₂')
            (s₁ : square_double_bicat h₁ h₂ v₁ w₁)
            (s₂ : square_double_bicat h₂ h₃ v₂ w₂)
  : (τ₁ ▹s s₁) ⋆v (τ₂ ▹s s₂)= (τ₂ ⋆⋆ τ₁) ▹s s₁ ⋆v s₂.
Proof.
  rewrite r_rwhisker_v_comp_square.
  rewrite l_rwhisker_v_comp_square.
  rewrite <- rwhisker_square_comp.
  apply idpath.
Qed.

Proposition l_uwhisker_h_comp_square
            {B : verity_double_bicat}
            {x₁ x₂ x₃ y₁ y₂ y₃ : B}
            {h₁ h₁' : x₁ --> x₂}
            {h₂ : x₂ --> x₃}
            {k₁ : y₁ --> y₂}
            {k₂ : y₂ --> y₃}
            {v₁ : x₁ -|-> y₁}
            {v₂ : x₂ -|-> y₂}
            {v₃ : x₃ -|-> y₃}
            (τ : h₁' ==> h₁)
            (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
            (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
  : (τ ▵s s₁) ⋆h s₂ = (τ ▹ h₂) ▵s (s₁ ⋆h s₂).
Proof.
  rewrite rwhisker_hcomp.
  refine (!_).
  etrans.
  {
    refine (!_).
    use (hor_bicat_hcomp_h_comp_square B τ (id2 _) (id2 _) (id2 _) (τ ▵s s₁)).
    - exact s₂.
    - rewrite dwhisker_square_id.
      apply idpath.
    - rewrite dwhisker_square_id, uwhisker_square_id.
      apply idpath.
  }
  rewrite hcomp_identity.
  rewrite dwhisker_square_id.
  apply idpath.
Qed.

Proposition r_uwhisker_h_comp_square
            {B : verity_double_bicat}
            {x₁ x₂ x₃ y₁ y₂ y₃ : B}
            {h₁ : x₁ --> x₂}
            {h₂ h₂' : x₂ --> x₃}
            {k₁ : y₁ --> y₂}
            {k₂ : y₂ --> y₃}
            {v₁ : x₁ -|-> y₁}
            {v₂ : x₂ -|-> y₂}
            {v₃ : x₃ -|-> y₃}
            (τ : h₂' ==> h₂)
            (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
            (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
  : s₁ ⋆h (τ ▵s s₂) = (h₁ ◃ τ) ▵s (s₁ ⋆h s₂).
Proof.
  rewrite lwhisker_hcomp.
  refine (!_).
  etrans.
  {
    refine (!_).
    use (hor_bicat_hcomp_h_comp_square B (id2 _) τ (id2 _) (id2 _) s₁).
    - exact (τ ▵s s₂).
    - rewrite dwhisker_square_id, uwhisker_square_id.
      apply idpath.
    - rewrite dwhisker_square_id.
      apply idpath.
  }
  rewrite hcomp_identity.
  rewrite dwhisker_square_id.
  apply idpath.
Qed.

Proposition lr_uwhisker_h_comp_square
            {B : verity_double_bicat}
            {x₁ x₂ x₃ y₁ y₂ y₃ : B}
            {h₁ h₁' : x₁ --> x₂}
            {h₂ h₂' : x₂ --> x₃}
            {k₁ : y₁ --> y₂}
            {k₂ : y₂ --> y₃}
            {v₁ : x₁ -|-> y₁}
            {v₂ : x₂ -|-> y₂}
            {v₃ : x₃ -|-> y₃}
            (τ₁ : h₁' ==> h₁)
            (τ₂ : h₂' ==> h₂)
            (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
            (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
  : (τ₁ ▵s s₁) ⋆h (τ₂ ▵s s₂) = (τ₂ ⋆⋆ τ₁) ▵s (s₁ ⋆h s₂).
Proof.
  rewrite l_uwhisker_h_comp_square.
  rewrite r_uwhisker_h_comp_square.
  rewrite <- uwhisker_square_comp.
  apply idpath.
Qed.

Proposition l_dwhisker_h_comp_square
            {B : verity_double_bicat}
            {x₁ x₂ x₃ y₁ y₂ y₃ : B}
            {h₁ : x₁ --> x₂}
            {h₂ : x₂ --> x₃}
            {k₁ k₁' : y₁ --> y₂}
            {k₂ : y₂ --> y₃}
            {v₁ : x₁ -|-> y₁}
            {v₂ : x₂ -|-> y₂}
            {v₃ : x₃ -|-> y₃}
            (τ : k₁ ==> k₁')
            (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
            (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
  : (τ ▿s s₁) ⋆h s₂ = (τ ▹ k₂) ▿s (s₁ ⋆h s₂).
Proof.
  rewrite rwhisker_hcomp.
  refine (!_).
  etrans.
  {
    use (hor_bicat_hcomp_h_comp_square B (id2 _) (id2 _) τ (id2 _)).
    - exact (τ ▿s s₁).
    - exact s₂.
    - rewrite uwhisker_square_id.
      apply idpath.
    - rewrite dwhisker_square_id, uwhisker_square_id.
      apply idpath.
  }
  rewrite hcomp_identity.
  rewrite uwhisker_square_id.
  apply idpath.
Qed.

Proposition r_dwhisker_h_comp_square
            {B : verity_double_bicat}
            {x₁ x₂ x₃ y₁ y₂ y₃ : B}
            {h₁ : x₁ --> x₂}
            {h₂ : x₂ --> x₃}
            {k₁ : y₁ --> y₂}
            {k₂ k₂' : y₂ --> y₃}
            {v₁ : x₁ -|-> y₁}
            {v₂ : x₂ -|-> y₂}
            {v₃ : x₃ -|-> y₃}
            (τ : k₂ ==> k₂')
            (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
            (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
  : s₁ ⋆h (τ ▿s s₂) = (k₁ ◃ τ) ▿s (s₁ ⋆h s₂).
Proof.
  rewrite lwhisker_hcomp.
  refine (!_).
  etrans.
  {
    use (hor_bicat_hcomp_h_comp_square B (id2 _) (id2 _) (id2 _) τ).
    - exact s₁.
    - exact (τ ▿s s₂).
    - rewrite dwhisker_square_id, uwhisker_square_id.
      apply idpath.
    - rewrite uwhisker_square_id.
      apply idpath.
  }
  rewrite hcomp_identity.
  rewrite uwhisker_square_id.
  apply idpath.
Qed.

Proposition lr_dwhisker_h_comp_square
            {B : verity_double_bicat}
            {x₁ x₂ x₃ y₁ y₂ y₃ : B}
            {h₁ : x₁ --> x₂}
            {h₂ : x₂ --> x₃}
            {k₁ k₁' : y₁ --> y₂}
            {k₂ k₂' : y₂ --> y₃}
            {v₁ : x₁ -|-> y₁}
            {v₂ : x₂ -|-> y₂}
            {v₃ : x₃ -|-> y₃}
            (τ₁ : k₁ ==> k₁')
            (τ₂ : k₂ ==> k₂')
            (s₁ : square_double_bicat h₁ k₁ v₁ v₂)
            (s₂ : square_double_bicat h₂ k₂ v₂ v₃)
  : (τ₁ ▿s s₁) ⋆h (τ₂ ▿s s₂) = (τ₂ ⋆⋆ τ₁) ▿s (s₁ ⋆h s₂).
Proof.
  rewrite r_dwhisker_h_comp_square.
  rewrite l_dwhisker_h_comp_square.
  rewrite <- dwhisker_square_comp.
  apply idpath.
Qed.

(** * 5. Equality laws for whiskering *)
Proposition eq_lwhisker_square
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ v₁' : w -|-> y}
            {v₂ : x -|-> z}
            {τ τ' : v₁ =|=> v₁'}
            {s s' : square_double_bicat h₁ h₂ v₁' v₂}
            (p : τ = τ')
            (q : s = s')
  : τ ◃s s = τ' ◃s s'.
Proof.
  rewrite p, q.
  apply idpath.
Qed.

Proposition eq_rwhisker_square
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ v₂' : x -|-> z}
            {τ τ' : v₂ =|=> v₂'}
            {s s' : square_double_bicat h₁ h₂ v₁ v₂}
            (p : τ = τ')
            (q : s = s')
  : τ ▹s s = τ' ▹s s'.
Proof.
  rewrite p, q.
  apply idpath.
Qed.

Proposition eq_uwhisker_square
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ h₁' : w --> x}
            {h₂ : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            {τ τ' : h₁ ==> h₁'}
            {s s' : square_double_bicat h₁' h₂ v₁ v₂}
            (p : τ = τ')
            (q : s = s')
  : τ ▵s s = τ' ▵s s'.
Proof.
  rewrite p, q.
  apply idpath.
Qed.

Proposition eq_dwhisker_square
            {B : verity_double_bicat}
            {w x y z : B}
            {h₁ : w --> x}
            {h₂ h₂' : y --> z}
            {v₁ : w -|-> y}
            {v₂ : x -|-> z}
            {τ τ' : h₂ ==> h₂'}
            {s s' : square_double_bicat h₁ h₂ v₁ v₂}
            (p : τ = τ')
            (q : s = s')
  : τ ▿s s = τ' ▿s s'.
Proof.
  rewrite p, q.
  apply idpath.
Qed.

(** * 6. Operations on globular squares *)
Definition comp_ver_globular_square
           {B : verity_double_bicat}
           {x y : B}
           {v₁ v₂ v₃ : x -|-> y}
           (s₁ : square_double_bicat (id_h x) (id_h y) v₁ v₂)
           (s₂ : square_double_bicat (id_h x) (id_h y) v₂ v₃)
  : square_double_bicat (id_h x) (id_h y) v₁ v₃
  := linvunitor _ ▵s (lunitor _ ▿s s₁ ⋆h s₂).

Arguments comp_ver_globular_square {B x y v₁ v₂ v₃} s₁ s₂ /.

Definition comp_hor_globular_square
           {B : verity_double_bicat}
           {x y : B}
           {h₁ h₂ h₃ : x --> y}
           (s₁ : square_double_bicat h₁ h₂ (id_v x) (id_v y))
           (s₂ : square_double_bicat h₂ h₃ (id_v x) (id_v y))
  : square_double_bicat h₁ h₃ (id_v x) (id_v y)
  := linvunitor _ ◃s (lunitor _ ▹s s₁ ⋆v s₂).

Arguments comp_hor_globular_square {B x y h₁ h₂ h₃} s₁ s₂ /.

(** * 7. Composing corners *)
Definition comp_diag_dr_corner
           {B : verity_double_bicat}
           {x y z : B}
           {v₁ : x -|-> y}
           {v₂ : y -|-> z}
           {h₁ : x --> y}
           {h₂ : y --> z}
           (s₁ : square_double_bicat h₁ (id_h y) v₁ (id_v y))
           (s₂ : square_double_bicat h₂ (id_h z) v₂ (id_v z))
  : square_double_bicat (h₁ · h₂) (id_h z) (v₁ · v₂) (id_v z)
  := lunitor _ ▹s
       (lunitor _ ▿s ((s₁ ⋆h id_v_square_bicat h₂)
                      ⋆v
                      (id_h_square_bicat v₂ ⋆h s₂))).

Arguments comp_diag_dr_corner {B x y z v₁ v₂ h₁ h₂} s₁ s₂ /.

Definition comp_diag_ul_corner
           {B : verity_double_bicat}
           {x y z : B}
           {v₁ : x -|-> y}
           {v₂ : y -|-> z}
           {h₁ : x --> y}
           {h₂ : y --> z}
           (s₁ : square_double_bicat (id_h x) h₁ (id_v x) v₁)
           (s₂ : square_double_bicat (id_h y) h₂ (id_v y) v₂)
  : square_double_bicat (id_h x) (h₁ · h₂) (id_v x) (v₁ · v₂)
  := linvunitor _ ◃s
       (linvunitor _
          ▵s ((s₁ ⋆h id_h_square_bicat _)
              ⋆v
              (id_v_square_bicat h₁ ⋆h s₂))).

Arguments comp_diag_ul_corner {B x y z v₁ v₂ h₁ h₂} s₁ s₂ /.

Proposition comp_ul_dr_corner
            {B : verity_double_bicat}
            {x y z : B}
            {v₁ : x -|-> y}
            {v₂ : y -|-> z}
            {h₁ : x --> y}
            {h₂ : y --> z}
            (s₁ : square_double_bicat h₁ (id_h y) v₁ (id_v y))
            (s₂ : square_double_bicat h₂ (id_h z) v₂ (id_v z))
            (s₃ : square_double_bicat (id_h x) h₁ (id_v x) v₁)
            (s₄ : square_double_bicat (id_h y) h₂ (id_v y) v₂)
  : linvunitor _ ◃s (runitor _ ▹s comp_diag_ul_corner s₃ s₄ ⋆v comp_diag_dr_corner s₁ s₂)
    =
    (linvunitor _ • (_ ◃ (_ ◃ linvunitor _)) • lassociator _ _ _) ◃s
      ((rassociator _ _ _ • (_ ◃ (lunitor _ • runitor _))) ▹s
         ((s₃ ⋆v s₁) ⋆v (s₄ ⋆v s₂))).
Proof.
  unfold comp_diag_ul_corner, comp_diag_dr_corner.
  rewrite r_rwhisker_v_comp_square.
  rewrite <- rwhisker_square_comp.
  rewrite !vassocl.
  rewrite lwhisker_square_comp.
  apply maponpaths.
  rewrite <- lwhisker_vcomp.
  rewrite !vassocr.
  rewrite lunitor_lwhisker.
  rewrite l_lwhisker_v_comp_square.
  rewrite rwhisker_lwhisker_square.
  rewrite <- uwhisker_vcomp_square.
  rewrite <- dwhisker_vcomp_square.
  etrans.
  {
    rewrite runitor_h_comp_square'.
    rewrite dwhisker_uwhisker_square.
    rewrite <- !uwhisker_vcomp_square.
    rewrite dwhisker_uwhisker_square.
    rewrite <- uwhisker_square_comp.
    rewrite lunitor_h_comp_square'.
    rewrite <- !dwhisker_vcomp_square.
    rewrite <- dwhisker_square_comp.
    rewrite lassociator_v_comp_square'.
    rewrite <- lwhisker_dwhisker_square.
    rewrite <- lwhisker_uwhisker_square.
    rewrite rwhisker_lwhisker_square.
    rewrite <- lwhisker_square_comp.
    rewrite <- rwhisker_dwhisker_square.
    rewrite <- rwhisker_uwhisker_square.
    rewrite <- rwhisker_square_comp.
    etrans.
    {
      do 4 apply maponpaths.
      apply maponpaths.
      apply lassociator_v_comp_square''.
    }
    rewrite r_lwhisker_v_comp_square.
    rewrite r_rwhisker_v_comp_square.
    rewrite <- lwhisker_dwhisker_square.
    rewrite <- lwhisker_uwhisker_square.
    rewrite rwhisker_lwhisker_square.
    rewrite <- lwhisker_square_comp.
    rewrite <- rwhisker_dwhisker_square.
    rewrite <- rwhisker_uwhisker_square.
    rewrite <- rwhisker_square_comp.
    rewrite <- double_bicat_interchange.
    rewrite lunitor_v_comp_square'.
    rewrite rwhisker_lwhisker_square.
    rewrite <- lwhisker_hcomp_square.
    rewrite l_lwhisker_v_comp_square.
    rewrite r_lwhisker_v_comp_square.
    rewrite <- lwhisker_dwhisker_square.
    rewrite <- lwhisker_uwhisker_square.
    rewrite rwhisker_lwhisker_square.
    rewrite <- lwhisker_square_comp.
    rewrite runitor_v_comp_square'.
    rewrite <- rwhisker_hcomp_square.
    rewrite l_rwhisker_v_comp_square.
    rewrite r_rwhisker_v_comp_square.
    rewrite <- rwhisker_dwhisker_square.
    rewrite <- rwhisker_uwhisker_square.
    rewrite <- rwhisker_square_comp.
    rewrite <- ud_whisker_vcomp_square.
    etrans.
    {
      do 4 apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply runitor_h_comp_square''.
    }
    etrans.
    {
      do 4 apply maponpaths.
      rewrite ud_whisker_vcomp_square.
      rewrite <- dwhisker_square_comp.
      rewrite runitor_rinvunitor.
      rewrite dwhisker_square_id.
      rewrite <- uwhisker_vcomp_square.
      apply maponpaths.
      rewrite lassociator_v_comp_square''.
      do 2 apply maponpaths.
      rewrite <- double_bicat_interchange.
      rewrite r_rwhisker_v_comp_square.
      rewrite <- lrwhisker_hcomp_square.
      apply maponpaths_2.
      apply maponpaths.
      rewrite r_lwhisker_v_comp_square.
      rewrite <- lwhisker_square_comp.
      rewrite runitor_lunitor_identity.
      rewrite lwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite lwhisker_id2.
      apply lwhisker_square_id.
    }
    rewrite dwhisker_uwhisker_square.
    rewrite <- uwhisker_square_comp.
    rewrite linvunitor_lunitor.
    rewrite dwhisker_square_id.
    rewrite !vassocl.
    rewrite runitor_rinvunitor.
    rewrite id2_right.
    rewrite <- lwhisker_uwhisker_square.
    rewrite rwhisker_lwhisker_square.
    rewrite <- lwhisker_square_comp.
    rewrite lwhisker_vcomp.
    rewrite lunitor_triangle.
    rewrite lunitor_lwhisker.
    rewrite runitor_lunitor_identity.
    rewrite rwhisker_vcomp.
    rewrite linvunitor_lunitor.
    rewrite id2_rwhisker.
    rewrite id2_left.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite lunitor_lwhisker.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite id2_rwhisker.
      rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    }
    apply idpath.
  }
  rewrite lwhisker_lwhisker.
  rewrite lwhisker_square_comp.
  apply maponpaths.
  rewrite <- runitor_triangle.
  rewrite !vassocr.
  rewrite lassociator_rassociator.
  rewrite id2_left.
  rewrite <- rwhisker_lwhisker_square.
  rewrite rwhisker_square_comp.
  apply maponpaths.
  etrans.
  {
    do 2 apply maponpaths.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply runitor_v_comp_square''.
    }
    rewrite rwhisker_lwhisker_square.
    rewrite <- lwhisker_hcomp_square.
    apply maponpaths.
    rewrite <- lrwhisker_hcomp_square.
    rewrite <- id_h_square_bicat_id.
    apply idpath.
  }
  pose (double_bicat_interchange
          B
          (s₃ ⋆v s₁)
          (id_h_square_bicat (id_v y))
          (id_h_square_bicat _)
          s₄)
    as p.
  rewrite runitor_h_comp_square' in p.
  rewrite lunitor_h_comp_square' in p.
  rewrite <- dwhisker_vcomp_square in p.
  rewrite dwhisker_uwhisker_square in p.
  rewrite <- uwhisker_vcomp_square in p.
  rewrite <- ud_whisker_vcomp_square in p.
  rewrite lunitor_runitor_identity in p.
  rewrite <- uwhisker_square_comp in p.
  rewrite rinvunitor_runitor in p.
  rewrite uwhisker_square_id in p.
  rewrite lassociator_v_comp_square''.
  rewrite !rwhisker_lwhisker_square.
  rewrite <- lwhisker_square_comp.
  rewrite <- rwhisker_square_comp.
  pose (maponpaths
          (λ z, rinvunitor _ ▵s (lunitor _ ▿s z))
          p)
    as p'.
  cbn -[ver_bicat_of_ver_bicat_sq_bicat] in p'.
  rewrite <- dwhisker_square_comp in p'.
  rewrite linvunitor_lunitor in p'.
  rewrite dwhisker_square_id in p'.
  rewrite <- uwhisker_square_comp in p'.
  rewrite rinvunitor_runitor in p'.
  rewrite uwhisker_square_id in p'.
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    apply maponpaths_2.
    exact (!p').
  }
  rewrite <- uwhisker_vcomp_square.
  rewrite rwhisker_uwhisker_square.
  rewrite lwhisker_uwhisker_square.
  rewrite lunitor_V_id_is_left_unit_V_id.
  apply maponpaths.
  rewrite <- ud_whisker_vcomp_square.
  rewrite <- id_h_square_bicat_comp.
  rewrite id_h_square_bicat_id.
  etrans.
  {
    do 2 apply maponpaths.
    apply maponpaths_2.
    apply maponpaths.
    apply maponpaths_2.
    apply runitor_v_comp_square'.
  }
  rewrite l_rwhisker_v_comp_square.
  rewrite l_lwhisker_v_comp_square.
  rewrite <- rwhisker_hcomp_square.
  rewrite l_rwhisker_v_comp_square.
  rewrite <- rwhisker_square_comp.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    rewrite !vassocr.
    rewrite rwhisker_rwhisker_alt.
    rewrite !vassocl.
    rewrite rwhisker_vcomp.
    rewrite rinvunitor_runitor.
    rewrite id2_rwhisker.
    apply id2_right.
  }
  rewrite <- rwhisker_lwhisker_square.
  apply maponpaths.
  etrans.
  {
    apply maponpaths_2.
    rewrite lwhisker_hcomp.
    rewrite triangle_l_inv.
    rewrite <- rwhisker_hcomp.
    apply idpath.
  }
  rewrite <- l_lwhisker_v_comp_square.
  rewrite !lwhisker_hcomp_square.
  apply maponpaths_2.
  rewrite <- lunitor_lwhisker.
  rewrite <- runitor_triangle.
  rewrite runitor_lunitor_identity.
  apply idpath.
Qed.
