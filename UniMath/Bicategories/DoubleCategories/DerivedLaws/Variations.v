(********************************************************************************

 Variations of the double category laws

 We provide several variations of the usual laws of double categories. These
 are minor reformulations of the usual laws of double categories. We also provide
 laws governing the map from paths to globular iso squares.

 Content
 1. Variations of the double category laws
 2. Laws involving identities and globular iso squares

 ********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.DerivedLaws.TransportLaws.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.

Local Open Scope cat.
Local Open Scope double_cat.

(** * 1. Variations of the double category laws *)
Proposition square_id_left_v'
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : transportf_square (id_left _) (id_left _) (id_v_square h₁ ⋆v s)
    =
    s.
Proof.
  rewrite square_id_left_v.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition square_id_right_v'
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : transportf_square (id_right _) (id_right _) (s ⋆v id_v_square h₂)
    =
      s.
Proof.
  rewrite square_id_right_v.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition square_assoc_v'
            {C : double_cat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ : w₁ -->v x₁} {v₁' : x₁ -->v y₁} {v₁'' : y₁ -->v z₁}
            {v₂ : w₂ -->v x₂} {v₂' : x₂ -->v y₂} {v₂'' : y₂ -->v z₂}
            {h₁ : w₁ -->h w₂}
            {h₂ : x₁ -->h x₂}
            {h₃ : y₁ -->h y₂}
            {h₄ : z₁ -->h z₂}
            (s₁ : square v₁ v₂ h₁ h₂)
            (s₂ : square v₁' v₂' h₂ h₃)
            (s₃ : square v₁'' v₂'' h₃ h₄)
  : transportf_square (assoc _ _ _) (assoc _ _ _) (s₁ ⋆v (s₂ ⋆v s₃))
    =
    ((s₁ ⋆v s₂) ⋆v s₃).
Proof.
  rewrite square_assoc_v.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition lunitor_linvunitor_h'
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : transportf_square (id_v_left _) (id_v_left _) (lunitor_h f ⋆v linvunitor_h f)
    =
    id_v_square _.
Proof.
  rewrite lunitor_linvunitor_h.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition linvunitor_lunitor_h'
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : transportf_square (id_v_left _) (id_v_left _) (linvunitor_h f ⋆v lunitor_h f)
    =
    id_v_square _.
Proof.
  rewrite linvunitor_lunitor_h.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition lunitor_square'
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : x₂ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : transportf_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      ((id_h_square _ ⋆h s) ⋆v lunitor_h h₂)
    =
    lunitor_h h₁ ⋆v s.
Proof.
  rewrite lunitor_square.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition runitor_rinvunitor_h'
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : transportf_square (id_v_left _) (id_v_left _) (runitor_h f ⋆v rinvunitor_h f)
    =
    id_v_square _.
Proof.
  rewrite runitor_rinvunitor_h.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition rinvunitor_runitor_h'
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : transportf_square (id_v_left _) (id_v_left _) (rinvunitor_h f ⋆v runitor_h f)
    =
    id_v_square _.
Proof.
  rewrite rinvunitor_runitor_h.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition runitor_square'
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : x₂ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : transportf_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      ((s ⋆h id_h_square _) ⋆v runitor_h h₂)
    =
    runitor_h h₁ ⋆v s.
Proof.
  rewrite runitor_square.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition lassociator_rassociator_h'
            {C : double_cat}
            {w x y z : C}
            (f : w -->h x)
            (g : x -->h y)
            (h : y -->h z)
  : transportf_square (id_v_left _) (id_v_left _) (lassociator_h f g h ⋆v rassociator_h f g h)
    =
    id_v_square _.
Proof.
  rewrite lassociator_rassociator_h.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition rassociator_lassociator_h'
            {C : double_cat}
            {w x y z : C}
            (f : w -->h x)
            (g : x -->h y)
            (h : y -->h z)
  : transportf_square (id_v_left _) (id_v_left _) (rassociator_h f g h ⋆v lassociator_h f g h)
    =
    id_v_square _.
Proof.
  rewrite rassociator_lassociator_h.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition linvunitor_square
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : x₂ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : linvunitor_h h₁ ⋆v  (id_h_square _ ⋆h s)
    =
    transportf_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      (s ⋆v linvunitor_h h₂).
Proof.
  refine (!(square_id_right_v' _) @ _).
  rewrite <- lunitor_linvunitor_h'.
  rewrite transportf_square_postwhisker.
  rewrite transportf_f_square.
  etrans.
  {
    apply maponpaths.
    apply square_assoc_v.
  }
  unfold transportb_square.
  rewrite transportf_f_square.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    refine (!_).
    apply square_assoc_v'.
  }
  rewrite transportf_square_prewhisker.
  rewrite transportf_f_square.
  rewrite lunitor_square.
  unfold transportb_square.
  rewrite transportf_square_postwhisker.
  rewrite transportf_square_prewhisker.
  rewrite transportf_f_square.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply square_assoc_v.
  }
  unfold transportb_square.
  rewrite transportf_square_prewhisker.
  rewrite transportf_f_square.
  rewrite linvunitor_lunitor_h.
  unfold transportb_square.
  rewrite !transportf_square_prewhisker.
  rewrite transportf_f_square.
  rewrite square_id_left_v.
  unfold transportb_square.
  rewrite transportf_square_prewhisker.
  rewrite transportf_f_square.
  use transportf_square_eq.
  apply idpath.
Qed.

Proposition linvunitor_square'
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : x₂ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : transportb_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      (linvunitor_h h₁ ⋆v  (id_h_square _ ⋆h s))
    =
    s ⋆v linvunitor_h h₂.
Proof.
  rewrite linvunitor_square.
  rewrite transportbf_square.
  apply idpath.
Qed.

Proposition rinvunitor_square
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : x₂ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : rinvunitor_h h₁ ⋆v  (s ⋆h id_h_square _)
    =
    transportf_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      (s ⋆v rinvunitor_h h₂).
Proof.
  refine (!(square_id_right_v' _) @ _).
  rewrite <- runitor_rinvunitor_h'.
  rewrite transportf_square_postwhisker.
  rewrite transportf_f_square.
  etrans.
  {
    apply maponpaths.
    apply square_assoc_v.
  }
  unfold transportb_square.
  rewrite transportf_f_square.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    refine (!_).
    apply square_assoc_v'.
  }
  rewrite transportf_square_prewhisker.
  rewrite transportf_f_square.
  rewrite runitor_square.
  unfold transportb_square.
  rewrite transportf_square_postwhisker.
  rewrite transportf_square_prewhisker.
  rewrite transportf_f_square.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply square_assoc_v.
  }
  unfold transportb_square.
  rewrite transportf_square_prewhisker.
  rewrite transportf_f_square.
  rewrite rinvunitor_runitor_h.
  unfold transportb_square.
  rewrite !transportf_square_prewhisker.
  rewrite transportf_f_square.
  rewrite square_id_left_v.
  unfold transportb_square.
  rewrite transportf_square_prewhisker.
  rewrite transportf_f_square.
  use transportf_square_eq.
  apply idpath.
Qed.

Proposition rinvunitor_square'
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : x₂ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : transportb_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      (rinvunitor_h h₁ ⋆v  (s ⋆h id_h_square _))
    =
    s ⋆v rinvunitor_h h₂.
Proof.
  rewrite rinvunitor_square.
  rewrite transportbf_square.
  apply idpath.
Qed.

Proposition rassociator_square
            {C : double_cat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {vw : w₁ -->v w₂} {vx : x₁ -->v x₂}
            {vy : y₁ -->v y₂} {vz : z₁ -->v z₂}
            {h₁ : w₁ -->h x₁} {h₂ : w₂ -->h x₂}
            {j₁ : x₁ -->h y₁} {j₂ : x₂ -->h y₂}
            {k₁ : y₁ -->h z₁} {k₂ : y₂ -->h z₂}
            (s₁ : square vw vx h₁ h₂)
            (s₂ : square vx vy j₁ j₂)
            (s₃ : square vy vz k₁ k₂)
  : rassociator_h h₁ j₁ k₁ ⋆v (s₁ ⋆h (s₂ ⋆h s₃))
    =
    transportf_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      (((s₁ ⋆h s₂) ⋆h s₃) ⋆v rassociator_h h₂ j₂ k₂).
Proof.
  refine (!(square_id_right_v' _) @ _ @ square_id_right_v' _).
  apply maponpaths.
  rewrite <- !lassociator_rassociator_h'.
  rewrite !transportf_square_postwhisker.
  apply maponpaths.
  refine (square_assoc_v _ _ _ @ _ @ !(square_assoc_v _ _ _)).
  apply maponpaths.
  apply maponpaths_2.
  rewrite transportf_square_prewhisker.
  refine (!(square_assoc_v' _ _ _) @ _).
  rewrite <- square_assoc_v'.
  rewrite transportf_f_square.
  rewrite lassociator_square.
  unfold transportb_square.
  rewrite transportf_square_postwhisker.
  rewrite transportf_f_square.
  etrans.
  {
    apply maponpaths.
    apply square_assoc_v.
  }
  unfold transportb_square.
  rewrite transportf_f_square.
  rewrite !rassociator_lassociator_h.
  unfold transportb_square.
  rewrite transportf_square_prewhisker.
  rewrite transportf_square_postwhisker.
  rewrite !transportf_f_square.
  rewrite square_id_left_v.
  rewrite square_id_right_v.
  unfold transportb_square.
  rewrite !transportf_f_square.
  use transportf_square_eq.
  apply idpath.
Qed.

Proposition rassociator_square'
            {C : double_cat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {vw : w₁ -->v w₂} {vx : x₁ -->v x₂}
            {vy : y₁ -->v y₂} {vz : z₁ -->v z₂}
            {h₁ : w₁ -->h x₁} {h₂ : w₂ -->h x₂}
            {j₁ : x₁ -->h y₁} {j₂ : x₂ -->h y₂}
            {k₁ : y₁ -->h z₁} {k₂ : y₂ -->h z₂}
            (s₁ : square vw vx h₁ h₂)
            (s₂ : square vx vy j₁ j₂)
            (s₃ : square vy vz k₁ k₂)
  : transportb_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      (rassociator_h h₁ j₁ k₁ ⋆v (s₁ ⋆h (s₂ ⋆h s₃)))
    =
    ((s₁ ⋆h s₂) ⋆h s₃) ⋆v rassociator_h h₂ j₂ k₂.
Proof.
  rewrite rassociator_square.
  rewrite transportbf_square.
  apply idpath.
Qed.

(** * 2. Laws involving identities and globular iso squares *)
Proposition path_to_globular_iso_square_id
            {C : univalent_double_cat}
            {x y : C}
            {h : x -->h y}
  : id_v_square h
    =
    path_to_globular_iso_square (idpath h).
Proof.
  apply idpath.
Qed.

Proposition path_to_globular_iso_square_inv
            {C : univalent_double_cat}
            {x y : C}
            {h₁ h₂ : x -->h y}
            (p : h₁ = h₂)
  : globular_iso_square_inv (path_to_globular_iso_square p)
    =
    path_to_globular_iso_square (!p).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition path_to_globular_iso_square_comp
            {C : univalent_double_cat}
            {x y : C}
            {h₁ h₂ h₃ : x -->h y}
            (p : h₁ = h₂)
            (q : h₂ = h₃)
  : transportf_square
      (id_v_left _)
      (id_v_left _)
      (path_to_globular_iso_square p ⋆v path_to_globular_iso_square q)
    =
    path_to_globular_iso_square (p @ q).
Proof.
  induction p, q.
  rewrite <- !path_to_globular_iso_square_id.
  rewrite square_id_left_v.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition path_to_globular_iso_to_path
            {C : univalent_double_cat}
            {x y : C}
            {h₁ h₂ : x -->h y}
            (p : h₁ = h₂)
  : globular_iso_square_to_path (path_to_globular_iso_square p) = p.
Proof.
  exact (idtoisotoid_twosided_disp
           (is_univalent_twosided_disp_cat_hor_mor C)
           (idpath _) (idpath _)
           p).
Qed.

Proposition globular_iso_to_path_to_iso
            {C : univalent_double_cat}
            {x y : C}
            {h₁ h₂ : x -->h y}
            (p : globular_iso_square h₁ h₂)
  : path_to_globular_iso_square (globular_iso_square_to_path p) = p.
Proof.
  exact (isotoidtoiso_twosided_disp
           (is_univalent_twosided_disp_cat_hor_mor C)
           (idpath _) (idpath _)
           p).
Qed.

Definition path_weq_globular_iso_square
           {C : univalent_double_cat}
           {x y : C}
           (h₁ h₂ : x -->h y)
  : h₁ = h₂ ≃ globular_iso_square h₁ h₂.
Proof.
  use weq_iso.
  - apply path_to_globular_iso_square.
  - apply globular_iso_square_to_path.
  - apply path_to_globular_iso_to_path.
  - apply globular_iso_to_path_to_iso.
Defined.
