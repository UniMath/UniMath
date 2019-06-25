(* ******************************************************************************* *)
(** * Univalence for bicategories
    Benedikt Ahrens, Marco Maggesi
    May 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Local Open Scope bicategory_scope.
Local Open Scope cat.

Section Idtoiso.
  Context {C : bicat}.

  Definition internal_adjunction_data_identity (a : C)
    : left_adjoint_data (identity a).
  Proof.
    exists (identity a).
    exact (linvunitor (identity a),, lunitor (identity a)).
  Defined.

  Definition is_internal_adjunction_identity (a : C)
    : left_adjoint_axioms (internal_adjunction_data_identity a).
  Proof.
    split.
    - etrans.
      { apply maponpaths_2.
        etrans; [apply (!vassocr _ _ _) | ].
        etrans.
        { apply maponpaths.
          etrans; [apply lunitor_lwhisker | ].
          apply maponpaths, pathsinv0, lunitor_runitor_identity.
        }
        etrans; [apply (!vassocr _ _ _) | ].
        etrans.
        { apply maponpaths.
          etrans; [apply rwhisker_vcomp | ].
          etrans; [apply maponpaths, linvunitor_lunitor | ].
          apply id2_rwhisker.
        }
        apply id2_right.
      }
      etrans; [apply maponpaths, pathsinv0, lunitor_runitor_identity | ].
      apply linvunitor_lunitor.
    - etrans.
      { apply maponpaths_2.
        etrans; [apply (!vassocr _ _ _) | ].
        etrans.
        { apply maponpaths.
          etrans.
          { apply maponpaths.
            apply maponpaths.
            apply lunitor_runitor_identity.
          }
          apply runitor_rwhisker.
        }
        etrans; [apply (!vassocr _ _ _) | ].
        apply maponpaths.
        etrans; [ apply lwhisker_vcomp | ].
        apply maponpaths.
        apply linvunitor_lunitor.
      }
      etrans; [apply (!vassocr _ _ _) | ].
      etrans.
      { apply maponpaths.
        etrans; [apply maponpaths_2, lwhisker_id2 | ].
        apply id2_left.
      }
      etrans; [apply maponpaths, lunitor_runitor_identity | ].
      apply rinvunitor_runitor.
  Qed.

  Definition internal_adjoint_equivalence_identity (a : C)
    : adjoint_equivalence a a.
  Proof.
    exists (identity a).
    use tpair.
    - apply internal_adjunction_data_identity.
    - split; [ apply is_internal_adjunction_identity |].
      split.
      + apply is_invertible_2cell_linvunitor.
      + apply is_invertible_2cell_lunitor.
  Defined.

  Definition idtoiso_2_0 (a b : C)
    : a = b -> adjoint_equivalence a b.
  Proof.
    induction 1.
    apply internal_adjoint_equivalence_identity.
  Defined.

  Definition idtoiso_2_1 {a b : C} (f g : C⟦a,b⟧)
    : f = g -> invertible_2cell f g.
  Proof.
    induction 1. apply id2_invertible_2cell.
  Defined.
End Idtoiso.

Definition is_univalent_2_1 (C : bicat) : UU
  := ∏ (a b : C) (f g : C⟦a,b⟧), isweq (idtoiso_2_1 f g).

Definition is_univalent_2_0 (C : bicat) : UU
    := ∏ (a b : C), isweq (idtoiso_2_0 a b).

Definition is_univalent_2 (C : bicat) : UU
  := is_univalent_2_0 C × is_univalent_2_1 C.

Definition isaprop_is_univalent_2_1 (C : bicat)
  : isaprop (is_univalent_2_1 C).
Proof.
  do 4 (apply impred ; intro).
  apply isapropisweq.
Defined.

Definition isaprop_is_univalent_2_0 (C : bicat)
  : isaprop (is_univalent_2_0 C).
Proof.
  do 2 (apply impred ; intro).
  apply isapropisweq.
Defined.

Definition isaprop_is_univalent_2 (C : bicat)
  : isaprop (is_univalent_2 C).
Proof.
  apply isapropdirprod.
  apply isaprop_is_univalent_2_0.
  apply isaprop_is_univalent_2_1.
Defined.

Definition isotoid_2_1
           {C : bicat}
           (HC : is_univalent_2_1 C)
           {a b : C}
           {f g : C⟦a,b⟧}
           (α : invertible_2cell f g)
  : f = g
  := invmap (idtoiso_2_1 f g ,, HC a b f g) α.

Definition isotoid_2_0
           {C : bicat}
           (HC : is_univalent_2_0 C)
           {a b : C}
           (f : adjoint_equivalence a b)
  : a = b
  := invmap (idtoiso_2_0 a b ,, HC a b) f.


(** In a univalent bicategory 0-cells are 1-types.
For the proofs that 1-cells are 2-types see AdjointUnique.v *)
Lemma univalent_bicategory_1_cell_hlevel_3
      (C : bicat) (HC : is_univalent_2_1 C) (a b : C) :
  isofhlevel 3 (C⟦a,b⟧).
Proof.
  intros f g.
  apply (isofhlevelweqb _ (idtoiso_2_1 f g,, HC _ _ f g)).
  apply isaset_invertible_2cell.
Qed.

(** Local Univalence implies the hom cats are univalent *)
Section IsoInvertible2Cells.
  Context {C : bicat}.
  Variable (C_is_univalent_2_1 : is_univalent_2_1 C).

  Definition is_inv2cell_to_is_iso {a b : C} (f g : hom a b) (η : f ==> g)
    : is_invertible_2cell η → is_iso η.
  Proof.
    intros p h.
    use isweq_iso.
    - intro ψ.
      cbn in *.
      exact (p^-1 • ψ).
    - abstract (intro ψ;
                cbn in *;
                rewrite vassocr;
                rewrite vcomp_lid;
                apply id2_left).
    - abstract (intro ψ;
                cbn in *;
                rewrite vassocr;
                rewrite vcomp_rinv;
                apply id2_left).
  Defined.

  Definition inv2cell_to_iso {a b : C} (f g : hom a b) : invertible_2cell f g → iso f g.
  Proof.
    intro i.
    use make_iso.
    - apply i.
    - apply is_inv2cell_to_is_iso.
      apply i.
  Defined.


  Definition iso_to_inv2cell {a b : C} (f g : hom a b) : iso f g → invertible_2cell f g.
  Proof.
    intro i.
    use tpair.
    + exact (morphism_from_iso i).
    + use make_is_invertible_2cell.
      * exact (inv_from_iso i).
      * exact (iso_inv_after_iso i).
      * exact (iso_after_iso_inv i).
  Defined.

  Definition inv2cell_to_iso_isweq {a b : C} (f g : hom a b) : isweq (inv2cell_to_iso f g).
  Proof.
    use isweq_iso.
    - exact (iso_to_inv2cell f g).
    - intro i.
      apply cell_from_invertible_2cell_eq.
      apply idpath.
    - intro i.
      apply eq_iso.
      apply idpath.
  Defined.

  Definition inv2cell_to_iso_weq {a b : C} (f g : hom a b) : invertible_2cell f g ≃ iso f g.
  Proof.
    use make_weq.
    - exact (inv2cell_to_iso f g).
    - exact (inv2cell_to_iso_isweq f g).
  Defined.

  Definition idtoiso_alt_weq {a b : C} (f g : hom a b) : f = g ≃ iso f g.
  Proof.
    refine (inv2cell_to_iso_weq f g ∘ _)%weq.
    use make_weq.
    - exact (idtoiso_2_1 f g).
    - apply C_is_univalent_2_1.
  Defined.

  Definition idtoiso_weq {a b : C} (f g : hom a b) : isweq (λ p : f = g, idtoiso p).
  Proof.
    use weqhomot.
    + exact (idtoiso_alt_weq f g).
    + intro p.
      apply eq_iso.
      induction p.
      apply idpath.
  Defined.
End IsoInvertible2Cells.

Definition univ_hom
           {C : bicat}
           (C_is_univalent_2_1 : is_univalent_2_1 C)
           (X Y : C)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (hom X Y).
  - split.
    + apply idtoiso_weq.
      exact C_is_univalent_2_1.
    + exact (pr2 C X Y).
Defined.
