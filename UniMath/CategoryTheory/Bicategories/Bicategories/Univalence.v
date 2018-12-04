(* ******************************************************************************* *)
(** * Univalence for bicategories
    Benedikt Ahrens, Marco Maggesi
    May 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
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