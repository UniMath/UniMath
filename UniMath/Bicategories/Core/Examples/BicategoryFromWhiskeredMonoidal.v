(** adaptation to whiskered notions by Ralph Matthes 2022 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat.

Local Open Scope cat.

(* Defines a bicategory from a whiskered monoidal category. *)
Section Bicat_From_Monoidal_Cat.

Import Bicat.Notations.
Import BifunctorNotations.

Context {C: category} (M : monoidal C).

(* The type of 0-cells is unit type and the 1-cells are the objects of the monoidal category. The
 2-cells are given by the morphisms of the original monoidal category. *)
Definition one_cells_data_from_monoidal : precategory_data.
Proof.
  use tpair.
  - exact (unit ,, (λ _ _, ob C)).
  - split.
    + intros dummy. exact I_{ M }.
    + intros dummy0 dummy1 dummy2. exact (λ a b, a ⊗_{M} b).
Defined.

Definition two_cells_from_monoidal : prebicat_2cell_struct (one_cells_data_from_monoidal)
  := λ _ _ a b, C ⟦ a , b⟧.

Definition prebicat_data_from_monoidal : prebicat_data.
Proof.
  use make_prebicat_data.
  - exact (one_cells_data_from_monoidal ,, two_cells_from_monoidal).
  - split. { intros ? ? f. exact (id₁ f). }
    split. { intros ? ? f. apply monoidal_leftunitordata. }
    split. { intros ? ? f. apply monoidal_rightunitordata. }
    split. { intros ? ? f. apply monoidal_leftunitorinvdata. }
    split. { intros ? ? f. apply monoidal_rightunitorinvdata. }
    split. { intros ? ? ? ? f g h. exact ( α_{ M } f g h ). }
    split. { intros ? ? ? ? f g h. exact ( αinv_{ M } f g h ). }
    split. { intros ? ? f g h. exact compose. }
    split. { intros ? ? ? f g h. exact (λ u, (f ⊗^{ M }_{l} u)). }
             intros ? ? ? f g h. exact (λ u, (u ⊗^{ M }_{r} h)).
Defined.

Lemma prebicat_laws_from_monoidal : prebicat_laws (prebicat_data_from_monoidal).
Proof.
  (* 1. Identities. *)
  split. { intros. apply id_left. }
  split. { intros. apply id_right. }

  (* 2. Vertical right associativity. *)
  split. { intros. apply assoc. }

  (* 3. Whiskering and identities. *)
  split. { intros ? ? ? f g. apply bifunctor_leftid. }
  split. { intros ? ? ? f g. apply bifunctor_rightid. }

  (* 4. Left whiskering vertical composition. *)
  split. {
    intros ? ? ? f g h i x y.
    apply pathsinv0, bifunctor_leftcomp.
  }

  (* 5. Right whiskering vertical composition. *)
  split. {
    intros ? ? ? f g h i x y.
    apply pathsinv0, bifunctor_rightcomp.
  }

  (* 6 and 7. Vertical composition and unitors. *)
  split. { intros. apply (leftunitorlaw_nat (monoidal_leftunitorlaw M)). }
  split. { intros. apply (rightunitorlaw_nat (monoidal_rightunitorlaw M)). }

  (* 8. Associator and left/left whiskering *)
  split. {
    intros ? ? ? ? f g h i x.
    cbn.
    apply pathsinv0.
    apply (z_iso_inv_on_right _ _ _ (_,,(_,,associatorlaw_iso_law (monoidal_associatorlaw M) f g h))).
    rewrite assoc.
    apply (z_iso_inv_on_left _ _ _ _ (_,,(_,,associatorlaw_iso_law (monoidal_associatorlaw M) f g i))).
    apply (associatorlaw_natleft (monoidal_associatorlaw M)).
  }

  (* 9. Associator and right/left whiskering *)
  split. {
    intros ? ? ? ? f g h i x.
    cbn.
    apply pathsinv0.
    apply (z_iso_inv_on_right _ _ _ (_,,(_,,associatorlaw_iso_law (monoidal_associatorlaw M) f g i))).
    rewrite assoc.
    apply (z_iso_inv_on_left _ _ _ _ (_,,(_,,associatorlaw_iso_law (monoidal_associatorlaw M) f h i))).
    apply (associatorlaw_natleftright (monoidal_associatorlaw M)).
  }

  (* 10. Associator and right/right whiskering *)
  split. {
    intros ? ? ? ? f g h i x.
    cbn.
    apply (z_iso_inv_on_right _ _ _ (_,,(_,,associatorlaw_iso_law (monoidal_associatorlaw M) f h i))).
    rewrite assoc.
    apply (z_iso_inv_on_left _ _ _ _ (_,,(_,,associatorlaw_iso_law (monoidal_associatorlaw M) g h i))).
    apply (associatorlaw_natright (monoidal_associatorlaw M)).
  }

  (* 11. Vertical composition and whiskering *)
  split. {
    intros.
    cbn.
    apply bifunctor_equalwhiskers.
  }

  (* 12. Left unitor invertible. *)
  split. { intros ? ? f. exact (pr1 (leftunitorlaw_iso_law (monoidal_leftunitorlaw M) f)). }
  split. { intros ? ? f. exact (pr2 (leftunitorlaw_iso_law (monoidal_leftunitorlaw M) f)). }

  (* 13. Right unitor invertible. *)
  split. { intros ? ? f. exact (pr1 (rightunitorlaw_iso_law (monoidal_rightunitorlaw M) f)). }
  split. { intros ? ? f. exact (pr2 (rightunitorlaw_iso_law (monoidal_rightunitorlaw M) f)). }

  (* 14. Associator invertible. *)
  split. { intros ? ? ? ? f g h. exact (pr2 (associatorlaw_iso_law (monoidal_associatorlaw M) f g h)). }
  split. { intros ? ? ? ? f g h. exact (pr1 (associatorlaw_iso_law (monoidal_associatorlaw M) f g h)). }

  (* 15. Right unitor whiskering. *)
  split. {
    intros ? ? ? f g.
    apply (z_iso_inv_on_right _ _ _ (_,,(_,,associatorlaw_iso_law (monoidal_associatorlaw M) f I_{ M} g))).
    apply pathsinv0, monoidal_triangleidentity.
  }

  (* 16. Pentagon equation *)
  intros ? ? ? ? ? f g h i.
  cbn.
  (* the pentagon equation in bicategories is formulated for the left associator while it is based
     on the right associator in whiskered monoidal categories *)
  apply pentagon_identity_leftassociator.
Qed.

Definition prebicat_from_monoidal : prebicat :=
  prebicat_data_from_monoidal ,, prebicat_laws_from_monoidal.

Definition bicat_from_monoidal : bicat.
  use build_bicategory.
  - exact prebicat_data_from_monoidal.
  - exact prebicat_laws_from_monoidal.
  - red. intros. apply homset_property.
Defined.

End Bicat_From_Monoidal_Cat.
