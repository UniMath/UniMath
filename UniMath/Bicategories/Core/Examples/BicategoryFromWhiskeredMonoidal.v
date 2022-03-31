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

Local Notation "f '==>' g" := (prebicat_cells _ f g) (at level 60).
Local Notation "f '<==' g" := (prebicat_cells _ g f) (at level 60, only parsing).


(* The type of 0-cells is unit type and the 1-cells are the objects of the monoidal category. The
 2-cells are given by the morphisms of the original monoidal category. *)
Definition one_cells_data_from_monoidal : precategory_data.
Proof.
  red.
  use tpair.
  - exact (unit ,, (λ _ _, ob C)).
  - cbn.
    red.
    cbn.
    split.
    + intros _. exact I_{ M }.
    + intros _ _ _. exact (λ a b, a ⊗_{M} b).
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
    split. { intros ? ? f. apply (is_z_isomorphism_mor (leftunitorlaw_iso (monoidal_leftunitorlaw M) f)). }
    split. { intros ? ? f. apply (is_z_isomorphism_mor (rightunitorlaw_iso (monoidal_rightunitorlaw M) f)). }
    split. { intros ? ? ? ? f g h. exact ( α_{ M } f g h ). }
    split. { intros ? ? ? ? f g h. apply (is_z_isomorphism_mor (associatorlaw_iso (monoidal_associatorlaw M) f g h)). }
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

TODO

    etrans.
    exact (pr21 (nat_z_iso_inv α) _ _ ((id f #, id g) #, x)).
    exact (maponpaths (fun z => _ · (z #⊗ _)) (functor_id tensor (f , g))).
  }

  (* 9. Associator and right/left whiskering *)
  split. {
    intros ? ? ? ? f g h i x.
    etrans.
    exact (pr21 (nat_z_iso_inv α) _ _ ((id f #, x) #, id i)).
    apply idpath.
  }

  (* 10. Associator and right/right whiskering *)
  split. {
    intros ? ? ? ? f g h i x.
    etrans.
    exact (!(pr21 (nat_z_iso_inv α) _ _ ((x #, id h) #, id i))).
    exact (maponpaths (fun z => (_ #⊗ z) · _) (functor_id tensor (h , i))).
  }

  (* 11. Vertical composition and whiskering *)
  split. {
    intros.
    etrans. exact (!(functor_comp tensor _ _)).
    etrans. exact (maponpaths (fun z => (_ #⊗ z)) (id_left _)).
    etrans. exact (maponpaths (fun z => (z #⊗ _)) (id_right _)).
    apply pathsinv0.
    etrans. exact (!(functor_comp tensor _ _)).
    etrans. exact (maponpaths (fun z => (z #⊗ _)) (id_left _)).
    etrans. exact (maponpaths (fun z => (_ #⊗ z)) (id_right _)).
    apply idpath.
  }

  (* 12. Left unitor invertible. *)
  split. { intros ? ? f. exact (z_iso_inv_after_z_iso (l f,, pr2 l f)). }
  split. { intros ? ? f. exact (z_iso_after_z_iso_inv (l f,, pr2 l f)). }

  (* 13. Right unitor invertible. *)
  split. { intros ? ? f. exact (z_iso_inv_after_z_iso (ρ f,, pr2 ρ f)). }
  split. { intros ? ? f. exact (z_iso_after_z_iso_inv (ρ f,, pr2 ρ f)). }

  (* 14. Associator invertible. *)
  split. { intros ? ? ? ? f g h. exact (z_iso_after_z_iso_inv (α ((f, g), h) ,, pr2 α ((f, g), h) )). }
  split. { intros ? ? ? ? f g h. exact (z_iso_inv_after_z_iso (α ((f, g), h) ,, pr2 α ((f, g), h) )). }

  (* 15. Right unitor whiskering. *)
  split. {
    intros ? ? ? f g.
    etrans. exact (maponpaths (fun z => _ · z) (triangle_equality _ _)).
    etrans. exact (assoc _ _ _).
    etrans. exact (maponpaths (fun z => z · _) (z_iso_after_z_iso_inv (α ((f, I), g) ,, pr2 α ((f, I), g) ))).
    exact (id_left _).
  }

  (* 16. Pentagon equation *)
  (* The pentagon equation is backwards on the definition of bicategory and in the definition of
  monoidal category, we need to rewrite the equation in order to apply it. *)
  intros ? ? ? ? ? f g h i.
  cbn.
  apply (pre_comp_with_z_iso_is_inj'(f := α ((f, g), h ⊗ i)) (pr2 α _)).
  apply (pre_comp_with_z_iso_is_inj'(f := α (((f ⊗ g), h) , i)) (pr2 α _)).
  apply pathsinv0.
  etrans. exact (maponpaths (fun z => _ · z) (assoc _ _ _)).
  etrans. exact (maponpaths (fun z => _ · (z · _)) (z_iso_inv_after_z_iso (α ((f, g), _) ,, pr2 α _ ))).
  etrans. exact (maponpaths (fun z => _ · z) (id_left _)).
  etrans. exact (z_iso_inv_after_z_iso (α ((f ⊗ g, h), _) ,, pr2 α _ )).
  apply pathsinv0.
  etrans. exact (assoc _ _ _).
  etrans. exact (assoc _ _ _).
  etrans. exact (maponpaths (fun z => (z · _) · _) (pentagon_equation _ _ _ _)).
  etrans. exact (maponpaths (fun z => (z · _)) (!(assoc _ _ _))).
  etrans. exact (maponpaths (fun z => (_ · z · _)) (assoc _ _ _)).
  etrans. exact (maponpaths (fun z => (_ · (z · _) · _)) (!(functor_comp tensor _ _))). cbn.
  etrans. exact (maponpaths (fun z => (_ · ((z #⊗ _) · _) · _)) (id_left _)).
  etrans. exact (maponpaths (fun z => (_ · ((_ #⊗ z) · _) · _)) (z_iso_inv_after_z_iso (α ((g, h), i) ,, pr2 α _))).
  assert (aux: # tensor (id (f, (assoc_left (pr12 M)) ((g, h), i))) = id (f ⊗ (assoc_left (pr12 M)) ((g, h), i))) by
  exact (functor_id tensor ( f , (assoc_left (pr12 M)) ((g, h), i))).
  etrans. exact (maponpaths (fun z => (_ · (z · _) · _)) aux).
  etrans. exact (maponpaths (fun z => (_ · z · _)) (id_left _)).
  etrans. exact (maponpaths (fun z => (z · _)) (!(assoc _ _ _))).
  etrans. exact (maponpaths (fun z => (_ · z · _)) (z_iso_inv_after_z_iso (α ((f,g ⊗ h),i) ,, pr2 α _))).
  etrans. exact (maponpaths (fun z => (z · _)) (id_right _)).
  etrans. exact (!(functor_comp tensor _ _)).
  etrans. exact (maponpaths (fun z => (_ #⊗ z)) (id_right _)).
  etrans. exact (maponpaths (fun z => (z #⊗ _)) (z_iso_inv_after_z_iso (α ((f,g),h) ,, pr2 α _))).
  apply (functor_id tensor).
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
