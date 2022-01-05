Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat.

Local Open Scope cat.

(* Defines a bicategory from a monoidal category. *)
Section Bicat_From_Monoidal_Cat.

Context (M : monoidal_cat).
Let pM := monoidal_cat_cat M.
Let I := monoidal_cat_unit M.
Let tensor := monoidal_cat_tensor M.
Let α := monoidal_cat_associator M.
Let l := monoidal_cat_left_unitor M.
Let ρ := monoidal_cat_right_unitor M.
Let triangle_equality := pr1 (pr222 (pr222 M)).
Let pentagon_equation := pr2 (pr222 (pr222 M)).

Notation "X ⊗ Y" := (tensor (X, Y)).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Local Notation "f '==>' g" := (prebicat_cells _ f g) (at level 60).
Local Notation "f '<==' g" := (prebicat_cells _ g f) (at level 60, only parsing).


(* The type of 0-cells is unit type and the 1-cells are the objects of the monoidal category. The
 2-cells are given by the morphisms of the original monoidal category. *)
Definition one_cells_data_from_monoidal : precategory_data.
Proof.
  red.
  use tpair.
  - exact (unit ,, (λ _ _, ob pM)).
  - cbn.
    red.
    cbn.
    split.
    + intros _. exact I.
    + intros _ _ _. exact (λ a b, tensor (a , b)).
Defined.

Definition two_cells_from_monoidal : prebicat_2cell_struct (one_cells_data_from_monoidal)
  := λ _ _ a b, pM ⟦ a , b⟧.

Definition prebicat_data_from_monoidal : prebicat_data.
Proof.
  use make_prebicat_data.
  - exact (one_cells_data_from_monoidal ,, two_cells_from_monoidal).
  - split. { intros ? ? f. exact (id f). }
    split. { intros ? ? f. apply l. }
    split. { intros ? ? f. apply ρ. }
    split. { intros ? ? f. apply (nat_z_iso_inv l). }
    split. { intros ? ? f. apply (nat_z_iso_inv ρ). }
    split. { intros ? ? ? ? f g h. apply (α ((f , g) , h)). }
    split. { intros ? ? ? ? f g h. apply ((nat_z_iso_inv α) ((f , g) , h)). }
    split. { intros ? ? f g h. exact compose. }
    split. { intros ? ? ? f g h. exact (λ u, (id f #⊗ u)). }
             intros ? ? ? f g h. exact (λ u, (u #⊗ id h)).
Defined.

Lemma prebicat_laws_from_monoidal : prebicat_laws (prebicat_data_from_monoidal).
Proof.
  (* 1. Identities. *)
  split. { intros. apply id_left. }
  split. { intros. apply id_right. }

  (* 2. Vertical right associativity. *)
  split. { intros. apply assoc. }

  (* 3. Whiskering and identities. *)
  split. { intros ? ? ? f g. exact (functor_id tensor (f , g)). }
  split. { intros ? ? ? f g. exact (functor_id tensor (f , g)). }

  (* 4. Left whiskering vertical composition. *)
  split. {
    intros ? ? ? f g h i x y.
    etrans.
    exact (!(functor_comp tensor (id f #, x) (id f #, y))).
    exact (maponpaths (fun z => z #⊗ (x · y)) (id_left _)).
  }

  (* 5. Right whiskering vertical composition. *)
  split. {
    intros ? ? ? f g h i x y.
    etrans.
    exact (!(functor_comp tensor _ _)).
    exact (maponpaths (fun z => (x · y) #⊗ z) (id_left _)).
  }

  (* 6 and 7. Vertical composition and unitors. *)
  split. { intros. exact (pr21 l _ _ _). }
  split. { intros. exact (pr21 ρ _ _ _). }

  (* 8. Associator and left/left whiskering *)
  split. {
    intros ? ? ? ? f g h i x.
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
