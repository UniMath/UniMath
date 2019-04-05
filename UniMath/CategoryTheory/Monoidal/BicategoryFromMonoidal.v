Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.

Local Open Scope cat.

(* Defines a prebicategory from a monoidal precategory. *)
Section Prebicat_From_Monoidal_Precat.

Context (M : monoidal_precat).
Let pM := monoidal_precat_precat M.
Let I := monoidal_precat_unit M.
Let tensor := monoidal_precat_tensor M.
Let α := monoidal_precat_associator M.
Let l := monoidal_precat_left_unitor M.
Let ρ := monoidal_precat_right_unitor M.
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
  unfold precategory_data.
  use tpair.
  apply (unit ,, (λ _ _, ob pM)).
  simpl.
  unfold precategory_id_comp.
  split.
  * intro c. apply I.
  * intros a b c. apply (λ a b, tensor (a , b)).
Defined.

Definition two_cells_from_monoidal : prebicat_2cell_struct (one_cells_data_from_monoidal)
  := λ _ _ a b, pM ⟦ a , b⟧.

Definition prebicat_data_from_monoidal : prebicat_data.
Proof.
  use mk_prebicat_data.
  - apply (one_cells_data_from_monoidal ,, two_cells_from_monoidal).
  - split. { intros a b f. apply (identity f). }
    split. { intros a b f. apply l. }
    split. { intros a b f. apply ρ. }
    split. { intros a b f. apply (nat_iso_inv l). }
    split. { intros a b f. apply (nat_iso_inv ρ). }
    split. { intros a b c d f g h. apply (pr1 α ((f , g) , h)). }
    split. { intros a b c d f g h. apply (pr1 (nat_iso_inv α) ((f , g) , h)). }
    split. { intros a b f g h. apply compose. }
    split. { intros a b c f g h. apply (λ u, (identity f #⊗ u)). }
             intros a b c f g h. apply (λ u, (u #⊗ identity h)).
Defined.

Definition prebicat_laws_from_monoidal : prebicat_laws (prebicat_data_from_monoidal).
Proof.
  (* 1. Identities. *)
  split. { intros a b f g x. apply id_left. }
  split. { intros a b f g x. apply id_right. }

  (* 2. Vertical right associativity. *)
  split. { intros a b f g h k x y z. apply assoc. }

  (* 3. Whiskering and identities. *)
  split. { intros a b c f g. apply (functor_id tensor (f , g)). }
  split. { intros a b c f g. apply (functor_id tensor (f , g)). }

  (* 4. Left whiskering vertical copmosition. *)
  split. {
    intros a b c f g h i x y. cbn.
    etrans.
    apply (!(functor_comp tensor (identity f #, x) (identity f #, y))).
    cbn.
    apply (maponpaths (fun z => z #⊗ (x · y)) (id_left _)).
  }

  (* 5. Right whiskering vertical copmosition. *)
  split. {
    intros a b c f g h i x y.
    etrans.
    apply (!(functor_comp tensor _ _)).
    apply (maponpaths (fun z => (x · y) #⊗ z) (id_left _)).
  }

  (* 6 and 7. Vertical composition and unitors. *)
  split. { intros. apply (pr21 l _ _ _). }
  split. { intros. apply (pr21 ρ _ _ _). }

  (* 8. Associator and left/left whiskering *)
  split. {
    intros a b c d f g h i x. cbn.
    etrans.
    apply (pr21 (nat_iso_inv α) _ _ ((id f #, id g) #, x)).
    apply (maponpaths (fun z => _ · (z #⊗ _)) (functor_id tensor (f , g))).
  }

  (* 9. Associator and right/left whiskering *)
  split. {
    intros a b c d f g h i x. cbn.
    etrans.
    apply (pr21 (nat_iso_inv α) _ _ ((id f #, x) #, id i)).
    apply idpath.
  }

  (* 10. Associator and right/right whiskering *)
  split. {
    intros a b c d f g h i x. cbn.
    etrans.
    apply (!(pr21 (nat_iso_inv α) _ _ ((x #, id h) #, id i))).
    apply (maponpaths (fun z => (_ #⊗ z) · _) (functor_id tensor (h , i))).
  }

  (* 11. Vertical composition and whiskering *)
  split. {
    intros a b c f g h i x y. cbn.
    etrans. apply (!(functor_comp tensor _ _)).
    etrans. apply (maponpaths (fun z => (_ #⊗ z)) (id_left _)).
    etrans. apply (maponpaths (fun z => (z #⊗ _)) (id_right _)).
    apply pathsinv0.
    etrans. apply (!(functor_comp tensor _ _)).
    etrans. apply (maponpaths (fun z => (z #⊗ _)) (id_left _)).
    etrans. apply (maponpaths (fun z => (_ #⊗ z)) (id_right _)).
    apply idpath.
  }

  (* 12. Left unitor invertible. *)
  split. { intros a b f. apply (iso_inv_after_iso (pr1 l f,, pr2 l f)). }
  split. { intros a b f. apply (iso_after_iso_inv (pr1 l f,, pr2 l f)). }

  (* 13. Right unitor invertible. *)
  split. { intros a b f. apply (iso_inv_after_iso (pr1 ρ f,, pr2 ρ f)). }
  split. { intros a b f. apply (iso_after_iso_inv (pr1 ρ f,, pr2 ρ f)). }

  (* 14. Associator invertible. *)
  split. { intros a b c d f g h. apply (iso_after_iso_inv ( pr1 α ((f, g), h) ,, pr2 α ((f, g), h) )). }
  split. { intros a b c d f g h. apply (iso_inv_after_iso ( pr1 α ((f, g), h) ,, pr2 α ((f, g), h) )). }

  (* 15. Right unitor whiskering. *)
  split. {
    intros a b c f g.
    etrans. apply (maponpaths (fun z => _ · z) (triangle_equality _ _)).
    etrans. apply (assoc _ _ _).
    etrans. apply (maponpaths (fun z => z · _) (iso_after_iso_inv ( pr1 α ((f, I), g) ,, pr2 α ((f, I), g) ))).
    apply (id_left _).
  }

  (* 16. Pentagon equation *)
  (* The pentagon equation is backwards on the definition of bicategory and in the definition of
  monoidal category, we need to rewrite the equation in order to apply it. *)
  intros a b c d e f g h i.
  cbn.
  apply (pre_comp_with_iso_is_inj _ _ _ _ (pr1 α ((f, g), h ⊗ i)) (pr2 α _) _ _).
  apply (pre_comp_with_iso_is_inj _ _ _ _ (pr1 α (((f ⊗ g), h) , i)) (pr2 α _) _ _).
  apply pathsinv0.
  etrans. apply (maponpaths (fun z => _ · z) (assoc _ _ _)).
  etrans. apply (maponpaths (fun z => _ · (z · _)) (iso_inv_after_iso (pr1 α ((f, g), _) ,, pr2 α _ ))).
  etrans. apply (maponpaths (fun z => _ · z) (id_left _)).
  etrans. apply (iso_inv_after_iso (pr1 α ((f ⊗ g, h), _) ,, pr2 α _ )).
  apply pathsinv0.
  etrans. apply (assoc _ _ _).
  etrans. apply (assoc _ _ _).
  etrans. apply (maponpaths (fun z => (z · _) · _) (pentagon_equation _ _ _ _)).
  etrans. apply (maponpaths (fun z => (z · _)) (!(assoc _ _ _))).
  etrans. apply (maponpaths (fun z => (_ · z · _)) (assoc _ _ _)).
  etrans. apply (maponpaths (fun z => (_ · (z · _) · _)) (!(functor_comp tensor _ _))). cbn.
  etrans. apply (maponpaths (fun z => (_ · ((z #⊗ _) · _) · _)) (id_left _)). cbn.
  etrans. apply (maponpaths (fun z => (_ · ((_ #⊗ z) · _) · _)) (iso_inv_after_iso (pr1 α ((g, h), i) ,, pr2 α _ ))).
  assert (# tensor (id (f, (assoc_left (pr12 M)) ((g, h), i))) = id (f ⊗ (assoc_left (pr12 M)) ((g, h), i))).
  apply (functor_id tensor ( f , (assoc_left (pr12 M)) ((g, h), i))  ).
  etrans. apply (maponpaths (fun z => (_ · (z · _) · _)) X).
  etrans. apply (maponpaths (fun z => (_ · z · _)) (id_left _)).
  etrans. apply (maponpaths (fun z => (z · _)) (!(assoc _ _ _))).
  etrans. apply (maponpaths (fun z => (_ · z · _)) (iso_inv_after_iso (pr1 α ((f,g ⊗ h),i) ,, pr2 α _))).
  etrans. apply (maponpaths (fun z => (z · _)) (id_right _)).
  etrans. apply (!(functor_comp tensor _ _)).
  etrans. apply (maponpaths (fun z => (_ #⊗ z)) (id_right _)).
  etrans. apply (maponpaths (fun z => (z #⊗ _)) (iso_inv_after_iso (pr1 α ((f,g),h) ,, pr2 α _))).
  apply (functor_id tensor).
Defined.

Definition prebicat_from_monoidal : prebicat :=
  prebicat_data_from_monoidal ,, prebicat_laws_from_monoidal.

End Prebicat_From_Monoidal_Precat.
