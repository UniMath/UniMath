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
    split. { intros ? ? ? ? f g h. apply (pr1 α ((f , g) , h)). }
    split. { intros ? ? ? ? f g h. apply (pr1 (nat_z_iso_inv α) ((f , g) , h)). }
    split. { intros ? ? f g h. exact compose. }
    split. { intros ? ? ? f g h. exact (λ u, (id f #⊗ u)). }
             intros ? ? ? f g h. exact (λ u, (u #⊗ id h)).
Defined.

Definition prebicat_laws_from_monoidal : prebicat_laws (prebicat_data_from_monoidal).
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
  split. { intros ? ? f. exact (z_iso_inv_after_z_iso (pr1 l f,, pr2 l f)). }
  split. { intros ? ? f. exact (z_iso_after_z_iso_inv (pr1 l f,, pr2 l f)). }

  (* 13. Right unitor invertible. *)
  split. { intros ? ? f. exact (z_iso_inv_after_z_iso (pr1 ρ f,, pr2 ρ f)). }
  split. { intros ? ? f. exact (z_iso_after_z_iso_inv (pr1 ρ f,, pr2 ρ f)). }

  (* 14. Associator invertible. *)
  split. { intros ? ? ? ? f g h. exact (z_iso_after_z_iso_inv ( pr1 α ((f, g), h) ,, pr2 α ((f, g), h) )). }
  split. { intros ? ? ? ? f g h. exact (z_iso_inv_after_z_iso ( pr1 α ((f, g), h) ,, pr2 α ((f, g), h) )). }

  (* 15. Right unitor whiskering. *)
  split. {
    intros ? ? ? f g.
    etrans. exact (maponpaths (fun z => _ · z) (triangle_equality _ _)).
    etrans. exact (assoc _ _ _).
    etrans. exact (maponpaths (fun z => z · _) (z_iso_after_z_iso_inv ( pr1 α ((f, I), g) ,, pr2 α ((f, I), g) ))).
    exact (id_left _).
  }

  (* 16. Pentagon equation *)
  (* The pentagon equation is backwards on the definition of bicategory and in the definition of
  monoidal category, we need to rewrite the equation in order to apply it. *)
  intros ? ? ? ? ? f g h i.
  cbn.
  apply (pre_comp_with_z_iso_is_inj'(f := pr1 α ((f, g), h ⊗ i)) (pr2 α _)).
  apply (pre_comp_with_z_iso_is_inj'(f := pr1 α (((f ⊗ g), h) , i)) (pr2 α _)).
  apply pathsinv0.
  etrans. exact (maponpaths (fun z => _ · z) (assoc _ _ _)).
  etrans. exact (maponpaths (fun z => _ · (z · _)) (z_iso_inv_after_z_iso (pr1 α ((f, g), _) ,, pr2 α _ ))).
  etrans. exact (maponpaths (fun z => _ · z) (id_left _)).
  etrans. exact (z_iso_inv_after_z_iso (pr1 α ((f ⊗ g, h), _) ,, pr2 α _ )).
  apply pathsinv0.
  etrans. exact (assoc _ _ _).
  etrans. exact (assoc _ _ _).
  etrans. exact (maponpaths (fun z => (z · _) · _) (pentagon_equation _ _ _ _)).
  etrans. exact (maponpaths (fun z => (z · _)) (!(assoc _ _ _))).
  etrans. exact (maponpaths (fun z => (_ · z · _)) (assoc _ _ _)).
  etrans. exact (maponpaths (fun z => (_ · (z · _) · _)) (!(functor_comp tensor _ _))). cbn.
  etrans. exact (maponpaths (fun z => (_ · ((z #⊗ _) · _) · _)) (id_left _)).
  etrans. exact (maponpaths (fun z => (_ · ((_ #⊗ z) · _) · _)) (z_iso_inv_after_z_iso (pr1 α ((g, h), i) ,, pr2 α _))).
  assert (aux: # tensor (id (f, (assoc_left (pr12 M)) ((g, h), i))) = id (f ⊗ (assoc_left (pr12 M)) ((g, h), i))) by
  exact (functor_id tensor ( f , (assoc_left (pr12 M)) ((g, h), i))).
  etrans. exact (maponpaths (fun z => (_ · (z · _) · _)) aux).
  etrans. exact (maponpaths (fun z => (_ · z · _)) (id_left _)).
  etrans. exact (maponpaths (fun z => (z · _)) (!(assoc _ _ _))).
  etrans. exact (maponpaths (fun z => (_ · z · _)) (z_iso_inv_after_z_iso (pr1 α ((f,g ⊗ h),i) ,, pr2 α _))).
  etrans. exact (maponpaths (fun z => (z · _)) (id_right _)).
  etrans. exact (!(functor_comp tensor _ _)).
  etrans. exact (maponpaths (fun z => (_ #⊗ z)) (id_right _)).
  etrans. exact (maponpaths (fun z => (z #⊗ _)) (z_iso_inv_after_z_iso (pr1 α ((f,g),h) ,, pr2 α _))).
  apply (functor_id tensor).
Defined.

Definition prebicat_from_monoidal : prebicat :=
  prebicat_data_from_monoidal ,, prebicat_laws_from_monoidal.

Definition bicat_from_monoidal (hs : has_homsets pM) : bicat.
  use build_bicategory.
  - exact prebicat_data_from_monoidal.
  - exact prebicat_laws_from_monoidal.
  - red. intros. apply hs.
Defined.

End Prebicat_From_Monoidal_Precat.

(** *** Going into the opposite direction *)
(** We fix a bicategory and an object of it and construct the monoidal category of endomorphisms.

This part written by Ralph Matthes in 2019.

*)

Section Monoidal_Precat_From_Prebicat.

Local Open Scope bicategory_scope.
Import Bicat.Notations.

Context {C : prebicat}.
Context (c0: ob C).

Definition precategory_data_from_prebicat_and_ob: precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact (C⟦c0,c0⟧).
    + apply prebicat_cells.
  - intro c; apply id2.
  - intros a b c; apply vcomp2.
Defined.

Lemma is_precategory_data_from_prebicat_and_ob: is_precategory precategory_data_from_prebicat_and_ob.
Proof.
  use make_is_precategory.
  - intros a b f; apply id2_left.
  - intros a b f; apply id2_right.
  - intros a b c d f g h; apply vassocr.
  - intros a b c d f g h; apply pathsinv0; apply vassocr.
Qed.

Definition precategory_from_prebicat_and_ob: precategory := _,, is_precategory_data_from_prebicat_and_ob.

Local Notation EndC := precategory_from_prebicat_and_ob.

Definition tensor_from_prebicat_and_ob: precategory_from_prebicat_and_ob ⊠ precategory_from_prebicat_and_ob ⟶ precategory_from_prebicat_and_ob.
Proof.
  use make_functor.
  - use make_functor_data.
    + intro ab.
      exact (pr1 ab · pr2 ab).
    + intros ab1 ab2 f.
      exact (hcomp (pr1 f) (pr2 f)).
  - abstract ( split; [ intro c; apply hcomp_identity |
                        intros a b c f g; apply hcomp_vcomp ] ).
Defined.

Local Notation tensor := tensor_from_prebicat_and_ob.

Local Definition build_left_unitor: left_unitor tensor (id c0).
Proof.
  use make_nat_z_iso.
  + use make_nat_trans.
    * intro c.
      apply lunitor.
    * abstract ( intros a b f; apply lunitor_natural ).
  + intro c; apply is_z_iso_lunitor.
Defined.

Local Definition build_right_unitor: right_unitor tensor (id c0).
Proof.
  use make_nat_z_iso.
  + use make_nat_trans.
    * intro c.
      apply runitor.
    * abstract ( intros a b f; apply runitor_natural ).
  + intro c; apply is_z_iso_runitor.
Defined.

Definition nat_trans_associator: assoc_left tensor ⟹ assoc_right tensor.
Proof.
  (* very slow with library elements:
  set (aux := rassociator_transf(C := C) c0 c0 c0 c0).
  set (aux' := pre_whisker (precategory_binproduct_unassoc _ _ _) aux).
  use mk_nat_trans.
  - intro c. exact (pr1 aux' c).
  - apply (pr2 aux').
   *)
  (* still very slow with new additions to library:
  set (aux := rassociator_transf'(C := C) c0 c0 c0 c0).
  use mk_nat_trans.
  - intro c. exact (pr1 aux c).
  - abstract ( apply (pr2 aux) ).
   *)
  (* now def. by Anders Mörtberg: *)
  exists rassociator_fun'.
  abstract (intros f g x; apply hcomp_rassoc).
Defined.

Local Definition build_associator: associator tensor.
Proof.
  use make_nat_z_iso.
  - exact nat_trans_associator.
  - intro c; apply is_z_iso_rassociator.
Defined.

Definition monoidal_precat_from_prebicat_and_ob: monoidal_precat.
Proof.
  use (mk_monoidal_precat precategory_from_prebicat_and_ob tensor_from_prebicat_and_ob (id c0) build_left_unitor build_right_unitor build_associator).
  - abstract ( intros a b; apply pathsinv0; apply unit_triangle ).
  - abstract ( intros a b c d; apply pathsinv0; apply associativity_pentagon ).
Defined.

End Monoidal_Precat_From_Prebicat.

Section AddHomsets.

Context {C : bicat}.
Context (c0: ob C).

Lemma precategory_from_prebicat_and_ob_has_homsets: has_homsets (precategory_from_prebicat_and_ob c0).
Proof.
  red. intros.
  apply (cellset_property(C:=C)).
Qed.

End AddHomsets.
