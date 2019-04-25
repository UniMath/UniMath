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
  use mk_prebicat_data.
  - exact (one_cells_data_from_monoidal ,, two_cells_from_monoidal).
  - split. { intros ? ? f. exact (id f). }
    split. { intros ? ? f. apply l. }
    split. { intros ? ? f. apply ρ. }
    split. { intros ? ? f. apply (nat_iso_inv l). }
    split. { intros ? ? f. apply (nat_iso_inv ρ). }
    split. { intros ? ? ? ? f g h. apply (pr1 α ((f , g) , h)). }
    split. { intros ? ? ? ? f g h. apply (pr1 (nat_iso_inv α) ((f , g) , h)). }
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
    exact (pr21 (nat_iso_inv α) _ _ ((id f #, id g) #, x)).
    exact (maponpaths (fun z => _ · (z #⊗ _)) (functor_id tensor (f , g))).
  }

  (* 9. Associator and right/left whiskering *)
  split. {
    intros ? ? ? ? f g h i x.
    etrans.
    exact (pr21 (nat_iso_inv α) _ _ ((id f #, x) #, id i)).
    apply idpath.
  }

  (* 10. Associator and right/right whiskering *)
  split. {
    intros ? ? ? ? f g h i x.
    etrans.
    exact (!(pr21 (nat_iso_inv α) _ _ ((x #, id h) #, id i))).
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
  split. { intros ? ? f. exact (iso_inv_after_iso (pr1 l f,, pr2 l f)). }
  split. { intros ? ? f. exact (iso_after_iso_inv (pr1 l f,, pr2 l f)). }

  (* 13. Right unitor invertible. *)
  split. { intros ? ? f. exact (iso_inv_after_iso (pr1 ρ f,, pr2 ρ f)). }
  split. { intros ? ? f. exact (iso_after_iso_inv (pr1 ρ f,, pr2 ρ f)). }

  (* 14. Associator invertible. *)
  split. { intros ? ? ? ? f g h. exact (iso_after_iso_inv ( pr1 α ((f, g), h) ,, pr2 α ((f, g), h) )). }
  split. { intros ? ? ? ? f g h. exact (iso_inv_after_iso ( pr1 α ((f, g), h) ,, pr2 α ((f, g), h) )). }

  (* 15. Right unitor whiskering. *)
  split. {
    intros ? ? ? f g.
    etrans. exact (maponpaths (fun z => _ · z) (triangle_equality _ _)).
    etrans. exact (assoc _ _ _).
    etrans. exact (maponpaths (fun z => z · _) (iso_after_iso_inv ( pr1 α ((f, I), g) ,, pr2 α ((f, I), g) ))).
    exact (id_left _).
  }

  (* 16. Pentagon equation *)
  (* The pentagon equation is backwards on the definition of bicategory and in the definition of
  monoidal category, we need to rewrite the equation in order to apply it. *)
  intros ? ? ? ? ? f g h i.
  cbn.
  apply (pre_comp_with_iso_is_inj _ _ _ _ (pr1 α ((f, g), h ⊗ i)) (pr2 α _) _ _).
  apply (pre_comp_with_iso_is_inj _ _ _ _ (pr1 α (((f ⊗ g), h) , i)) (pr2 α _) _ _).
  apply pathsinv0.
  etrans. exact (maponpaths (fun z => _ · z) (assoc _ _ _)).
  etrans. exact (maponpaths (fun z => _ · (z · _)) (iso_inv_after_iso (pr1 α ((f, g), _) ,, pr2 α _ ))).
  etrans. exact (maponpaths (fun z => _ · z) (id_left _)).
  etrans. exact (iso_inv_after_iso (pr1 α ((f ⊗ g, h), _) ,, pr2 α _ )).
  apply pathsinv0.
  etrans. exact (assoc _ _ _).
  etrans. exact (assoc _ _ _).
  etrans. exact (maponpaths (fun z => (z · _) · _) (pentagon_equation _ _ _ _)).
  etrans. exact (maponpaths (fun z => (z · _)) (!(assoc _ _ _))).
  etrans. exact (maponpaths (fun z => (_ · z · _)) (assoc _ _ _)).
  etrans. exact (maponpaths (fun z => (_ · (z · _) · _)) (!(functor_comp tensor _ _))). cbn.
  etrans. exact (maponpaths (fun z => (_ · ((z #⊗ _) · _) · _)) (id_left _)).
  etrans. exact (maponpaths (fun z => (_ · ((_ #⊗ z) · _) · _)) (iso_inv_after_iso (pr1 α ((g, h), i) ,, pr2 α _))).
  assert (aux: # tensor (id (f, (assoc_left (pr12 M)) ((g, h), i))) = id (f ⊗ (assoc_left (pr12 M)) ((g, h), i))) by
  exact (functor_id tensor ( f , (assoc_left (pr12 M)) ((g, h), i))).
  etrans. exact (maponpaths (fun z => (_ · (z · _) · _)) aux).
  etrans. exact (maponpaths (fun z => (_ · z · _)) (id_left _)).
  etrans. exact (maponpaths (fun z => (z · _)) (!(assoc _ _ _))).
  etrans. exact (maponpaths (fun z => (_ · z · _)) (iso_inv_after_iso (pr1 α ((f,g ⊗ h),i) ,, pr2 α _))).
  etrans. exact (maponpaths (fun z => (z · _)) (id_right _)).
  etrans. exact (!(functor_comp tensor _ _)).
  etrans. exact (maponpaths (fun z => (_ #⊗ z)) (id_right _)).
  etrans. exact (maponpaths (fun z => (z #⊗ _)) (iso_inv_after_iso (pr1 α ((f,g),h) ,, pr2 α _))).
  apply (functor_id tensor).
Defined.

Definition prebicat_from_monoidal : prebicat :=
  prebicat_data_from_monoidal ,, prebicat_laws_from_monoidal.

End Prebicat_From_Monoidal_Precat.

Section Monoidal_Precat_From_Prebicat.

Local Open Scope bicategory_scope.
Local Notation "x • y" := (vcomp2 x y) (at level 60).
Local Notation "x ⋆ y" := (hcomp x y) (at level 50, left associativity).
Local Notation "f ◃ x" := (lwhisker f x) (at level 60). (* \tw *)
Local Notation "y ▹ g" := (rwhisker g y) (at level 60). (* \tw nr 2 *)

Context {C : prebicat}.
Variable (c0: ob C).

Definition precategory_from_prebicat_and_ob: precategory.
Proof.
  use mk_precategory.
  + use precategory_data_pair.
    * use precategory_ob_mor_pair.
      -- exact (C⟦c0,c0⟧).
      -- apply prebicat_cells.
    * intro c.
      apply id2.
    * intros a b c.
      apply vcomp2.
  + use mk_is_precategory.
    * intros a b f.
      apply id2_left.
    * intros a b f.
      apply id2_right.
    * intros a b c d f g h.
      apply vassocr.
    * intros a b c d f g h.
      apply pathsinv0.
      apply vassocr.
Defined.

Local Notation EndC := precategory_from_prebicat_and_ob.

Definition tensor_from_prebicat_and_ob: precategory_from_prebicat_and_ob ⊠ precategory_from_prebicat_and_ob ⟶ precategory_from_prebicat_and_ob.
Proof.
  use mk_functor.
  - use mk_functor_data.
    + intro ab.
      induction ab as [a b].
      exact (a · b).
    + intros ab1 ab2 f.
      induction ab1 as [a1 b1].
      induction ab2 as [a2 b2].
      induction f as [f1 f2].
      cbn in f1, f2.
      exact (hcomp f1 f2).
  - split.
    + red.
      intro a.
      cbn.
      apply hcomp_identity.
    + red.
      intros a b c f g.
      cbn.
      apply hcomp_vcomp.
Defined.

Local Notation tensor := tensor_from_prebicat_and_ob.

Local Definition build_left_unitor: left_unitor tensor (id c0).
Proof.
  red.
  use mk_nat_iso.
  + use mk_nat_trans.
    * intro c.
      apply lunitor.
    * intros a b f.
      cbn.
      apply lunitor_natural.
  + red.
    intro c.
    cbn.
    apply is_iso_lunitor.
Defined.

Local Definition build_right_unitor: right_unitor tensor (id c0).
Proof.
  red.
  use mk_nat_iso.
  + use mk_nat_trans.
    * intro c.
      apply runitor.
    * intros a b f.
      cbn.
      apply runitor_natural.
  + red.
    intro c.
    cbn.
    apply is_iso_runitor.
Defined.

Local Definition build_associator: associator tensor.
Proof.
  use mk_nat_iso.
  + use mk_nat_trans.
    * intro c.
      apply (rassociator_fun (pr11 c,, (pr21 c,, pr2 c))).
    * intros a b f. unfold rassociator_fun.
      set (rassociator_fun_natural_inst := rassociator_fun_natural (pr11 a,, (pr21 a,, pr2 a)) (pr11 b,, (pr21 b,, pr2 b)) (pr11 f,, (pr21 f,, pr2 f))).
      unfold rassociator_fun in rassociator_fun_natural_inst.
      (* cbn in rassociator_fun_natural_inst. *) (* if not given, then [exact] takes very long *)
      exact rassociator_fun_natural_inst.
  + intro c.
    apply is_iso_rassociator.
Defined.

Definition monoidal_precat_from_prebicat_and_ob: monoidal_precat.
Proof.
  use (mk_monoidal_precat precategory_from_prebicat_and_ob tensor_from_prebicat_and_ob (id c0)).
  - exact build_left_unitor.
  - exact build_right_unitor.
  - exact build_associator.
  - red. intros a b. unfold rassociator_fun.
    cbn.
    apply pathsinv0.
    apply unit_triangle.
(* a historic proof without rewriting:
    unfold hcomp.
    intermediate_path ((runitor a ▹ b) • id2 (a · b)).
    apply maponpaths.
    apply lwhisker_id2.
    intermediate_path (rassociator a (id c0) b • (id2 (a · (id c0 · b)) • (a ◃ lunitor b))).
    2: { apply maponpaths.
         apply (maponpaths ( λ x, vcomp2 x _)).
         apply pathsinv0.
         apply id2_rwhisker. }
    eapply pathscomp0.
    { apply id2_right. }
    eapply pathscomp0.
    { apply pathsinv0. apply lunitor_lwhisker. }
    apply maponpaths.
    apply pathsinv0.
    apply id2_left.
*)
  - red. intros a b c d. unfold rassociator_fun.
    cbn.
    apply pathsinv0.
    apply associativity_pentagon.
(* a historic proof without rewriting:
    unfold hcomp.
    eapply pathscomp0.
    { apply pathsinv0. apply rassociator_rassociator. }
    intermediate_path (((rassociator a b c ▹ d) • rassociator a (b · c) d) • ((id2 a ▹ b · c · d) • (a ◃ rassociator b c d))).
    { apply maponpaths.
      eapply pathscomp0.
      { apply pathsinv0. apply id2_left. }
      apply (maponpaths ( λ x, vcomp2 x _)).
      apply pathsinv0.
      apply id2_rwhisker.
    }
    apply (maponpaths ( λ x, vcomp2 x _)).
    apply (maponpaths ( λ x, vcomp2 x _)).
    rewrite lwhisker_id2.
    intermediate_path ((rassociator a b c ▹ d) • id2 (a · (b · c) · d)).
    { apply pathsinv0.
      apply id2_right. }
    apply idpath.
*)
Defined.

End Monoidal_Precat_From_Prebicat.
