Require Import UniMath.Foundations.Basics.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.category_hset
        UniMath.CategoryTheory.slicecat
        UniMath.CategoryTheory.opp_precat
        UniMath.CategoryTheory.equivalences
        UniMath.Ktheory.ElementsOp.

(* Proof that pshf (el P) ≃ (pshf C) / P *)
Section elems_slice_equiv.

  Local Open Scope cat.

  Local Open Scope set.

  Local Definition el {C : Precategory} (P : C^op ==> SET) : Precategory := @cat C P.
  Local Definition pshf (C : Precategory) : Precategory := [C^op, SET].
  Local Definition slice (C : Precategory) (X : C) : Precategory :=
    ((slice_precat C X (pr2 C)) ,, (has_homsets_slice_precat C (pr2 C) X)).

  Variable (C : Precategory).
  Variable (P : pshf C).

  Definition pshf_to_slice_ob_funct_fun (F : pshf (el P)) : C^op → SET :=
    fun X => total2_hSet (fun (p : pr1 ((pr1 P) X)) => ((pr1 F) (X ,, p))).

  Definition pshf_to_slice_ob_funct_mor (F : pshf (el P)) (X Y : C^op) (f : X --> Y) :
    pshf_to_slice_ob_funct_fun F X --> pshf_to_slice_ob_funct_fun F Y :=
    fun p => # (pr1 P) f (pr1 p) ,, pr2 (pr1 F) (X ,, (pr1 p)) (Y,, # (pr1 P) f (pr1 p)) (f ,, idpath (# (pr1 P) f (pr1 p))) (pr2 p).

  Definition pshf_to_slice_ob_funct_data (F : pshf (el P)) : functor_data C^op SET :=
    (pshf_to_slice_ob_funct_fun F) ,, (pshf_to_slice_ob_funct_mor F).

  Definition pshf_to_slice_ob_is_funct (F : pshf (el P)) : is_functor (pshf_to_slice_ob_funct_data F).
  Proof.
    destruct F as [[ F Fmor ] [ Fid Fcomp ]].
    split.
    + intro a. simpl.
      unfold pshf_to_slice_ob_funct_mor.
      unfold pshf_to_slice_ob_funct_fun.
      simpl.
      apply funextsec. intro p. Check (Fid (a ,, pr1 p)).
      assert (H : pr1 p = # (pr1 P) (identity a) (pr1 p)).
    - apply (transportb (fun f => pr1 p = f (pr1 p)) ((pr1 (pr2 P)) a) (idpath _)).
    - unfold functor_on_morphisms. unfold functor_on_morphisms in H.
      unfold identity. simpl.
      rewrite tppr. (* rewrite <- H.
      Set Printing All. simpl.
      unfold identity. simpl.
      rewrite tppr.
      apply (total2_paths2 (transportb (fun f => f (pr1 p) = pr1 p) ((pr1 (pr2 P)) a) (idpath _))).
      unfold identity. simpl. rewrite ((pr1 (pr2 P)) a).

              ((pr1 (pr2 P)) a)
       *)
  Admitted.

  Definition presheaf_to_slice_ob : pshf (el P) → slice (pshf C) P.
  Proof.
    simpl.
    intro F.
    unfold slicecat_ob. simpl.
  Admitted.

  (* make/find helper functions to extract various pieces of stuff I want *)

  Definition slice_to_presheaf_ob_ob (Q : slice (pshf C) P) : el P → SET :=
    fun p =>
      hfiber ((pr1 (pr2 Q)) (pr1 p)) (pr2 p) ,,
             isaset_hfiber ((pr1 (pr2 Q)) (pr1 p)) (pr2 p) (pr2 (((pr1 (pr1 Q)) (pr1 p)))) (pr2 ((pr1 P) (pr1 p))).

  Definition slice_to_presheaf_ob_mor (Q : slice (pshf C) P) (F G : el P) (f : F --> G) :
    slice_to_presheaf_ob_ob Q F --> slice_to_presheaf_ob_ob Q G.
    unfold slice_to_presheaf_ob_ob. unfold hfiber. simpl.
    intros Q F G f s. (*
    exists ((pr2 (pr1 (pr1 Q))) _ _ (pr1 f) (pr1 s)).
    rewrite <- (pr2 f).
    Check (pr2 s). Check (pr2 Q). *)
  Admitted.

  Definition slice_to_presheaf_ob : slice (pshf C) P → pshf (el P).
  Proof.
    simpl. unfold slicecat_ob. simpl.
    intro Q. unfold "==>".
  Admitted.


End elems_slice_equiv.