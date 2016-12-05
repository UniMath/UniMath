Require Import UniMath.Foundations.Basics.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.category_hset
        UniMath.CategoryTheory.slicecat
        UniMath.CategoryTheory.opp_precat
        UniMath.Ktheory.ElementsOp
        UniMath.CategoryTheory.UnicodeNotations.



(* Proof that pshf (el P) ≃ (pshf C) / P *)
Section elems_slice_equiv.

  Local Open Scope cat.
  Local Open Scope set.
  Local Open Scope type.

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
    fun p => # (pr1 P) f (pr1 p) ,,
               pr2 (pr1 F) (X ,, (pr1 p)) (Y,, # (pr1 P) f (pr1 p)) (f ,, idpath (# (pr1 P) f (pr1 p))) (pr2 p).

  Definition pshf_to_slice_ob_funct_data (F : pshf (el P)) : functor_data C^op SET :=
    (pshf_to_slice_ob_funct_fun F) ,, (pshf_to_slice_ob_funct_mor F).

  Definition pshf_to_slice_ob_is_funct (F : pshf (el P)) : is_functor (pshf_to_slice_ob_funct_data F).
  Proof.
    intros [[ F Fmor ] [ Fid Fcomp ]].
    split.
    + intro a. simpl.
      unfold pshf_to_slice_ob_funct_mor.
      unfold pshf_to_slice_ob_funct_fun.
      simpl.
      apply funextsec. intro p.
      unfold identity. simpl.
      SearchAbout tpair.

      rewrite tppr.
      apply (total2_paths2 (transportf (fun f => f (pr1 p) = pr1 p) (!(pr1 (pr2 P)) a) (idpath _))).

      SearchAbout transportf.

      (*
      rewrite transport_idfun.
      rewrite (transport_idfun ((λ f : pr1 ((pr1 P) a) → pr1 ((pr1 P) a), (f (pr1 p) = pr1 p)%type))). *)

  Admitted.

  Definition presheaf_to_slice_ob : pshf (el P) → slice (pshf C) P.
  Proof.
    simpl.
    intro F.
    unfold slicecat_ob. simpl.
  Admitted.

  (* make/find helper functions to extract various pieces of stuff I want *)
  Local Definition sl_nat {C : Precategory} {P : pshf C} (Q : slice (pshf C) P) := pr1 (pr2 Q).
  Local Definition sl_funct {C : Precategory} {P : pshf C} (Q : slice (pshf C) P) := pr1 (pr1 Q).

  Definition slice_to_presheaf_ob_ob (Q : slice (pshf C) P) : (el P)^op → SET :=
    fun p =>
      hfiber ((sl_nat Q) (pr1 p)) (pr2 p) ,,
             isaset_hfiber ((sl_nat Q) (pr1 p)) (pr2 p) (pr2 (((sl_funct Q) (pr1 p)))) (pr2 ((pr1 P) (pr1 p))).

  Definition slice_to_presheaf_ob_mor (Q : slice (pshf C) P) (F G : (el P)^op) (f : F --> G) :
    slice_to_presheaf_ob_ob Q F --> slice_to_presheaf_ob_ob Q G.
    unfold slice_to_presheaf_ob_ob. simpl.
    intros Q [x Px] [y Py] [f feq] s.
    apply (hfibersgftog (# (sl_funct Q) f) (sl_nat Q y)).
    exists (pr1 s).
    rewrite (feq).
    assert (H : funcomp (# (sl_funct Q) f) (sl_nat Q y) (pr1 s) = (sl_nat Q (pr1 (y,, Py)) ∘ # (sl_funct Q) f) (pr1 s)).
    admit.
    rewrite H.
    unfold sl_nat , sl_funct.
    set (K := (apevalat (pr1 s) ((pr2 (pr2 Q)) _ _ f))).
    simpl in K. simpl.


(*
    intros [[Q Qis] [Qnat Qisnat]] [x Px] [y Py] [f feq] s.
    apply (hfibersgftog (# Q f) (Qnat y)).
    exists (pr1 s).
    rewrite (feq).
    assert (H : funcomp (# Q f) (Qnat y) (pr1 s) = (Qnat (pr1 (y,, Py)) ∘ # Q f) (pr1 s)).
    admit.
    rewrite H.
    Check (Qisnat _ _ f).
    rewrite (apevalat (pr1 s) (Qisnat _ _ f)).
*)

  (* exists ((pr2 (pr1 (pr1 Q))) _ _ (pr1 f) (pr1 s)).
     rewrite <- (pr2 f).
     Check (pr2 s). Check (pr2 Q). *)
  Admitted.

  Definition slice_to_presheaf_ob : slice (pshf C) P → pshf (el P).
  Proof.
    simpl. unfold slicecat_ob. simpl.
    intro Q. unfold "==>". unfold functor_data. simpl.
  Admitted.


End elems_slice_equiv.