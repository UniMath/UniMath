(** * The univalent category of algebras over a signature. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)
(**
We use display categories to define the category of algebras and prove its univalence.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Univalence.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.limits.initial.

Require Import UniMath.Algebra.Universal.TermAlgebras.

Section Algebras.

  Local Open Scope sorted_scope.

  Context (σ : signature).

  Definition shSet_precategory_ob_mor : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (shSet (sorts σ)).
    - intros F G. exact (F s→ G).
  Defined.

  Definition shSet_precategory_data : precategory_data.
  Proof.
    use make_precategory_data.
    - exact shSet_precategory_ob_mor.
    - intro C. simpl. apply idsfun.
    - simpl. intros F G H. intros f g. exact (g s∘ f).
  Defined.

  Definition is_precategory_shSet_precategory_data : is_precategory shSet_precategory_data.
  Proof.
    repeat split.
  Defined.

  Definition shSet_precategory : precategory.
  Proof.
    use make_precategory.
    - apply shSet_precategory_data.
    - apply is_precategory_shSet_precategory_data.
  Defined.

  Definition has_homsets_shSet_precategory : has_homsets shSet_precategory.
  Proof.
    intros F G. simpl.
    use isaset_set_sfun_space.
  Defined.

  Definition shSet_category : category := (shSet_precategory ,, has_homsets_shSet_precategory).

  Definition algebras_disp : disp_cat shSet_category.
  Proof.
    use disp_cat_from_SIP_data. simpl.
    - intro A. exact (∏ nm: names σ, A⋆ (arity nm) → A (sort nm)).
    - simpl. intros A B asA asB f. exact (@ishom σ (make_algebra A asA) (make_algebra B asB) f).
    - simpl. intros A B asA asB f opA opB.
      apply isapropishom.
    - cbn. intros A asA. apply ishomid.
    - cbn. intros A B C opA opB opC. intros f g ishomf ishomg.
      exact (ishomcomp (make_hom ishomf) (make_hom ishomg)).
  Defined.

  Lemma is_univalent_algebras_disp : is_univalent_disp algebras_disp.
  Proof.
    use is_univalent_disp_from_SIP_data.
    - intro A. cbn. use impred_isaset. intro nm. cbn.
      use isaset_set_fun_space.
    - cbn. intros A op1 op2 ishomid1 _. use funextsec. intro nm. use funextfun. intro vec.
      unfold ishom in *. cbn in *. set (H1:= ishomid1 nm vec).
      rewrite staridfun in H1. apply H1.
  Qed.

  Local Open Scope cat.

  (**
  Here follows the proof that [shSet_category] is univalent. The proof is obtained by
  following the example of the proof of univalence of the functor category.
  *)

  Lemma shSet_iso_fiber {A B : shSet_category} (i : iso A B): ∏ s, @iso HSET (A s) (B s).
  Proof.
    intro s.
    apply z_iso_to_iso.
    apply iso_to_z_iso in i.
    induction i as [i [i' [p q]]].
    simpl in *.
    use make_z_iso.
    - exact (i s).
    - exact (i' s).
    - split.
      + exact (eqtohomot p s).
      + exact (eqtohomot q s).
  Defined.

  Definition shSet_eq_from_shSet_iso (F G : shSet_category) (i : iso F G) : F = G.
  Proof.
    apply funextsec.
    intro s.
    apply (isotoid HSET is_univalent_HSET).
    apply shSet_iso_fiber.
    assumption.
  Defined.

  Lemma idtoiso_shSet_category_compute_pointwise {F G : shSet_category} (p : F = G) (s: sorts σ)
    : shSet_iso_fiber (idtoiso p) s = idtoiso(C:=HSET) (toforallpaths (λ _ , hSet) F G p s).
  Proof.
    induction p.
    apply eq_iso. apply idpath.
  Qed.

  Lemma shSet_eq_from_shSet_iso_idtoiso  (F G : shSet_category) (p : F = G)
    : shSet_eq_from_shSet_iso F G (idtoiso p) = p.
  Proof.
    unfold shSet_eq_from_shSet_iso.
    apply (invmaponpathsweq (weqtoforallpaths _ _ _ )).
    simpl (pr1weq (weqtoforallpaths (λ _ : sorts σ, hSet) F G)).
    rewrite (toforallpaths_funextsec).
    apply funextsec.
    intro a.
    rewrite idtoiso_shSet_category_compute_pointwise.
    rewrite isotoid_idtoiso.
    apply idpath.
  Defined.

  Lemma idtoiso_shSet_eq_from_shSet_iso (F G : shSet_category) (i : iso F G)
    : idtoiso (shSet_eq_from_shSet_iso F G i) = i.
  Proof.
    apply eq_iso.
    apply funextsec.
    intro s.
    unfold shSet_eq_from_shSet_iso.
    assert (H' := idtoiso_shSet_category_compute_pointwise (shSet_eq_from_shSet_iso F G i) s).
    simpl in *.
    assert (H2 := maponpaths (@pr1 _ _ ) H').
    simpl in H2.
    etrans.
    { apply H2. }
    intermediate_path (pr1 (idtoiso (isotoid HSET is_univalent_HSET (shSet_iso_fiber i s)))).
    - apply maponpaths.
      apply maponpaths.
      unfold shSet_eq_from_shSet_iso.
      rewrite toforallpaths_funextsec.
      apply idpath.
    - rewrite idtoiso_isotoid.
      apply idpath.
  Qed.

  Definition is_univalent_shSet_category : is_univalent shSet_category.
  Proof.
    intros F G.
    apply (isweq_iso _ (shSet_eq_from_shSet_iso F G)).
    - apply shSet_eq_from_shSet_iso_idtoiso.
    - apply idtoiso_shSet_eq_from_shSet_iso.
  Defined.

  Definition category_algebras : category := total_category algebras_disp.

  Lemma is_univalent_category_algebras : is_univalent category_algebras.
  Proof.
    exact (@is_univalent_total_category shSet_category algebras_disp is_univalent_shSet_category is_univalent_algebras_disp).
  Qed.

  Lemma isinitial_termalgebra : Initial (category_algebras).
  Proof.
    exact (term_algebra σ ,, iscontrhomsfromgterm).
  Defined.

End Algebras.
