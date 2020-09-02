(** * Displayed category of algebras over a signature *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Univalence.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.limits.initial.


Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.Algebra.Universal.SortedTypes.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.Algebras.

Section Algebras.
  Local Open Scope sorted_scope.
  Definition sfun_from_setfun{A B : hSet}(f : A → B)(σ: signature): (λ s: pr1 (sorts σ), A) s→ (λ s: pr1(sorts σ), B).
  Proof.
    unfold sfun. intro S. exact f. Defined.
  Context (σ : signature).

  Definition shSet_precategory_ob_mor : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (shSet (pr1(sorts σ))).
    - intros F G. exact (F s→ G).
  Defined.

  Definition shSet_precategory_data : precategory_data.
  Proof.
    use make_precategory_data.
    - apply shSet_precategory_ob_mor.
    - intro C. simpl. intros S As. exact As.
    - simpl. intros F G H. intros f g S. Search "fun" "assoc".
      exact ((g S ∘ f S)%functions).
  Defined.

  Definition is_precategory_shSet_precategory_data :  is_precategory shSet_precategory_data.
  Proof.
    split; simpl.
    - split.
      -- intros F G f. use funextsec. intros S. apply idpath.
      -- intros F G f. use funextsec. intros S. apply idpath.
    - split.
      -- intros F G H I f g h. use funextsec. intro S. apply idpath.
      -- intros F G H I f g h. use funextsec. intro S. apply idpath.
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
    Search "isaset" "fun_space".
    use isaset_set_sfun_space.
  Defined.

  Definition shSet_category : category := (shSet_precategory ,, has_homsets_shSet_precategory).


  Definition algebras_disp : disp_cat shSet_category.
  Proof.
    use disp_cat_from_SIP_data. simpl.
    - intro A. exact (∏ nm: names σ, A ↑ (arity nm) → A (sort nm)).
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
    - cbn. intros A op1 op2 ishomid1 ishomid2. use funextsec. intro nm. use funextfun. intro vec.
      unfold ishom in *. cbn in *. set (H1:= ishomid1 nm vec). (*rewrite vector_map_id in H1*)
      unfold sfun_from_setfun in H1. rewrite staridfun in H1. apply H1.
  Qed.
Local Open Scope cat.
  Lemma aux{A : UU}{B : A → UU}{f g : ∏ a:A, B a}(p : f = g) : ∏ a, f a = g a.
    Proof. intro a. induction p. apply idpath. Defined. 
    Search (?a = ?b) "homot".
    
  Lemma iso_fiber {A B : shSet_category} (i : Isos.iso A B): ∏ s, @Isos.iso SET (A s) (B s).
  Proof.
    intro S.
    apply z_iso_to_iso.
    apply iso_to_z_iso in i.
    induction i as [i [i' [p q]]].
    - simpl in *.
      use make_z_iso.
      * exact (i S).
      * exact (i' S).
      * split.
        + set (X:=eqtohomot p S). apply X.
        + set (X:=eqtohomot q S). apply X.
  Defined.
(*  Lemma isaset_shSet : isaset (shSet (pr1(sorts σ))).
  Proof.
    unfold shSet.
 *)

  Definition functor_eq_from_functor_iso (F G : shSet_category) (H : iso F G) : F = G.
  Proof.
    apply funextsec.
    intro S.
    apply (isotoid HSET is_univalent_HSET).
    apply iso_fiber.
    assumption.
  Defined.

  Lemma idtoiso_functorcat_compute_pointwise {A B : shSet_category} (p : A = B) (s: pr1 (sorts σ)):
    iso_fiber (idtoiso p) s = idtoiso(C:=HSET) (toforallpaths (λ _ , hSet) A B p s).
  Proof.
    induction p.
    apply eq_iso. apply idpath.
  Qed.

  Lemma functor_eq_from_functor_iso_idtoiso  (F G : shSet_category) (p : F = G) :
    functor_eq_from_functor_iso  F G (idtoiso p) = p.
  Proof.
    unfold functor_eq_from_functor_iso.
    apply (invmaponpathsweq (weqtoforallpaths _ _ _ )).
    simpl (pr1weq (weqtoforallpaths (λ _ : pr1 (sorts σ), hSet) F G)).
    rewrite (toforallpaths_funextsec).
    apply funextsec.
    intro a.
    rewrite idtoiso_functorcat_compute_pointwise.
    rewrite  isotoid_idtoiso.
    apply idpath.
  Defined.

  Lemma idtoiso_functor_eq_from_functor_iso (F G : shSet_category) (gamma : iso F G) :
          idtoiso (functor_eq_from_functor_iso F G gamma) = gamma.
  Proof.
    apply eq_iso.
    apply funextsec.
    intro a.
    unfold functor_eq_from_functor_iso.
    assert (H' := idtoiso_functorcat_compute_pointwise (functor_eq_from_functor_iso F G gamma) a).
    simpl in *.
    assert (H2 := maponpaths (@pr1 _ _ ) H').
    simpl in H2.
    etrans.
    { apply H2. }
    intermediate_path (pr1 (idtoiso (isotoid HSET is_univalent_HSET (iso_fiber gamma a)))).
    - apply maponpaths.
      apply maponpaths.
      unfold functor_eq_from_functor_iso.
      rewrite toforallpaths_funextsec.
      apply idpath.
    - rewrite idtoiso_isotoid.
      apply idpath.
  Qed.

   Definition is_univalent_shSet_category : is_univalent shSet_category.
  Proof.
    split.
    2: apply has_homsets_shSet_precategory.
    intros F G.
    apply (isweq_iso _ (functor_eq_from_functor_iso F G)).
    - apply functor_eq_from_functor_iso_idtoiso.
    - apply idtoiso_functor_eq_from_functor_iso.
  Defined.
 
  Definition is_univalent_shSet_category_old : is_univalent shSet_category.
  Proof.
    split.
    2: apply has_homsets_shSet_precategory.
    - intros F G. intro i. Search "contr" "prop". use iscontraprop1.
      Focus 2.
      use tpair. use funextfun. intro S.
      Print z_iso.
       apply hSet_univalence.
        Search "iso" "weq" . set (X:= invweq (hset_equiv_weq_iso (F S) (G S))).
        induction X as [eq _]. use eq. exact (iso_fiber i S).
    - simpl. use total2_paths_f.
      2: apply isaprop_is_iso.
      * induction i as [i isiso]. simpl in *.
        use funextsec; intro S. use funextfun. intro FS.
        Check (i S FS). unfold iso_fiber. simpl. unfold all. simpl.

      Search "is_univalent". Search "weq".
       use gradth.
      + intro i. use funextfun. intro S. apply hSet_univalence.
        Search "iso" "weq" . set (X:= invweq (hset_equiv_weq_iso (F S) (G S))).
        induction X as [eq _]. use eq. exact (iso_fiber i S).
      + intros e. induction e.

    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
      + simpl. intro p. Search "funspace". Search "is_univalent".
        Search "shSet".
        Search "inv" "eq".








        use univalence.
        * exact (F S ≃ G S).
        *  apply pathsinv0. apply univalence. Search "univ" "hSet".
        * exact (@Isos.iso SET (F S) (G S)).
        * apply univalence. set (X:= is_univalent_HSET).
          unfold is_univalent_HSET in X. simpl in *. induction X as [X _]. simpl in *.


         apply  hset_equiv_weq_iso.
           hset_id_weq_iso.

  (*  - intro A. exact (∏ nm: σ, (λ _, A)* (arity nm) → (λ _, A) (sort nm)).
    - cbn. intros A B asA asB f.
      Search "s→".
      exact (@ishom σ (make_algebra (λ _, A) asA) (make_algebra (λ _, B) asB) (sfun_from_setfun f σ)).
(*        (∏ (nm: σ) (x: dom (make_algebra (λ _, A) asA) nm), (sfun_from_setfun f σ) (sort nm) ((make_algebra (λ _, A) asA) nm x) = (make_algebra (λ _, B) asB) nm ((sfun_from_setfun f σ)** _ x)).
 *)    - intros A B asA asB f opA opB.
         apply isapropishom.
    - cbn. intros A asA. apply ishomid.
    - cbn. intros A B C opA opB opC. intros f g ishomf ishomg.
      exact (ishomcomp (make_hom ishomf) (make_hom ishomg)).
  Defined.


(*    - exact (λ A, shSet A).
    - cbn. intros A B sA sB f.

  Definition algebras_cat : category.
  Proof.
    use make_category.
    - use make_precategory.
      + use make_precategory_data.
        * use make_precategory_ob_mor.
          { exact (algebra σ). }
          {  intros. exact}
          { exact (shSet (pr1 (sorts σ))).  }
          { intros F G. unfold shSet in *. exact (∑ f : hSet → hSet, f ∘ F = G). }
        * cbn. intro F. use tpair.
          { intro A. exact A. }
          { cbn. apply idpath. }
        * cbn. intros F G H [α alpha] [β Beta]. use tpair.
          { exact (β ∘ α). }
          { simpl in *. Search "assoc" "fun". rewrite <- funcomp_assoc. rewrite alpha. apply Beta. }
      + unfold is_precategory. simpl. split.
        * split.
          { intros F G [α alpha]. apply idpath. }
          { intros F G [α alpha]. use total2_paths2_f. simpl. apply idpath.
            simpl.
            etrans. use (id_right (α,, alpha)).
          { intro A. exact A. }
          { cbn.

          Local Open Scope sorted_scope.

    - exact (λ A:hSet, ∏ (nm : names sigma),  Vector A (arity nm) → A).
    - cbn. intros. exact (@ishom sigma (make_algebra x X) (make_algebra y X0) X1).
    - intros. apply isapropishom.
    -  cbn. intros. apply ishomidfun.
    - cbn. intros A B C opA opB opC. intros f g ishomf ishomg.
      exact (ishomcomp (make_hom ishomf) (make_hom ishomg)).
  Defined.*)

  Lemma is_univalent_algebras_disp : is_univalent_disp algebras_disp.
  Proof.
    use is_univalent_disp_from_SIP_data.
    - intro A. cbn. use impred_isaset. intro nm. cbn.
      use isaset_set_fun_space.
    - cbn. intros A op1 op2 ishomid1 ishomid2. use funextsec. intro nm. use funextfun. intro vec.
      unfold ishom in *. cbn in *. set (H1:= ishomid1 nm vec). (*rewrite vector_map_id in H1*)
      unfold sfun_from_setfun in H1. rewrite staridfun in H1. apply H1.
  Qed.

  Definition category_algebras : category := total_category algebras_disp.

  Lemma is_univalent_category_algebras : is_univalent category_algebras.
  Proof.
    exact (@is_univalent_total_category
             SET algebras_disp (is_univalent_HSET) is_univalent_algebras_disp).
  Qed.

End Algebras.

Lemma isinitial_termalgebra (sigma: signature) : Initial (category_algebras sigma).
Proof.
  exact (term_algebra sigma ,, iscontrhomsfromterm).
Defined.
