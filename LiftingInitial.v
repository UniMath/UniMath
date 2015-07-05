Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.
Require Import SubstSystems.UnicodeNotations.
Require Import UniMath.RezkCompletion.whiskering.
Require Import UniMath.RezkCompletion.Monads.
Require Import UniMath.RezkCompletion.limits.products.
Require Import UniMath.RezkCompletion.limits.coproducts.
Require Import UniMath.RezkCompletion.limits.initial.
Require Import UniMath.RezkCompletion.FunctorAlgebras.
Require Import SubstSystems.Auxiliary.
Require Import SubstSystems.PointedFunctors.
Require Import SubstSystems.ProductPrecategory.
Require Import SubstSystems.HorizontalComposition.
Require Import SubstSystems.PointedFunctorsComposition.
Require Import SubstSystems.Signatures.
Require Import SubstSystems.SubstitutionSystems.
Require Import SubstSystems.FunctorsPointwiseCoproduct.
Require Import SubstSystems.GenMendlerIteration.
Require Import SubstSystems.FunctorAlgebraViews.
Require Import SubstSystems.RightKanExtension.
Require Import SubstSystems.GenMendlerIteration.
Require Import SubstSystems.EndofunctorsMonoidal.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Arguments functor_composite {_ _ _} _ _ .
Arguments nat_trans_comp {_ _ _ _ _} _ _ .
Local Notation "G ∙ F" := (functor_composite F G : [ _ , _ , _ ]) (at level 35).
Local Notation "α ∙∙ β" := (hor_comp β α) (at level 20).
Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Local Notation "Z ∘ α" := (post_whisker _ _ _ _ α Z) (at level 35).
Local Notation "A ⊗ B" := (prodcatpair _ _ A B) (at level 10).
Local Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (at level 50).

Arguments θ_source {_ _} _ .
Arguments θ_target {_ _} _ .
Arguments θ_Strength1 {_ _ _} _ .
Arguments θ_Strength2 {_ _ _} _ .

Section Precategory_Algebra.



Variable C : precategory.
Variable hs : has_homsets C.

Variable CP : Coproducts C.

Local Notation "'EndC'":= ([C, C, hs]) .
Local Notation "'Ptd'" := (precategory_Ptd C hs).
Local Notation "'U'" := (functor_ptd_forget C hs).

Let hsEndC : has_homsets EndC := functor_category_has_homsets C C hs.
Let CPEndC : Coproducts EndC := Coproducts_functor_precat _ _ CP hs.

Opaque hsEndC.
(*Opaque CPEndC.*)

Variable KanExt : ∀ Z : Ptd, GlobalRightKanExtensionExists _ _ (U Z) _ hs hs.

Variable H : Signature C hs.
Let θ := theta H. 


Let Id_H :
    functor EndC EndC
  := coproduct_functor _ _ CPEndC
                       (constant_functor _ _ (functor_identity _ : EndC))
                       H.
 

Let Alg : precategory := precategory_FunctorAlg _ Id_H hsEndC.


Variable IA : Initial Alg.
Definition SpecializedGMIt (Z : Ptd) (X : EndC) :=
  SpecialGenMendlerIteration _ _ _ IA EndC hsEndC X _ (KanExt Z) .


Definition θ_in_first_arg (Z: Ptd) := nat_trans_fix_snd_arg _ _ _ _ _ θ Z. 

Definition InitAlg : Alg := InitialObject _ IA.

Let EndEndC := [EndC, EndC, hsEndC].
Let CPEndEndC:= Coproducts_functor_precat _ _ CPEndC hsEndC: Coproducts EndEndC.
(*Opaque CPEndEndC.*)

(* original try in bracket_for_InitAlg with
  assert (iso_1 : functor_composite Id_H (pre_composition_functor C C C hs hs (U Z)) ⟶  
                 coproduct_functor_data ([C, C] hs) ([C, C] hs) CPEndC
    (constant_functor ([C, C] hs) ([C, C] hs) (pr1 Z))
    (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_source H) Z) : EndEndC ⟦ _ , _ ⟧ ).
  { admit. }
 *)

Lemma aux_iso_1_is_nat_trans (Z : Ptd) :
   is_nat_trans
     (functor_composite Id_H (pre_composition_functor C C C hs hs (U Z)))
     (pr1 (CoproductObject EndEndC
        (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
           (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_source H) Z))))
     (λ X : [C, C] hs,
      CoproductOfArrows ([C, C] hs)
        (CPEndC (functor_composite (U Z) (functor_identity C))
           ((θ_source H) (X ⊗ Z))) (CPEndC (U Z) ((θ_source H) (X ⊗ Z)))
        (ρ_functor C (U Z)) (nat_trans_id ((θ_source H) (X ⊗ Z):functor C C))).
Proof.
  unfold is_nat_trans; simpl.
    intros X X' α.
    apply nat_trans_eq; try (exact hs).
    intro c; simpl.
    unfold coproduct_nat_trans_data; simpl.
    unfold coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; simpl.
    eapply pathscomp0.
    apply CoproductOfArrows_comp.
    eapply pathscomp0.
Focus 2.
    eapply pathsinv0.
    apply CoproductOfArrows_comp.
    apply CoproductOfArrows_eq.
    + rewrite id_right.
      apply pathsinv0.
      apply id_right.
    + rewrite functor_id.
      do 2 rewrite id_right.
      apply pathsinv0.
      apply id_left.
Qed.
  
Definition aux_iso_1 (Z: Ptd): EndEndC ⟦ functor_composite Id_H
                                        (pre_composition_functor C C C hs hs (U Z)),
                            CoproductObject EndEndC
           (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
              (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_source H) Z))
                          ⟧.
Proof.
  refine (tpair _ _ _).
  - intro X.
    exact (CoproductOfArrows EndC (CPEndC _ _) (CPEndC _ _) (ρ_functor _ (U Z)) (nat_trans_id (θ_source H (X⊗Z):functor C C))).
  - exact (aux_iso_1_is_nat_trans Z).
Defined.

Lemma aux_iso_1_inv_is_nat_trans (Z : Ptd) :
   is_nat_trans
     (pr1 (CoproductObject EndEndC
        (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
           (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_source H) Z))) )
     (functor_composite Id_H (pre_composition_functor C C C hs hs (U Z)))
     (λ X : [C, C] hs,
      CoproductOfArrows ([C, C] hs)
        (CPEndC (functor_composite (functor_identity C) (U Z))
           ((θ_source H) (X ⊗ Z))) (CPEndC (U Z) ((θ_source H) (X ⊗ Z)))
        (λ_functor C (U Z)) (nat_trans_id ((θ_source H) (X ⊗ Z):functor C C))).
Proof.
  unfold is_nat_trans; simpl.
    intros X X' α.
    apply nat_trans_eq; try (exact hs).
    intro c; simpl.
    unfold coproduct_nat_trans_data; simpl.
    unfold coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; simpl.
    eapply pathscomp0.
    apply CoproductOfArrows_comp.
    eapply pathscomp0.
Focus 2.
    eapply pathsinv0.
    apply CoproductOfArrows_comp.
    apply CoproductOfArrows_eq.
    + rewrite id_right.
      apply pathsinv0.
      apply id_right.
    + rewrite functor_id.
      do 2 rewrite id_right.
      apply pathsinv0.
      apply id_left.
Qed.
  
Definition aux_iso_1_inv (Z: Ptd): EndEndC ⟦ CoproductObject EndEndC
           (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
              (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_source H) Z)),
             functor_composite Id_H (pre_composition_functor C C C hs hs (U Z)) ⟧.
Proof.
  refine (tpair _ _ _).
  - intro X.
    exact (CoproductOfArrows EndC (CPEndC _ _) (CPEndC _ _) (λ_functor _ (U Z)) (nat_trans_id (θ_source H (X⊗Z):functor C C))).
  - exact (aux_iso_1_inv_is_nat_trans Z). 
Defined.

Let H_Thm15 (Z: Ptd) := coproduct_functor _ _ CPEndC
                       (constant_functor _ _ (U Z))
                       H.

Lemma aux_iso_2_inv_is_nat_trans (Z : Ptd) :
   is_nat_trans
     (pr1 (CoproductObject EndEndC
        (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
           (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_target H) Z))) )
     (functor_composite (pre_composition_functor C C C hs hs (U Z))
        (H_Thm15 Z))
     (λ X : [C, C] hs,
      nat_trans_id
        (CoproductObject ([C, C] hs) (CPEndC (U Z) ((θ_target H) (X ⊗ Z)))
         :functor C C)).
Proof.
  unfold is_nat_trans; simpl.
    intros X X' α.
    rewrite (id_left EndC).
    rewrite (id_right EndC).
    apply nat_trans_eq; try (exact hs).
    intro c; simpl.
    unfold coproduct_nat_trans_data; simpl.
    unfold coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data; simpl.
    apply CoproductOfArrows_eq.
    + apply idpath.
    + unfold functor_fix_snd_arg_mor; simpl.
      unfold θ_target_mor; simpl.
      revert c.
      apply nat_trans_eq_pointwise.
      apply maponpaths.
      apply nat_trans_eq; try (exact hs).
      intro c.
      simpl.
      rewrite <- (nat_trans_ax α).
      rewrite functor_id.
      apply id_left.
Qed.

Definition aux_iso_2_inv (Z: Ptd): EndEndC ⟦
                           CoproductObject EndEndC
         (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
                    (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_target H) Z)),

                       functor_composite (pre_composition_functor C C C hs hs (U Z) )   (H_Thm15 Z) ⟧.   
  Proof.
  refine (tpair _ _ _).
  - intro X.
    exact (nat_trans_id ((@CoproductObject EndC (U Z) (θ_target H (X⊗Z)) (CPEndC _ _) ): functor C C)).
  - exact (aux_iso_2_inv_is_nat_trans Z). 
Defined.

Definition θ'_Thm15 (Z: Ptd):= CoproductOfArrows EndEndC (CPEndEndC _ _) (CPEndEndC _ _) (identity (constant_functor EndC _ (U Z): functor_precategory EndC EndC hsEndC)) (θ_in_first_arg Z).

Definition ρ_Thm15 (Z: Ptd)(f : Ptd ⟦ Z, ALG_from_Alg C hs CP H InitAlg ⟧):= @CoproductArrow EndC _ _  (CPEndC (U Z) (H (pr1 InitAlg))) (pr1 InitAlg) (#U f)(CoproductIn2 _ _ ;; (alg_map _ _ InitAlg)).

Definition SpecializedGMIt_Thm15 (Z: Ptd)(f : Ptd ⟦ Z, ALG_from_Alg C hs CP H InitAlg ⟧) := SpecializedGMIt Z (pr1 InitAlg) (H_Thm15 Z) (ρ_Thm15 Z f) (aux_iso_1 Z ;; θ'_Thm15 Z ;; aux_iso_2_inv Z).

Definition bracket_Thm15 (Z: Ptd)(f : Ptd ⟦ Z, ALG_from_Alg C hs CP H InitAlg ⟧) :=
   pr1 (pr1 (SpecializedGMIt_Thm15 Z f)).

(* the property in h_eq in the Alg world has to be translated into the ALG setting *)
(* we prove the individual components for ease of compilation *)
Lemma bracket_Thm15_ok_part1 (Z: Ptd)(f : Ptd ⟦ Z, ALG_from_Alg C hs CP H InitAlg ⟧):
# U f =
 # (pre_composition_functor_data C C C hs hs (U Z))
   (ptd_pt C (pr1 (ALG_from_Alg C hs CP H InitAlg)));; 
 bracket_Thm15 Z f.
Proof.
  apply nat_trans_eq; try (exact hs).
  intro c.
  assert (h_eq := pr2 (pr1 (SpecializedGMIt_Thm15 Z f))).
  assert (h_eq' := maponpaths (fun m:EndC⟦_,pr1 InitAlg⟧ => (((aux_iso_1_inv Z):(_⟶_)) _);; m) h_eq); clear h_eq.
         simpl in h_eq'.
         assert (h_eq1' := maponpaths (fun m:EndC⟦_,pr1 InitAlg⟧ => (CoproductIn1 EndC (CPEndC _ _));; m) h_eq'); clear h_eq'.
         assert (h_eq1'_inst := nat_trans_eq_pointwise _ _ _ _ _ _ h_eq1' c);
           clear h_eq1'.
(* match goal right in the beginning in contrast with earlier approach - suggestion by Benedikt *)
         match goal with |[ H1 : _  = ?f |- _ = _   ] => 
         transitivity (f) end.

  *      clear h_eq1'_inst.
         unfold coproduct_nat_trans_data; simpl.
         unfold coproduct_nat_trans_in1_data ; simpl.
         repeat rewrite <- assoc .
         apply CoproductIn1Commutes_right_in_ctx_dir.
         unfold λ_functor; simpl.
         rewrite id_left.
         apply CoproductIn1Commutes_right_in_ctx_dir.
         unfold ρ_functor; simpl.
         rewrite id_left.
         apply CoproductIn1Commutes_right_in_ctx_dir.
         rewrite (id_left EndC).
(*         rewrite (id_left EndC). *)
         rewrite id_left.
         apply CoproductIn1Commutes_right_in_ctx_dir.
         rewrite (id_left EndC).
         apply CoproductIn1Commutes_right_dir.
         apply idpath.
  *      rewrite <- h_eq1'_inst.
         clear h_eq1'_inst.

         apply CoproductIn1Commutes_left_in_ctx_dir.
         unfold λ_functor, nat_trans_id; simpl.
         rewrite id_left.
         repeat rewrite (id_left EndEndC).
         repeat rewrite (id_left EndC).
         unfold functor_fix_snd_arg_ob.
         repeat rewrite assoc.
         apply maponpaths.
         apply idpath.
Qed.   (* one may consider Admitted for speedup during development *)

(* produce some output to keep TRAVIS running *)
Check bracket_Thm15_ok_part1.

Lemma bracket_Thm15_ok_part2 (Z: Ptd)(f : Ptd ⟦ Z, ALG_from_Alg C hs CP H InitAlg ⟧):
 (theta H) ((U (ALG_from_Alg C hs CP H InitAlg)) ⊗ Z);;
   # H (bracket_Thm15 Z f);;
   SubstitutionSystems.τ (ALG_from_Alg C hs CP H InitAlg) =
   # (pre_composition_functor_data C C C hs hs (U Z))
     (SubstitutionSystems.τ (ALG_from_Alg C hs CP H InitAlg));;
   bracket_Thm15 Z f.
Proof.
  apply nat_trans_eq; try (exact hs).
  intro c.
  assert (h_eq := pr2 (pr1 (SpecializedGMIt_Thm15 Z f))).
  assert (h_eq' := maponpaths (fun m:EndC⟦_,pr1 InitAlg⟧ => (((aux_iso_1_inv Z):(_⟶_)) _);; m) h_eq); clear h_eq.
 (*        simpl in h_eq'. (* until here same as in previous lemma *) *)
         
         assert (h_eq2' := maponpaths (fun m:EndC⟦_,pr1 InitAlg⟧ => (CoproductIn2 EndC (CPEndC _ _));; m) h_eq').
         clear h_eq'.
         assert (h_eq2'_inst := nat_trans_eq_pointwise _ _ _ _ _ _ h_eq2' c).
         clear h_eq2'.
 (*        simpl in h_eq2'_inst. *)
         match goal with |[ H1 : _  = ?f |- _ = _   ] => 
         transitivity (f) end.
         + clear h_eq2'_inst.
 (*          unfold coproduct_nat_trans_data.
           unfold coproduct_nat_trans_in2_data.
*)
           apply CoproductIn2Commutes_right_in_ctx_dir.
           unfold aux_iso_1; simpl.
           rewrite id_right.
           rewrite id_left.
           do 3 rewrite <- assoc.
           apply CoproductIn2Commutes_right_in_ctx_dir.
           unfold nat_trans_id; simpl. rewrite id_left.
           apply CoproductIn2Commutes_right_in_ctx_dir.
           unfold nat_trans_fix_snd_arg_data.
           apply CoproductIn2Commutes_right_in_double_ctx_dir.
           rewrite <- assoc.
           apply maponpaths.
           eapply pathscomp0. Focus 2. apply assoc.
           apply maponpaths.
           apply pathsinv0.
           apply CoproductIn2Commutes.


(* alternative with slightly less precise control:
           do 4 rewrite <- assoc.
           apply CoproductIn2Commutes_right_in_ctx_dir.
           rewrite id_left.
           apply CoproductIn2Commutes_right_in_ctx_dir.
           apply CoproductIn2Commutes_right_in_ctx_dir.
           unfold nat_trans_fix_snd_arg_data.
           rewrite id_left.
           apply CoproductIn2Commutes_right_in_double_ctx_dir.
           do 2 rewrite <- assoc.
           apply maponpaths.
           apply maponpaths.
           apply pathsinv0.
           apply CoproductIn2Commutes.
*)
         + rewrite <- h_eq2'_inst. clear h_eq2'_inst.
           apply CoproductIn2Commutes_left_in_ctx_dir.
           (* unfold Coproducts_functor_precat.
              unfold functor_precat_coproduct_cocone. *)
(*           simpl. *)
           (* unfold coproduct_nat_trans_in2_data. *)
           repeat rewrite id_left.
           apply assoc.
(*           repeat rewrite <- assoc.
           (* apply maponpaths.
              apply maponpaths. *)
           apply idpath. *)  
Qed. (* Qed works fine but takes quite some time, hence Admitted for the purpose of development *)

(* produce some output to keep TRAVIS running *)
Check bracket_Thm15_ok_part2.


Lemma bracket_Thm15_ok (Z: Ptd)(f : Ptd ⟦ Z, ALG_from_Alg C hs CP H InitAlg ⟧):
# U f =
 # (pre_composition_functor_data C C C hs hs (U Z))
   (ptd_pt C (pr1 (ALG_from_Alg C hs CP H InitAlg)));; 
 bracket_Thm15 Z f
 × (theta H) ((U (ALG_from_Alg C hs CP H InitAlg)) ⊗ Z);;
   # H (bracket_Thm15 Z f);;
   SubstitutionSystems.τ (ALG_from_Alg C hs CP H InitAlg) =
   # (pre_composition_functor_data C C C hs hs (U Z))
     (SubstitutionSystems.τ (ALG_from_Alg C hs CP H InitAlg));;
   bracket_Thm15 Z f.
Proof.
  split.
  + exact (bracket_Thm15_ok_part1 Z f).
  + exact (bracket_Thm15_ok_part2 Z f).
(*
(* the property in h_eq in the Alg world has to be translated into the ALG setting *)
      simpl.
      assert (h_eq := pr2 (pr1 (SpecializedGMIt_Thm15 Z f))).
      assert (h_eq' := maponpaths (fun m:EndC⟦_,pr1 InitAlg⟧ => (((aux_iso_1_inv Z):(_⟶_)) _);; m) h_eq).
      clear h_eq.
      split.
      *  apply nat_trans_eq; try (exact hs).
         intro c.
         simpl in h_eq'.
         assert (h_eq1' := maponpaths (fun m:EndC⟦_,pr1 InitAlg⟧ => (CoproductIn1 EndC (CPEndC _ _));; m) h_eq').
         clear h_eq'.
         assert (h_eq1'_inst := nat_trans_eq_pointwise _ _ _ _ _ _ h_eq1' c).
         clear h_eq1'.
         simpl in h_eq1'_inst.
         unfold coproduct_nat_trans_data in h_eq1'_inst; simpl in h_eq1'_inst.
         unfold coproduct_nat_trans_in1_data in h_eq1'_inst; simpl in h_eq1'_inst.
         repeat rewrite <- assoc in h_eq1'_inst.
         apply CoproductIn1Commutes_right_in_ctx in h_eq1'_inst.
         apply CoproductIn1Commutes_left_in_ctx in h_eq1'_inst.
         rewrite id_left in h_eq1'_inst.
         apply CoproductIn1Commutes_right_in_ctx in h_eq1'_inst.
         apply CoproductIn1Commutes_right_in_ctx in h_eq1'_inst.
         do 2 rewrite id_left in h_eq1'_inst.
         apply CoproductIn1Commutes_right_in_ctx in h_eq1'_inst.
         rewrite id_left in h_eq1'_inst.
         repeat rewrite <- assoc in h_eq1'_inst.
         apply CoproductIn1Commutes_right in h_eq1'_inst.
         simpl.
         unfold coproduct_nat_trans_in1_data.
         match goal with |[ H1 : _  = ?f |- _ = _   ] => 
         transitivity (f) end.
         apply idpath.
         rewrite <- h_eq1'_inst.
         clear h_eq1'_inst.

         repeat rewrite id_left.
         unfold nat_trans_id; simpl.
         repeat rewrite (id_left EndEndC).
         repeat rewrite (id_left EndC).
         unfold functor_fix_snd_arg_ob.
         repeat rewrite assoc.
         apply maponpaths.
         apply idpath.
 
     *   apply nat_trans_eq; try (exact hs).
         intro c.
         simpl in h_eq'.
         assert (h_eq2' := maponpaths (fun m:EndC⟦_,pr1 InitAlg⟧ => (CoproductIn2 EndC (CPEndC _ _));; m) h_eq').
         clear h_eq'.
         assert (h_eq2'_inst := nat_trans_eq_pointwise _ _ _ _ _ _ h_eq2' c).
         clear h_eq2'.
         simpl in h_eq2'_inst.
         unfold coproduct_nat_trans_data in h_eq2'_inst; simpl in h_eq2'_inst.
         unfold coproduct_nat_trans_in2_data in h_eq2'_inst; simpl in h_eq2'_inst.
         repeat rewrite <- assoc in h_eq2'_inst.
         apply CoproductIn2Commutes_right_in_ctx in h_eq2'_inst.
         apply CoproductIn2Commutes_left_in_ctx in h_eq2'_inst.
         rewrite id_left in h_eq2'_inst.
         apply CoproductIn2Commutes_right_in_ctx in h_eq2'_inst.
         apply CoproductIn2Commutes_right_in_ctx in h_eq2'_inst.
         unfold nat_trans_fix_snd_arg_data in h_eq2'_inst.
         rewrite id_left in h_eq2'_inst.
(* now need even context to the left *)
         apply CoproductIn2Commutes_right_in_double_ctx in h_eq2'_inst.
         match goal with |[ H1 : _  = ?f |- _ = _   ] => 
         transitivity (f) end.
Focus 2.
         rewrite <- h_eq2'_inst.
         repeat rewrite <- assoc.
         unfold Coproducts_functor_precat.
         unfold functor_precat_coproduct_cocone.
         simpl.
         unfold coproduct_nat_trans_in2_data.
         repeat rewrite <- assoc.
         (* apply maponpaths.
         apply maponpaths. *)
         apply idpath.   

         clear h_eq2'_inst.
         repeat rewrite <- assoc.
         unfold Coproducts_functor_precat.
         unfold functor_precat_coproduct_cocone.
         simpl.
         unfold coproduct_nat_trans_in2_data.
         repeat rewrite <- assoc.
         apply maponpaths.
         apply maponpaths.
         apply pathsinv0.
         apply CoproductIn2Commutes.

(* verification of the original proof was very time-consuming *)
*)
Qed.

Lemma foo (Z : Ptd) (f : Ptd ⟦ Z, ALG_from_Alg C hs CP H InitAlg ⟧) :
   ∀
   t : Σ
       h : [C, C] hs
           ⟦ functor_composite (U Z) (U (ALG_from_Alg C hs CP H InitAlg)),
           U (ALG_from_Alg C hs CP H InitAlg) ⟧,
       # U f =
       # (pre_composition_functor_data C C C hs hs (U Z))
         (ptd_pt C (pr1 (ALG_from_Alg C hs CP H InitAlg)));; h
       × (theta H) ((U (ALG_from_Alg C hs CP H InitAlg)) ⊗ Z);; # H h;;
         SubstitutionSystems.τ (ALG_from_Alg C hs CP H InitAlg) =
         # (pre_composition_functor_data C C C hs hs (U Z))
           (SubstitutionSystems.τ (ALG_from_Alg C hs CP H InitAlg));; h,
   t =
   tpair
     (λ h : [C, C] hs
            ⟦ functor_composite (U Z) (U (ALG_from_Alg C hs CP H InitAlg)),
            U (ALG_from_Alg C hs CP H InitAlg) ⟧,
      # U f =
      # (pre_composition_functor_data C C C hs hs (U Z))
        (ptd_pt C (pr1 (ALG_from_Alg C hs CP H InitAlg)));; h
      × (theta H) ((U (ALG_from_Alg C hs CP H InitAlg)) ⊗ Z);; # H h;;
        SubstitutionSystems.τ (ALG_from_Alg C hs CP H InitAlg) =
        # (pre_composition_functor_data C C C hs hs (U Z))
          (SubstitutionSystems.τ (ALG_from_Alg C hs CP H InitAlg));; h)
     (bracket_Thm15 Z f) (bracket_Thm15_ok Z f).
Proof.
  intros [h' [h'_eq1 h'_eq2]].
    (* simpl in *. *)
    apply total2_paths_second_isaprop.
    + apply isofhleveltotal2.
      * apply isaset_nat_trans. exact hs.
      * intro Hyp. apply isaset_nat_trans. exact hs.
    + simpl.
      unfold bracket_Thm15.
      simpl. 
      rewrite It_is_It_which_is_unique.
      apply path_to_ctr.
      apply nat_trans_eq; try (exact hs).
      intro c; simpl.
      unfold coproduct_nat_trans_data.
      repeat rewrite (id_left EndC).
      rewrite id_right.
      repeat rewrite <- assoc.
      eapply pathscomp0.
Focus 2.
      eapply pathsinv0.
      apply postcompWithCoproductArrow.
      apply CoproductArrowUnique.
      * simpl.
        clear h'_eq2.
        rewrite (id_left C).
(*        unfold coproduct_nat_trans_in1_data; simpl. *)
        assert (h'_eq1_inst := nat_trans_eq_pointwise _ _ _ _ _ _ h'_eq1 c);
          clear h'_eq1.
        simpl in h'_eq1_inst.
        unfold coproduct_nat_trans_in1_data in h'_eq1_inst; simpl in h'_eq1_inst.
        rewrite <- assoc in h'_eq1_inst.
        eapply pathscomp0.
          eapply pathsinv0.
          exact h'_eq1_inst. 
        clear h'_eq1_inst.
        apply CoproductIn1Commutes_right_in_ctx_dir.
        apply CoproductIn1Commutes_right_in_ctx_dir.
        apply CoproductIn1Commutes_right_dir.
        apply idpath.
      * clear h'_eq1.
        (*simpl.
        unfold coproduct_nat_trans_in2_data; simpl. *)
        assert (h'_eq2_inst := nat_trans_eq_pointwise _ _ _ _ _ _ h'_eq2 c);
          clear h'_eq2.
        simpl in h'_eq2_inst.
        unfold coproduct_nat_trans_in2_data in h'_eq2_inst; simpl in h'_eq2_inst.
        apply pathsinv0 in h'_eq2_inst.
        rewrite <- assoc in h'_eq2_inst.
        eapply pathscomp0.
          exact h'_eq2_inst. clear h'_eq2_inst.

        apply CoproductIn2Commutes_right_in_ctx_dir.
        apply CoproductIn2Commutes_right_in_double_ctx_dir.
        unfold nat_trans_fix_snd_arg_data; simpl.
        do 2 rewrite <- assoc.
        apply maponpaths.
        rewrite <- assoc.
        apply maponpaths.
        apply pathsinv0.
        apply CoproductIn2Commutes.
Qed.

Definition bracket_for_InitAlg : bracket _ _ H (ALG_from_Alg _ _ _ _ InitAlg).
Proof.
  intros Z f.
  refine (tpair _ _ _ ).
  - refine (tpair _ _ _ ).
    + exact (bracket_Thm15 Z f).
    + exact (bracket_Thm15_ok Z f).
(* when the first components were not opaque, the following proof
   became extremely slow *)

      
  - apply foo.
 (*   
    intros [h' [h'_eq1 h'_eq2]].
    (* simpl in *. *)
    apply total2_paths_second_isaprop.
    + apply isofhleveltotal2.
      * apply isaset_nat_trans. exact hs.
      * intro Hyp. apply isaset_nat_trans. exact hs.
    + simpl.
      unfold bracket_Thm15.
      simpl. 
      rewrite It_is_It_which_is_unique.
      apply path_to_ctr.
      apply nat_trans_eq; try (exact hs).
      intro c; simpl.
      unfold coproduct_nat_trans_data.
      repeat rewrite (id_left EndC).
      rewrite id_right.
      repeat rewrite <- assoc.
      eapply pathscomp0.
Focus 2.
      eapply pathsinv0.
      apply postcompWithCoproductArrow.
      apply CoproductArrowUnique.
      * simpl.
        clear h'_eq2.
        rewrite (id_left C).
(*        unfold coproduct_nat_trans_in1_data; simpl. *)
        assert (h'_eq1_inst := nat_trans_eq_pointwise _ _ _ _ _ _ h'_eq1 c);
          clear h'_eq1.
        simpl in h'_eq1_inst.
        unfold coproduct_nat_trans_in1_data in h'_eq1_inst; simpl in h'_eq1_inst.
        rewrite <- assoc in h'_eq1_inst.
        eapply pathscomp0.
          eapply pathsinv0.
          exact h'_eq1_inst. 
        clear h'_eq1_inst.
        apply CoproductIn1Commutes_right_in_ctx_dir.
        apply CoproductIn1Commutes_right_in_ctx_dir.
        apply CoproductIn1Commutes_right_dir.
        apply idpath.
      * clear h'_eq1.
        (*simpl.
        unfold coproduct_nat_trans_in2_data; simpl. *)
        assert (h'_eq2_inst := nat_trans_eq_pointwise _ _ _ _ _ _ h'_eq2 c);
          clear h'_eq2.
        simpl in h'_eq2_inst.
        unfold coproduct_nat_trans_in2_data in h'_eq2_inst; simpl in h'_eq2_inst.
        apply pathsinv0 in h'_eq2_inst.
        rewrite <- assoc in h'_eq2_inst.
        eapply pathscomp0.
          exact h'_eq2_inst. clear h'_eq2_inst.

        apply CoproductIn2Commutes_right_in_ctx_dir.
        apply CoproductIn2Commutes_right_in_double_ctx_dir.
        unfold nat_trans_fix_snd_arg_data; simpl.
        do 2 rewrite <- assoc.
        apply maponpaths.
        rewrite <- assoc.
        apply maponpaths.
        apply pathsinv0.
        apply CoproductIn2Commutes.
    (* this was the back translation of the data into an argument for h_unique (Alg view) *)
*)
Defined.

(* produce some output to keep TRAVIS running *)
Check bracket_for_InitAlg.


Definition InitHSS : hss_precategory H.
Proof.
 (* 
  red. (* FORBIDDEN, otherwise universe problem when checking the definition *)
  unfold hss_precategory; simpl.
*)
  exists (ALG_from_Alg _ _ _ _ InitAlg).
  exact bracket_for_InitAlg.
Defined.


Lemma isInitial_InitHSS : isInitial (hss_precategory H) InitHSS.
Proof.
  intro T.
  simpl.
  set (T' := Alg_from_ALG _ _ CP _  (pr1 T)).
(*
  assert (auxT' : ALG_from_Alg C hs CP H T' = pr1 T).
Focus 2.
*)
  set (β := InitialArrow _ IA T').
  set (β' := ALG_mor_from_Alg_mor _ hs CP _ β).
  refine (tpair _ _ _ ).
  - refine (tpair _ _ _ ).
    + refine (tpair _ _ _ ).
      * apply β.
      * destruct β as [β βalg].
        assert (β_is_ptd := pr2 (pr1 β')).
        simpl in β_is_ptd.
        (* does not work: apply β_is_ptd.*)
        intro c.
        assert (β_is_ptd_inst := β_is_ptd c); clear β_is_ptd.
        eapply pathscomp0.
          exact  β_is_ptd_inst.
        clear β_is_ptd_inst.
        apply CoproductIn1Commutes.      
    + destruct β as [β βalg].
      split.
      * assert (β_isALGMor := pr2 β').
        

        (* apply another component of βalg *)
        admit.
      * simpl.

        destruct β as [β βalg]; simpl in *.
        unfold isbracketMor. simpl.
        intros Z f.        
        (* now define Ψ for fusion law *)
      admit.
Admitted.

Lemma Ihss : Initial (hss_precategory H).
Proof.
  exists InitHSS.
  apply isInitial_InitHSS.
Defined.


End Precategory_Algebra.


(*


(** Define the precategory of Id+H-algebras.

    We could define this precategory before that of hss, and
    define hss as a sub-precategory of that of Id+H-algebras
    As a consequence, we would have faithfulness of the forgetful
    functor for free.
    Also, composition and identity would be inherited instead of
    having to be defined twice.

    On the other hand, the category of hss is the main object of 
    investigation, so maybe it is better to give it more explicitly.
    Working with sub-precategories is a pain in the butt.

*)

Local Notation "'Alg_obj'" := (Alg H).

Definition Alg_mor (A B : Alg_obj) : UU 
  := Σ f : Ptd ⟦A, B⟧, isAlgMor C hs H f. 

(* explicit coercion not necessary, this works, too:
Definition Alg_mor' (A B : Alg_obj) : UU 
  := Σ f : A ⇒ pr1 B, isAlgMor C hs H f.
*)

Coercion Ptd_mor_from_Alg_mor (A B : Alg_obj)(f : Alg_mor A B) : Ptd ⟦A, B⟧ := pr1 f.

Definition isAlgMor_Alg_mor (A B : Alg_obj)(f : Alg_mor A B) : isAlgMor _ _ _ f := pr2 f.

Definition Alg_mor_eq_weq (A B : Alg_obj) (f g : Alg_mor A B) 
  : f = g ≃ #U f = #U g.
Proof.
  eapply weqcomp.
  - apply total2_paths_isaprop_equiv.
    intro h. apply isaprop_isAlgMor.
  - apply eq_ptd_mor.
    apply hs.
Defined.

Definition isAlgMor_id (A : Alg_obj) : isAlgMor C hs H (identity A : Ptd⟦A,A⟧).
Proof.
  unfold isAlgMor.
  rewrite functor_id.
  rewrite functor_id.
  rewrite id_left.
  set (H2 := id_right ([C,C,hs])).
  apply pathsinv0, H2.
Qed.

Definition AlgMor_id (A : Alg_obj) : Alg_mor A A := tpair _ _ (isAlgMor_id A).


Definition isAlgMor_comp (A B D : Alg_obj) (f : Alg_mor A B) (g : Alg_mor B D) 
  : isAlgMor C hs H (f ;; g : Ptd⟦A, D⟧).
Proof.
  unfold isAlgMor.
  rewrite functor_comp.
  rewrite functor_comp.
  rewrite <- assoc.
  rewrite isAlgMor_Alg_mor.
  rewrite assoc.
  rewrite isAlgMor_Alg_mor.
  apply pathsinv0, assoc.
Qed.

Definition AlgMor_comp (A B D : Alg_obj) (f : Alg_mor A B) (g : Alg_mor B D) : Alg_mor A D
  := tpair _ _ (isAlgMor_comp A B D f g).

Definition Alg_precategory_ob_mor : precategory_ob_mor.
Proof.
  exists Alg_obj.
  exact (Alg_mor).
Defined.

Definition Alg_precategory_data : precategory_data.
Proof.
  exists Alg_precategory_ob_mor.
  split.
  - exact AlgMor_id.
  - exact AlgMor_comp.
Defined.

Lemma is_precategory_Alg : is_precategory Alg_precategory_data.
Proof.
  repeat split; intros.
  - apply (invmap (Alg_mor_eq_weq _ _ _ _ )).
    apply (id_left EndC).
  - apply (invmap (Alg_mor_eq_weq _ _ _ _ )).
    apply (id_right EndC).
  - apply (invmap (Alg_mor_eq_weq _ _ _ _ )).
    apply (assoc EndC).
Qed.

Definition precategory_Alg : precategory := tpair _ _ is_precategory_Alg.

Local Notation "'ALG'" := precategory_Alg.
 *)


   
