Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.SubstitutionSystems.Auxiliary.
Require Import UniMath.SubstitutionSystems.PointedFunctors.
Require Import UniMath.SubstitutionSystems.ProductPrecategory.
Require Import UniMath.SubstitutionSystems.HorizontalComposition.
Require Import UniMath.SubstitutionSystems.PointedFunctorsComposition.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.FunctorsPointwiseCoproduct.
Require Import UniMath.SubstitutionSystems.GenMendlerIteration.
Require Import UniMath.SubstitutionSystems.RightKanExtension.
Require Import UniMath.SubstitutionSystems.GenMendlerIteration.
Require Import UniMath.SubstitutionSystems.EndofunctorsMonoidal.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Arguments functor_composite {_ _ _} _ _ .
Arguments nat_trans_comp {_ _ _ _ _} _ _ .
Local Notation "G ∙ F" := (functor_composite F G : [ _ , _ , _ ]) (at level 35).
Local Notation "α ∙∙ β" := (hor_comp β α) (at level 20).
Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Local Notation "Z ∘ α" := (post_whisker _ _ _ _ α Z) (at level 50).
Local Notation "A ⊗ B" := (prodcatpair _ _ A B) (at level 10).
Local Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (at level 50).

Local Coercion alg_carrier : algebra_ob >-> ob.

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
Let EndEndC := [EndC, EndC, hsEndC].
Let CPEndEndC:= Coproducts_functor_precat _ _ CPEndC hsEndC: Coproducts EndEndC.
(*Opaque CPEndEndC.*)

Definition ℓ (X : EndC) : EndEndC := (pre_composition_functor C C C hs hs X).
(*   in Agda mode \ell *)

(*
Opaque hsEndC.
*)
(*Opaque CPEndC.*)

Variable KanExt : ∀ Z : Ptd, GlobalRightKanExtensionExists _ _ (U Z) _ hs hs.

Variable H : Signature C hs.
Let θ := theta H. 

Definition Const_plus_H (X : EndC) : functor EndC EndC
  := coproduct_functor _ _ CPEndC
                       (constant_functor _ _ X)
                       H.
 

Definition Id_H := Const_plus_H (functor_identity _ : EndC).
 

Let Alg : precategory := precategory_FunctorAlg _ Id_H hsEndC.


Variable IA : Initial Alg.
Definition SpecializedGMIt (Z : Ptd) (X : EndC) :=
  SpecialGenMendlerIteration _ _ _ IA EndC hsEndC X _ (KanExt Z) .


Definition θ_in_first_arg (Z: Ptd) := nat_trans_fix_snd_arg _ _ _ _ _ θ Z. 

Definition InitAlg : Alg := InitialObject _ IA.



(* original try in bracket_for_InitAlg with
  assert (iso_1 : functor_composite Id_H (pre_composition_functor C C C hs hs (U Z)) ⟶  
                 coproduct_functor_data ([C, C] hs) ([C, C] hs) CPEndC
    (constant_functor ([C, C] hs) ([C, C] hs) (pr1 Z))
    (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_source H) Z) : EndEndC ⟦ _ , _ ⟧ ).
  { admit. }
 *)

Lemma aux_iso_1_is_nat_trans (Z : Ptd) :
   is_nat_trans
     (functor_composite Id_H (ℓ (U Z)))
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
                                        (ℓ (U Z)),
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
     (functor_composite Id_H (ℓ (U Z)))
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
             functor_composite Id_H (ℓ (U Z)) ⟧.
Proof.
  refine (tpair _ _ _).
  - intro X.
    exact (CoproductOfArrows EndC (CPEndC _ _) (CPEndC _ _) (λ_functor _ (U Z)) (nat_trans_id (θ_source H (X⊗Z):functor C C))).
  - exact (aux_iso_1_inv_is_nat_trans Z). 
Defined.

(*
Definition G_Thm15 (X : EndC) := coproduct_functor _ _ CPEndC
                       (constant_functor _ _ X)
                       H.
 *)

Lemma aux_iso_2_inv_is_nat_trans (Z : Ptd) :
   is_nat_trans
     (pr1 (CoproductObject EndEndC
        (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
           (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_target H) Z))) )
     (functor_composite (ℓ (U Z))
        (Const_plus_H (U Z)))
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

                       functor_composite (ℓ (U Z) )   (Const_plus_H (U Z)) ⟧.   
  Proof.
  refine (tpair _ _ _).
  - intro X.
    exact (nat_trans_id ((@CoproductObject EndC (U Z) (θ_target H (X⊗Z)) (CPEndC _ _) ): functor C C)).
  - exact (aux_iso_2_inv_is_nat_trans Z). 
Defined.

Definition θ'_Thm15 (Z: Ptd):= CoproductOfArrows EndEndC (CPEndEndC _ _) (CPEndEndC _ _) (identity (constant_functor EndC _ (U Z): functor_precategory EndC EndC hsEndC)) (θ_in_first_arg Z).

Definition ρ_Thm15 (Z: Ptd)(f : Ptd ⟦ Z,  ptd_from_alg _ _ _ _ InitAlg ⟧):= @CoproductArrow EndC _ _  (CPEndC (U Z) (H (pr1 InitAlg))) (pr1 InitAlg) (#U f)(CoproductIn2 _ _ ;; (alg_map _ _ InitAlg)).

Definition SpecializedGMIt_Thm15 (Z: Ptd)(f : Ptd ⟦ Z, ptd_from_alg _ _ _ _  InitAlg ⟧) := SpecializedGMIt Z (pr1 InitAlg) (Const_plus_H (U Z)) (ρ_Thm15 Z f) (aux_iso_1 Z ;; θ'_Thm15 Z ;; aux_iso_2_inv Z).

Definition bracket_Thm15 (Z: Ptd)(f : Ptd ⟦ Z, ptd_from_alg _ _ _ _  InitAlg ⟧) :=
   pr1 (pr1 (SpecializedGMIt_Thm15 Z f)).

(* the property in h_eq in the Alg world has to be translated into the ALG setting *)
(* we prove the individual components for ease of compilation *)
Lemma bracket_Thm15_ok_part1 (Z: Ptd)(f : Ptd ⟦ Z, ptd_from_alg _ _ _ _  InitAlg ⟧):
# U f =
 # (pr1 (ℓ (U Z)))
   (eta_from_alg _ _ _ _ (InitAlg));; 
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
         pathvia (f) end.

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

Lemma bracket_Thm15_ok_part2 (Z: Ptd)(f : Ptd ⟦ Z, ptd_from_alg _ _ _ _  InitAlg ⟧):
 (theta H) ((pr1 InitAlg) ⊗ Z);;
   # H (bracket_Thm15 Z f);;
   tau_from_alg  _ _ _ _ InitAlg =
   # (pr1 (ℓ (U Z)))
     (tau_from_alg  _ _ _ _  InitAlg);;
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
         pathvia (f) end.
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


Lemma bracket_Thm15_ok (Z: Ptd)(f : Ptd ⟦ Z, ptd_from_alg _ _ _ _  InitAlg ⟧):
 bracket_property_parts _ hs CP H InitAlg f (bracket_Thm15 Z f).
Proof.
  split.
  + exact (bracket_Thm15_ok_part1 Z f).
  + exact (bracket_Thm15_ok_part2 Z f).
Qed.

Lemma bracket_Thm15_ok_cor (Z: Ptd)(f : Ptd ⟦ Z, ptd_from_alg _ _ _ _  InitAlg ⟧):
 bracket_property _ hs CP H InitAlg f (bracket_Thm15 Z f).
Proof.
  apply whole_from_parts.
  apply bracket_Thm15_ok.
Qed.

(* we will directly need the later lemma foo'
Lemma foo (Z : Ptd) (f : Ptd ⟦ Z, ptd_from_alg _ _ _ _  InitAlg ⟧) :
 ∀
   t : Σ
       h : [C, C] hs
           ⟦ functor_composite (U Z) (pr1  InitAlg),
            pr1 InitAlg ⟧,
       bracket_property_parts _ hs CP H InitAlg f h,
   t =
   tpair
     (λ h : [C, C] hs
            ⟦ functor_composite (U Z) (pr1 InitAlg),
              pr1 InitAlg ⟧,
      bracket_property_parts _ hs CP H InitAlg f h)
     (bracket_Thm15 Z f) (bracket_Thm15_ok Z f).
(*
   ∀
   t : Σ
       h : [C, C] hs
           ⟦ functor_composite (U Z) (pr1  InitAlg),
            pr1 InitAlg ⟧,
       # U f =
       # (pre_composition_functor_data C C C hs hs (U Z))
         (eta_from_alg _ _ _ _  InitAlg);; h
       × (theta H) ((pr1 InitAlg) ⊗ Z);; # H h;;
         tau_from_alg _ _ _ _  InitAlg =
         # (pre_composition_functor_data C C C hs hs (U Z))
           (tau_from_alg _ _ _ _  InitAlg);; h,
   t =
   tpair
     (λ h : [C, C] hs
            ⟦ functor_composite (U Z) (pr1 InitAlg),
              pr1 InitAlg ⟧,
      # U f =
      # (pre_composition_functor_data C C C hs hs (U Z))
        (eta_from_alg _ _ _  _ InitAlg);; h
      × (theta H) ((pr1 InitAlg) ⊗ Z);; # H h;;
        tau_from_alg _ _ _ _  InitAlg =
        # (pre_composition_functor_data C C C hs hs (U Z))
          (tau_from_alg _ _ _ _  InitAlg);; h)
     (bracket_Thm15 Z f) (bracket_Thm15_ok Z f).
*)
Proof.
  intros [h' [h'_eq1 h'_eq2]].
    (* simpl in *. *)
    apply total2_paths_second_isaprop.
    + apply isofhleveltotal2.
      * apply isaset_nat_trans. exact hs.
      * intro Hyp. apply isaset_nat_trans. exact hs.
    + simpl.
      unfold bracket_Thm15.
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
*)

Lemma foo' (Z : Ptd) (f : Ptd ⟦ Z, ptd_from_alg _ _ _ _  InitAlg ⟧) :
 ∀
   t : Σ
       h : [C, C] hs
           ⟦ functor_composite (U Z) (pr1  InitAlg),
            pr1 InitAlg ⟧,
       bracket_property _ hs CP H InitAlg f h,
   t =
   tpair
     (λ h : [C, C] hs
            ⟦ functor_composite (U Z) (pr1 InitAlg),
              pr1 InitAlg ⟧,
      bracket_property _ hs CP H InitAlg f h)
     (bracket_Thm15 Z f) (bracket_Thm15_ok_cor Z f).
Proof.
   intros [h' h'_eq].
    (* simpl in *. *)
    apply total2_paths_second_isaprop.
    + unfold bracket_property.
      apply isaset_nat_trans. exact hs.
    + simpl.
      apply parts_from_whole in h'_eq.
      destruct h'_eq as [h'_eq1 h'_eq2].
      unfold bracket_Thm15.
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

Definition bracket_for_InitAlg : bracket _ _ CP H (InitAlg).
Proof.
  intros Z f.
  refine (tpair _ _ _ ).
  - refine (tpair _ _ _ ).
    + exact (bracket_Thm15 Z f).
    + exact (bracket_Thm15_ok_cor Z f).
       (* B: better to prove the whole outside, and apply it here *)
     (* when the first components were not opaque, the following proof
        became extremely slow *)
  - apply foo'.
Defined.

(* produce some output to keep TRAVIS running *)
Check bracket_for_InitAlg.


Definition InitHSS : hss_precategory CP H.
Proof.
 (* 
  red. (* FORBIDDEN, otherwise universe problem when checking the definition *)
  unfold hss_precategory; simpl.
*)
  exists (InitAlg).
  exact bracket_for_InitAlg.
Defined.


Definition Ghat : EndEndC := Const_plus_H (pr1 InitAlg).

Definition constant_nat_trans (C' D : precategory) (hsD : has_homsets D) (d d' : D) (m : d ⇒ d')
    : [C', D, hsD] ⟦constant_functor C' D d, constant_functor C' D d'⟧.
Proof.
  exists (fun _ => m).
  abstract ( 
    intros ? ? ? ;
    pathvia m ;
    [
    apply id_left |
    apply pathsinv0 ;
  apply id_right] ).
Defined.

Definition thetahat_0 (Z : Ptd) (f : Z ⇒ ptd_from_alg _ _ _ _ InitAlg): 
EndEndC
⟦ CoproductObject EndEndC
    (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
       (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_source H) Z)),
CoproductObject EndEndC
  (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (pr1 InitAlg))
             (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_target H) Z)) ⟧ .
Proof.
  exact (CoproductOfArrows EndEndC (CPEndEndC _ _) (CPEndEndC _ _) 
                           (constant_nat_trans _ _ hsEndC _ _ (#U f))
                           (θ_in_first_arg Z)).
Defined.

Definition iso1' (Z : Ptd) :  EndEndC ⟦ functor_composite Id_H
                                        (ℓ (U Z)),
 CoproductObject EndEndC
    (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
               (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_source H) Z)) ⟧.
Proof.
  exact (aux_iso_1 Z).
Defined.  


Lemma is_nat_trans_iso2' (Z : Ptd) :
   is_nat_trans
     (pr1 (CoproductObject EndEndC
        (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (pr1 InitAlg))
           (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_target H) Z))))
     (functor_composite (ℓ (U Z)) Ghat)
     (λ X : [C, C] hs,
      nat_trans_id
        (CoproductObject ([C, C] hs)
           (CPEndC
              ((constant_functor ([C, C] hs) ([C, C] hs) (pr1 InitAlg)) X)
              ((θ_target H) (X ⊗ Z)))
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

Definition iso2' (Z : Ptd) : EndEndC ⟦
  CoproductObject EndEndC
  (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (pr1 InitAlg))
             (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_target H) Z)),
  functor_composite (ℓ (U Z) ) (Ghat) ⟧.
Proof.
    refine (tpair _ _ _).
  - intro X.
    exact (nat_trans_id ((@CoproductObject EndC _ (θ_target H (X⊗Z)) (CPEndC _ _) ): functor C C)).
  - exact (is_nat_trans_iso2' Z).
Defined.

Definition thetahat (Z : Ptd)  (f : Z ⇒ ptd_from_alg _ _ _ _ InitAlg)
           : EndEndC ⟦ functor_composite Id_H
                                        (ℓ (U Z)),
                     functor_composite (ℓ (U Z)) (Ghat) ⟧.
Proof.
  exact (iso1' Z ;; thetahat_0 Z f ;; iso2' Z).
Defined.


Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.category_hset.
 
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

Let Yon (X : EndC) : functor EndC^op HSET := yoneda_objects EndC hsEndC X.

Definition Phi_fusion (Z : Ptd) (X : EndC) (b : pr1 InitAlg ⇒ X) :
  functor_composite (functor_opp (ℓ (U Z))) (Yon (pr1 InitAlg))
   ⟶
  functor_composite (functor_opp (ℓ (U Z))) (Yon X) .
Proof.
  refine (tpair _ _ _ ).
  - intro Y.
    intro a.
    exact (a ;; b).
  - abstract (
    intros ? ? ? ; simpl ;
    apply funextsec ;
    intro ;
    unfold yoneda_objects_ob ; simpl ;
    unfold compose ;
    simpl ;
    apply nat_trans_eq ;
    [
      assumption
        |
      simpl ; intros ? ;
      apply pathsinv0, assoc ]).
Defined.    
    
Lemma ishssMor_InitAlg (T' : hss CP H) :
  @ishssMor C hs CP H
        InitHSS T'        
           (InitialArrow Alg IA (pr1 T') : algebra_mor EndC Id_H InitAlg T' ).  
Proof.
  unfold ishssMor.
  unfold isbracketMor.
  intros Z f.
  set (β0 := InitialArrow Alg IA (pr1 T')).
  match goal with | [|- _ ;; ?b = _ ] => set (β := b) end.
  set ( rhohat := CoproductArrow EndC  (CPEndC _ _ )  β (tau_from_alg _ _ _ _ T')
                  :  pr1 Ghat T' ⇒ T').
  set (X:= SpecializedGMIt Z _ Ghat rhohat (thetahat Z f)).
  pathvia (pr1 (pr1 X)).
  - set (TT:= fusion_law _ _ _ IA _ hsEndC (pr1 InitAlg) T' _ (KanExt Z)).
    set (Psi := ψ_from_comps _ (Id_H) _ hsEndC _ (ℓ (U Z)) (Const_plus_H (U Z)) (ρ_Thm15 Z f)
                             (aux_iso_1 Z ;; θ'_Thm15 Z ;; aux_iso_2_inv Z) ).
    set (T2 := TT Psi).
    set (T3 := T2 (ℓ (U Z)) (KanExt Z)).
    set (Psi' := ψ_from_comps _ (Id_H) _ hsEndC _ (ℓ (U Z)) (Ghat) (rhohat)
                             (iso1' Z ;; thetahat_0 Z f ;; iso2' Z) ).
    set (T4 := T3 Psi').
    set (Φ := (Phi_fusion Z T' β)).
    set (T5 := T4 Φ).
    pathvia (Φ _ (fbracket InitHSS f)).
      apply idpath.
    eapply pathscomp0.
      Focus 2.
        eapply T5.
      (* hypothesis of fusion law *)
      apply funextsec. intro.
      simpl.
      unfold compose. simpl.
      apply nat_trans_eq. assumption.
      simpl.
      intro c.
      rewrite id_right.
      rewrite id_right.
      (* should be decomposed into two diagrams *)
      apply CoproductArrow_eq_cor.
      * (* first diagram *)
        clear TT T2 T3 T4 T5.
        do 5 rewrite <- assoc.
        apply CoproductIn1Commutes_left_in_ctx_dir.
        apply CoproductIn1Commutes_right_in_ctx_dir.
        simpl.
        rewrite id_left.
        apply CoproductIn1Commutes_left_in_ctx_dir.
        apply CoproductIn1Commutes_right_in_ctx_dir.
        simpl.
        rewrite id_left.
        apply CoproductIn1Commutes_left_in_ctx_dir.
        simpl.
        rewrite id_left.
        apply CoproductIn1Commutes_left_in_ctx_dir.
        rewrite <- assoc.
        apply maponpaths.
        apply CoproductIn1Commutes_right_in_ctx_dir.
        simpl.
        rewrite id_left.
        apply CoproductIn1Commutes_right_dir.
        apply idpath.
      * (* a bit out of order what follows *)
        apply cancel_postcomposition.
        apply idpath.
      * (* second diagram *)
        clear TT T2 T3 T4 T5.
        do 5 rewrite <- assoc.
        apply CoproductIn2Commutes_left_in_ctx_dir.
        apply CoproductIn2Commutes_right_in_ctx_dir.
        rewrite (id_left EndC).
        apply CoproductIn2Commutes_left_in_ctx_dir.
        apply CoproductIn2Commutes_right_in_ctx_dir.
        simpl.
        unfold nat_trans_fix_snd_arg_data.
        repeat rewrite <- assoc.
        apply maponpaths.
        apply CoproductIn2Commutes_left_in_ctx_dir.
        apply CoproductIn2Commutes_right_in_ctx_dir.
        simpl.
        assert (H_nat_inst := functor_comp H _ _ _ t β).
        assert (H_nat_inst_c := nat_trans_eq_pointwise _ _ _ _ _ _ H_nat_inst c); clear H_nat_inst.
        match goal with |[ H1 : _  = ?f |- _ = _;; ?g ;; ?h  ] => 
         pathvia (f;;g;;h) end.
        + clear H_nat_inst_c.
          simpl.
          repeat rewrite <- assoc.
          apply maponpaths.
          apply CoproductIn2Commutes_left_in_ctx_dir.
          simpl.
          unfold coproduct_nat_trans_in2_data, coproduct_nat_trans_data.
          assert (Hyp := τ_part_of_alg_mor _ hs CP _ _ _ (InitialArrow Alg IA (pr1 T'))).
          assert (Hyp_c := nat_trans_eq_pointwise _ _ _ _ _ _ Hyp c); clear Hyp.
          simpl in Hyp_c.
          eapply pathscomp0.
            eapply pathsinv0.
            exact Hyp_c.
          clear Hyp_c.
          apply maponpaths.
          apply pathsinv0.
          apply CoproductIn2Commutes.
        + rewrite <- H_nat_inst_c.
          apply idpath.
  - apply pathsinv0. 
    apply path_to_ctr.
    (* now a lot of serious verification work to be done *)
    apply nat_trans_eq; try (exact hs).
    intro c.
    simpl.
    rewrite id_right.
    (* look at type:
       match goal with | [ |- ?l = _ ] => let ty:= (type of l) in idtac ty end. *)
    apply CoproductArrow_eq_cor.
    + repeat rewrite <- assoc.
      apply CoproductIn1Commutes_right_in_ctx_dir.
      simpl.
      unfold coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data, coproduct_nat_trans_data.
      rewrite id_left.
      apply CoproductIn1Commutes_right_in_ctx_dir.

      simpl.
      repeat rewrite <- assoc.
      
      eapply pathscomp0.
Focus 2.
      apply maponpaths.
      apply CoproductIn1Commutes_right_in_ctx_dir.
      rewrite id_left.
      apply CoproductIn1Commutes_right_dir.
      apply idpath.

      do 2 rewrite assoc.
      eapply pathscomp0.
        apply cancel_postcomposition.
        assert (ptd_mor_commutes_inst := ptd_mor_commutes _ (ptd_from_alg_mor _ hs CP H β0) ((pr1 Z) c)). 
        apply ptd_mor_commutes_inst.
           
      eapply pathscomp0.
        eapply pathsinv0.
        assert (fbracket_η_inst := fbracket_η T' (f;; ptd_from_alg_mor _ hs CP H β0)).
        assert (fbracket_η_inst_c := nat_trans_eq_pointwise _ _ _ _ _ _ fbracket_η_inst c); clear fbracket_η_inst.
        apply fbracket_η_inst_c.
    
      rewrite functor_comp.
      apply idpath.
    + (* now the difficult case *)
      repeat rewrite <- assoc.
      apply CoproductIn2Commutes_right_in_ctx_dir.
      simpl.
      unfold coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data, coproduct_nat_trans_data.
      rewrite id_left.
      apply CoproductIn2Commutes_right_in_ctx_dir.
      unfold nat_trans_fix_snd_arg_data.
      simpl.
      unfold coproduct_nat_trans_in2_data.
      repeat rewrite <- assoc.
      
      eapply pathscomp0.
Focus 2.
      apply maponpaths.
      apply CoproductIn2Commutes_right_in_ctx_dir.
      rewrite <- assoc.
      apply maponpaths.
      apply CoproductIn2Commutes_right_dir.
      apply idpath. 
  
      do 2 rewrite assoc.
      eapply pathscomp0.
        apply cancel_postcomposition.
        eapply pathsinv0.
        assert (τ_part_of_alg_mor_inst := τ_part_of_alg_mor _ hs CP H _ _ β0).
        assert (τ_part_of_alg_mor_inst_Zc := nat_trans_eq_pointwise _ _ _ _ _ _  τ_part_of_alg_mor_inst ((pr1 Z) c)); clear τ_part_of_alg_mor_inst.
        apply τ_part_of_alg_mor_inst_Zc.
      
      simpl.   
      unfold coproduct_nat_trans_in2_data.  
      repeat rewrite <- assoc.
      eapply pathscomp0.
        apply maponpaths.
        rewrite assoc.
        eapply pathsinv0.
        assert (fbracket_τ_inst := fbracket_τ T' (f;; ptd_from_alg_mor _ hs CP H β0)).
        assert (fbracket_τ_inst_c := nat_trans_eq_pointwise _ _ _ _ _ _ fbracket_τ_inst c); clear fbracket_τ_inst.
        apply fbracket_τ_inst_c.

      simpl.
      unfold coproduct_nat_trans_in2_data.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      assert (Hyp: ((# (pr1 (ℓ(U Z))) (# H β));; (theta H) ((alg_carrier _ _  T') ⊗ Z);; # H (fbracket T' (f;; ptd_from_alg_mor C hs CP H β0)) = θ (tpair (λ _ : functor C C, ptd_obj C) (pr1 (pr1 IA)) Z) ;; # H (# (pr1 (ℓ(U Z))) β ;; fbracket T' (f;; ptd_from_alg_mor C hs CP H β0)))).
      
Focus 2.
      assert (Hyp_c := nat_trans_eq_pointwise _ _ _ _ _ _ Hyp c); clear Hyp. 
      exact Hyp_c.    

      clear c.
      rewrite (functor_comp H).
      rewrite assoc.
      apply cancel_postcomposition.
      fold θ.
      apply nat_trans_eq; try (exact hs).
      intro c.
      assert (θ_nat_1_pointwise_inst := θ_nat_1_pointwise _ hs H θ _ _ β Z c).
      eapply pathscomp0 ; [exact θ_nat_1_pointwise_inst | ].
      clear θ_nat_1_pointwise_inst.
      simpl.
      apply maponpaths.
      assert (Hyp: # H (β ∙∙ nat_trans_id (pr1 Z)) = # H (# (pr1 (ℓ(U Z))) β)).
      { apply maponpaths.
        apply nat_trans_eq; try (exact hs).
        intro c'.
        simpl.
        rewrite functor_id.
        apply id_right. }
      apply (nat_trans_eq_pointwise _ _ _ _ _ _ Hyp c).
Qed.

Definition hss_InitMor : ∀ T' : hss CP H, hssMor InitHSS T'.
Proof.
  intro T'.
  exists (InitialArrow Alg IA (pr1 T')).
  apply ishssMor_InitAlg.
Defined.

Lemma hss_InitMor_unique (T' : hss_precategory CP H):
  ∀ t : hss_precategory CP H ⟦ InitHSS, T' ⟧, t = hss_InitMor T'.
Proof.
  intro t.
  (* show lemma that says that two hss morphisms are equal if their underlying alg morphisms are *)
  apply (invmap (hssMor_eq1 _ _ _ _ _ _ _ _ )).
  set (T2:= pr2 IA).
  simpl in T2.
  set (T3 := T2 (pr1 T')).
  simpl.
  set (T4 := pr2 T3).
  simpl in T4.
  set (T5 := T4 (pr1 t)).
  apply T5.
Qed.

Lemma isInitial_InitHSS : isInitial (hss_precategory CP H) InitHSS.
Proof.
  intro T.
  exists (hss_InitMor T).
  apply hss_InitMor_unique.
Defined.

(*
  simpl.
  set (T' :=  (pr1 T)).
*)
(*
  assert (auxT' : ALG_from_Alg C hs CP H T' = pr1 T).
Focus 2.
 *)
(*
  set (β := InitialArrow _ IA T').
  (*set (β' := ALG_mor_from_Alg_mor _ hs CP _ β). *)
  refine (tpair _ _ _ ).
  - refine (tpair _ _ _ ).
    apply β.
    unfold ishssMor.
    unfold isbracketMor.
    intros Z f.
*)
    
(*

    + refine (tpair _ _ _ ).
      * apply β.
      * destruct β as [β βalg].
        assert (β_is_ptd := pr2 (pr1 β')).
        simpl in β_is_ptd.
        unfold is_ptd_mor in β_is_ptd. simpl in *.
        unfold is_ptd_mor. simpl.
        (* does not work: apply β_is_ptd.*)
        intro c.
        assert (β_is_ptd_inst := β_is_ptd c); clear β_is_ptd.
        eapply pathscomp0.
          exact  β_is_ptd_inst.
        clear β_is_ptd_inst.
        apply CoproductIn1Commutes.      
 *)
(*    
   + destruct β as [β βalg].
      simpl in *.
      unfold ishssMor. 
      split.
      * assert (β_isALGMor := pr2 β').
        unfold isALGMor. simpl.
        unfold isALGMor in β_isALGMor. simpl in β_isALGMor.
        eapply pathscomp0. Focus 2. apply β_isALGMor.
        apply maponpaths.
        apply pathsinv0.
        eapply pathscomp0.
        apply (CoproductIn2Commutes EndC). apply idpath.
      * simpl.
        unfold isbracketMor. simpl.
        intros Z f.
(*        destruct β as [β βalg]; simpl in *.
        unfold isbracketMor. simpl.
        intros Z f.        
*)
*)

        (* now define Ψ for fusion law *)


Lemma Ihss : Initial (hss_precategory CP H).
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


   
