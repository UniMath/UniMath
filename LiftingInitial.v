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

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Arguments functor_composite {_ _ _} _ _ .
Arguments nat_trans_comp {_ _ _ _ _} _ _ .
Local Notation "G ∙ F" := (functor_composite F G : [ _ , _ , _ ]) (at level 35).
Local Notation "α ∙∙ β" := (hor_comp β α) (at level 20).
Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Local Notation "Z ∘ α" := (post_whisker _ _ _ _ α Z) (at level 35).

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
Definition GG (Z : Ptd) (X : EndC) :=
  SpecialGenMendlerIteration _ _ _ IA EndC hsEndC X _ (KanExt Z) .


Definition θ_in_first_arg (Z: Ptd) := nat_trans_fix_snd_arg _ _ _ _ _ θ Z. 

Definition InitAlg : Alg := InitialObject _ IA.

Definition bracket_for_InitAlg : bracket _ _ H (ALG_from_Alg _ _ _ _ InitAlg).
Proof.
  intros Z f.
  set (GGG:= GG Z (pr1 InitAlg)).
  set (HHH := coproduct_functor _ _ CPEndC
                       (constant_functor _ _ (U Z))
                       H).
  set (G3 := GGG HHH).
  
  set (ρ := @CoproductArrow EndC _ _  (CPEndC (U Z) (H (pr1 InitAlg))) (pr1 InitAlg) (#U f)(CoproductIn2 _ _ ;; (alg_map _ _ InitAlg))).
  set (G4 := G3 ρ).

  set (EndEndC := [EndC, EndC, hsEndC]).
  set (CPEndEndC:= Coproducts_functor_precat _ _ CPEndC hsEndC: Coproducts EndEndC).
  set (θ' := CoproductOfArrows EndEndC (CPEndEndC _ _) (CPEndEndC _ _) (identity (constant_functor EndC _ (U Z): functor_precategory EndC EndC hsEndC)) (θ_in_first_arg Z)).

  (* simpl in θ'. *)

  idtac.

  
  
 (*
  assert (iso_1 : functor_composite Id_H (pre_composition_functor C C C hs hs (U Z)) ⟶  
                 coproduct_functor_data ([C, C] hs) ([C, C] hs) CPEndC
    (constant_functor ([C, C] hs) ([C, C] hs) (pr1 Z))
    (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_source H) Z) : EndEndC ⟦ _ , _ ⟧ ).
  { admit. }
  *)

  assert (iso_1 : EndEndC ⟦ functor_composite Id_H
                                        (pre_composition_functor C C C hs hs (U Z)),
                            CoproductObject EndEndC
           (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
              (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_source H) Z))
                          ⟧).
  {  admit. }

  
  assert (iso_2_inv : EndEndC ⟦
                           CoproductObject EndEndC
         (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
                    (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_target H) Z)),

                       functor_composite (pre_composition_functor C C C hs hs (U Z) )   HHH 
                           
                        ⟧).
  { admit . }
  set (G5:= G4 (iso_1 ;; θ' ;; iso_2_inv  )).


(*
  assert (type_of_θ'_ok : functor_composite Id_H (pre_composition_functor C C C hs hs (U Z))
           ⟶ functor_composite (pre_composition_functor C C C hs hs (U Z))
               HHH =  EndEndC
       ⟦ CoproductObject EndEndC
           (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
              (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_source H) Z)),
       CoproductObject EndEndC
         (CPEndEndC (constant_functor ([C, C] hs) ([C, C] hs) (U Z))
            (functor_fix_snd_arg ([C, C] hs) Ptd ([C, C] hs) (θ_target H) Z))
       ⟧).
   unfold precategory_morphisms.
   unfold EndEndC. simpl.
   unfold coproduct_functor_data at 3 4; simpl.
   admit.
 
  rewrite <- type_of_θ'_ok in θ'.  (* has to be done with transport so that the computational content does not get lost *)
  set (G5 := G4 θ').
 *)
  (*
  destruct G5 as [[h h_eq] h_unique].
  *)
  refine (tpair _ _ _ ).
  - refine (tpair _ _ _ ).
    + exact (pr1 (pr1 G5)).
    + (* the property in h_eq in the Alg world has to be translated into the ALG setting *)
      simpl.
      split.
      *  apply nat_trans_eq; try assumption.
         intro x; simpl.
         admit.
     * admit.
  - intros [h' [h'_eq1 h'_eq2]].
    simpl in *.
    apply total2_paths_second_isaprop.
    + apply isofhleveltotal2.
      * apply isaset_nat_trans. assumption.
      * intro.  apply isaset_nat_trans. assumption.
    + simpl.
      rewrite It_is_It_which_is_unique.
      apply path_to_ctr.
      apply nat_trans_eq; try assumption.
      intro c; simpl .
      
    (* now back translation of the data into an argument for h_unique (Alg view) *)
    admit.
Admitted.


Definition InitHSS : hss_precategory H.
Proof.
  red.
  unfold hss_precategory; simpl.
  exists (ALG_from_Alg _ _ _ _ InitAlg).
  exact bracket_for_InitAlg.
(* now universe problem when checking the definition *)
Admitted.

Lemma isInitial_InitHSS : isInitial (hss_precategory H) InitHSS.
Proof.
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


   
