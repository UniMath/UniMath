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
Require Import UniMath.RezkCompletion.limits.terminal.
Require Import UniMath.RezkCompletion.limits.initial.
Require Import UniMath.RezkCompletion.FunctorAlgebras.
Require Import SubstSystems.Auxiliary.
Require Import SubstSystems.PointedFunctors.
Require Import SubstSystems.ProductPrecategory.
Require Import SubstSystems.HorizontalComposition.
Require Import SubstSystems.PointedFunctorsComposition.
Require Import SubstSystems.Signatures.
(* Require Import SubstSystems.SubstitutionSystems. *)
Require Import SubstSystems.FunctorsPointwiseCoproduct.
Require Import SubstSystems.FunctorsPointwiseProduct.
Require Import SubstSystems.EndofunctorsMonoidal.
Require Import SubstSystems.SumOfSignatures.
Require Import SubstSystems.SubstitutionSystems_alt.
Require Import SubstSystems.LamSignature.
Require Import SubstSystems.LiftingInitial_alt.


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



Section Lambda.

Variable C : precategory.
Variable hs : has_homsets C.

(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hs]) .

Variable terminal : Terminal C.

Variable CC : Coproducts C.
Variable CP : Products C.

Local Notation "'EndC'":= ([C, C, hs]) .
Local Notation "'Ptd'" := (precategory_Ptd C hs).
Local Notation "'U'" := (functor_ptd_forget C hs).

Let hsEndC : has_homsets EndC := functor_category_has_homsets C C hs.
Let CPEndC : Coproducts EndC := Coproducts_functor_precat _ _ CC hs.
Let EndEndC := [EndC, EndC, hsEndC].
Let CPEndEndC:= Coproducts_functor_precat _ _ CPEndC hsEndC: Coproducts EndEndC.


Let one : C :=  @TerminalObject C terminal.

Variable KanExt : ∀ Z : precategory_Ptd C hs,
   RightKanExtension.GlobalRightKanExtensionExists C C
     ((functor_ptd_forget C hs) Z) C hs hs.


Let Lam_S : Signature _ _ := Lam_Sig C hs terminal CC CP.
Let LamE_S : Signature _ _ := LamE_Sig C hs terminal CC CP.

(* assume initial algebra for signature Lam *)

Variable Lam_Initial : Initial
     (precategory_FunctorAlg ([C, C] hs)
                             (Id_H C hs CC Lam_S) (functor_category_has_homsets C C hs)).

Let Lam := InitialObject _ Lam_Initial.


(* extract constructors *)


Definition Lam_Var : EndC ⟦functor_identity C, ob_from_algebra_ob _ _ Lam ⟧.
Proof.
  exact (CoproductIn1 _ _ ;; alg_map _ _ Lam).
Defined.

(* we later prefer leaving App and Abs bundled in the definition of LamE_algebra_on_Lam *)

Definition Lam_App : [C, C] hs ⟦ (App_H C hs CP) (ob_from_algebra_ob _ _ Lam) , ob_from_algebra_ob _ _ Lam ⟧.
Proof.
  exact (CoproductIn1 _ _ ;; CoproductIn2 _ _ ;; alg_map _ _ Lam).
Defined.

Definition Lam_Abs : [C, C] hs ⟦ (Abs_H C hs terminal CC) (ob_from_algebra_ob _ _ Lam), ob_from_algebra_ob _ _ Lam ⟧.
Proof.
  exact (CoproductIn2 _ _ ;; CoproductIn2 _ _ ;; alg_map _ _ Lam).
Defined.


Definition Lam_App_Abs :  [C, C] hs
   ⟦ (H C hs CC (App_H C hs CP) (Abs_H C hs terminal CC)) (ob_from_algebra_ob _ _ Lam) ,
   ob_from_algebra_ob _ _ Lam ⟧.
Proof.
  exact (CoproductIn2 _ _ ;; alg_map _ _ Lam).
Defined.


(* we need a flattening in order to get a model for LamE *)

Definition Lam_Flatten : 
  [C, C] hs ⟦ (Flat_H C hs) (ob_from_algebra_ob _ _ Lam) , ob_from_algebra_ob _ _ Lam ⟧.
Proof.
  admit.
Admitted.


(* now get a LamE-algebra *)


Definition LamE_algebra_on_Lam : precategory_FunctorAlg _ (Id_H _ _ CC LamE_S) hsEndC.
Proof.
  exists (ob_from_algebra_ob _ _  (InitialObject _ Lam_Initial)).
  simpl.
  refine (CoproductArrow _ (CPEndC _ _ )  _ _ ) .
  + exact Lam_Var.
  + refine (CoproductArrow _ (CPEndC _ _ )  _ _ ).
    * apply Lam_App_Abs. (* do NOT destruct and reassemble more, use App_Abs directly *)
    * apply Lam_Flatten.
Defined.



(* now define bracket operation for a given [Z] and [f] *)

Definition fbracket_for_LamE_algebra_on_Lam (Z : Ptd)
   (f : Ptd ⟦ Z, ptd_from_alg C hs CC LamE_S LamE_algebra_on_Lam ⟧ ) :
   [C, C] hs
   ⟦ functor_composite (U Z)
       (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam),
     ob_from_algebra_ob _ _ LamE_algebra_on_Lam ⟧ .
Proof.
  admit.
Admitted.


(* above fbracket satisfies diagram *)

Lemma fbracket_diagram (Z : Ptd)
  (f : Ptd ⟦ Z, ptd_from_alg C hs CC LamE_S LamE_algebra_on_Lam ⟧)
  :
   # (pre_composition_functor_data C C C hs hs (U Z))
     (alg_map ([C, C] hs)
        (coproduct_functor ([C, C] hs) ([C, C] hs)
           (Coproducts_functor_precat C C CC hs)
           (constant_functor ([C, C] hs) ([C, C] hs) (functor_identity C))
           LamE_S) LamE_algebra_on_Lam);;
   fbracket_for_LamE_algebra_on_Lam Z f =
   CoproductOfArrows ([C, C] hs)
     (Coproducts_functor_precat C C CC hs (U Z)
        ((θ_source LamE_S)
           (prodcatpair C hs
              (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam) Z)))
     (Coproducts_functor_precat C C CC hs (U Z)
        ((θ_target LamE_S)
           (prodcatpair C hs
              (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam) Z)))
     (identity (U Z))
     ((theta LamE_S)
        (prodcatpair C hs
           (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam) Z));;
   CoproductOfArrows ([C, C] hs)
     (Coproducts_functor_precat C C CC hs (U Z)
        (LamE_S
           (functor_composite (U Z)
              (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam))))
     (Coproducts_functor_precat C C CC hs (U Z) (LamE_S (ob_from_algebra_ob _ _ LamE_algebra_on_Lam)))
     (identity (U Z)) (# LamE_S (fbracket_for_LamE_algebra_on_Lam Z f));;
   CoproductArrow ([C, C] hs)
     (Coproducts_functor_precat C C CC hs (U Z) (LamE_S (ob_from_algebra_ob _ _ LamE_algebra_on_Lam)))
     (# U f) (tau_from_alg C hs CC LamE_S LamE_algebra_on_Lam).
Proof.
  admit.
Admitted.

(* bundle fbracket and its property *)

Definition fbracket_with_property (Z : Ptd)
  (f : Ptd ⟦ Z, ptd_from_alg C hs CC LamE_S LamE_algebra_on_Lam ⟧)
:
   Σ
   h : [C, C] hs
       ⟦ functor_composite (U Z)
           (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam),
       (ob_from_algebra_ob _ _ LamE_algebra_on_Lam) ⟧,
   # (pre_composition_functor_data C C C hs hs (U Z))
     (alg_map ([C, C] hs)
        (coproduct_functor ([C, C] hs) ([C, C] hs)
           (Coproducts_functor_precat C C CC hs)
           (constant_functor ([C, C] hs) ([C, C] hs) (functor_identity C))
           LamE_S) LamE_algebra_on_Lam);; h =
   CoproductOfArrows ([C, C] hs)
     (Coproducts_functor_precat C C CC hs (U Z)
        ((θ_source LamE_S)
           (prodcatpair C hs
              (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam) Z)))
     (Coproducts_functor_precat C C CC hs (U Z)
        ((θ_target LamE_S)
           (prodcatpair C hs
              (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam) Z)))
     (identity (U Z))
     ((theta LamE_S)
        (prodcatpair C hs
           (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam) Z));;
   CoproductOfArrows ([C, C] hs)
     (Coproducts_functor_precat C C CC hs (U Z)
        (LamE_S
           (functor_composite (U Z)
              (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam))))
     (Coproducts_functor_precat C C CC hs (U Z) (LamE_S (ob_from_algebra_ob _ _ LamE_algebra_on_Lam)))
     (identity (U Z)) (# LamE_S h);;
   CoproductArrow ([C, C] hs)
     (Coproducts_functor_precat C C CC hs (U Z) (LamE_S (ob_from_algebra_ob _ _ LamE_algebra_on_Lam)))
     (# U f) (tau_from_alg C hs CC LamE_S LamE_algebra_on_Lam).
Proof.
  exists (fbracket_for_LamE_algebra_on_Lam Z f).
  exact (fbracket_diagram Z f).
Defined.

(* fbracket is unique *)

Lemma fbracket_LamE_unique (Z : Ptd)
  (f : Ptd ⟦ Z, ptd_from_alg C hs CC LamE_S LamE_algebra_on_Lam ⟧)
:
   ∀
   t : Σ
       h : [C, C] hs
           ⟦ functor_composite (U Z)
               (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam),
           ob_from_algebra_ob _ _ LamE_algebra_on_Lam ⟧,
       # (pre_composition_functor_data C C C hs hs (U Z))
         (alg_map ([C, C] hs)
            (coproduct_functor ([C, C] hs) ([C, C] hs)
               (Coproducts_functor_precat C C CC hs)
               (constant_functor ([C, C] hs) ([C, C] hs) (functor_identity C))
               LamE_S) LamE_algebra_on_Lam);; h =
       CoproductOfArrows ([C, C] hs)
         (Coproducts_functor_precat C C CC hs (U Z)
            ((θ_source LamE_S)
               (prodcatpair C hs
                  (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam)
                  Z)))
         (Coproducts_functor_precat C C CC hs (U Z)
            ((θ_target LamE_S)
               (prodcatpair C hs
                  (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam)
                  Z))) (identity (U Z))
         ((theta LamE_S)
            (prodcatpair C hs
               (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam) Z));;
       CoproductOfArrows ([C, C] hs)
         (Coproducts_functor_precat C C CC hs (U Z)
            (LamE_S
               (functor_composite (U Z)
                  (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam))))
         (Coproducts_functor_precat C C CC hs (U Z)
            (LamE_S (ob_from_algebra_ob _ _ LamE_algebra_on_Lam))) (identity (U Z)) 
         (# LamE_S h);;
       CoproductArrow ([C, C] hs)
         (Coproducts_functor_precat C C CC hs (U Z)
            (LamE_S (ob_from_algebra_ob _ _ LamE_algebra_on_Lam))) (# U f)
         (tau_from_alg C hs CC LamE_S LamE_algebra_on_Lam),
   t =
   tpair
     (λ h : [C, C] hs
            ⟦ functor_composite (U Z)
                (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam),
            (ob_from_algebra_ob _ _ LamE_algebra_on_Lam) ⟧,
      # (pre_composition_functor_data C C C hs hs (U Z))
        (alg_map ([C, C] hs)
           (coproduct_functor ([C, C] hs) ([C, C] hs)
              (Coproducts_functor_precat C C CC hs)
              (constant_functor ([C, C] hs) ([C, C] hs) (functor_identity C))
              LamE_S) LamE_algebra_on_Lam);; h =
      CoproductOfArrows ([C, C] hs)
        (Coproducts_functor_precat C C CC hs (U Z)
           ((θ_source LamE_S)
              (prodcatpair C hs
                 (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam)
                 Z)))
        (Coproducts_functor_precat C C CC hs (U Z)
           ((θ_target LamE_S)
              (prodcatpair C hs
                 (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam)
                 Z))) (identity (U Z))
        ((theta LamE_S)
           (prodcatpair C hs
              (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam) Z));;
      CoproductOfArrows ([C, C] hs)
        (Coproducts_functor_precat C C CC hs (U Z)
           (LamE_S
              (functor_composite (U Z)
                 (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam))))
        (Coproducts_functor_precat C C CC hs (U Z)
           (LamE_S (ob_from_algebra_ob _ _ LamE_algebra_on_Lam))) (identity (U Z)) 
        (# LamE_S h);;
      CoproductArrow ([C, C] hs)
        (Coproducts_functor_precat C C CC hs (U Z)
           (LamE_S (ob_from_algebra_ob _ _ LamE_algebra_on_Lam))) (# U f)
        (tau_from_alg C hs CC LamE_S LamE_algebra_on_Lam))
     (fbracket_for_LamE_algebra_on_Lam Z f) (fbracket_diagram Z f)
.
Proof.
  intro t.
  apply total2_paths_second_isaprop.
  apply isaset_nat_trans. apply hs.
  simpl.
  destruct t as [t Ht]; simpl.
  admit.
Admitted.
  
Definition bracket_for_LamE_algebra_on_Lam : bracket C hs CC LamE_S LamE_algebra_on_Lam.
Proof.
  intros Z f.
  simpl.
  exists (fbracket_with_property Z f).
  apply fbracket_LamE_unique.
Defined.
  
Definition LamE_model_on_Lam : hss CC LamE_S.
Proof.
  exists LamE_algebra_on_Lam.
  exact bracket_for_LamE_algebra_on_Lam.
Defined.



(*  this is only needed later, so comment out for the time being *)
(*
Variable  LamE_Initial : Initial
     (precategory_FunctorAlg ([C, C] hs)
        (Id_H C hs CC LamE_S) (functor_category_has_homsets C C hs)).


Definition LamE : Initial (hss_precategory CC LamE_S).
Proof.
  apply  Ihss.
  - apply KanExt.
  - apply LamE_Initial.
Defined.
*)



End Lambda.
