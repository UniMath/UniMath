Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.
Require Import SubstSystems.UnicodeNotations.
Require Import UniMath.RezkCompletion.whiskering.
(*Require Import UniMath.RezkCompletion.Monads.*)
Require Import UniMath.RezkCompletion.limits.products.
Require Import UniMath.RezkCompletion.limits.coproducts.
Require Import UniMath.RezkCompletion.limits.terminal.
Require Import UniMath.RezkCompletion.limits.initial.
Require Import UniMath.RezkCompletion.FunctorAlgebras.
Require Import SubstSystems.Auxiliary.
Require Import SubstSystems.PointedFunctors.
Require Import SubstSystems.ProductPrecategory.
(*Require Import SubstSystems.HorizontalComposition.*)
(*Require Import SubstSystems.PointedFunctorsComposition.*)
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
(*Local Notation "α ∙∙ β" := (hor_comp β α) (at level 20).*)
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
                             (Id_H C hs CC Lam_S) hsEndC).

Let Lam := InitialObject _ Lam_Initial.
Local Notation "` XX" := (ob_from_algebra_ob _ _ XX) (at level 3).
About "`".
(*
(* assume initial algebra for signature LamE *)

Variable  LamE_Initial : Initial
     (precategory_FunctorAlg ([C, C] hs)
        (Id_H C hs CC LamE_S) hsEndC).


Definition LamEHSS_Initial : Initial (hss_precategory CC LamE_S).
Proof.
  apply  Ihss.
  - apply KanExt.
  - apply LamE_Initial.
Defined.
Let LamEHSS := InitialObject _ LamEHSS_Initial.
*)


(* bracket for Lam from the initial hss obtained via theorem 15+ *)

Definition LamHSS_Initial : Initial (hss_precategory CC Lam_S).
Proof.
  apply  Ihss.
  - apply KanExt.
  - apply Lam_Initial.
Defined.
Let LamHSS := InitialObject _ LamHSS_Initial.

(* extract constructors *)


Definition Lam_Var : EndC ⟦functor_identity C, `Lam ⟧.
Proof.
  exact (CoproductIn1 _ _ ;; alg_map _ _ Lam).
Defined.

(* we later prefer leaving App and Abs bundled in the definition of LamE_algebra_on_Lam *)

Definition Lam_App : [C, C] hs ⟦ (App_H C hs CP) `Lam , `Lam ⟧.
Proof.
  exact (CoproductIn1 _ _ ;; (CoproductIn2 _ _ ;; alg_map _ _ Lam)).
Defined.

Definition Lam_Abs : [C, C] hs ⟦ (Abs_H C hs terminal CC) `Lam, `Lam ⟧.
Proof.
  exact (CoproductIn2 _ _ ;; (CoproductIn2 _ _ ;; alg_map _ _ Lam)).
Defined.


Definition Lam_App_Abs :  [C, C] hs
   ⟦ (H C hs CC (App_H C hs CP) (Abs_H C hs terminal CC)) `Lam , `Lam ⟧.
Proof.
  exact (CoproductIn2 _ _ ;; alg_map _ _ Lam).
Defined.


(* we need a flattening in order to get a model for LamE *)

Definition Lam_Flatten : 
  [C, C] hs ⟦ (Flat_H C hs) `Lam , `Lam ⟧.
Proof.
  exact (fbracket LamHSS (identity _ )).
Defined.


(* now get a LamE-algebra *)

Definition LamE_algebra_on_Lam : precategory_FunctorAlg _ (Id_H _ _ CC LamE_S) hsEndC.
Proof.
  exists ((*ob_from_algebra_ob _ _*) `Lam).
  refine (CoproductArrow _ (CPEndC _ _ )  _ _ ) .
  + exact Lam_Var.
  + refine (CoproductArrow _ (CPEndC _ _ )  _ _ ).
    * apply Lam_App_Abs. (* do NOT destruct and reassemble more, use App_Abs directly *)
    * apply Lam_Flatten.
Defined.



(* now define bracket operation for a given [Z] and [f] *)

(* preparations for typedness *)
Definition bla': (ptd_from_alg_functor C hs CC LamE_S LamE_algebra_on_Lam) ⇒ (ptd_from_alg_functor C hs CC _ Lam).
Proof.
  refine (tpair _ _ _ ).
    + apply (nat_trans_id _ ). 
    + intro c; simpl. rewrite id_right.
      apply CoproductIn1Commutes_left_dir.
      apply idpath.
Defined.

Definition bla'_inv: (ptd_from_alg_functor C hs CC _ Lam) ⇒ (ptd_from_alg_functor C hs CC LamE_S LamE_algebra_on_Lam).
Proof.
  refine (tpair _ _ _ ).
    + apply (nat_trans_id _ ). 
    + intro c; simpl. rewrite id_right.
      apply CoproductIn1Commutes_right_dir.
      apply idpath.
Defined.

(* this iso does nothing, but is needed to make the argument to [fbracket] below well-typed *)
(* maybe a better definition somewhere above could make this iso superfluous *)
(* maybe don't need iso, but only morphism *)
Definition bla : iso (ptd_from_alg_functor C hs CC LamE_S LamE_algebra_on_Lam) (ptd_from_alg_functor C hs CC _ Lam).
Proof.
  unfold iso.
  exists bla'.
  unfold is_iso.
  intro Z.
  apply (gradth _ (precomp_with bla'_inv)).
  + intro α.
    apply eq_ptd_mor_precat.
    apply (invmap (eq_ptd_mor _ hs _ _)). 
    apply nat_trans_eq; try (exact hs).
    intro c.
    simpl.
    rewrite id_left.
    apply id_left.
  + intro α.
    apply eq_ptd_mor_precat.
    apply (invmap (eq_ptd_mor _ hs _ _)). 
    apply nat_trans_eq; try (exact hs).
    intro c.
    simpl.
    rewrite id_left.
    apply id_left.
Defined.

(* earlier attempt:
Lemma bla :  iso (ptd_from_alg_functor C hs CC LamE_S LamE_algebra_on_Lam) (ptd_from_alg_functor C hs CC _ Lam).
Proof.
  refine (tpair _ _ _ ).
  (* apply ptd_id. *) (* is ill-typed - that is the whole problem *)
  - refine (tpair _ _ _ ).
    + apply (nat_trans_id _ ). 
    + intro c; simpl. rewrite id_right.
      apply CoproductIn1Commutes_left_dir.
      apply idpath.
  - admit.    
Admitted.
*)

Definition fbracket_for_LamE_algebra_on_Lam (Z : Ptd)
   (f : Ptd ⟦ Z, ptd_from_alg_functor C hs CC LamE_S LamE_algebra_on_Lam ⟧ ) :
   [C, C] hs
   ⟦ functor_composite (U Z)
       (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam),
     ob_from_algebra_ob _ _ LamE_algebra_on_Lam ⟧ .
Proof.
  exact (fbracket LamHSS (f ;; bla)).
Defined.


Lemma bracket_property_for_LamE_algebra_on_Lam (Z : Ptd)
  (f : Ptd ⟦ Z, ptd_from_alg C hs CC LamE_S LamE_algebra_on_Lam ⟧)
 :
   bracket_property C hs CC LamE_S LamE_algebra_on_Lam f
                    (fbracket_for_LamE_algebra_on_Lam Z f).
Proof.
  assert (Hyp := pr2 (pr1 (pr2 LamHSS _ (f;; bla)))).
  apply parts_from_whole in Hyp.
  apply whole_from_parts.
  split.
  + (* the "easy" eta part *)
    apply pr1 in Hyp.
    apply (maponpaths (fun x => x;; #U (inv_from_iso bla))) in Hyp.
    rewrite <- functor_comp in Hyp.
    rewrite <- assoc in Hyp.
    rewrite iso_inv_after_iso in Hyp.
    rewrite id_right in Hyp.
    eapply pathscomp0.
      exact Hyp.
    clear Hyp.
    fold (fbracket LamHSS (f ;; bla)).
    unfold fbracket_for_LamE_algebra_on_Lam.
    match goal with |[ |- _;; _ ;; ?h = _  ] => 
         assert (idness : h = nat_trans_id _) end.
      apply nat_trans_eq; try (exact hs).
      intro c.
      unfold functor_ptd_forget.
      simpl.
      apply id_left.
    rewrite idness. clear idness.
    rewrite id_right.
    (* does not work:
       apply cancel_postcomposition.
       although the terms are of identical type:
    match goal with | [ |- _ ;; ?l = _ ] => let ty:= (type of l) in idtac ty end.
(*
([C, C] hs
 ⟦ functor_composite (U Z) (functor_from_algebra_ob C hs CC Lam_S LamHSS)
   :[C, C] hs, LamHSS ⟧)
*)
    match goal with | [ |- _ = _ ;; ?l ] => let ty:= (type of l) in idtac ty end.
(*
([C, C] hs
 ⟦ functor_composite (U Z) (functor_from_algebra_ob C hs CC Lam_S LamHSS)
   :[C, C] hs, LamHSS ⟧)
*)
*)
    apply nat_trans_eq; try (exact hs).
    intro c.
    simpl.
    apply cancel_postcomposition.
    apply CoproductIn1Commutes_right_dir.
    apply idpath.   
    (* this proof did not work with pointedness but with brute force *)
  + (* now the difficult case of the domain-specific constructors *)
    
(*
  match goal with | [ |- ?l = _ ] => let ty:= (type of l) in idtac ty end.
  match goal with | [ H1: ?l = _ |- _] => let ty:= (type of l) in idtac ty end.
*)
  admit.
Admitted.

Lemma bracket_for_LamE_algebra_on_Lam_unique (Z : Ptd)
  (f : Ptd ⟦ Z, ptd_from_alg C hs CC LamE_S LamE_algebra_on_Lam ⟧)
 :
   ∀
   t : Σ
       h : [C, C] hs
           ⟦ functor_composite (U Z)
               (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam),
           `LamE_algebra_on_Lam ⟧,
       bracket_property C hs CC LamE_S LamE_algebra_on_Lam f h,
   t =
   tpair
     (λ h : [C, C] hs
            ⟦ functor_composite (U Z)
                (functor_from_algebra_ob C hs CC LamE_S LamE_algebra_on_Lam),
            `LamE_algebra_on_Lam ⟧,
      bracket_property C hs CC LamE_S LamE_algebra_on_Lam f h)
     (fbracket_for_LamE_algebra_on_Lam Z f) (bracket_property_for_LamE_algebra_on_Lam Z f).
Proof.
  intro t.
  apply total2_paths_second_isaprop.
  apply isaset_nat_trans. apply hs.
  simpl.
  destruct t as [t Ht]; simpl.
  admit.
Admitted.

Definition bracket_for_LamE_algebra_on_Lam_at (Z : Ptd)
  (f : Ptd ⟦ Z, ptd_from_alg C hs CC LamE_S LamE_algebra_on_Lam ⟧)
  :
    bracket_at C hs CC LamE_S LamE_algebra_on_Lam f.
Proof.
  refine (tpair _ _ _ ).
  - exists (fbracket_for_LamE_algebra_on_Lam Z f).
    apply (bracket_property_for_LamE_algebra_on_Lam Z f).
  - apply bracket_for_LamE_algebra_on_Lam_unique.
Defined.
  
Definition bracket_for_LamE_algebra_on_Lam : bracket C hs CC LamE_S LamE_algebra_on_Lam.
Proof.
  intros Z f.
  simpl.
  apply bracket_for_LamE_algebra_on_Lam_at.
Defined.
  
Definition LamE_model_on_Lam : hss CC LamE_S.
Proof.
  exists LamE_algebra_on_Lam.
  exact bracket_for_LamE_algebra_on_Lam.
Defined.


End Lambda.
