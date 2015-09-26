Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functor_categories.
Require Import UniMath.SubstitutionSystems.UnicodeNotations.
Require Import UniMath.RezkCompletion.whiskering.
Require Import UniMath.RezkCompletion.limits.products.
Require Import UniMath.RezkCompletion.limits.coproducts.
Require Import UniMath.RezkCompletion.limits.terminal.
Require Import UniMath.RezkCompletion.limits.initial.
Require Import UniMath.RezkCompletion.FunctorAlgebras.
Require Import UniMath.SubstitutionSystems.Auxiliary.
Require Import UniMath.SubstitutionSystems.PointedFunctors.
Require Import UniMath.SubstitutionSystems.ProductPrecategory.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.FunctorsPointwiseCoproduct.
Require Import UniMath.SubstitutionSystems.FunctorsPointwiseProduct.
Require Import UniMath.SubstitutionSystems.EndofunctorsMonoidal.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.LiftingInitial.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.


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
Local Notation "` T" := (alg_carrier _ _ T) (at level 3).
Local Notation "A ⊗ B" := (prodcatpair _ _ A B) (at level 10).



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


Local Notation "'ℓ'" := (pre_composition_functor_data _ _ _ _ _ ).

Local Notation "'τ'" := (tau_from_alg _ _ _ _ ).

Let one : C :=  @TerminalObject C terminal.

Variable KanExt : ∀ Z : precategory_Ptd C hs,
   RightKanExtension.GlobalRightKanExtensionExists C C
     (U Z) C hs hs.


Let Lam_S : Signature _ _ := Lam_Sig C hs terminal CC CP.
Let LamE_S : Signature _ _ := LamE_Sig C hs terminal CC CP.

(* assume initial algebra for signature Lam *)

Variable Lam_Initial : Initial
     (precategory_FunctorAlg ([C, C] hs)
                             (Id_H C hs CC Lam_S) hsEndC).

Let Lam := InitialObject _ Lam_Initial.




(* bracket for Lam from the initial hss obtained via theorem 15+ *)

Definition LamHSS_Initial : Initial (hss_precategory CC Lam_S).
Proof.
  apply Ihss.
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

Lemma τ_LamE_algebra_on_Lam : τ LamE_algebra_on_Lam =
                              CoproductArrow _ (CPEndC _ _ ) Lam_App_Abs Lam_Flatten.
Proof.
  apply CoproductIn2Commutes.
Defined.


(* now define bracket operation for a given [Z] and [f] *)

(* preparations for typedness *)
Definition bla': (ptd_from_alg_functor C hs CC LamE_S LamE_algebra_on_Lam) ⇒ (ptd_from_alg_functor C hs CC _ Lam).
Proof.
  refine (tpair _ _ _ ).
    + apply (nat_trans_id _ ). 
    + abstract
        (intro c; rewrite id_right (* should be opaque *)
         ; apply CoproductIn1Commutes_left_dir;
         apply idpath).
Defined.

Definition bla'_inv: (ptd_from_alg_functor C hs CC _ Lam) ⇒ (ptd_from_alg_functor C hs CC LamE_S LamE_algebra_on_Lam).
Proof.
  refine (tpair _ _ _ ).
    + apply (nat_trans_id _ ). 
    + abstract
        (intro c; rewrite id_right ; (* should be opaque *)
         apply CoproductIn1Commutes_right_dir;
         apply idpath) .
Defined.

(* this iso does nothing, but is needed to make the argument to [fbracket] below well-typed *)
(* maybe a better definition somewhere above could make this iso superfluous *)
(* maybe don't need iso, but only morphism *)
Definition bla : iso (ptd_from_alg_functor C hs CC LamE_S LamE_algebra_on_Lam) (ptd_from_alg_functor C hs CC _ Lam).
Proof.
  unfold iso.
  exists bla'.
  apply is_iso_from_is_z_iso.
  exists bla'_inv.
  abstract (
   split; [
    apply (invmap (eq_ptd_mor _ hs _ _));
    apply nat_trans_eq; try (exact hs) ;
    intro c ;
    apply id_left
                   |
    apply eq_ptd_mor_precat; (* idem *)
    apply (invmap (eq_ptd_mor _ hs _ _)) ;
    apply nat_trans_eq; try (exact hs) ;
    intro c ;
    apply id_left ]
           ).
Defined.

(* A simple but important lemma *)

Definition fbracket_for_LamE_algebra_on_Lam (Z : Ptd)
   (f : Ptd ⟦ Z, ptd_from_alg_functor C hs CC LamE_S LamE_algebra_on_Lam ⟧ ) :
   [C, C] hs
   ⟦ functor_composite (U Z) `LamE_algebra_on_Lam, `LamE_algebra_on_Lam ⟧ .
Proof.
  exact (fbracket LamHSS (f ;; bla)).
Defined.


Lemma bracket_property_for_LamE_algebra_on_Lam (Z : Ptd)
  (f : Ptd ⟦ Z, ptd_from_alg C hs CC LamE_S LamE_algebra_on_Lam ⟧)
 :
   bracket_property C hs CC LamE_S LamE_algebra_on_Lam f
                    (fbracket_for_LamE_algebra_on_Lam Z f).
Proof.
  (* Could we have this in a more declarative style? *)
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
    apply cancel_postcomposition.
    apply CoproductIn1Commutes_right_dir.
    apply idpath.   
    (* this proof did not work with pointedness but with brute force *)
  + (* now the difficult case of the domain-specific constructors *)
    destruct Hyp as [_ Hyp2].
    fold (fbracket LamHSS (f ;; bla)) in Hyp2.
    unfold fbracket_for_LamE_algebra_on_Lam.
    apply nat_trans_eq; try (exact hs).
    intro c.

    (* from here slightly interesting, because it is crucial to see that
       the τ considered here is a Coproduct arrow *)
    
    rewrite τ_LamE_algebra_on_Lam.
    eapply pathscomp0; [apply cancel_postcomposition ; apply CoproductOfArrows_comp | ].
    idtac.
    eapply pathscomp0.
    apply precompWithCoproductArrow.
    apply pathsinv0.

    (* showing that a diagram of coproduct arrows splits into two is slightly cumbersome,
       but a general theorem seems difficult to formulate

       instead we apply [CoproductArrowUnique] and then use the coproduct beta laws in 
       each branch; this gives precisely what we want *)
    
    apply CoproductArrowUnique.
  - eapply pathscomp0. apply assoc.
    eapply pathscomp0.
    apply cancel_postcomposition. apply CoproductIn1Commutes.
    assert (T:= nat_trans_eq_pointwise _ _ _ _ _ _ Hyp2 c).
    clear Hyp2.
    match goal with | [H : ?e = _ |- _ ] => transitivity e end.
    Focus 2. apply idpath.

    match goal with | [H : _ = ?f |- _ ] => transitivity f end.
    Focus 1. apply idpath.
    apply pathsinv0. assumption.
    
    
    (* There should be a more general hypothesis than 'Hyp' defined above,
       one where one has a quantification over maps 'f', no? *)

  - clear Hyp2.
    eapply pathscomp0. apply assoc.
    eapply pathscomp0.
    apply cancel_postcomposition. apply CoproductIn2Commutes.
    unfold Lam_Flatten.
    (* now we have the equation that is mentioned in the documents *)

    (* maybe make a better writeup of the proof before proceeding here ?*)

    (* from here on not sure how to proceed, but 'simpl' is feasible 
       after some opacification, at least *)
    Opaque fbracket.
    Opaque LamHSS.
    set (X:= f ;; bla).
    
    assert (TT:=compute_fbracket C hs CC Lam_S LamHSS(Z:=Z)).
    simpl in *.
    assert (T3 := TT  X).
    clear TT.
    unfold X; unfold X in T3; clear X.
    rewrite id_left.
    rewrite id_left.
    rewrite id_left.

    Local Notation "⦃ f ⦄" := (fbracket _ f)(at level 0).
    (* written '\{{' and '\}}', respectively *)

    set (Tη := ptd_from_alg C hs CC Lam_S _ ).

    rewrite functor_id.
    rewrite functor_id.
    rewrite id_right.
    destruct Z as [Z e]. simpl in *.
    set (T := ` Lam).


    (* now we want to rewrite with T3 in 3 places *)
    
    assert (T3':= nat_trans_eq_pointwise _ _ _ _ _ _ T3 c).
    simpl in *.
    match goal with |[ T3' : _ = ?f |- ?a ;; _ = _ ] => transitivity (a ;; f) end.
    { apply maponpaths. apply T3'. }
    
    repeat rewrite assoc.
(*
    apply cancel_postcomposition. (* that's a bad idea, because it fucks up use of third monad law *)
*)
    
    match goal with |[ T3' : _ = ?f |- _ = ?a ;; ?b ;; _ ;; ?d  ] => transitivity (a ;; b ;; #T f ;; d) end.
    Focus 2.  apply cancel_postcomposition. apply maponpaths. apply maponpaths. apply (!T3'). 
    clear T3'.

    apply pathsinv0.

    assert (T3':= nat_trans_eq_pointwise _ _ _ _ _ _ T3 (T (Z c))).
    
    eapply pathscomp0. apply cancel_postcomposition. apply cancel_postcomposition. 
                       apply maponpaths. apply T3'.

    clear T3'.                   
    apply pathsinv0.

    destruct f as [f fptdmor]. simpl in *.
    simpl.

    rewrite id_right.
    rewrite id_right.

    repeat rewrite assoc.

    assert (X := fptdmor (T (Z c))). clear T3 fptdmor.
    assert (X' := maponpaths (#T) X).
    rewrite functor_comp in X'.

    apply pathsinv0.
    eapply pathscomp0. apply cancel_postcomposition. apply cancel_postcomposition.
                       apply cancel_postcomposition. apply X'.
                       clear X'.

    clear X.
    
    assert (X := Monad_law_2_from_hss _ _ CC Lam_S LamHSS (T (Z c))).
    unfold μ_0 in X. unfold μ_2 in X.

    match goal with |[ X : ?e = _ |- ?a ;; ?b ;; _ ;; _  = _ ] =>
                     assert (X' : e = a ;; b) end.
    { apply cancel_postcomposition. apply maponpaths.
      simpl.
      unfold coproduct_nat_trans_in1_data. simpl.
      repeat rewrite  assoc.
      unfold coproduct_nat_trans_data.
      apply pathsinv0. eapply pathscomp0. apply CoproductIn1Commutes.
      apply idpath. }

    rewrite X' in X. clear X'.

    eapply pathscomp0. apply cancel_postcomposition. apply cancel_postcomposition. apply X. clear X.

    rewrite id_left.

    assert (μ_2_nat := nat_trans_ax (μ_2 C hs CC Lam_S LamHSS)).
    assert (X := μ_2_nat _ _ (f c)).
    unfold μ_2 in X.

    eapply pathscomp0. Focus 2. apply cancel_postcomposition. apply X. clear X.

    rewrite functor_comp.
    repeat rewrite <- assoc.
    apply maponpaths.

    
    assert (X := third_monad_law_from_hss _ _ CC Lam_S LamHSS).
    assert (X' := nat_trans_eq_pointwise _ _ _ _ _ _ X). clear X.
    simpl in X'.

    eapply pathscomp0. apply X'.

    rewrite id_left. apply idpath.


    
 (*   
    Check θ.
    Arguments θ {_ _ _ _ _ } _ _ .
    idtac.
    Opaque θ.
    Opaque fbracket.
    simpl.
    unfold coproduct_nat_trans_in2_data.
    
    unfold Flat_H. simpl.

    simpl.

    unfold coproduct_nat_trans_data. simpl.
    unfold coproduct_nat_trans_in1_data.
    unfold product_nat_trans_data.

    simpl.
    
    rewrite assoc.

    unfold bla1.

    rewrite id_left.
    
    unfold coproduct_nat_trans_data. simpl.
*)

(*
    apply nat_trans_eq; try (exact hs).
    intro c.
    simpl.
    apply CoproductArrow_eq_cor.
    simpl.
    repeat rewrite <- assoc.
    apply CoproductIn1Commutes_left_in_ctx_dir.



    unfold LamE_S. unfold LamE_Sig.


(*
  match goal with | [ |- ?l = _ ] => let ty:= (type of l) in idtac ty end.
  match goal with | [ H1: ?l = _ |- _] => let ty:= (type of l) in idtac ty end.
*)

 *)

Qed.

Lemma bracket_for_LamE_algebra_on_Lam_unique (Z : Ptd)
  (f : Ptd ⟦ Z, ptd_from_alg C hs CC LamE_S LamE_algebra_on_Lam ⟧)
 :
   ∀
   t : Σ
       h : [C, C] hs
           ⟦ functor_composite (U Z)
               (` LamE_algebra_on_Lam),
           `LamE_algebra_on_Lam ⟧,
       bracket_property C hs CC LamE_S LamE_algebra_on_Lam f h,
   t =
   tpair
     (λ h : [C, C] hs
            ⟦ functor_composite (U Z)
                (` LamE_algebra_on_Lam),
            `LamE_algebra_on_Lam ⟧,
      bracket_property C hs CC LamE_S LamE_algebra_on_Lam f h)
     (fbracket_for_LamE_algebra_on_Lam Z f) (bracket_property_for_LamE_algebra_on_Lam Z f).
Proof.
  intro t.
  apply total2_paths_second_isaprop.
  apply isaset_nat_trans. apply hs.
  simpl.
  destruct t as [t Ht]; simpl.
  unfold fbracket_for_LamE_algebra_on_Lam.
  apply (fbracket_unique LamHSS).
  split.
  -  apply parts_from_whole in Ht. destruct Ht as [H1 _].
     apply nat_trans_eq; try assumption.
     intro c.
     assert (HT:=nat_trans_eq_pointwise _ _ _ _ _ _ H1 c).
     simpl.
     rewrite id_right.
     match goal with |[ H : _ = ?a |- _ ] => transitivity a end.
     + apply HT.
     + simpl. repeat rewrite assoc. apply cancel_postcomposition.
       repeat rewrite <- assoc.
       unfold coproduct_nat_trans_in1_data.
       unfold coproduct_nat_trans_data.
       eapply pathscomp0. apply CoproductIn1Commutes.
       apply idpath.
  - apply parts_from_whole in Ht. destruct Ht as [_ H2].
     apply nat_trans_eq; try assumption.
     intro c.
     assert (HT := nat_trans_eq_pointwise _ _ _ _ _ _ H2 c).
     match goal with |[H2 : ?e = ?f |- _ ] =>
                         assert (X: CoproductIn1 _ _ ;; e = CoproductIn1 _ _ ;; f) end.
     { apply maponpaths . assumption. }
     clear HT. clear H2.

     match goal with |[X : _ = ?f |- _ ] => transitivity f end.
     Focus 2. rewrite τ_LamE_algebra_on_Lam.
     eapply pathscomp0. apply assoc.
     eapply pathscomp0. apply cancel_postcomposition. apply CoproductIn1Commutes.
     apply idpath.

     match goal with |[X : ?e = _ |- _ ] => transitivity e end.
     Focus 2. apply X.

     rewrite τ_LamE_algebra_on_Lam.
     
     apply pathsinv0.
     eapply pathscomp0. apply assoc.
     eapply pathscomp0.
     apply cancel_postcomposition. apply assoc.
     eapply pathscomp0.
     apply cancel_postcomposition.
     apply cancel_postcomposition.
     apply CoproductIn1Commutes.

     repeat rewrite <- assoc.

     eapply pathscomp0. apply maponpaths.
     apply assoc.

     eapply pathscomp0. apply maponpaths. apply cancel_postcomposition.
     apply CoproductIn1Commutes.

     eapply pathscomp0. apply maponpaths. apply (!assoc _ _ _ _ _ _ _ _ ).
     eapply pathscomp0. apply maponpaths. apply maponpaths.
     apply CoproductIn1Commutes.
     apply idpath.
Qed.     


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


Definition FLATTEN : (hss_precategory CC LamE_S) ⟦LamEHSS, LamE_model_on_Lam⟧
  := InitialArrow _ _ _ .

End Lambda.
