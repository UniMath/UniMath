Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functor_categories.
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


Require Import SubstSystems.FunctorsPointwiseCoproduct.

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

Section two_views_on_Id_H_algebras.

Variable C : precategory.
Variable hs : has_homsets C.

Variable CP : Coproducts C.

Local Notation "'EndC'":= ([C, C, hs]) .
Local Notation "'Ptd'" := (precategory_Ptd C hs).
Local Notation "'U'" := (functor_ptd_forget C hs).

Let hsEndC : has_homsets EndC := functor_category_has_homsets C C hs.
Let CPEndC : Coproducts EndC := Coproducts_functor_precat _ _ CP hs.

Variable H : functor EndC EndC.


Let Id_H
: functor EndC EndC
  := coproduct_functor _ _ CPEndC 
                       (constant_functor _ _ (functor_identity _ : EndC))
                       H.

Definition ALGStruct (T : Ptd) : UU := pr1 (H(U T)) ⟶ pr1 (U T).
Definition ALG : UU := Σ T : Ptd, ALGStruct T.
Coercion PtdFromAlg (T : ALG) : Ptd := pr1 T.
Definition tau (T : ALG) : pr1 (H (U T)) ⟶ pr1 (U T) := pr2 T.


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

(** A morphism [f] of pointed functors is an algebra morphism when... *)

Definition isALGMor {T T' : ALG} (f : T ⇒ T') : UU :=
  #H (# U f) ;; tau T' = compose (C:=EndC) (tau T) (#U f).

Lemma isaprop_isALGMor (T T' : ALG) (f : T ⇒ T') : isaprop (isALGMor f).
Proof.
  apply isaset_nat_trans.
  apply hs.
Qed.


Definition ALG_mor (A B : ALG) : UU 
  := Σ f : Ptd ⟦A, B⟧, isALGMor f. 

(* explicit coercion not necessary, this works, too:
Definition Alg_mor' (A B : Alg_obj) : UU 
  := Σ f : A ⇒ pr1 B, isAlgMor C hs H f.
*)

Coercion Ptd_mor_from_ALG_mor (A B : ALG)(f : ALG_mor A B) : Ptd ⟦A, B⟧ := pr1 f.

Definition isALGMor_Alg_mor {A B : ALG}(f : ALG_mor A B) : isALGMor f := pr2 f.

Definition ALG_mor_eq_weq (A B : ALG) (f g : ALG_mor A B) 
  : f = g ≃ #U f = #U g.
Proof.
  eapply weqcomp.
  - apply total2_paths_isaprop_equiv.
    intro h. apply isaprop_isALGMor.
  - apply eq_ptd_mor.
    apply hs.
Defined.

Lemma isALGMor_id (A : ALG) : isALGMor (identity A : Ptd⟦A,A⟧).
Proof.
  red.
  do 2 rewrite functor_id.
  rewrite id_left.
  rewrite id_right.
  apply idpath.
Qed.

Definition ALGMor_id (A : ALG) : ALG_mor A A := tpair _ _ (isALGMor_id A).


Lemma isALGMor_comp (A B D : ALG) (f : ALG_mor A B) (g : ALG_mor B D) 
  : isALGMor (f ;; g : Ptd⟦A, D⟧).
Proof.
  red.
  do 2 rewrite functor_comp.
  rewrite <- assoc.
  rewrite isALGMor_Alg_mor.
  rewrite assoc.
  rewrite isALGMor_Alg_mor.
  apply pathsinv0, assoc.
Qed.

Definition ALGMor_comp (A B D : ALG) (f : ALG_mor A B) (g : ALG_mor B D) : ALG_mor A D
  := tpair _ _ (isALGMor_comp A B D f g).

Definition ALG_precategory_ob_mor : precategory_ob_mor.
Proof.
  exists ALG.
  exact ALG_mor.
Defined.

Definition ALG_precategory_data : precategory_data.
Proof.
  exists ALG_precategory_ob_mor.
  split.
  - exact ALGMor_id.
  - exact ALGMor_comp.
Defined.

Lemma is_precategory_ALG : is_precategory ALG_precategory_data.
Proof.
  repeat split; intros.
  - apply (invmap (ALG_mor_eq_weq _ _ _ _ )).
    apply (id_left EndC).
  - apply (invmap (ALG_mor_eq_weq _ _ _ _ )).
    apply (id_right EndC).
  - apply (invmap (ALG_mor_eq_weq _ _ _ _ )).
    apply (assoc EndC).
Qed.

Definition precategory_ALG : precategory := tpair _ _ is_precategory_ALG.



Let precategory_Alg : precategory := precategory_FunctorAlg  _ Id_H hsEndC.

Definition Alg_from_ALG (T : ALG) : algebra_ob _ Id_H.
Proof.
  exists (pr1 (pr1 T)).
  simpl.
  eapply (CoproductArrow _ (CPEndC _ _ )).
  - simpl.
    apply (pr2 (pr1 T)).
  - apply (tau T).
Defined.

Definition is_Alg_mor {T T': algebra_ob _ Id_H}(f: pr1(pr1 T)⟶pr1(pr1 T')):= alg_map _ _ T ;; f = #Id_H f ;; alg_map _ _ T'.

Lemma is_Alg_mor_ALG_mor {T T' : ALG} (f : ALG_mor T T')
  : is_Alg_mor(T:= Alg_from_ALG T)(T':= Alg_from_ALG T') (pr1(pr1 f)).
Proof.
  unfold is_Alg_mor.
  simpl. unfold coproduct_functor_mor.
  apply pathsinv0.
  eapply pathscomp0.
  + apply (precompWithCoproductArrow ([C, C] hs) (CPEndC _ (H (pr1 (pr1 T))))
     (CPEndC _ (H (pr1 (pr1 T'))))).
  + rewrite id_left.
    eapply pathscomp0.
Focus 2.
    eapply pathsinv0. 
    apply (postcompWithCoproductArrow ([C, C] hs) (CPEndC _ (H (pr1 (pr1 T))))).
    apply (CoproductArrow_eq ([C, C] hs) CPEndC).
    * apply pathsinv0.
      apply nat_trans_eq; try (exact hs).
      intro c.
      assert (f_pointed_mor:= pr2 (pr1 f) c).
      exact f_pointed_mor.
    * apply isALGMor_Alg_mor.
Qed.

Definition Alg_mor_from_ALG_mor {T T' : ALG} (f : ALG_mor T T')
  : algebra_mor _ _ (Alg_from_ALG T) (Alg_from_ALG T').
Proof.
  exists (pr1 (pr1 f)).
  apply is_Alg_mor_ALG_mor.
Defined.

Definition ALG_from_Alg (T : algebra_ob _ Id_H) : ALG.
Proof.
  refine (tpair _ _ _ ).
  - exists (pr1 T).
    apply (CoproductIn1 _ (CPEndC (functor_identity C) (H (pr1 T))) ;; (pr2 T)).
  - apply (CoproductIn2 _ (CPEndC (functor_identity C) (H (pr1 T))) ;; (pr2 T)).
Defined.

Lemma ALG_mor_from_Alg_mor_is_ptd_mor {T T' : algebra_ob _ Id_H} (f : algebra_mor _ _  T T') : is_ptd_mor(F:= PtdFromAlg (ALG_from_Alg T))(G:= PtdFromAlg (ALG_from_Alg T')) C (pr1 f).   
Proof.
    unfold is_ptd_mor; simpl.
    intro c.
    unfold coproduct_nat_trans_in1_data; simpl.
    rewrite <- assoc.
    assert (f_is_alg_mor := algebra_mor_commutes ([C, C] hs) _ _ _ f).
    assert (f_is_alg_mor_inst := nat_trans_eq_pointwise _ _ _ _ _ _ f_is_alg_mor c);
    clear f_is_alg_mor.
    simpl in f_is_alg_mor_inst.
    unfold coproduct_nat_trans_data in f_is_alg_mor_inst; simpl in  f_is_alg_mor_inst.
    unfold coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data in f_is_alg_mor_inst; simpl in  f_is_alg_mor_inst.
    unfold alg_map in f_is_alg_mor_inst; simpl in f_is_alg_mor_inst.
    rewrite id_left in f_is_alg_mor_inst.
    match goal with |[ H1: ?f = _ |- ?h ;; _ = _ ] => 
         pathvia (h;;f) end.
    + apply idpath.
    + rewrite f_is_alg_mor_inst.
      rewrite assoc.
      apply (maponpaths (fun x => x;;(pr1 ((pr2 T'):([C, C] hs ⟦ Id_H (pr1 T'), pr1 T' ⟧))) c)).
      apply CoproductIn1Commutes.
Qed.

Definition ALG_mor_from_Alg_mor_ptd  {T T' : algebra_ob _ Id_H} (f : algebra_mor _ _  T T') : ptd_mor _ (PtdFromAlg (ALG_from_Alg T)) (PtdFromAlg (ALG_from_Alg T')).
Proof.
  refine (tpair _ _ _ ).
  - exact (pr1 f).
    (* wrong approach:
    exists (pr1 (pr1 f)).
    set (f0 := mor_from_algebra_mor _ _ _ _ f).
    assert (f_is_nat := nat_trans_ax f0).
    exact f_is_nat. *)
  - apply ALG_mor_from_Alg_mor_is_ptd_mor.
Defined.

Lemma ALG_mor_from_Alg_mor_is_ALG_mor {T T' : algebra_ob _ Id_H} (f : algebra_mor _ _  T T'): isALGMor(T:= ALG_from_Alg T)(T':= ALG_from_Alg T') (ALG_mor_from_Alg_mor_ptd f).
Proof.
    apply nat_trans_eq; try (exact hs).
    intro c.
    simpl.
    unfold coproduct_nat_trans_in2_data; simpl.
    assert (f_is_alg_mor := algebra_mor_commutes ([C, C] hs) _ _ _ f).
    assert (f_is_alg_mor_inst := nat_trans_eq_pointwise _ _ _ _ _ _ f_is_alg_mor c);
    clear f_is_alg_mor.
    simpl in f_is_alg_mor_inst.
    unfold coproduct_nat_trans_data in f_is_alg_mor_inst; simpl in  f_is_alg_mor_inst.
    unfold coproduct_nat_trans_in1_data, coproduct_nat_trans_in2_data in f_is_alg_mor_inst; simpl in  f_is_alg_mor_inst.
    unfold alg_map in f_is_alg_mor_inst; simpl in  f_is_alg_mor_inst.
    rewrite id_left in f_is_alg_mor_inst.
    rewrite <- assoc.    
    match goal with |[ H1: ?f = _ |- _ = ?h ;; _ ] => 
         pathvia (h;;f) end.
    + rewrite f_is_alg_mor_inst.
      do 2 rewrite assoc.
      apply (maponpaths (fun x => x;;(pr1 ((pr2 T'):([C, C] hs ⟦ Id_H (pr1 T'), pr1 T' ⟧))) c)).
      apply pathsinv0.
      apply CoproductIn2Commutes.
    + apply idpath.
Qed.

Definition ALG_mor_from_Alg_mor {T T' : algebra_ob _ Id_H} (f : algebra_mor _ _  T T')
  : ALG_mor (ALG_from_Alg T) (ALG_from_Alg T').
Proof.
  refine (tpair _ _ _ ).
  - exact (ALG_mor_from_Alg_mor_ptd f).
  - apply ALG_mor_from_Alg_mor_is_ALG_mor.
Defined.

(*
Lemma ALG_from_Alg_from_ALG (T : ALG) : ALG_from_Alg (Alg_from_ALG T) = T.
Proof.
  refine (total2_paths _ _ ).
  - refine (total2_paths _ _ ).
    * apply idpath.
    * simpl.
      refine (CoproductIn1Commutes _ _ _ (CPEndC (functor_identity C) _ ) _ _ _ ).
  - Search (transportf _ _  _ = _ ).
    Search (transportf (λ (_ : Σ _ , _) , _ ) _ _ = _ ). 
    set (HT:=@transportf_total2).
    set (HT' := HT Ptd ALGStruct).
    set (HT'' := HT' 
    eapply pathscomp0.
    apply HT'.
    rewrite HT.
    apply nat_trans_eq. assumption.
    intro c; simpl.
    apply idpath.
    Check (pr2 T). Print ALGStruct.
    

    simpl.
      apply idpath.
*)

End two_views_on_Id_H_algebras.

Arguments tau {_ _ _ } _ .
Arguments ALG {_ _} _.
Arguments isALGMor {_ _ _ _ _} _ .
Arguments ALG_mor {_ _ _} _ _ .
