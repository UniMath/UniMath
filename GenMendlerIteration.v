Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.
Require Import SubstSystems.UnicodeNotations.
Require Import UniMath.RezkCompletion.limits.initial.
Require Import UniMath.RezkCompletion.FunctorAlgebras.
Require Import UniMath.RezkCompletion.category_hset.
Require Import UniMath.RezkCompletion.opp_precat.
Require Import UniMath.RezkCompletion.yoneda.
Require Import UniMath.RezkCompletion.equivalences. (* for adjunctions *)
Require Import SubstSystems.AdjunctionHomTypesWeq. (* for alternative reading of adj *)
Require Import SubstSystems.Auxiliary.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Arguments functor_composite {_ _ _} _ _ .
Arguments nat_trans_comp {_ _ _ _ _} _ _ .
Local Notation "G ∙ F" := (functor_composite F G : [ _ , _ , _ ]) (at level 35).
Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Notation "↓ f" := (mor_from_algebra_mor _ _ _ _ f) (at level 3, format "↓ f").
(* in Agda mode \downarrow *)


Section GenMenIt.

Variable C : precategory.
Variable hsC : has_homsets C.

Variable F : functor C C.

Let AF := precategory_FunctorAlg _ F hsC.

Definition AlgConstr (A : C) (α : F A ⇒ A) : AF.
Proof.
  exists A.
  exact α.
Defined.

Notation "⟨ A , α ⟩" := (AlgConstr A α). 
(* \<  , \> *)

Variable μF_Initial : Initial AF.

Let μF : C := pr1 (pr1 μF_Initial).
Let inF : F μF ⇒ μF := alg_map _ _ (pr1 μF_Initial).


Let iter {A : C} (α : F A ⇒ A) : μF ⇒ A :=
  ↓(InitialArrow _ μF_Initial ⟨A,α⟩).

Variable C' : precategory.
Variable hsC' : has_homsets C'.

Variable X : C'.

Let Yon : functor C'^op HSET := yoneda_objects C' hsC' X.


Section the_iteration_principle.

Variable L : functor C C'.

Variable is_left_adj_L : is_left_adjoint L.

Let φ := @φ_adj _ _ _ is_left_adj_L.
Let φ_inv := @φ_adj_inv _ _ _ is_left_adj_L.
Let R : functor _ _ := right_adjoint is_left_adj_L.
Let η : nat_trans _ _ := eta_from_left_adjoint is_left_adj_L.
Let ε : nat_trans _ _ := eps_from_left_adjoint is_left_adj_L.
(* Let φ_natural_precomp := @φ_adj_natural_precomp _ _ _ is_left_adj_L.
Let φ_inv_natural_precomp := @φ_adj_inv_natural_precomp _ _ _ is_left_adj_L.
Let φ_after_φ_inv := @φ_adj_after_φ_adj_inv _ _ _ is_left_adj_L.
Let φ_inv_after_φ := @φ_adj_inv_after_φ_adj _ _ _ is_left_adj_L.*)


Arguments φ {_ _} _ .
Arguments φ_inv {_ _} _ .

Definition ψ_source : functor C^op HSET := functor_composite (functor_opp L) Yon.
Definition ψ_target : functor C^op HSET := functor_composite (functor_opp F) ψ_source.

Section general_case.

Variable ψ : ψ_source ⟶ ψ_target.

Definition It : L μF ⇒ X := φ_inv (iter (φ (ψ (R X) (ε X)))).

(* what is the usual name of the following lemma? it is toforallpaths
Lemma aux0 (A B: UU)(f g: A -> B)(a: A): f = g -> f a = g a.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply idpath.
Qed.
*)
   
Lemma ψ_naturality (A B: C)(h: B ⇒ A)(f: L A ⇒ X): ψ B (#L h;; f) = #L (#F h);; ψ A f.
Proof.
  assert (ψ_is_nat := nat_trans_ax ψ);
  assert (ψ_is_nat_inst1 := ψ_is_nat _ _ h).
  (* assert (ψ_is_nat_inst2 := aux0 _ _ _ _ f ψ_is_nat_inst1). *)
  assert (ψ_is_nat_inst2 := toforallpaths _ _ _ ψ_is_nat_inst1 f).
  apply ψ_is_nat_inst2.
Qed.

Lemma truth_about_ε (A: C'): ε A = φ_inv (identity (R A)).
Proof.
  unfold φ_inv, φ_adj_inv.
  rewrite functor_id.
  apply pathsinv0.
  apply id_left.
Qed.

Lemma φ_ψ_μF_eq (h: L μF ⇒ X): φ (ψ μF h) = #F (φ h) ;; φ(ψ (R X) (ε X)).
Proof.
  rewrite <- φ_adj_natural_precomp.
  apply maponpaths.
  eapply pathscomp0.
Focus 2.
  apply ψ_naturality.  
  apply maponpaths.
  rewrite truth_about_ε.
  rewrite <- (φ_adj_inv_natural_precomp _ _ _ is_left_adj_L).
  rewrite id_right.
  apply pathsinv0.
  change (φ_inv(φ h) = h).
  apply φ_adj_inv_after_φ_adj.
Qed.

Lemma cancel_φ {A: C}{B: C'} (f g : L A ⇒ B): φ f = φ g -> f = g.
Proof.
  intro Hyp.
(* pedestrian way:
  rewrite <- (φ_adj_inv_after_φ_adj _ _ _ is_left_adj_L f).
  rewrite <- (φ_adj_inv_after_φ_adj _ _ _ is_left_adj_L g).
  apply maponpaths.
  exact Hyp.
*)
  apply (invmaponpathsweq (adjunction_hom_weq _ _ _ is_left_adj_L _ _)).
  exact Hyp.
Qed.

Lemma It_ok : # L inF;; It = ψ μF It.
Proof.
    apply cancel_φ.
    rewrite φ_ψ_μF_eq.
    rewrite (φ_adj_natural_precomp _ _ _ is_left_adj_L).
    unfold It.
    rewrite φ_adj_after_φ_adj_inv.
    rewrite (φ_adj_after_φ_adj_inv _ _ _ is_left_adj_L).
    assert (iter_eq := algebra_mor_commutes _ _ _ _ (InitialArrow _ μF_Initial ⟨_,φ (ψ (R X) (ε X))⟩)).
    exact iter_eq.
Qed.

Lemma It_uniq (t : Σ h : L μF ⇒ X, # L inF;; h = ψ μF h):
    t = tpair (λ h : L μF ⇒ X, # L inF;; h = ψ μF h) It It_ok.
Proof.
    destruct t as [h h_rec_eq]; simpl.
    assert (same: h = It).
Focus 2.
    apply (total2_paths_second_isaprop).
    + simpl.
      apply hsC'.
Focus 2.
    simpl.
    exact same.

    apply cancel_φ.
    unfold It.
    rewrite (φ_adj_after_φ_adj_inv _ _ _ is_left_adj_L).
    assert (iter_uniq := pr2 (pr2 μF_Initial ⟨_,φ (ψ (R X) (ε X))⟩)).
    simpl in iter_uniq.
    assert(φh_is_alg_mor: inF ;; φ h = #F(φ h) ;; φ (ψ (R X) (ε X))).
      (* remark: I am missing a definition of the algebra morphism property in UniMath.RezkCompletion.FunctorAlgebras *)
    + rewrite <- φ_ψ_μF_eq. 
      rewrite <- φ_adj_natural_precomp.
      apply maponpaths.
      exact h_rec_eq.
    + (* set(φh_alg_mor := tpair _ _ φh_is_alg_mor : pr1 μF_Initial ⇒ ⟨ R X, φ (ψ (R X) (ε X)) ⟩). *)
      apply path_to_ctr.
      exact φh_is_alg_mor.
Qed.

Theorem GenMendlerIteration : iscontr (Σ h : L μF ⇒ X, #L inF ;; h = ψ μF h).
Proof.
  refine (tpair _ _ _ ).
  - exists It.
    exact It_ok.
  - exact It_uniq.
Defined.

Definition It_which_is_unique: L μF ⇒ X := pr1 (pr1 GenMendlerIteration).
Lemma It_is_It_which_is_unique: It = It_which_is_unique.
Proof.
  apply idpath.
Qed.

End general_case.


Section special_case.

  Variable G : functor C' C'.
  Variable ρ : G X ⇒ X.
  Variable θ : functor_composite F L ⟶ functor_composite L G.

  Definition ψ_from_comps : ψ_source ⟶ ψ_target.
  Proof.
    refine (tpair _ _ _ ).
    - intro A. simpl. intro f.
      unfold yoneda_objects_ob in *.
      exact (θ A ;; #G f ;; ρ).
    - red; intros A B h.
      apply funextfun.
      intro f.
      simpl.
      unfold compose at 1 5; simpl.
      rewrite functor_comp. 
      repeat rewrite assoc.
      assert (θ_nat_trans_ax := nat_trans_ax θ).
      unfold functor_composite in θ_nat_trans_ax.
      simpl in θ_nat_trans_ax.
      rewrite <- θ_nat_trans_ax.
      apply idpath.          
  Defined.   


  Definition SpecialGenMendlerIteration :
    iscontr
      (Σ h : L μF ⇒ X, # L inF ;; h = θ μF ;; #G h ;; ρ)
    := GenMendlerIteration ψ_from_comps.

End special_case.

End the_iteration_principle.

Variable L : functor C C'.
Variable is_left_adj_L : is_left_adjoint L.
Variable ψ : ψ_source L ⟶ ψ_target L.
Variable L' : functor C C'.
Variable is_left_adj_L' : is_left_adjoint L'.
Variable ψ' : ψ_source L' ⟶ ψ_target L'.

Variable Φ : functor_composite (functor_opp L) Yon ⟶ functor_composite (functor_opp L') Yon.

Section fusion_law.
  
  Variable H : ψ μF ;; Φ (F μF) = Φ μF ;; ψ' μF.

  Theorem fusion_law : Φ μF (It L is_left_adj_L ψ) = It L' is_left_adj_L' ψ'.
  Proof.
    apply pathsinv0.
    rewrite It_is_It_which_is_unique.
    apply pathsinv0.
    apply path_to_ctr.
    assert (Φ_is_nat := nat_trans_ax Φ).
    assert (Φ_is_nat_inst1 := Φ_is_nat _ _ inF).
    assert (Φ_is_nat_inst2 := toforallpaths _ _ _ Φ_is_nat_inst1 (It L is_left_adj_L ψ)).
    unfold compose in Φ_is_nat_inst2; simpl in Φ_is_nat_inst2.
    simpl.
    rewrite <- Φ_is_nat_inst2.
    assert (H_inst :=  toforallpaths _ _ _ H (It L is_left_adj_L ψ)).
    unfold compose in H_inst; simpl in H_inst.
    rewrite <- H_inst.
    apply maponpaths.
    apply It_ok.    
  Qed.
    
End fusion_law.



End GenMenIt.
