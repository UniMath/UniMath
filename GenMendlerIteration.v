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

Variable L : functor C C'.

Variable is_left_adj_L : is_left_adjoint L.

Let φ := @φ_adj _ _ _ is_left_adj_L.
Let φ_inv := @φ_adj_inv _ _ _ is_left_adj_L.
Let R : functor _ _ := right_adjoint is_left_adj_L.
Let η : nat_trans _ _ := eta_from_left_adjoint is_left_adj_L.
Let ε : nat_trans _ _ := eps_from_left_adjoint is_left_adj_L.
Let φ_natural_precomp := @φ_adj_natural_precomp _ _ _ is_left_adj_L.
Let φ_inv_natural_precomp := @φ_adj_inv_natural_precomp _ _ _ is_left_adj_L.
Let φ_after_φ_inv := @φ_adj_after_φ_adj_inv _ _ _ is_left_adj_L.
Let φ_inv_after_φ := @φ_adj_inv_after_φ_adj _ _ _ is_left_adj_L.


Arguments φ {_ _} _ .
Arguments φ_inv {_ _} _ .

Variable X : C'.

Let Y : functor C'^op HSET := yoneda_objects C' hsC' X.

Let ψ_source : functor C^op HSET := functor_composite (functor_opp L) Y.
Let ψ_target : functor C^op HSET := functor_composite (functor_opp F) ψ_source.

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
  destruct ψ as [ψ0 ψ0_is_nat].
  simpl.
  red in ψ0_is_nat.
  assert (ψ0_is_nat_inst1 := ψ0_is_nat _ _ h).
  (* assert (ψ0_is_nat_inst2 := aux0 _ _ _ _ f ψ0_is_nat_inst1). *)
  assert (ψ0_is_nat_inst2 := toforallpaths _ _ _ ψ0_is_nat_inst1 f).
  apply ψ0_is_nat_inst2.
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
  rewrite <- φ_natural_precomp.
  apply maponpaths.
  eapply pathscomp0.
Focus 2.
  apply ψ_naturality.  
  apply maponpaths.
  rewrite truth_about_ε.
  rewrite <- φ_inv_natural_precomp.
  rewrite id_right.
  apply pathsinv0.
  change (φ_inv(φ h) = h).
  apply φ_inv_after_φ.
Qed.

Lemma cancel_φ {A: C}{B: C'} (f g : L A ⇒ B): φ f = φ g -> f = g.
Proof.
  intro Hyp.
  rewrite <- (φ_inv_after_φ _ _ f).
  rewrite <- (φ_inv_after_φ _ _ g).
  apply maponpaths.
  exact Hyp.
Qed.


Theorem GenMendlerIteration : iscontr (Σ h : L μF ⇒ X, #L inF ;; h = ψ μF h).
Proof.
  refine (tpair _ _ _ ).
  - exists It.
    apply cancel_φ.
    rewrite φ_ψ_μF_eq.
    rewrite φ_natural_precomp.
    unfold It.
    do 2 rewrite φ_after_φ_inv.
    assert (iter_eq := algebra_mor_commutes _ _ _ _ (InitialArrow _ μF_Initial ⟨_,φ (ψ (R X) (ε X))⟩)).
    exact iter_eq.
  - intros [h h_rec_eq]; simpl.
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
    rewrite φ_after_φ_inv.
    assert (iter_uniq := pr2 (pr2 μF_Initial ⟨_,φ (ψ (R X) (ε X))⟩)).
    simpl in iter_uniq.
    assert(φh_is_alg_mor: inF ;; φ h = #F(φ h) ;; φ (ψ (R X) (ε X))).
      (* remark: I am missing a definition of the algebra morphism property in UniMath.RezkCompletion.FunctorAlgebras *)
    + rewrite <- φ_ψ_μF_eq. 
      rewrite <- φ_natural_precomp.
      apply maponpaths.
      exact h_rec_eq.
    + set(φh_alg_mor := tpair _ _ φh_is_alg_mor : pr1 μF_Initial ⇒ ⟨ R X, φ (ψ (R X) (ε X)) ⟩).
      assert (iter_uniq_inst := iter_uniq φh_alg_mor). clear iter_uniq.
      apply (maponpaths pr1) in iter_uniq_inst.
      exact iter_uniq_inst.
Qed.

End GenMenIt.
