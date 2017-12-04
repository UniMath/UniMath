(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

- Derivation of Generalized Iteration in Mendler-style
- Instantiation to a special case, Specialized Mendler Iteration
- Proof of a fusion law à la Bird-Paterson (Generalised folds
  for nested datatypes) for Generalized Iteration in Mendler-style




************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.Adjunctions.

Arguments functor_composite {_ _ _} _ _ .
Arguments nat_trans_comp {_ _ _ _ _} _ _ .
Local Notation "G ∙ F" := (functor_composite F G : [ _ , _ , _ ]) (at level 35).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "↓ f" := (mor_from_algebra_mor _ _ _ f) (at level 3, format "↓ f").
(* in Agda mode \downarrow *)

(** Goal: derive Generalized Iteration in Mendler-style and a fusion law *)

(** * Generalized Iteration in Mendler-style *)

Section GenMenIt.

Variable C : precategory.
Variable hsC : has_homsets C.

Variable F : functor C C.

Let AF := FunctorAlg F hsC.

Definition AlgConstr (A : C) (α : F A --> A) : AF.
Proof.
  exists A.
  exact α.
Defined.

Notation "⟨ A , α ⟩" := (AlgConstr A α).
(* \<  , \> *)

Variable μF_Initial : Initial AF.

Let μF : C := alg_carrier _ (InitialObject μF_Initial).
Let inF : F μF --> μF := alg_map _ (InitialObject μF_Initial).

Let iter {A : C} (α : F A --> A) : μF --> A :=
  ↓(InitialArrow μF_Initial ⟨A,α⟩).

Variable C' : precategory.
Variable hsC' : has_homsets C'.


Section the_iteration_principle.

Variable X : C'.

Let Yon : functor C'^op HSET := yoneda_objects C' hsC' X.

Variable L : functor C C'.

Variable is_left_adj_L : is_left_adjoint L.

Let φ := @φ_adj _ _ _ _ (pr2 is_left_adj_L).
Let φ_inv := @φ_adj_inv _ _ _ _ (pr2 is_left_adj_L).
Let R : functor _ _ := right_adjoint is_left_adj_L.
Let η : nat_trans _ _ := unit_from_left_adjoint is_left_adj_L.
Let ε : nat_trans _ _ := counit_from_left_adjoint is_left_adj_L.
(* Let φ_natural_precomp := @φ_adj_natural_precomp _ _ _ is_left_adj_L.
Let φ_inv_natural_precomp := @φ_adj_inv_natural_precomp _ _ _ is_left_adj_L.
Let φ_after_φ_inv := @φ_adj_after_φ_adj_inv _ _ _ is_left_adj_L.
Let φ_inv_after_φ := @φ_adj_inv_after_φ_adj _ _ _ is_left_adj_L.*)


Arguments φ {_ _} _ .
Arguments φ_inv {_ _} _ .

Definition ψ_source : functor C^op HSET := functor_composite (functor_opp L) Yon.
Definition ψ_target : functor C^op HSET := functor_composite (functor_opp F) ψ_source.

Section general_case.

Variable ψ : ψ_source ⟹ ψ_target.

Definition preIt : L μF --> X := φ_inv (iter (φ (ψ (R X) (ε X)))).


Lemma ψ_naturality (A B: C)(h: B --> A)(f: L A --> X): ψ B (#L h· f) = #L (#F h)· ψ A f.
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

Lemma φ_ψ_μF_eq (h: L μF --> X): φ (ψ μF h) = #F (φ h) · φ(ψ (R X) (ε X)).
Proof.
  rewrite <- (φ_adj_natural_precomp (pr2 is_left_adj_L)).
  apply maponpaths.
  eapply pathscomp0.
Focus 2.
  apply ψ_naturality.
  apply maponpaths.
  rewrite truth_about_ε.
  rewrite <- (φ_adj_inv_natural_precomp (pr2 is_left_adj_L)).
  rewrite id_right.
  apply pathsinv0.
  change (φ_inv(φ h) = h).
  apply φ_adj_inv_after_φ_adj.
Qed.

Lemma cancel_φ {A: C}{B: C'} (f g : L A --> B): φ f = φ g -> f = g.
Proof.
  intro Hyp.
(* pedestrian way:
  rewrite <- (φ_adj_inv_after_φ_adj _ _ _ is_left_adj_L f).
  rewrite <- (φ_adj_inv_after_φ_adj _ _ _ is_left_adj_L g).
  apply maponpaths.
  exact Hyp.
*)
  apply (invmaponpathsweq (adjunction_hom_weq (pr2 is_left_adj_L) _ _)).
  exact Hyp.
Qed.

Lemma preIt_ok : # L inF· preIt = ψ μF preIt.
Proof.
    apply cancel_φ.
    rewrite φ_ψ_μF_eq.
    rewrite (φ_adj_natural_precomp (pr2 is_left_adj_L)).
    unfold preIt.
    rewrite (φ_adj_after_φ_adj_inv (pr2 is_left_adj_L)).
    rewrite (φ_adj_after_φ_adj_inv (pr2 is_left_adj_L)).
    assert (iter_eq := algebra_mor_commutes _ _ _ (InitialArrow μF_Initial ⟨_,φ (ψ (R X) (ε X))⟩)).
    exact iter_eq.
Qed.

Lemma preIt_uniq (t : ∑ h : L μF --> X, # L inF· h = ψ μF h):
    t = tpair (λ h : L μF --> X, # L inF· h = ψ μF h) preIt preIt_ok.
Proof.
    destruct t as [h h_rec_eq]; simpl.
    assert (same: h = preIt).
Focus 2.
    apply subtypeEquality.
    + intro.
      simpl.
      apply hsC'.
Focus 2.
    simpl.
    exact same.

    apply cancel_φ.
    unfold preIt.
    rewrite (φ_adj_after_φ_adj_inv (pr2 is_left_adj_L)).
    (* assert (iter_uniq := algebra_mor_commutes _ _ _ *)
    (*                        (InitialArrow μF_Initial ⟨_,φ (ψ (R X) (ε X))⟩)). *)
    (* simpl in iter_uniq. *)
    assert(φh_is_alg_mor: inF · φ h = #F(φ h) · φ (ψ (R X) (ε X))).
      (* remark: I am missing a definition of the algebra morphism property in UniMath.CategoryTheory.FunctorAlgebras *)
    + rewrite <- φ_ψ_μF_eq.
      rewrite <- (φ_adj_natural_precomp (pr2 is_left_adj_L)).
      apply maponpaths.
      exact h_rec_eq.
    + (* set(φh_alg_mor := tpair _ _ φh_is_alg_mor : pr1 μF_Initial --> ⟨ R X, φ (ψ (R X) (ε X)) ⟩). *)
       use (let X : AF ⟦ InitialObject μF_Initial, ⟨ R X, φ (ψ (R X) (ε X)) ⟩ ⟧ := _ in _).
       * apply (tpair _ (φ h)); assumption.
       * apply (maponpaths pr1 (InitialArrowUnique _ _ X0)).
Qed.

Theorem GenMendlerIteration : iscontr (∑ h : L μF --> X, #L inF · h = ψ μF h).
Proof.
  use tpair.
  - exists preIt.
    exact preIt_ok.
  - exact preIt_uniq.
Defined.

Definition It : L μF --> X := pr1 (pr1 GenMendlerIteration).
Lemma It_is_preIt : It = preIt.
Proof.
  apply idpath.
Qed.

End general_case.

(** * Specialized Mendler Iteration *)

Section special_case.

  Variable G : functor C' C'.
  Variable ρ : G X --> X.
  Variable θ : functor_composite F L ⟹ functor_composite L G.


  Lemma is_nat_trans_ψ_from_comps
        :  is_nat_trans ψ_source ψ_target
                        (λ (A : C^op) (f : yoneda_objects_ob C' X (L A)), θ A· # G f· ρ).
  Proof.
    intros A B h.
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
   Qed.

  Definition ψ_from_comps : ψ_source ⟹ ψ_target.
  Proof.
    use tpair.
    - intro A. simpl. intro f.
      unfold yoneda_objects_ob in *.
      exact (θ A · #G f · ρ).
    - apply is_nat_trans_ψ_from_comps.
  Defined.


  Definition SpecialGenMendlerIteration :
    iscontr
      (∑ h : L μF --> X, # L inF · h = θ μF · #G h · ρ)
    := GenMendlerIteration ψ_from_comps.

End special_case.

End the_iteration_principle.

(** * Fusion law for Generalized Iteration in Mendler-style *)

Variable X X': C'.
Let Yon : functor C'^op HSET := yoneda_objects C' hsC' X.
Let Yon' : functor C'^op HSET := yoneda_objects C' hsC' X'.
Variable L : functor C C'.
Variable is_left_adj_L : is_left_adjoint L.
Variable ψ : ψ_source X L ⟹ ψ_target X L.
Variable L' : functor C C'.
Variable is_left_adj_L' : is_left_adjoint L'.
Variable ψ' : ψ_source X' L' ⟹ ψ_target X' L'.

Variable Φ : functor_composite (functor_opp L) Yon ⟹ functor_composite (functor_opp L') Yon'.

Section fusion_law.

  Variable H : ψ μF · Φ (F μF) = Φ μF · ψ' μF.

  Theorem fusion_law : Φ μF (It X L is_left_adj_L ψ) = It X' L' is_left_adj_L' ψ'.
  Proof.
    apply pathsinv0.
    apply pathsinv0.
    apply path_to_ctr.
    assert (Φ_is_nat := nat_trans_ax Φ).
    assert (Φ_is_nat_inst1 := Φ_is_nat _ _ inF).
    assert (Φ_is_nat_inst2 := toforallpaths _ _ _ Φ_is_nat_inst1 (It X L is_left_adj_L ψ)).
    unfold compose in Φ_is_nat_inst2; simpl in Φ_is_nat_inst2.
    simpl.
    rewrite <- Φ_is_nat_inst2.
    assert (H_inst :=  toforallpaths _ _ _ H (It X L is_left_adj_L ψ)).
    unfold compose in H_inst; simpl in H_inst.
    rewrite <- H_inst.
    apply maponpaths.
    rewrite It_is_preIt.
    apply preIt_ok.
  Qed.

End fusion_law.



End GenMenIt.
