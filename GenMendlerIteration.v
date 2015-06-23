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

Require SubstSystems.AdjunctionHomTypesWeq. (* for alternative reading of adj *)

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

Let φ := @SubstSystems.AdjunctionHomTypesWeq.φ _ _ _ is_left_adj_L.
Let φ_inv := @SubstSystems.AdjunctionHomTypesWeq.φ_inv _ _ _ is_left_adj_L.
Let R : functor _ _ := right_adjoint is_left_adj_L.
Let η : nat_trans _ _ := eta_from_left_adjoint is_left_adj_L.
Let ε : nat_trans _ _ := eps_from_left_adjoint is_left_adj_L.


Arguments φ {_ _} _ .
Arguments φ_inv {_ _} _ .

Variable X : C'.

Let Y : functor C'^op HSET := yoneda_objects C' hsC' X.

Let ψ_source : functor C^op HSET := functor_composite (functor_opp L) Y.
Let ψ_target : functor C^op HSET := functor_composite (functor_opp F) ψ_source.

Variable ψ : ψ_source ⟶ ψ_target.

Definition It : L μF ⇒ X := φ_inv (iter (φ (ψ (R X) (ε X)))).

Theorem GenMendlerIteration : iscontr (Σ h : L μF ⇒ X, #L inF ;; h = ψ μF h).
Proof.
  refine (tpair _ _ _ ).
  - exists It.
    admit.
  - admit.
Admitted.

End GenMenIt.