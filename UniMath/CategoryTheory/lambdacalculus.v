Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.cats.limits.
Require Import UniMath.CategoryTheory.chains.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.EquivalencesExamples.
Require Import UniMath.CategoryTheory.AdjunctionHomTypesWeq.
Require Import UniMath.CategoryTheory.cocontfunctors.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section lambdacalculus.

Local Notation "'HSET2'":= [HSET, HSET, has_homsets_HSET].

Local Definition has_homsets_HSET2 : has_homsets HSET2.
Proof.
apply functor_category_has_homsets.
Defined.

Local Definition ProductsHSET2 : Products HSET2.
Proof.
apply (Products_functor_precat _ _ ProductsHSET).
Defined.

Local Definition CoproductsHSET2 : Coproducts HSET2.
Proof.
apply (Coproducts_functor_precat _ _ CoproductsHSET).
Defined.

Local Lemma has_exponentials_HSET2 : has_exponentials ProductsHSET2.
Proof.
apply has_exponentials_functor_HSET, has_homsets_HSET.
Defined.

Local Lemma InitialHSET2 : Initial HSET2.
Proof.
apply (Initial_functor_precat _ _ InitialHSET).
Defined.

Local Notation "' x" := (omega_cocont_constant_functor _ _ has_homsets_HSET2 x)
                          (at level 10).

Local Notation "'Id'" := (omega_cocont_functor_identity _ has_homsets_HSET2).

Local Notation "F * G" :=
  (omega_cocont_product_of_functors _ _ ProductsHSET2 _
     has_exponentials_HSET2 has_homsets_HSET2 has_homsets_HSET2 F G).

Local Notation "F + G" :=
  (omega_cocont_coproduct_of_functors _ _ ProductsHSET2 CoproductsHSET2
     has_homsets_HSET2 has_homsets_HSET2 F G).

Local Notation "'_' 'o' 'option'" :=
  (omega_cocont_pre_composition_functor _ _ _
      (option_functor HSET CoproductsHSET TerminalHSET)
      has_homsets_HSET has_homsets_HSET cats_LimsHSET) (at level 0).

Definition lambdaOmegaFunctor : omega_cocont_functor HSET2 HSET2 :=
  ' (functor_identity HSET) + (Id * Id + _ o option).

Let lambdaFunctor : functor HSET2 HSET2 := pr1 lambdaOmegaFunctor.
Let is_omega_cocont_lambdaFunctor : is_omega_cocont lambdaFunctor :=
  pr2 lambdaOmegaFunctor.

(* Old version *)
(* Definition Lambda : functor HSET2 HSET2. *)
(* Proof. *)
(* eapply coproduct_of_functors. *)
(*   apply CoproductsHSET2. *)
(*   apply (constant_functor HSET2 HSET2 (functor_identity HSET)). *)
(* eapply coproduct_of_functors. *)
(*   apply CoproductsHSET2. *)
(*   (* app *) *)
(*   eapply functor_composite. *)
(*     apply delta_functor. *)
(*     apply binproduct_functor. *)
(*     apply ProductsHSET2. *)
(* (* lam *) *)
(* apply (pre_composition_functor _ _ _ has_homsets_HSET _ *)
(*          (option_functor _ CoproductsHSET TerminalHSET)). *)
(* Defined. *)

(* Bad approach *)
(* Definition Lambda : functor [HSET,HSET,has_homsets_HSET] [HSET,HSET,has_homsets_HSET]. *)
(* Proof. *)
(* eapply functor_composite. *)
(*   apply delta_functor. *)
(* eapply functor_composite. *)
(*   eapply product_of_functors. *)
(*     apply functor_identity. *)
(*     apply delta_functor. *)
(* eapply functor_composite. *)
(*   eapply product_of_functors. *)
(*     apply (constant_functor [HSET, HSET, has_homsets_HSET] [HSET, HSET, has_homsets_HSET] (functor_identity HSET)). *)
(*     eapply product_of_functors. *)
(*       apply delta_functor. *)

(* Lemma omega_cocont_LambdaFunctor : is_omega_cocont LambdaFunctor. *)
(* Proof. *)
(* apply is_omega_cocont_coproduct_of_functors. *)
(*   apply (Products_functor_precat _ _ ProductsHSET). *)
(*   apply functor_category_has_homsets. *)
(*   apply functor_category_has_homsets. *)
(* simpl. *)
(* apply is_omega_cocont_functor_identity. *)
(*   apply has_homsets_HSET2. *)
(* apply is_omega_cocont_coproduct_of_functors. *)
(*   apply (Products_functor_precat _ _ ProductsHSET). *)
(*   apply functor_category_has_homsets. *)
(*   apply functor_category_has_homsets. *)
(*   apply is_omega_cocont_functor_composite. *)
(*   apply functor_category_has_homsets. *)
(*   apply is_omega_cocont_delta_functor. *)
(*   apply (Products_functor_precat _ _ ProductsHSET). *)
(*   apply functor_category_has_homsets. *)
(*   apply is_omega_cocont_binproduct_functor. *)
(*   apply functor_category_has_homsets. *)
(*   apply has_exponentials_functor_HSET. *)
(*   apply has_homsets_HSET. *)
(* apply is_omega_cocont_pre_composition_functor. *)
(* apply cats_LimsHSET. *)
(* Defined. *)

Lemma lambdaFunctor_Initial :
  Initial (precategory_FunctorAlg lambdaFunctor has_homsets_HSET2).
Proof.
apply (colimAlgInitial _ _ _ is_omega_cocont_lambdaFunctor InitialHSET2).
apply ColimsFunctorCategory; apply ColimsHSET.
Defined.

Definition LC : HSET2 :=
  alg_carrier _ (InitialObject lambdaFunctor_Initial).

Let LC_mor : HSET2⟦lambdaFunctor LC,LC⟧ :=
  alg_map _ (InitialObject lambdaFunctor_Initial).

Let LC_alg : algebra_ob lambdaFunctor :=
  InitialObject lambdaFunctor_Initial.

(* This is needed to not make things too slow below *)
(* Opaque LC_mor. *)

Definition var_map : HSET2⟦functor_identity HSET,LC⟧.
Proof.
apply (CoproductIn1 HSET2 _ ;; LC_mor).
(* simple refine (tpair _ _ _). *)
(* - intro x. *)
(*   simple refine (_ ;; pr1 LC_mor x). *)
(*   intro z; apply (inl z). *)
(* - intros x y f; rewrite <- assoc. *)
(*   apply pathsinv0. *)
(*   eapply pathscomp0. *)
(*   eapply maponpaths, pathsinv0. *)
(*   apply (nat_trans_ax LC_mor x y f). *)
(*   now apply funextsec; intro z; unfold compose; simpl. *)
Defined.

(* How to do this nicer? *)
Definition prod2 (x y : HSET2) : HSET2.
Proof.
apply ProductsHSET2; [apply x | apply y].
Defined.

Definition app_map : HSET2⟦prod2 LC LC,LC⟧.
Proof.
apply (CoproductIn1 HSET2 _ ;; CoproductIn2 HSET2 _ ;; LC_mor).
(* simple refine (tpair _ _ _). *)
(* - intros x. *)
(*   simple refine (_ ;; pr1 LC_mor x). *)
(*   intro z. *)
(*   apply inr. *)
(*   apply (inl z). *)
(* - intros x y f; rewrite <- assoc. *)
(*   apply pathsinv0. *)
(*   eapply pathscomp0. *)
(*   eapply maponpaths, pathsinv0. *)
(*   apply (nat_trans_ax LC_mor x y f). *)
(*   now apply funextsec; intro z; unfold compose; simpl. *)
Defined.

Definition app_map' (x : HSET) :
  HSET⟦(pr1 LC x × pr1 LC x)%set,pr1 LC x⟧.
Proof.
apply app_map.
Defined.

Let optionLC := (pre_composition_functor _ _ _ has_homsets_HSET _
                  (option_functor HSET CoproductsHSET TerminalHSET) LC).

Definition lam_map : HSET2⟦optionLC,LC⟧.
Proof.
apply (CoproductIn2 HSET2 _ ;; CoproductIn2 HSET2 _ ;; LC_mor).
(* simple refine (tpair _ _ _). *)
(* - intros x. *)
(*   simple refine (_ ;; pr1 LC_mor x). *)
(*   intro z. *)
(*   apply inr. *)
(*   apply (inr z). *)
(* - intros x y f; rewrite <- assoc. *)
(*   apply pathsinv0. *)
(*   eapply pathscomp0. *)
(*   eapply maponpaths, pathsinv0. *)
(*   apply (nat_trans_ax LC_mor x y f). *)
(*   now apply funextsec; intro z; unfold compose; simpl. *)
Defined.

End lambdacalculus.