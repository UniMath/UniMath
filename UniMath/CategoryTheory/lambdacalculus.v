Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.colimits.colimits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.colimits.chains.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.EquivalencesExamples.
Require Import UniMath.CategoryTheory.AdjunctionHomTypesWeq.
Require Import UniMath.CategoryTheory.colimits.polynomialfunctors.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

(* The functor "* : C^2 -> C" is omega cocont *)
Section binprod_functor.

Variables (C : precategory) (PC : Products C) (hsC : has_homsets C).

(* The functor "x * _" and "_ * x" *)
(* Definition constprod_functor1 (x : C) : functor C C := *)
(*   product_functor C C PC (constant_functor C C x) (functor_identity C). *)

(* Definition constprod_functor2 (x : C) : functor C C := *)
(*   product_functor C C PC (functor_identity C) (constant_functor C C x). *)

(* Lemma omega_cocont_constprod_functor1 (x : C) : omega_cocont (constprod_functor1 x). *)
(* Admitted. *)

(* Lemma omega_cocont_constprod_functor2 (x : C) : omega_cocont (constprod_functor2 x). *)
(* Admitted. *)

Lemma omega_cocont_binproduct_functor : omega_cocont (binproduct_functor PC).
(* Proof. *)
(* intros c LM ccLM HccLM K ccK; simpl in *. *)
(* generalize (isColimCocone_pr2_functor _ _ hsC _ _ _ HccLM). *)
(* generalize (isColimCocone_pr1_functor _ _ hsC _ _ _ HccLM). *)
(* set (L := pr1 LM); set (M := pr2 LM). *)
(* intros HA HB. *)
(* (* Form the colimiting cocones of "A_i * B_0 -> A_i * B_1 -> ..." *) *)
(* assert (HAiB : forall i, isColimCocone *)
(*      (mapdiagram (constprod_functor1 (pr1 (pr1 c i))) *)
(*         (mapchain (pr2_functor C C) c)) *)
(*      ((constprod_functor1 (pr1 (pr1 c i))) M) *)
(*      (mapcocone (constprod_functor1 (pr1 (pr1 c i))) *)
(*         (mapchain (pr2_functor C C) c) (cocone_pr2_functor C C c LM ccLM))). *)
(*   intro i. *)
(*   apply (omega_cocont_constprod_functor1 (pr1 (pr1 c i)) _ _ _ HB). *)
(* generalize (omega_cocont_constprod_functor2 M _ _ _ HA); intro HAiM. *)
(* simple refine (let X : ColimCocone *)
(*        (mapdiagram (constprod_functor2 M) (mapchain (pr1_functor C C) c)) := _ in _). *)
(* mkpair. *)
(* mkpair. *)
(* apply (ProductObject _ (PC L M)). *)
(* apply (mapcocone (constprod_functor2 M) (mapchain (pr1_functor C C) c) *)
(*               (cocone_pr1_functor C C c LM ccLM)). *)
(* apply HAiM. *)
(* simple refine (let Y : cocone (mapdiagram (constprod_functor2 M) (mapchain (pr1_functor C C) c)) K := _ in _). *)
(*   admit. *)
(* mkpair. *)
(* mkpair. *)
(* apply (colimArrow X K Y). *)
(* intro n. *)
(* generalize (colimArrowCommutes X K Y n). *)
(* simpl. *)
(* unfold colimIn. *)
(* simpl. *)
(* unfold product_functor_mor. *)
(* unfold ProductOfArrows. *)
(* admit. *)
(* admit. *)
Admitted.

End binprod_functor.

Section rightkanextension.

Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.RightKanExtension.

Variables C D E : precategory.
Variables (K : functor C D).

(* Lemma foo : has_limits D -> GlobalRightKanExtensionExists K. *)

(* has_limits D *)
Lemma cocont_pre_composition_functor (hsD : has_homsets D) (hsE : has_homsets E) :
  is_cocont (pre_composition_functor _ _ E hsD hsE K).
Admitted. (* will be a simple consequence of foo *)

Lemma omega_cocont_pre_composition_functor (hsD : has_homsets D) (hsE : has_homsets E) :
  omega_cocont (pre_composition_functor _ _ E hsD hsE K).
Proof.
intros c L ccL.
apply cocont_pre_composition_functor.
Defined.

End rightkanextension.

Section lambdacalculus.


Definition option_functor : [HSET,HSET,has_homsets_HSET].
Proof.
apply coproduct_functor.
apply CoproductsHSET.
apply (constant_functor _ _ unitHSET).
apply functor_identity.
Defined.

(* TODO: package omega cocont functors *)
Definition LambdaFunctor : functor [HSET,HSET,has_homsets_HSET] [HSET,HSET,has_homsets_HSET].
Proof.
eapply sum_of_functors.
  apply (Coproducts_functor_precat _ _ CoproductsHSET).
  apply (constant_functor [HSET, HSET, has_homsets_HSET] [HSET, HSET, has_homsets_HSET] (functor_identity HSET)).
eapply sum_of_functors.
  apply (Coproducts_functor_precat _ _ CoproductsHSET).
  (* app *)
  eapply functor_composite.
    apply delta_functor.
    apply binproduct_functor.
    apply (Products_functor_precat _ _ ProductsHSET).
(* lam *)
apply (pre_composition_functor _ _ _ _ _ option_functor).
Defined.

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

Lemma omega_cocont_LambdaFunctor : omega_cocont LambdaFunctor.
Proof.
apply omega_cocont_sum_of_functors.
  apply (Products_functor_precat _ _ ProductsHSET).
  apply functor_category_has_homsets.
  apply functor_category_has_homsets.
  apply omega_cocont_constant_functor.
  apply functor_category_has_homsets.
apply omega_cocont_sum_of_functors.
  apply (Products_functor_precat _ _ ProductsHSET).
  apply functor_category_has_homsets.
  apply functor_category_has_homsets.
  apply omega_cocont_functor_composite.
  apply functor_category_has_homsets.
  apply omega_cocont_delta_functor.
  apply (Products_functor_precat _ _ ProductsHSET).
  apply functor_category_has_homsets.
  apply omega_cocont_binproduct_functor.
  apply functor_category_has_homsets.
apply omega_cocont_pre_composition_functor.
Defined.

End lambdacalculus.