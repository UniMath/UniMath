Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

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
Require Import UniMath.CategoryTheory.chains.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.EquivalencesExamples.
Require Import UniMath.CategoryTheory.AdjunctionHomTypesWeq.
Require Import UniMath.CategoryTheory.polynomialfunctors.
Require Import UniMath.CategoryTheory.exponentials.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

(* The functor "* : C^2 -> C" is omega cocont *)
Section binprod_functor.

Variables (C : precategory) (PC : Products C) (hsC : has_homsets C).
Variables (hE : has_exponentials PC).

Definition inc1 (cAB : chain (product_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K) :
  forall i j,
              C ⟦ ProductObject C (PC (pr1 (pr1 cAB i)) (pr2 (dob cAB j))),
                  ProductObject C (PC (pr1 (pr1 cAB (S i))) (pr2 (dob cAB j))) ⟧.
Proof.
intros i j.
apply (ProductOfArrows _ (PC _ _) (PC _ _) (pr1 (dmor cAB (idpath _))) (identity (pr2 (dob cAB j)))).
Defined.

Definition inc2 (cAB : chain (product_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K) :
  forall i j,
              C ⟦ ProductObject C (PC (pr1 (pr1 cAB i)) (pr2 (dob cAB j))),
                  ProductObject C (PC (pr1 (pr1 cAB i)) (pr2 (dob cAB (S j)))) ⟧.
Proof.
intros i j.
apply (ProductOfArrows _ (PC _ _) (PC _ _) (identity (pr1 (dob cAB _))) (pr2 (dmor cAB (idpath _)))).
Defined.

Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.

Definition fun_lt (cAB : chain (product_precategory C C)) :
  forall i j, i < j ->
              C ⟦ ProductObject C (PC (pr1 (pr1 cAB i)) (pr2 (dob cAB j))),
                  ProductObject C (PC (pr1 (pr1 cAB j)) (pr2 (dob cAB j))) ⟧.
Proof.
intros i j hij.
apply (ProductOfArrows _ _ _ (pr1 (chain_mor cAB _ _ hij)) (identity _)).
Defined.

Definition fun_gt (cAB : chain (product_precategory C C)) :
  forall i j, i > j ->
              C ⟦ ProductObject C (PC (pr1 (pr1 cAB i)) (pr2 (dob cAB j))),
                  ProductObject C (PC (pr1 (pr1 cAB i)) (pr2 (dob cAB i))) ⟧.
Proof.
intros i j hij.
apply (ProductOfArrows _ _ _ (identity _) (pr2 (chain_mor cAB _ _ hij))).
Defined.

(* Lemma to construct ccAiB_K *)
Lemma temp (cAB : chain (product_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K)
  : ∀ i : nat, cocone (mapchain (constprod_functor1 PC (pr1 (pr1 cAB i))) (mapchain (pr2_functor C C) cAB)) K.
Proof.
intro i.
simple refine (mk_cocone _ _).
+ simpl; intro j.
unfold product_functor_ob; simpl.
destruct (natlthorgeh i j).
apply (fun_lt cAB _ _ h ;; coconeIn ccK j).
destruct (natgehchoice _ _ h) as [H|H].
apply (fun_gt cAB _ _ H ;; coconeIn ccK i).
rewrite H.
apply (coconeIn ccK j).
+ simpl; intros j k e.
destruct e; simpl.
unfold product_functor_mor.
simpl.
destruct (natlthorgeh i j).
destruct (natlthorgeh i (S j)).
rewrite assoc.
rewrite <- (coconeInCommutes ccK j (S j) (idpath _)).
simpl.
rewrite assoc.
apply cancel_postcomposition.
unfold fun_lt.
rewrite ProductOfArrows_comp.
rewrite id_left.
eapply pathscomp0.
apply ProductOfArrows_comp.
rewrite id_right.
apply ProductOfArrows_eq; trivial.
rewrite id_left.
simpl.
destruct (natlehchoice4 i j h0).
simpl.
apply cancel_postcomposition.
admit.
admit.
admit.
admit.
Admitted.

Lemma omega_cocont_binproduct_functor : omega_cocont (binproduct_functor PC).
Proof.
intros cAB LM ccLM HccLM K ccK; simpl in *.
generalize (isColimCocone_pr2_functor _ _ hsC _ _ _ HccLM).
generalize (isColimCocone_pr1_functor _ _ hsC _ _ _ HccLM).
set (L := pr1 LM); set (M := pr2 LM).
set (cA := mapchain (pr1_functor C C) cAB).
set (cB := mapchain (pr2_functor C C) cAB).
intros HA HB.

(* Form the colimiting cocones of "A_i * B_0 -> A_i * B_1 -> ..." *)
simple refine (let HAiB : forall i, isColimCocone _ _ (mapcocone (constprod_functor1 PC (pr1 (pr1 cAB i)))
                                                      _ (cocone_pr2_functor C C _ LM ccLM)) := _ in _).
{ intro i.
  apply (omega_cocont_constprod_functor1 _ PC hsC hE (pr1 (pr1 cAB i)) _ _ _ HB).
}
fold cB in HAiB; fold M in HAiB; simpl in HAiB.

(* Turn HAiB into a ColimCocone: *)
simple refine (let CCAiB : forall i, ColimCocone (mapdiagram (constprod_functor1 PC (pr1 (pr1 cAB i))) cB) := _ in _).
{ intro i.
mkpair.
mkpair.
apply (((constprod_functor1 PC (pr1 (pr1 cAB i))) M)).
Focus 2.
apply (HAiB i).
}

generalize (omega_cocont_constprod_functor2 _ PC hsC hE M _ _ _ HA); intro HAiM.

(* Turn HAiM into a ColimCocone: *)
simple refine (let X : ColimCocone (mapdiagram (constprod_functor2 PC M) cA) := _ in _).
{
  mkpair.
  - mkpair.
    + apply (ProductObject _ (PC L M)).
    + apply (mapcocone (constprod_functor2 PC M) cA (cocone_pr1_functor C C cAB LM ccLM)).
  - apply HAiM.
}

simple refine (let ccAiB_K : forall i, cocone (mapchain (constprod_functor1 PC (pr1 (pr1 cAB i))) cB) K := _ in _).
{ simpl; intro i.


(* INLINED temp *)
simple refine (mk_cocone _ _).
+ simpl; intro j.
unfold product_functor_ob; simpl.
destruct (natlthorgeh i j).
apply (fun_lt cAB _ _ h ;; coconeIn ccK j).
destruct (natgehchoice _ _ h) as [H|H].
apply (fun_gt cAB _ _ H ;; coconeIn ccK i).
rewrite H.
apply (coconeIn ccK j).
+ simpl; intros j k e.
destruct e; simpl.
unfold product_functor_mor.
simpl.
destruct (natlthorgeh i j).
destruct (natlthorgeh i (S j)).
rewrite assoc.
rewrite <- (coconeInCommutes ccK j (S j) (idpath _)).
simpl.
rewrite assoc.
apply cancel_postcomposition.
unfold fun_lt.
rewrite ProductOfArrows_comp.
rewrite id_left.
eapply pathscomp0.
apply ProductOfArrows_comp.
rewrite id_right.
apply ProductOfArrows_eq; trivial.
rewrite id_left.
simpl.
destruct (natlehchoice4 i j h0).
simpl.
apply cancel_postcomposition.
admit.
admit.
admit.
admit.

(* apply temp. *)
(* apply ccK. *)
}

simple refine (let ccAiM_K : cocone (mapdiagram (constprod_functor2 PC M) cA) K := _ in _).
{
simple refine (mk_cocone _ _).
- simpl; intro i.
apply (colimArrow (CCAiB i) K (ccAiB_K i)).
- simpl.
intros m n e.
apply (colimArrowUnique (CCAiB m)).
simpl.
intros x.
admit.
}

mkpair.
- mkpair.
  + apply (colimArrow X K ccAiM_K).
  + intro i.
    generalize (colimArrowCommutes X K ccAiM_K i).
assert (H : coconeIn ccAiM_K i = colimArrow (CCAiB i) K (ccAiB_K i)).
apply idpath.
rewrite H.
intros HH.
generalize (colimArrowCommutes (CCAiB i) K (ccAiB_K i) i).
rewrite <- HH.
simpl.
destruct (natlthorgeh i i).
admit.
destruct (natgehchoice i i h).
admit.
simpl.
destruct p.
simpl.
intros HHH.
rewrite <- HHH.
rewrite assoc.
apply cancel_postcomposition.
unfold colimIn.
simpl.
unfold product_functor_mor.
simpl.
eapply pathsinv0.
eapply pathscomp0.
apply ProductOfArrows_comp.
rewrite id_left, id_right.
apply idpath.


-
intro t.
apply subtypeEquality.
+ admit.
+
simpl.
apply (colimArrowUnique X K ccAiM_K).
destruct t.
simpl.
intro i.
apply (colimArrowUnique (CCAiB i) K (ccAiB_K i)).
intros j.
simpl.
destruct (natlthorgeh i j).
simpl.
rewrite <- (p j).
unfold fun_lt.
rewrite !assoc.
apply cancel_postcomposition.
unfold colimIn.
simpl.
unfold product_functor_mor.
simpl.
eapply pathscomp0.
apply ProductOfArrows_comp.
eapply pathsinv0.
eapply pathscomp0.
apply ProductOfArrows_comp.
rewrite !id_left, id_right.
apply ProductOfArrows_eq; trivial.
apply (maponpaths pr1 (chain_mor_commutes cAB LM ccLM i j h)).


destruct (natgehchoice i j h).

simpl.
rewrite <- (p i).
unfold fun_gt.
rewrite !assoc.
apply cancel_postcomposition.
unfold colimIn.
simpl.
unfold product_functor_mor.
simpl.
eapply pathscomp0.
apply ProductOfArrows_comp.
eapply pathsinv0.
eapply pathscomp0.
apply ProductOfArrows_comp.
rewrite !id_left, id_right.
apply ProductOfArrows_eq; trivial.
rewrite <- (chain_mor_commutes cAB LM ccLM _ _ h0).
apply idpath.

destruct p0.
simpl.
rewrite <- (p i).
rewrite assoc.
apply cancel_postcomposition.
simpl.
unfold colimIn.
simpl.
unfold product_functor_mor.
simpl.
eapply pathscomp0.
apply ProductOfArrows_comp.
rewrite id_left, id_right.
apply idpath.
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