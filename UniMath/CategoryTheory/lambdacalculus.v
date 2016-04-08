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

(* The map to K from the "grid" *)
Definition map_to_K (cAB : chain (product_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K) i j :
  C⟦ProductObject C (PC (pr1 (pr1 cAB i)) (pr2 (dob cAB j))), K⟧.
Proof.
destruct (natlthorgeh i j).
- apply (fun_lt cAB _ _ h ;; coconeIn ccK j).
- destruct (natgehchoice _ _ h) as [H|H].
  * apply (fun_gt cAB _ _ H ;; coconeIn ccK i).
  * destruct H; apply (coconeIn ccK i).
Defined.

Lemma map_to_K_commutes (cAB : chain (product_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K)
  i j k (e : edge j k) :
   product_functor_mor C C PC (constant_functor C C (pr1 (pr1 cAB i)))
     (functor_identity C) (pr2 (dob cAB j)) (pr2 (dob cAB k))
     (pr2 (dmor cAB e)) ;; map_to_K cAB K ccK i k =
   map_to_K cAB K ccK i j.
Proof.
destruct e; simpl.
unfold product_functor_mor, map_to_K.
destruct (natlthorgeh i j) as [h|h].
- destruct (natlthorgeh i (S j)) as [h0|h0].
  * rewrite assoc, <- (coconeInCommutes ccK j (S j) (idpath _)), assoc; simpl.
    apply cancel_postcomposition; unfold fun_lt.
    rewrite ProductOfArrows_comp, id_left.
    eapply pathscomp0; [apply ProductOfArrows_comp|].
    rewrite id_right.
    apply ProductOfArrows_eq; trivial.
    rewrite id_left; simpl.
    destruct (natlehchoice4 i j h0) as [h1|h1].
    + apply cancel_postcomposition, maponpaths, maponpaths, isasetbool.
    + destruct h1; destruct (isirreflnatlth _ h).
  * destruct (isirreflnatlth _ (natlthlehtrans _ _ _ (natlthtolths _ _ h) h0)).
- destruct (natlthorgeh i (S j)) as [h0|h0].
  * destruct (natgehchoice i j h) as [h1|h1].
    + destruct (natlthchoice2 _ _ h1) as [h2|h2].
      { destruct (isirreflnatlth _ (istransnatlth _ _ _ h0 h2)). }
      { destruct h2; destruct (isirreflnatlth _ h0). }
    + destruct h1; simpl.
      rewrite <- (coconeInCommutes ccK i (S i) (idpath _)), assoc.
      unfold fun_lt.
      eapply pathscomp0.
      eapply cancel_postcomposition.
      apply ProductOfArrows_comp.
      rewrite id_left, id_right.
      apply cancel_postcomposition, ProductOfArrows_eq; trivial.
      simpl; destruct (natlehchoice4 i i h0) as [h1|h1]; [destruct (isirreflnatlth _ h1)|].
      apply maponpaths, maponpaths, isasetnat.
  * destruct (natgehchoice i j h) as [h1|h1].
    + destruct (natgehchoice i (S j) h0) as [h2|h2].
      { unfold fun_gt; rewrite assoc.
        eapply pathscomp0.
        eapply cancel_postcomposition.
        apply ProductOfArrows_comp.
        rewrite id_right.
        apply cancel_postcomposition.
        apply ProductOfArrows_eq; trivial.
        rewrite <- (chain_mor_commutes2 cAB _ _ h1 h2).
        apply idpath. }
      { destruct h.
        unfold fun_gt; simpl.
        generalize h1; clear h1.
        rewrite h2; intro h1.
        apply cancel_postcomposition.
        apply ProductOfArrows_eq; trivial; simpl.
        destruct (natlehchoice4 j j h1); [destruct (isirreflnatlth _ h)|].
        apply maponpaths, maponpaths, isasetnat. }
    + destruct h1; destruct (negnatgehnsn _ h0).
Qed.

(* The cocone over K from the A_i * B chain *)
Lemma ccAiB_K (cAB : chain (product_precategory C C)) (K : C)
  (ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K) i :
  cocone (mapchain (constprod_functor1 PC (pr1 (pr1 cAB i)))
         (mapchain (pr2_functor C C) cAB)) K.
Proof.
simple refine (mk_cocone _ _).
+ intro j; apply (map_to_K cAB K ccK i j).
+ simpl; intros j k e; apply map_to_K_commutes.
Defined.

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
set (HAiB :=
  fun i => omega_cocont_constprod_functor1 _ PC hsC hE (pr1 (pr1 cAB i)) _ _ _ HB).

(* Turn HAiB into a ColimCocone: *)
set (CCAiB := fun i => mk_ColimCocone _ _ _ (HAiB i)).

(* Define the HAiM ColimCocone: *)
set (HAiM :=
  mk_ColimCocone _ _ _ (omega_cocont_constprod_functor2 _ PC hsC hE M _ _ _ HA)).

set (ccAiB_K := fun i => ccAiB_K _ _ ccK i).

(* The f which is using in colimOfArrows *)
simple refine (let f i j : C
   ⟦ product_functor_ob C C PC (constant_functor C C (pr1 (pr1 cAB i)))
       (functor_identity C) (pr2 (dob cAB j)),
   product_functor_ob C C PC (constant_functor C C (pr1 (pr1 cAB (S i))))
     (functor_identity C) (pr2 (dob cAB j)) ⟧ := _ in _).
{ apply ProductOfArrows; [apply (dmor cAB (idpath _)) | apply identity ]. }

assert (fNat : ∀ i u v (e : edge u v),
   dmor (mapdiagram (constprod_functor1 PC _) cB) e ;; f i v =
   f i u ;; dmor (mapdiagram (constprod_functor1 PC _) cB) e).
{ intros i j k e; destruct e; simpl.
  eapply pathscomp0; [apply ProductOfArrows_comp|].
  eapply pathscomp0; [|eapply pathsinv0; apply ProductOfArrows_comp].
  now rewrite !id_left, !id_right.
}

(* Define the chain A_i * M *)
simple refine (let AiM_chain : chain C := _ in _).
{ mkpair.
  - intro i; apply (colim (CCAiB i)).
  - intros i j e; destruct e.
    apply (colimOfArrows (CCAiB i) (CCAiB (S i)) (f i) (fNat i)).
}

assert (AiM_chain_eq : forall i, dmor AiM_chain (idpath (S i)) =
                       dmor (mapdiagram (constprod_functor2 PC M) cA) (idpath _)).
{ intro i; simpl; unfold colimOfArrows, product_functor_mor; simpl.
  apply pathsinv0, colimArrowUnique.
  simpl; intro j.
  unfold colimIn; simpl; unfold product_functor_mor, f; simpl.
  eapply pathscomp0; [apply ProductOfArrows_comp|].
  apply pathsinv0.
  eapply pathscomp0; [apply ProductOfArrows_comp|].
  now rewrite !id_left, !id_right.
}

(* Define a cocone over K from the A_i * M chain *)
assert (ccAiM_K_subproof : ∀ u v (e : edge u v),
   dmor (mapdiagram (constprod_functor2 PC M) cA) e ;;
   colimArrow (CCAiB v) K (ccAiB_K v) = colimArrow (CCAiB u) K (ccAiB_K u)).
{ intros i j e; destruct e; simpl.
  generalize (AiM_chain_eq i); simpl; intro H; rewrite <- H; clear H; simpl.
  eapply pathscomp0.
  apply (precompWithColimOfArrows _ _ (CCAiB i) (CCAiB (S i)) _ _ K (ccAiB_K (S i))).
  apply (colimArrowUnique (CCAiB i) K (ccAiB_K i)).
  simpl; intros j.
  eapply pathscomp0; [apply (colimArrowCommutes (CCAiB i) K)|]; simpl.
  unfold map_to_K.
  destruct (natlthorgeh (S i) j).
  + destruct (natlthorgeh i j).
    * rewrite assoc; apply cancel_postcomposition.
      unfold f, fun_lt; simpl.
      eapply pathscomp0; [apply ProductOfArrows_comp|].
      now rewrite id_right, <- (chain_mor_commutes2 _ i j h0 h).
    * destruct (isasymmnatgth _ _ h h0).
  + destruct (natgehchoice (S i) j h).
    * destruct h.
      { destruct (natlthorgeh i j).
        - destruct (natlthchoice2 _ _ h) as [h2|h2].
          + destruct (isirreflnatlth _ (istransnatlth _ _ _ h0 h2)).
          + destruct h2; destruct (isirreflnatlth _ h0).
        - destruct (natgehchoice i j h).
          + destruct h.
            rewrite <- (coconeInCommutes ccK i _ (idpath _)); simpl.
            rewrite !assoc; apply cancel_postcomposition.
            unfold f, fun_gt.
            rewrite ProductOfArrows_comp.
            eapply pathscomp0; [apply ProductOfArrows_comp|].
            now rewrite !id_left, !id_right, (chain_mor_commutes3 cAB _ _ h0 h1).
          + destruct p.
            rewrite <- (coconeInCommutes ccK i _ (idpath _)), assoc.
            apply cancel_postcomposition.
            unfold f, fun_gt.
            eapply pathscomp0; [apply ProductOfArrows_comp|].
            rewrite id_left, id_right.
            apply ProductOfArrows_eq; trivial; simpl.
            destruct (natlehchoice4 i i h0); [destruct (isirreflnatlth _ h1)|].
            apply maponpaths, maponpaths, isasetnat.
       }
    * destruct p, h.
      destruct (natlthorgeh i (S i)); [|destruct (negnatgehnsn _ h)].
      apply cancel_postcomposition; unfold f, fun_lt.
      apply ProductOfArrows_eq; trivial; simpl.
      destruct (natlehchoice4 i i h); [destruct (isirreflnatlth _ h0)|].
      assert (H : idpath (S i) = maponpaths S p). apply isasetnat.
      now rewrite H.
}

set (ccAiM_K := mk_cocone _ ccAiM_K_subproof).

mkpair.
- mkpair.
  + apply (colimArrow HAiM K ccAiM_K).
  + intro i.
    generalize (colimArrowCommutes HAiM K ccAiM_K i).
    assert (H : coconeIn ccAiM_K i = colimArrow (CCAiB i) K (ccAiB_K i)).
      apply idpath.
    rewrite H; intros HH.
    generalize (colimArrowCommutes (CCAiB i) K (ccAiB_K i) i).
    rewrite <- HH; simpl; unfold map_to_K.
    destruct (natlthorgeh i i); [destruct (isirreflnatlth _ h)|].
    destruct (natgehchoice i i h); [destruct (isirreflnatgth _ h0)|].
    simpl; destruct h, p.
    intros HHH.
    rewrite <- HHH, assoc.
    apply cancel_postcomposition.
    unfold colimIn; simpl; unfold product_functor_mor; simpl.
    apply pathsinv0.
    eapply pathscomp0; [apply ProductOfArrows_comp|].
    now rewrite id_left, id_right.
- intro t.
  apply subtypeEquality; simpl.
  + intro; apply impred; intros; apply hsC.
  + apply (colimArrowUnique HAiM K ccAiM_K).
    destruct t; simpl; intro i.
    apply (colimArrowUnique (CCAiB i) K (ccAiB_K i)).
    simpl; intros j; unfold map_to_K.
    destruct (natlthorgeh i j).
    * rewrite <- (p j); unfold fun_lt.
      rewrite !assoc.
      apply cancel_postcomposition.
      unfold colimIn; simpl; unfold product_functor_mor; simpl.
      eapply pathscomp0; [apply ProductOfArrows_comp|].
      apply pathsinv0.
      eapply pathscomp0; [apply ProductOfArrows_comp|].
      rewrite !id_left, id_right.
      apply ProductOfArrows_eq; trivial.
      apply (maponpaths pr1 (chain_mor_commutes cAB LM ccLM i j h)).
    * destruct (natgehchoice i j h).
      { unfold fun_gt; rewrite <- (p i), !assoc.
        apply cancel_postcomposition.
        unfold colimIn; simpl; unfold product_functor_mor; simpl.
        eapply pathscomp0; [apply ProductOfArrows_comp|].
        apply pathsinv0.
        eapply pathscomp0; [apply ProductOfArrows_comp|].
        now rewrite !id_left, id_right, <- (chain_mor_commutes cAB LM ccLM _ _ h0). }
      { destruct p0.
        rewrite <- (p i), assoc.
        apply cancel_postcomposition.
        unfold colimIn; simpl; unfold product_functor_mor; simpl.
        eapply pathscomp0; [apply ProductOfArrows_comp|].
        now rewrite id_left, id_right. }
Qed.

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
  admit.
apply omega_cocont_pre_composition_functor.
Admitted.

End lambdacalculus.