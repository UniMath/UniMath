(**

     Anders Mörtberg, 2015-2016

*)



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
Require Import UniMath.CategoryTheory.exponentials.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section move_upstream.

Lemma paireta {A B : UU} (p : A × B) : p = (pr1 p,, pr2 p).
Proof.
destruct p; apply idpath.
Defined.

End move_upstream.

Section polynomial_functors.

(* The constant functor is omega cocontinuous *)
Lemma omega_cocont_constant_functor (C D : precategory) (hsD : has_homsets D)
  (x : D) : omega_cocont (constant_functor C D x).
Proof.
intros c L ccL HcL y ccy; simpl.
simple refine (tpair _ _ _).
- simple refine (tpair _ _ _).
  + apply (coconeIn ccy 0).
  + abstract (simpl; intro n; rewrite id_left;
              destruct ccy as [f Hf]; simpl in *;
              induction n; [apply idpath|];
              now rewrite IHn, <- (Hf n (S n) (idpath _)), id_left).
- abstract (simpl; intro p; apply subtypeEquality;
              [ intros f; apply impred; intro; apply hsD
              | now simpl; destruct p as [p H]; rewrite <- (H 0), id_left]).
Defined.

(* The identity functor is omega cocontinuous *)
Lemma omega_cocont_functor_identity (C : precategory) (hsC : has_homsets C) :
  omega_cocont (functor_identity C).
Proof.
intros c L ccL HcL.
apply (preserves_colimit_identity hsC _ _ _ HcL).
Defined.

(* Functor composition preserves omega cocontinuity *)
Lemma omega_cocont_functor_composite {C D E : precategory}
  (hsE : has_homsets E) (F : functor C D) (G : functor D E) :
  omega_cocont F -> omega_cocont G -> omega_cocont (functor_composite F G).
Proof.
intros hF hG c L cc.
apply (preserves_colimit_comp hsE); [ apply hF | apply hG ].
Defined.

(* A pair of functors (F,G) : A * B -> C * D is omega_cocont if F and G are *)
Section pair_functor.

Variables A B C D : precategory.
Variables (F : functor A C) (G : functor B D).
Variables (hsA : has_homsets A) (hsB : has_homsets B).
Variables (hsC : has_homsets C) (hsD : has_homsets D).

(* Maybe generalize these to arbitrary diagrams? *)
Lemma cocone_pr1_functor (cAB : chain (product_precategory A B))
  (ab : A × B) (ccab : cocone cAB ab) :
  cocone (mapchain (pr1_functor A B)cAB) (pr1 ab).
Proof.
simple refine (mk_cocone _ _).
- simpl; intro n; apply (pr1 (coconeIn ccab n)).
- abstract (simpl; intros m n e; now rewrite <- (coconeInCommutes ccab m n e)).
Defined.

Lemma isColimCocone_pr1_functor (cAB : chain (product_precategory A B))
  (ab : A × B) (ccab : cocone cAB ab) (Hccab : isColimCocone cAB ab ccab) :
   isColimCocone (mapchain (pr1_functor A B) cAB) (pr1 ab)
     (cocone_pr1_functor cAB ab ccab).
Proof.
intros x ccx.
simple refine (let HHH : cocone cAB (x,, pr2 ab) := _ in _).
{ simple refine (mk_cocone _ _).
  - simpl; intro n; split;
      [ apply (pr1 ccx n) | apply (# (pr2_functor A B) (pr1 ccab n)) ].
  - abstract(
    simpl; intros m n e; rewrite (paireta (dmor cAB e));
    apply pathsdirprod; [ apply (pr2 ccx m n e)
                        | apply (maponpaths dirprod_pr2 ((pr2 ccab) m n e)) ]).
}
destruct (Hccab _ HHH) as [[[x1 x2] p1] p2]; simpl in *.
mkpair.
- apply (tpair _ x1).
  abstract (intro n; apply (maponpaths pr1 (p1 n))).
- intro t.
  simple refine (let X : Σ x0,
           ∀ v : nat, coconeIn ccab v ;; x0 =
                      prodcatmor (pr1 ccx v) (pr2 (pr1 ccab v)) := _ in _).
  { mkpair.
    - split; [ apply (pr1 t) | apply (identity _) ].
    - abstract (intro n; rewrite id_right; apply pathsdirprod;
                 [ apply (pr2 t) | apply idpath ]).
  }
  abstract (apply subtypeEquality; simpl;
            [ intro f; apply impred; intro; apply hsA
            | apply (maponpaths (fun x => pr1 (pr1 x)) (p2 X))]).
Defined.

Lemma omega_cocont_pr1_functor : omega_cocont (pr1_functor A B).
Proof.
intros c L ccL M.
now apply isColimCocone_pr1_functor.
Defined.

Lemma cocone_pr2_functor (cAB : chain (product_precategory A B))
  (ab : A × B) (ccab : cocone cAB ab) :
  cocone (mapchain (pr2_functor A B) cAB) (pr2 ab).
Proof.
simple refine (mk_cocone _ _).
- simpl; intro n; apply (pr2 (coconeIn ccab n)).
- abstract (simpl; intros m n e; now rewrite <- (coconeInCommutes ccab m n e)).
Defined.

Lemma isColimCocone_pr2_functor (cAB : chain (product_precategory A B))
  (ab : A × B) (ccab : cocone cAB ab) (Hccab : isColimCocone cAB ab ccab) :
   isColimCocone (mapchain (pr2_functor A B) cAB) (pr2 ab)
     (cocone_pr2_functor cAB ab ccab).
Proof.
intros x ccx.
simple refine (let HHH : cocone cAB (pr1 ab,, x) := _ in _).
{ simple refine (mk_cocone _ _).
  - simpl; intro n; split;
      [ apply (# (pr1_functor A B) (pr1 ccab n)) | apply (pr1 ccx n) ].
  - abstract(
    simpl; intros m n e; rewrite (paireta (dmor cAB e)); apply pathsdirprod;
      [ apply (maponpaths pr1 (pr2 ccab m n e)) | apply (pr2 ccx m n e) ]).
 }
destruct (Hccab _ HHH) as [[[x1 x2] p1] p2]; simpl in *.
mkpair.
- apply (tpair _ x2).
  abstract (intro n; apply (maponpaths dirprod_pr2 (p1 n))).
- intro t.
  simple refine (let X : Σ x0,
           ∀ v : nat, coconeIn ccab v ;; x0 =
                      prodcatmor (pr1 (pr1 ccab v)) (pr1 ccx v) := _ in _).
  { mkpair.
    - split; [ apply (identity _) | apply (pr1 t) ].
    - abstract (intro n; rewrite id_right; apply pathsdirprod;
                 [ apply idpath | apply (pr2 t) ]).
  }
  abstract (apply subtypeEquality; simpl;
              [ intro f; apply impred; intro; apply hsB
              | apply (maponpaths (fun x => dirprod_pr2 (pr1 x)) (p2 X)) ]).
Defined.

Lemma omega_cocont_pr2_functor : omega_cocont (pr2_functor A B).
Proof.
intros c L ccL M.
now apply isColimCocone_pr2_functor.
Defined.

(* TODO: Opacify more *)
Lemma omega_cocont_pair_functor (HF : omega_cocont F) (HG : omega_cocont G) :
  omega_cocont (pair_functor F G).
Proof.
intros cAB ml ccml Hccml xy ccxy; simpl in *.
simple refine (let cFAX : cocone (mapdiagram F (mapchain (pr1_functor A B) cAB))
                                 (pr1 xy) := _ in _).
{ simple refine (mk_cocone _ _).
  - intro n; apply (pr1 (pr1 ccxy n)).
  - abstract (intros m n e; apply (maponpaths pr1 (pr2 ccxy m n e))).
}
simple refine (let cGBY : cocone (mapdiagram G (mapchain (pr2_functor A B)cAB))
                                 (pr2 xy) := _ in _).
{ simple refine (mk_cocone _ _).
  - intro n; apply (pr2 (pr1 ccxy n)).
  - abstract (intros m n e; apply (maponpaths dirprod_pr2 (pr2 ccxy m n e))).
}
destruct (HF _ _ _ (isColimCocone_pr1_functor cAB ml ccml Hccml) _ cFAX) as [[f hf1] hf2].
destruct (HG _ _ _ (isColimCocone_pr2_functor cAB ml ccml Hccml) _ cGBY) as [[g hg1] hg2].
simpl in *.
mkpair.
- apply (tpair _ (f,,g)).
  abstract (intro n; unfold prodcatmor, compose; simpl;
            now rewrite hf1, hg1, (paireta (coconeIn ccxy n))).
- intro t.
  apply subtypeEquality; simpl.
  + intro x; apply impred; intro.
    apply isaset_dirprod; [ apply hsC | apply hsD ].
  + destruct t as [[f1 f2] ?]; simpl in *.
    apply pathsdirprod.
    * apply (maponpaths pr1 (hf2 (f1,, (λ n, maponpaths pr1 (p n))))).
    * apply (maponpaths pr1 (hg2 (f2,, (λ n, maponpaths dirprod_pr2 (p n))))).
Defined.

End pair_functor.

(* The delta functor C -> C^2 mapping x to (x,x) is omega_cocont *)
Section delta_functor.

Variables (C : precategory) (PC : Products C) (hsC : has_homsets C).

Lemma cocont_delta_functor : is_cocont (delta_functor C).
Proof.
apply (left_adjoint_cocont _ (is_left_adjoint_delta_functor PC) hsC).
apply (has_homsets_product_precategory _ _ hsC hsC).
Defined.

Lemma omega_cocont_delta_functor : omega_cocont (delta_functor C).
Proof.
intros c L ccL.
apply cocont_delta_functor.
Defined.

End delta_functor.

(* The functor "+ : C^2 -> C" is cocont *)
Section bincoprod_functor.

Variables (C : precategory) (PC : Coproducts C) (hsC : has_homsets C).

Lemma cocont_bincoproducts_functor : is_cocont (bincoproduct_functor PC).
Proof.
apply (left_adjoint_cocont _ (is_left_adjoint_bincoproduct_functor PC)).
- apply has_homsets_product_precategory; apply hsC.
- apply hsC.
Defined.

Lemma omega_cocont_bincoproduct_functor: omega_cocont (bincoproduct_functor PC).
Proof.
intros c L ccL; apply cocont_bincoproducts_functor.
Defined.

End bincoprod_functor.

(* Definition sum_of_functors {C D : precategory}  (HD : Coproducts D) (F G : functor C D) := coproduct_functor _ _ HD F G. *)
Section sum_of_functors.

Variables (C D : precategory) (PC : Products C) (HD : Coproducts D).
Variables (hsC : has_homsets C) (hsD : has_homsets D).

Lemma omega_cocont_sum_of_functors (F G : functor C D)
  (HF : omega_cocont F) (HG : omega_cocont G) :
  omega_cocont (sum_of_functors HD F G).
Proof.
apply (omega_cocont_functor_composite hsD).
  apply (omega_cocont_delta_functor _ PC hsC).
apply (omega_cocont_functor_composite hsD).
  apply (omega_cocont_pair_functor _ _ _ _ _ _ hsC hsC hsD hsD HF HG).
apply (omega_cocont_bincoproduct_functor _ _ hsD).
Defined.

End sum_of_functors.

Section constprod_functors.

Variables (C : precategory) (PC : Products C) (hsC : has_homsets C).
Variables (hE : has_exponentials PC).

Lemma cocont_constprod_functor1 (x : C) : is_cocont (constprod_functor1 PC x).
Proof.
apply (left_adjoint_cocont _ (hE _) hsC hsC).
Defined.

Lemma omega_cocont_constprod_functor1 (x : C) : omega_cocont (constprod_functor1 PC x).
Proof.
intros c L ccL.
apply cocont_constprod_functor1.
Defined.

Lemma cocont_constprod_functor2 (x : C) : is_cocont (constprod_functor2 PC x).
Proof.
apply left_adjoint_cocont; try apply hsC.
apply (is_left_adjoint_constprod_functor2 PC hsC), hE.
Defined.

Lemma omega_cocont_constprod_functor2 (x : C) : omega_cocont (constprod_functor2 PC x).
Proof.
intros c L ccL.
apply cocont_constprod_functor2.
Defined.

End constprod_functors.

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

Section omega_cocont_binproduct.
Variable cAB : chain (product_precategory C C).
Variable LM : C × C.
Variable ccLM : cocone cAB LM.
Variable HccLM : isColimCocone cAB LM ccLM.
Variable K : C.
Variable ccK : cocone (mapdiagram (binproduct_functor PC) cAB) K.
Let L := pr1 LM : C.
Let M := pr2 LM : (λ _ : C, C) (pr1 LM).
Let cA := mapchain (pr1_functor C C) cAB : chain C.
Let cB := mapchain (pr2_functor C C) cAB : chain C.
Let HA := isColimCocone_pr1_functor _ _ hsC _ _ _ HccLM
  : isColimCocone cA L (cocone_pr1_functor C C cAB LM ccLM).
Let HB := isColimCocone_pr2_functor _ _ hsC _ _ _ HccLM
  : isColimCocone cB M (cocone_pr2_functor C C cAB LM ccLM).

(* Form the colimiting cocones of "A_i * B_0 -> A_i * B_1 -> ..." *)
Let HAiB :=
  fun i => omega_cocont_constprod_functor1 _ PC hsC hE (pr1 (pr1 cAB i)) _ _ _ HB.

(* Turn HAiB into a ColimCocone: *)
Let CCAiB := fun i => mk_ColimCocone _ _ _ (HAiB i).

(* Define the HAiM ColimCocone: *)
Let HAiM :=
  mk_ColimCocone _ _ _ (omega_cocont_constprod_functor2 _ PC hsC hE M _ _ _ HA).

Let ccAiB_K := fun i => ccAiB_K _ _ ccK i.

(* The f which is using in colimOfArrows *)
Local Definition f i j : C
   ⟦ product_functor_ob C C PC (constant_functor C C (pr1 (pr1 cAB i)))
       (functor_identity C) (pr2 (dob cAB j)),
   product_functor_ob C C PC (constant_functor C C (pr1 (pr1 cAB (S i))))
     (functor_identity C) (pr2 (dob cAB j)) ⟧.
Proof.
  apply ProductOfArrows; [apply (dmor cAB (idpath _)) | apply identity ].
Defined.

Local Lemma fNat : ∀ i u v (e : edge u v),
   dmor (mapdiagram (constprod_functor1 PC _) cB) e ;; f i v =
   f i u ;; dmor (mapdiagram (constprod_functor1 PC _) cB) e.
Proof.
  intros i j k e; destruct e; simpl.
  eapply pathscomp0; [apply ProductOfArrows_comp|].
  eapply pathscomp0; [|eapply pathsinv0; apply ProductOfArrows_comp].
  now rewrite !id_left, !id_right.
Qed.

(* Define the chain A_i * M *)
Local Definition AiM_chain : chain C.
Proof.
  mkpair.
  - intro i; apply (colim (CCAiB i)).
  - intros i j e; destruct e.
    apply (colimOfArrows (CCAiB i) (CCAiB (S i)) (f i) (fNat i)).
Defined.

Local Lemma AiM_chain_eq : forall i, dmor AiM_chain (idpath (S i)) =
                       dmor (mapdiagram (constprod_functor2 PC M) cA) (idpath _).
Proof.
  intro i; simpl; unfold colimOfArrows, product_functor_mor; simpl.
  apply pathsinv0, colimArrowUnique.
  simpl; intro j.
  unfold colimIn; simpl; unfold product_functor_mor, f; simpl.
  eapply pathscomp0; [apply ProductOfArrows_comp|].
  apply pathsinv0.
  eapply pathscomp0; [apply ProductOfArrows_comp|].
  now rewrite !id_left, !id_right.
Qed.

(* Define a cocone over K from the A_i * M chain *)
Local Lemma ccAiM_K_subproof : ∀ u v (e : edge u v),
   dmor (mapdiagram (constprod_functor2 PC M) cA) e ;;
   colimArrow (CCAiB v) K (ccAiB_K v) = colimArrow (CCAiB u) K (ccAiB_K u).
Proof.
  intros i j e; destruct e; simpl.
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
Qed.

Local Definition ccAiM_K := mk_cocone _ ccAiM_K_subproof.

Local Lemma is_cocone_morphism :
 ∀ v : nat,
   ProductOfArrows C (PC L M) (PC (pr1 (dob cAB v)) (pr2 (dob cAB v)))
     (pr1 (coconeIn ccLM v)) (pr2 (coconeIn ccLM v)) ;;
   colimArrow HAiM K ccAiM_K = coconeIn ccK v.
Proof.
  intro i.
  generalize (colimArrowCommutes HAiM K ccAiM_K i).
  assert (H : coconeIn ccAiM_K i = colimArrow (CCAiB i) K (ccAiB_K i)).
  { apply idpath. }
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
Qed.

Lemma is_unique_cocone_morphism : ∀
   t : Σ x : C ⟦ ProductObject C (PC L M), K ⟧,
       ∀ v : nat,
       ProductOfArrows C (PC L M) (PC (pr1 (dob cAB v)) (pr2 (dob cAB v)))
         (pr1 (coconeIn ccLM v)) (pr2 (coconeIn ccLM v)) ;; x =
       coconeIn ccK v, t = colimArrow HAiM K ccAiM_K,, is_cocone_morphism.
Proof.
  intro t.
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

Definition isColimProductOfColims :  ∃! x : C ⟦ ProductObject C (PC L M), K ⟧,
   ∀ v : nat,
   ProductOfArrows C (PC L M) (PC (pr1 (dob cAB v)) (pr2 (dob cAB v)))
     (pr1 (coconeIn ccLM v)) (pr2 (coconeIn ccLM v)) ;; x =
   coconeIn ccK v.
Proof.
mkpair.
- mkpair.
  + apply (colimArrow HAiM K ccAiM_K).
  + apply is_cocone_morphism.
- apply is_unique_cocone_morphism.
Defined.

End omega_cocont_binproduct.


Lemma omega_cocont_binproduct_functor : omega_cocont (binproduct_functor PC).
Proof.
intros cAB LM ccLM HccLM K ccK; simpl in *.
apply isColimProductOfColims.
apply HccLM.
Defined.

End binprod_functor.

End polynomial_functors.
