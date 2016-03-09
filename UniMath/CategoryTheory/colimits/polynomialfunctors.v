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
apply (preserves_colimit_comp hsE); [apply hF|apply hG].
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

Definition bincoproduct_functor_data : functor_data (product_precategory C C) C.
Proof.
mkpair.
- intros p.
  apply (CoproductObject _ (PC (pr1 p) (pr2 p))).
- simpl; intros p q f.
  apply (CoproductOfArrows _ (PC (pr1 p) (pr2 p)) (PC (pr1 q) (pr2 q)) (pr1 f) (pr2 f)).
Defined.

Definition bincoproduct_functor : functor (product_precategory C C) C.
Proof.
mkpair.
- apply bincoproduct_functor_data.
- split.
  + intro x; simpl.
    apply pathsinv0, Coproduct_endo_is_identity.
    * now rewrite CoproductOfArrowsIn1, id_left.
    * now rewrite CoproductOfArrowsIn2, id_left.
  + now intros x y z f g; simpl; rewrite CoproductOfArrows_comp.
Defined.

Lemma is_left_adjoint_bincoproduct_functor : is_left_adjoint bincoproduct_functor.
Proof.
apply (tpair _ (delta_functor _)).
mkpair.
- split.
  + mkpair.
    * simpl; intro p; set (x := pr1 p); set (y := pr2 p).
      split; [ apply (CoproductIn1 _ (PC x y)) | apply (CoproductIn2 _ (PC x y)) ].
    * abstract (intros p q f; unfold prodcatmor, compose; simpl;
                now rewrite CoproductOfArrowsIn1, CoproductOfArrowsIn2).
  + mkpair.
    * intro x; apply (CoproductArrow _ _ (identity x) (identity x)).
    * abstract (intros p q f; simpl;
                now rewrite precompWithCoproductArrow, postcompWithCoproductArrow,
                            id_right, id_left).
- split; simpl; intro x.
  + rewrite precompWithCoproductArrow, !id_right.
    apply pathsinv0, Coproduct_endo_is_identity;
      [ apply CoproductIn1Commutes | apply CoproductIn2Commutes ].
  + unfold prodcatmor, compose; simpl.
    now rewrite CoproductIn1Commutes, CoproductIn2Commutes.
Defined.

Lemma cocont_bincoproducts_functor : is_cocont bincoproduct_functor.
Proof.
apply (left_adjoint_cocont _ is_left_adjoint_bincoproduct_functor).
- apply has_homsets_product_precategory; apply hsC.
- apply hsC.
Defined.

Lemma omega_cocont_bincoproduct_functor: omega_cocont bincoproduct_functor.
Proof.
intros c L ccL; apply cocont_bincoproducts_functor.
Defined.

End bincoprod_functor.

(* Should go to ProductPrecategory.v *)
(* The functor "F * G : A * B -> C * D" is cocont *)
(* Section product_of_functors. *)

(* Variable A B C D : precategory. *)
(* Variables (F : functor A C) (G : functor B D). *)

(* Definition product_of_functors : functor (product_precategory A B) (product_precategory C D). *)
(* Admitted. *)

(* End product_of_functors. *)

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

Section temp.
Variables (C D : precategory) (PC : Products C) (HD : Coproducts D).
Variables (hsC : has_homsets C) (hsD : has_homsets D).

Definition sum_of_functors (F G : functor C D) : functor C D.
eapply functor_composite.
  eapply delta_functor.
eapply functor_composite.
  eapply pair_functor.
  (* eapply product_of_functors. *)
    apply F.
    apply G.
apply bincoproduct_functor.
apply HD.
Defined.

Lemma omega_cocont_sum_of_functors (F G : functor C D)
  (HF : omega_cocont F) (HG : omega_cocont G) : omega_cocont (sum_of_functors F G).
Proof.
apply (omega_cocont_functor_composite hsD).
  apply (omega_cocont_delta_functor _ PC).
  apply hsC.
apply (omega_cocont_functor_composite hsD).
  apply (omega_cocont_pair_functor _ _ _ _ _ _ hsC hsC hsD hsD HF HG).
apply omega_cocont_bincoproduct_functor.
apply hsD.
Defined.

End temp.

End polynomial_functors.

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