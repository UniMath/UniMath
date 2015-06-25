Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.
Require Import UniMath.RezkCompletion.whiskering.
Require Import UniMath.RezkCompletion.limits.coproducts.
Require Import UniMath.RezkCompletion.limits.products.
Require Import UnicodeNotations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Lemma transportf_idpath (A : UU) (B : A -> UU) (a : A) (b : B a)
: transportf _ (idpath a) b = b.
Proof.
  apply idpath.
Defined.

Section Constant_Functor.
Variables C D : precategory.
Variable d : D.

Definition constant_functor_data: functor_data C D :=
   functor_data_constr C D (fun _ => d) (fun _ _ _  => identity _) .

Lemma is_functor_constant: is_functor constant_functor_data.
Proof.
  split; simpl.
  red; intros; apply idpath.
  red; intros; simpl.
  apply pathsinv0.
  apply id_left.
Qed.

Definition constant_functor: functor C D := tpair _ _ is_functor_constant.

End Constant_Functor.


Lemma functor_id_id (A B : precategory) (G : functor A B) (a : A) (f : a ⇒ a)
  : f = identity _ → #G f = identity _ .
Proof.
  intro e.
  rewrite e.
  apply functor_id.
Defined.

Lemma path_to_ctr (A : UU) (B : A -> UU) (isc : iscontr (total2 (fun a => B a))) 
           (a : A) (p : B a) : a = pr1 (pr1 isc).
Proof.
  set (Hi := tpair _ a p).
  apply (maponpaths pr1 (pr2 isc Hi)).
Defined.

Lemma dirprodeq (A B : UU) (ab ab' : A × B) : 
  pr1 ab = pr1 ab' → pr2 ab = pr2 ab' → ab = ab'.
Proof.
  intros H H'.
  destruct ab as [a b].
  destruct ab' as [a' b']; simpl in *.
  induction H.
  induction H'.
  apply idpath.
Defined.

Lemma is_nat_trans_post_whisker (B C D : precategory)
   (G H : functor B C) (gamma : nat_trans G H) (K : functor C D):
  is_nat_trans (functor_composite _ _ _ G K)
                         (functor_composite _ _ _ H K)
     (fun b : B => #K (gamma b)).
Proof.
  unfold is_nat_trans.
  intros b b' f.
  simpl.
  rewrite <- functor_comp.
  rewrite (nat_trans_ax gamma).
  rewrite functor_comp.
  apply idpath.
Qed.

Definition post_whisker {B C D : precategory} (hsC : has_homsets C) (hsD : has_homsets D)
   (G H: ob [B, C, hsC]) (gamma : G --> H) (I : ob [C, D, hsD]) 
  : functor_compose _ _ G I --> functor_compose _ _ H I.
Proof.
  exists (fun b : B => #(pr1 I) (pr1 gamma b)).
  apply is_nat_trans_post_whisker.
Defined.

Section nat_trans_eq.

Variables C D : precategory.
Variable hsD : has_homsets D.
Variables F G : functor C D.
Variables alpha beta : nat_trans F G.

Definition nat_trans_eq_weq : weq (alpha = beta) (forall c, alpha c = beta c).
Proof.
  eapply weqcomp.
  - apply total2_paths_isaprop_equiv. 
    intro x. apply isaprop_is_nat_trans. apply hsD.
  - apply weqtoforallpaths.
Defined.
End nat_trans_eq.


Section Coproducts.

Variable C : precategory.
Variable CC : Coproducts C.
Variables a b c d x y : C.

Lemma CoproductArrow_eq (f f' : a ⇒ c) (g g' : b ⇒ c) 
  : f = f' → g = g' → 
      CoproductArrow _ (CC _ _) f g = CoproductArrow _ _ f' g'. 
Proof.
  induction 1.
  induction 1.
  apply idpath.
Qed.


Definition CoproductOfArrows_comp (f : a ⇒ c) (f' : b ⇒ d) (g : c ⇒ x) (g' : d ⇒ y) 
  : CoproductOfArrows _ (CC a b) (CC c d) f f' ;; 
    CoproductOfArrows _ (CC _ _) (CC _ _) g g' 
    =
    CoproductOfArrows _ (CC _ _) (CC _ _)(f ;; g) (f' ;; g').
Proof.
  apply CoproductArrowUnique.
  - rewrite assoc.
    rewrite CoproductOfArrowsIn1.
    rewrite <- assoc.
    rewrite CoproductOfArrowsIn1.
    apply assoc.
  - rewrite assoc.
    rewrite CoproductOfArrowsIn2.
    rewrite <- assoc.
    rewrite CoproductOfArrowsIn2.
    apply assoc.
Qed.

Definition CoproductOfArrows_eq (f f' : a ⇒ c) (g g' : b ⇒ d) 
  : f = f' → g = g' → 
      CoproductOfArrows _ _ _ f g = CoproductOfArrows _ (CC _ _) (CC _ _) f' g'. 
Proof.
  induction 1.
  induction 1.
  apply idpath.
Qed.

Lemma precompWithCoproductArrow_eq  (CCab : CoproductCocone _ a b) 
    (CCcd : CoproductCocone _ c d) (f : a ⇒ c) (g : b ⇒ d)
     (k : c ⇒ x) (h : d ⇒ x) (fk : a ⇒ x) (gh : b ⇒ x):
      fk = f ;; k → gh = g ;; h →
        CoproductOfArrows _ CCab CCcd f g ;; CoproductArrow _ CCcd k h =
         CoproductArrow _ CCab (fk) (gh).
Proof.
  intros H H'.
  rewrite H.
  rewrite H'.
  apply precompWithCoproductArrow.
Qed.

End Coproducts.

Section Products.

Variable C : precategory.
Variable CC : Products C.
Variables a b c d x y : C.

Definition ProductOfArrows_comp (f : a ⇒ c) (f' : b ⇒ d) (g : c ⇒ x) (g' : d ⇒ y) 
  : ProductOfArrows _ (CC c d) (CC a b) f f' ;; 
    ProductOfArrows _ (CC _ _) (CC _ _) g g' 
    =
    ProductOfArrows _ (CC _ _) (CC _ _)(f ;; g) (f' ;; g').
Proof.
  apply ProductArrowUnique.
  - rewrite <- assoc.
    rewrite ProductOfArrowsPr1.
    rewrite assoc.
    rewrite ProductOfArrowsPr1.
    apply pathsinv0.
    apply assoc.
  - rewrite <- assoc.
    rewrite ProductOfArrowsPr2.
    rewrite assoc.
    rewrite ProductOfArrowsPr2.
    apply pathsinv0.
    apply assoc.
Qed.

Definition ProductOfArrows_eq (f f' : a ⇒ c) (g g' : b ⇒ d) 
  : f = f' → g = g' → 
      ProductOfArrows _ _ _ f g = ProductOfArrows _ (CC _ _) (CC _ _) f' g'. 
Proof.
  induction 1.
  induction 1.
  apply idpath.
Qed.

End Products.

Section Product_unique.

Variable C : precategory.
Variable CC : Products C.
Variables a b : C.

Lemma Product_endo_is_identity (P : ProductCone _ a b) 
  (k : ProductObject _ P ⇒ ProductObject _ P) 
  (H1 : k ;; ProductPr1 _ P = ProductPr1 _ P)
  (H2 : k ;; ProductPr2 _ P = ProductPr2 _ P)
  : identity _ = k.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
  apply ProductArrowEta.
  apply pathsinv0.
  apply ProductArrowUnique; apply pathsinv0.
  + rewrite id_left. exact H1.
  + rewrite id_left. exact H2.
Qed.

End Product_unique.
