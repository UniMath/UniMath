Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.
Require Import RezkCompletion.whiskering.
Require Import RezkCompletion.limits.coproducts.
Require Import UnicodeNotations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Lemma functor_id_id (A B : precategory) (G : functor A B) (a : A) (f : a ⇒ a)
  : f = identity _ → #G f = identity _ .
Proof.
  intro e.
  subst.
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


End Coproducts.

