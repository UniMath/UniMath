(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents : 

- Various helper lemmas that should be moved upstream
                	
           
************************************************************)


Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

(** to Foundations *)

Lemma transportf_idpath (A : UU) (B : A -> UU) (a : A) (b : B a)
: transportf _ (idpath a) b = b.
Proof.
  apply idpath.
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


(** to functor_categories.v *)


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


(** to whiskering.v *)

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



(** to CategoryTheory/limits/coproducts.v *)

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

Lemma CoproductArrow_eq_cor (f f' : CoproductObject C (CC a b) ⇒ c) 
  : CoproductIn1 _ _;; f = CoproductIn1 _ _;; f' → CoproductIn2 _ _;; f = CoproductIn2 _ _;; f' → 
      f = f' . 
Proof.
  intros Hyp1 Hyp2.
  rewrite (CoproductArrowEta _ _ _ _ _ f).
  rewrite (CoproductArrowEta _ _ _ _ _ f').
  apply CoproductArrow_eq; assumption.
Qed.

(** specialized versions of beta rules for coproducts *)
(* all the following lemmas for manipulation of the hypothesis
Lemma CoproductIn1Commutes_left (f : a ⇒ c)(g : b ⇒ c)(h : a ⇒ c): CoproductIn1 C (CC _ _) ;; CoproductArrow C (CC _ _) f g = h -> f = h. 
Proof.
  intro Hyp.
  rewrite CoproductIn1Commutes in Hyp. 
  exact Hyp.
Qed.

Lemma CoproductIn1Commutes_right (f : a ⇒ c)(g : b ⇒ c)(h : a ⇒ c): h = CoproductIn1 C (CC _ _) ;; CoproductArrow C (CC _ _) f g -> h = f. 
Proof.
  intro Hyp.
  rewrite CoproductIn1Commutes in Hyp. 
  exact Hyp.
Qed.

Lemma CoproductIn2Commutes_left (f : a ⇒ c)(g : b ⇒ c)(h : b ⇒ c): CoproductIn2 C (CC _ _) ;; CoproductArrow C (CC _ _) f g = h -> g = h. 
Proof.
  intro Hyp.
  rewrite CoproductIn2Commutes in Hyp. 
  exact Hyp.
Qed.

Lemma CoproductIn2Commutes_right (f : a ⇒ c)(g : b ⇒ c)(h : b ⇒ c): h = CoproductIn2 C (CC _ _) ;; CoproductArrow C (CC _ _) f g -> h = g. 
Proof.
  intro Hyp.
  rewrite CoproductIn2Commutes in Hyp. 
  exact Hyp.
Qed.

Lemma CoproductIn1Commutes_left_in_ctx (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : a ⇒ d): CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h) = h' -> f ;; h = h'. 
Proof.
  intro Hyp.
  rewrite assoc in Hyp.
  rewrite CoproductIn1Commutes in Hyp. 
  exact Hyp.
Qed.

Lemma CoproductIn1Commutes_right_in_ctx (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : a ⇒ d): h' = CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h)  -> h' = f ;; h. 
Proof.
  intro Hyp.
  apply pathsinv0 in Hyp.
  apply pathsinv0.
  exact (CoproductIn1Commutes_left_in_ctx _ _ _ _ Hyp).
Qed.

Lemma CoproductIn2Commutes_left_in_ctx (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : b ⇒ d): CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h) = h' -> g ;; h = h'. 
Proof.
  intro Hyp.
  rewrite assoc in Hyp.
  rewrite CoproductIn2Commutes in Hyp. 
  exact Hyp.
Qed.

Lemma CoproductIn2Commutes_right_in_ctx (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : b ⇒ d): h' = CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h)  -> h' = g ;; h. 
Proof.
  intro Hyp.
  apply pathsinv0 in Hyp.
  apply pathsinv0.
  exact (CoproductIn2Commutes_left_in_ctx _ _ _ _ Hyp).
Qed.

Lemma CoproductIn2Commutes_right_in_double_ctx (g0 : x ⇒ b)(f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : x ⇒ d): h' = g0 ;; CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h)  -> h' = g0 ;; g ;; h. 
Proof.
  intro Hyp.
  rewrite Hyp.
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite assoc.
  rewrite CoproductIn2Commutes.  
  apply idpath.
Qed.
*)


(* optimized versions in direct style *)
Lemma CoproductIn1Commutes_right_dir (f : a ⇒ c)(g : b ⇒ c)(h : a ⇒ c): h = f -> h = CoproductIn1 C (CC _ _) ;; CoproductArrow C (CC _ _) f g. 
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0.
  apply CoproductIn1Commutes. 
Qed.

Lemma CoproductIn2Commutes_right_dir (f : a ⇒ c)(g : b ⇒ c)(h : b ⇒ c): h = g -> h = CoproductIn2 C (CC _ _) ;; CoproductArrow C (CC _ _) f g. 
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0.
  apply CoproductIn2Commutes. 
Qed.

Lemma CoproductIn1Commutes_right_in_ctx_dir (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : a ⇒ d): h' = f ;; h -> h' = CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h). 
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite assoc.
  rewrite CoproductIn1Commutes.
  apply idpath.
Qed.

Lemma CoproductIn2Commutes_right_in_ctx_dir (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : b ⇒ d): h' = g ;; h -> h' = CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h). 
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite assoc.
  rewrite CoproductIn2Commutes.
  apply idpath.
Qed.

Lemma CoproductIn1Commutes_left_dir (f : a ⇒ c)(g : b ⇒ c)(h : a ⇒ c): f = h -> CoproductIn1 C (CC _ _) ;; CoproductArrow C (CC _ _) f g = h. 
Proof.
  intro Hyp.
  rewrite Hyp.
  apply CoproductIn1Commutes. 
Qed.

Lemma CoproductIn2Commutes_left_dir (f : a ⇒ c)(g : b ⇒ c)(h : b ⇒ c): g = h -> CoproductIn2 C (CC _ _) ;; CoproductArrow C (CC _ _) f g = h. 
Proof.
  intro Hyp.
  rewrite Hyp.
  apply CoproductIn2Commutes. 
Qed.

Lemma CoproductIn1Commutes_left_in_ctx_dir (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : a ⇒ d): f ;; h = h' -> CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h) = h'. 
Proof.
  intro Hyp.
  rewrite <- Hyp.
  rewrite assoc.
  rewrite CoproductIn1Commutes.
  apply idpath.
Qed.

Lemma CoproductIn2Commutes_left_in_ctx_dir (f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : b ⇒ d): g ;; h = h' -> CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h) = h'. 
Proof.
  intro Hyp.
  rewrite <- Hyp.
  rewrite assoc.
  rewrite CoproductIn2Commutes.
  apply idpath.
Qed.

Lemma CoproductIn1Commutes_right_in_double_ctx_dir (g0 : x ⇒ a)(f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : x ⇒ d): h' = g0 ;; f ;; h -> h' = g0 ;; CoproductIn1 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite assoc.
  rewrite CoproductIn1Commutes.
  apply idpath.
Qed.

Lemma CoproductIn2Commutes_right_in_double_ctx_dir (g0 : x ⇒ b)(f : a ⇒ c)(g : b ⇒ c)(h : c ⇒ d)(h' : x ⇒ d): h' = g0 ;; g ;; h -> h' = g0 ;; CoproductIn2 C (CC _ _) ;; (CoproductArrow C (CC _ _) f g ;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite assoc.
  rewrite CoproductIn2Commutes.  
  apply idpath.
Qed.
(** end of specialized versions of the beta laws for coproducts *) 


(* do we ever want to create a multitude of similar lemmas for other rewrite rules?
Lemma id_left_to_the_right (C': precategory)(a b : C')(f h : C' ⟦ a, b ⟧): h = f -> h = identity a;; f.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0, id_left.
Qed.

Lemma id_left_to_the_right_in_ctx (C': precategory)(a b c: C')(f : C' ⟦ a, b ⟧)(g : C' ⟦ b, c ⟧)(h : C' ⟦ a, c ⟧): h = f ;; g -> h = identity a ;; f ;; g.
Proof.
  intro Hyp.
  rewrite Hyp.
  rewrite id_left.
  apply idpath.
Qed.


Lemma assoc_to_the_right (C' : precategory) (a b c d : C') (f : C' ⟦ a, b ⟧)
       (g : C' ⟦ b, c ⟧) (h : C' ⟦ c, d ⟧)(res: C' ⟦ a, d ⟧) : res = f;; g;; h -> res = f;; (g;; h).
Proof.
  intro Hyp.
  rewrite Hyp.
  apply pathsinv0, assoc.
Qed.

Lemma assoc_back_to_the_right (C' : precategory) (a b c d : C') (f : C' ⟦ a, b ⟧)
       (g : C' ⟦ b, c ⟧) (h : C' ⟦ c, d ⟧)(res: C' ⟦ a, d ⟧) : res = f;; (g;; h) -> res = f;; g;; h.
Proof.
  intro Hyp.
  rewrite Hyp.
  apply assoc.
Qed.
*)

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


(** to CategoryTheory/limits/products.v *)


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
