(** organizes the (action-based) strong functors between two fixed precategories into a (pre-)category

Author: Ralph Matthes 2021
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.Actions.
Require Import UniMath.CategoryTheory.Monoidal.ActionBasedStrength.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.Core.Univalence.

Local Open Scope cat.

Section Strong_Functor_Category.

Context (Mon_V : monoidal_precat).

Context {A A': precategory}.
Context (actn : action Mon_V A)(actn' : action Mon_V A').

Local Definition odot := pr1 actn.
Local Definition odot' := pr1 actn'.

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (#odot (f #, g)) (at level 31).
Notation "X ⊙' Y" := (odot' (X , Y)) (at level 31).
Notation "f #⊙' g" := (#odot' (f #, g)) (at level 31).

Local Definition ζ (FF : actionbased_strong_functor Mon_V actn actn') := pr12 FF.

Section Strong_Functor_Category_mor.

  Context (FF GG : actionbased_strong_functor Mon_V actn actn').

  Context (η : FF ⟹ GG).

  Definition Strong_Functor_Category_mor_diagram (a: A) (v: Mon_V) : UU :=
    ζ FF (a,v) · η (a ⊙ v) = η a #⊙' id v · ζ GG (a,v).

  Definition quantified_strong_functor_category_mor_diagram : UU :=
    ∏ (a: A) (v: Mon_V), Strong_Functor_Category_mor_diagram a v.

End Strong_Functor_Category_mor.


Local Lemma Strong_Functor_Category_Mor_id_subproof (FF : actionbased_strong_functor Mon_V actn actn') a v :
  Strong_Functor_Category_mor_diagram FF FF (nat_trans_id FF) a v.
Proof.
  red.
  change (ζ FF (a, v) · nat_trans_id FF (a ⊙ v) = # odot' (id (FF a, v)) · ζ FF (a, v)).
  rewrite functor_id.
  now rewrite id_left, id_right.
Qed.

Local Lemma Strong_Functor_Category_Mor_comp_subproof (FF GG HH : actionbased_strong_functor Mon_V actn actn')
      (η : FF ⟹ GG) (η': GG ⟹ HH):
  quantified_strong_functor_category_mor_diagram FF GG η ->
  quantified_strong_functor_category_mor_diagram GG HH η' ->
  quantified_strong_functor_category_mor_diagram FF HH (nat_trans_comp _ _ _ η η').
Proof.
  intros ηisstrong η'isstrong.
  red. intros a v. red.
  rewrite <- (id_left (id v)).
  change (ζ FF (a, v) · (η (a ⊙ v) · η' (a ⊙ v)) = # odot' ((η a #, id v) · (η' a #, id v))  · ζ HH (a, v)).
  rewrite functor_comp.
  etrans.
  { rewrite assoc. apply cancel_postcomposition. apply ηisstrong. }
  do 2 rewrite <- assoc.
  apply maponpaths.
  apply η'isstrong.
Qed.

Section AsDisplayedCategory.

  Context (hsA': has_homsets A').

  Definition Strong_Functor_precategory_displayed : disp_cat (functor_category A (A',,hsA')).
  Proof.
    use disp_cat_from_SIP_data.
    - intro F.
      exact (actionbased_strength Mon_V actn actn' F).
    - intros F1 F2 FF1 FF2 η.
      exact (∏ a v, Strong_Functor_Category_mor_diagram (F1,,FF1) (F2,,FF2) η a v).
    - intros F1 F2 FF1 FF2 η.
      do 2 (apply impred; intro).
      apply hsA'.
    - intros F FF a v.
      apply Strong_Functor_Category_Mor_id_subproof.
    - intros F G H FF GG HH η η' ηmor η'mor a v. simpl in ηmor, η'mor.
      exact (Strong_Functor_Category_Mor_comp_subproof (F,,FF) (G,,GG) (H,,HH) η η' ηmor η'mor a v).
  Defined.

  Definition Strong_Functor_precategory : precategory := total_category Strong_Functor_precategory_displayed.

  Lemma Strong_Functor_precategory_ob_ok :
    ob Strong_Functor_precategory = actionbased_strong_functor Mon_V actn actn'.
  Proof.
    apply idpath.
  Qed.

  Definition Strong_Functor_Category_Mor :
    actionbased_strong_functor Mon_V actn actn' -> actionbased_strong_functor Mon_V actn actn' -> UU.
  Proof.
    exact (pr2 (precategory_ob_mor_from_precategory_data Strong_Functor_precategory)).
  Defined.

  Lemma Strong_Functor_Category_Mor_ok (FF GG: actionbased_strong_functor Mon_V actn actn') :
    Strong_Functor_Category_Mor FF GG = total2 (quantified_strong_functor_category_mor_diagram FF GG).
  Proof.
    apply idpath.
  Qed.

  Lemma Strong_Functor_Category_Mor_eq (FF GG : actionbased_strong_functor Mon_V actn actn')
        (sη sη' : Strong_Functor_Category_Mor FF GG) :
    pr1 sη = pr1 sη' -> sη = sη'.
  Proof.
    intros H.
    apply subtypePath; trivial.
    now intros α; repeat (apply impred; intro); apply hsA'.
  Qed.

  (* a "manual proof" - should this not follow later from the general method to obtain univalence? *)
  Lemma has_homsets_Strong_Functor_precategory: has_homsets Strong_Functor_precategory.
  Proof.
  intros FF GG.
  apply (isofhleveltotal2 2).
  * apply isaset_nat_trans, hsA'.
  * intros η.
    apply isasetaprop.
    apply impred; intros a; apply impred; intros v.
    apply hsA'.
  Qed.

  Definition Strong_Functor_category : category :=
  (Strong_Functor_precategory,, has_homsets_Strong_Functor_precategory).

  Definition Strong_FunctorForgetfulFunctor:
    functor Strong_Functor_precategory (functor_precategory A A' hsA').
  Proof.
    use tpair.
    - use tpair.
      + intros FF; apply FF.
      + intros FF GG η; apply η.
    - abstract (now split).
  Defined.

  Lemma Strong_FunctorForgetfulFunctorFaithful:
    faithful Strong_FunctorForgetfulFunctor.
  Proof.
    intros FF GG.
    apply isinclbetweensets.
    + apply has_homsets_Strong_Functor_precategory; try assumption.
    + apply functor_category_has_homsets.
    + apply Strong_Functor_Category_Mor_eq; try assumption.
  Qed.

(** towards univalence *)

  Lemma Strong_Functor_precategory_Pisset (F : [A, A',, hsA']) : isaset (actionbased_strength Mon_V actn actn' F).
  Proof.
    change isaset with (isofhlevel 2).
    apply isofhleveltotal2.
    apply (functor_category_has_homsets (A ⊠ Mon_V) _ hsA').
    intro ϛ.
    apply isasetaprop.
    apply isapropdirprod.
    + apply isaprop_actionbased_strength_triangle_eq, hsA'.
    + apply isaprop_actionbased_strength_pentagon_eq, hsA'.
  Qed.

  Lemma Strong_Functor_precategory_Hstandard (F : [A, A',, hsA']) (sη sη' : actionbased_strength Mon_V actn actn' F) :
    (∏ (a : A) (v : Mon_V), Strong_Functor_Category_mor_diagram (F,,sη) (F,,sη') (id F) a v)
  → (∏ (a : A) (v : Mon_V), Strong_Functor_Category_mor_diagram (F,,sη') (F,,sη) (id F) a v) → sη = sη'.
  Proof.
    intros leq geq.
    apply (actionbased_strength_eq _ _ _ hsA').
    apply (nat_trans_eq hsA').
    intro av.
    assert (leqinst := leq (pr1 av) (pr2 av)).
    (* assert (geqinst := geq (pr1 av) (pr2 av)). *)
    clear leq geq.
    etrans.
    { apply pathsinv0.
      apply id_right. }
    etrans.
    { exact leqinst. }
    clear leqinst.
    etrans.
    2: { apply id_left. }
    apply cancel_postcomposition.
    show_id_type.
    change (# odot' (id (pr1 F (pr1 av), pr2 av)) = id actionbased_strength_dom Mon_V actn' F av).
    rewrite functor_id.
    apply idpath.
  Qed.

  Definition is_univalent_Strong_Functor_precategory_displayed : is_univalent_disp Strong_Functor_precategory_displayed.
  Proof.
    use is_univalent_disp_from_SIP_data.
    - exact Strong_Functor_precategory_Pisset.
    - exact Strong_Functor_precategory_Hstandard.
  Defined.

End AsDisplayedCategory.

End Strong_Functor_Category.

Definition is_univalent_Strong_Functor_precategory (Mon_V : monoidal_precat) (A : precategory)
           (A' : univalent_category) (actn : action Mon_V A) (actn' : action Mon_V A') :
  is_univalent (Strong_Functor_precategory Mon_V actn actn' (homset_property A')).
Proof.
  apply SIP.
  - exact (is_univalent_functor_category A _ (pr2 A')).
  - apply Strong_Functor_precategory_Pisset.
  - apply Strong_Functor_precategory_Hstandard.
Defined.
