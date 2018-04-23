(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

(* =================================================================================== *)
(* Every (pre)bicategory of UniMath.CategoryTheory.bicat  is a                         *)
(* (pre)bicategory of UniMath.CategoryTheory.bicategories.                             *)
(* =================================================================================== *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.Bicategories.WkCatEnrichment.prebicategory.
Require Import UniMath.CategoryTheory.Bicategories.WkCatEnrichment.Notations.

Require Import UniMath.CategoryTheory.Bicategories.Bicat.

Open Scope cat.

Local Notation "C  'c×'  D" := (precategory_binproduct C D)
 (at level 75, right associativity).

Section Build_Bicategory.

Variable C : prebicat.

Definition bicate_ob_hom : prebicategory_ob_hom.
Proof.
  exists C. exact (λ a b : C, hom a b).
Defined.

Definition bicate_id_comp : prebicategory_id_comp.
Proof.
  exists bicate_ob_hom; unfold bicate_ob_hom; simpl; split.
  - exact identity.
  - unfold hom_data, hom_ob_mor. simpl. intros a b c.
    apply hcomp_functor.
Defined.

(* ----------------------------------------------------------------------------------- *)
(* Left associator. *)

Definition bicate_lassociator_fun {a b c d : bicate_id_comp}
           (x : C ⟦ a, b ⟧ × C ⟦ b, c ⟧ × C ⟦ c, d ⟧)
  : pr1 x · (pr12 x · pr22 x) ==> pr1 x · pr12 x · pr22 x
  := lassociator (pr1 x) (pr12 x) (pr22 x).

Lemma bicate_lassociator_fun_natural {a b c d : bicate_id_comp}
  : is_nat_trans
      (functor_composite
         (pair_functor (functor_identity (hom a b)) (compose_functor b c d))
         hcomp_functor)
      (functor_composite
         (precategory_binproduct_assoc (hom a b) (hom b c) (hom c d))
         (functor_composite
            (pair_functor (compose_functor a b c) (functor_identity (hom c d)))
            hcomp_functor)) bicate_lassociator_fun.
Proof.
  red; cbn. intros (f1, (f2, f3)) (g1, (g2, g3)).
  unfold precategory_binproduct_mor, hom_ob_mor. simpl.
  unfold precategory_binproduct_mor, hom_ob_mor. simpl.
  intros (x1, (x2, x3)). simpl.
  unfold bicate_lassociator_fun. simpl.
  apply hcomp_lassoc.
Defined.

Definition bicate_lassociator (a b c d : bicate_id_comp) : associator_trans_type a b c d.
Proof.
  exists bicate_lassociator_fun.
  exact bicate_lassociator_fun_natural.
Defined.

Lemma bicate_transfs :
  (∏ a b c d : bicate_id_comp, associator_trans_type a b c d) ×
  (∏ a b : bicate_id_comp, left_unitor_trans_type a b) ×
  (∏ a b : bicate_id_comp, right_unitor_trans_type a b).
Proof.
  repeat split.
  red. cbn.
  - exact lassociator_transf.
  - exact lunitor_transf.
  - exact runitor_transf.
Defined.

Definition bicate_data : prebicategory_data.
Proof.
  exists bicate_id_comp. exact bicate_transfs.
Defined.

Lemma prebicat_associator_and_unitors_are_iso
  : associator_and_unitors_are_iso bicate_data.
Proof.
  repeat split; cbn; intros.
  - apply lassociator_iso.
  - apply lunitor_iso.
  - apply runitor_iso.
Defined.

Lemma triangle_identity {a b c : C} (f : C ⟦ a, b ⟧) (g : C ⟦ b, c ⟧)
  : id2 f ⋆ lunitor g =
    lassociator f (identity b) g • (runitor f ⋆ id2 g).
Proof.
    unfold hcomp at 2.
    rewrite vassocr.
    rewrite runitor_rwhisker.
    rewrite hcomp_hcomp'.
    unfold hcomp'.
    apply maponpaths.
    rewrite lwhisker_id2.
    apply id2_rwhisker.
Defined.

Lemma pentagon_identity {a b c d e : C}
      (k : C ⟦ a, b ⟧)
      (h : C ⟦ b, c ⟧)
      (g : C ⟦ c, d ⟧)
      (f : C ⟦ d, e ⟧)
  : lassociator k h (g · f) • lassociator (k · h) g f =
    ((id2 k ⋆ lassociator h g f) • lassociator k (h · g) f) •
    (lassociator k h g ⋆ id2 f).
Proof.
  rewrite <- lassociator_lassociator.
  unfold hcomp at 2.
  rewrite lwhisker_id2. rewrite id2_right.
  apply maponpaths_2. apply maponpaths_2.
  unfold hcomp. rewrite id2_rwhisker.
  apply pathsinv0. apply id2_left.
Defined.

Lemma prebicat_prebicategory_coherence
  : prebicategory_coherence bicate_data.
Proof.
  split.
  - intros. apply pentagon_identity.
  - intros. apply triangle_identity.
Defined.

Lemma is_prebicategory_bicate : is_prebicategory bicate_data.
Proof.
  split; [ admit | split ].
  - exact prebicat_associator_and_unitors_are_iso.
  - exact prebicat_prebicategory_coherence.
Admitted.

Definition bicate : prebicategory.
Proof.
  exists bicate_data. exact is_prebicategory_bicate.
Defined.

End Build_Bicategory.
