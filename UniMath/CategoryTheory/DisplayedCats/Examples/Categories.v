(** * The category of categories, displayed over types *)

(** ** Contents

  - Definitions
    - [disp_categories]: The displayed precategory of categories
    - [disp_univalent_categories]: The displayed category of univalent categories
    - [disp_thin_categories]: The displayed category of thin categories (preorders)
 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Setcategories.

Require Import UniMath.CategoryTheory.categories.Type.Core.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Local Open Scope cat.

(** ** Definitions *)

(** Note that we can't display the precategory of precategories over the
    precategory of types: the axioms for a displayed category include some
    conditions on paths that aren't necessarily satisfied. *)

(** *** [disp_categories]: The displayed precategory of categories *)

Local Definition category_structure (ob : UU) : UU :=
  ∑ (hom : ob → ob → UU) (ids : ∏ c : ob, hom c c)
    (comp : ∏ a b c : ob, hom a b → hom b c → hom a c)
    (isp : is_precategory (make_precategory_data (make_precategory_ob_mor ob hom) ids comp)),
    has_homsets (make_precategory (make_precategory_data (make_precategory_ob_mor ob hom) ids comp) isp).

Local Definition mk_cat {ob : UU} (struct : category_structure ob) : category.
Proof.
  pose (ob_mor := make_precategory_ob_mor _ (pr1 struct)).
  pose (id := pr1 (pr2 struct)).
  pose (comp := pr1 (pr2 (pr2 struct))).
  pose (precat_data := make_precategory_data ob_mor id comp).
  use make_category.
  - apply (make_precategory precat_data).
    exact (pr1 (pr2 (pr2 (pr2 struct)))).
  - exact (pr2 (pr2 (pr2 (pr2 struct)))).
Defined.

Definition disp_categories : disp_precat type_precat.
  use tpair. (** TODO: constructor *)
  - use tpair. (** TODO: constructor *)
    + use make_disp_precat_ob_mor.
      * intros ob.
        refine (∑ hom : ob -> ob -> UU, _).
        pose (ob_mor := make_precategory_ob_mor ob hom).
        refine (∑ ids : (∏ c : ob_mor, c --> c), _).
        refine (∑ comp : (∏ a b c : ob_mor, a --> b -> b --> c -> a --> c), _).
        refine (∑ isp : is_precategory (make_precategory_data ob_mor ids comp), _).
        exact (has_homsets (make_precategory _ isp)).
      * intros ? ? structX structY f; cbn in *.
        pose (precatX := mk_cat structX).
        pose (precatY := mk_cat structY).
        pose (F := f : ob precatX -> ob precatY).
        refine (∑ data : (∏ a b : ob precatX, a --> b -> F a --> F b), _).
        pose (funct_data := make_functor_data F data).
        exact (is_functor funct_data).
    + use make_dirprod; cbn.
      * intros obX structX.
        pose (precatX := mk_cat structX).
        unfold idfun.
        use tpair.
        -- intros ? ?; exact (# (functor_identity precatX)).
        -- apply is_functor_identity.
      * intros ? ? ? ? ? ? ? ? data1 data2.
        pose (funct1 := make_functor _ (pr2 data1)).
        pose (funct2 := make_functor _ (pr2 data2)).
        use tpair.
        -- intros ? ?; exact (# (functor_composite funct1 funct2)).
        -- apply (is_functor_composite funct1 funct2).
  - use make_dirprod; [|use make_dirprod]. (** TODO: constructor *)
    + reflexivity.
    + intros ? obY ? ? structY ?.
      use total2_paths_f.
      * reflexivity.
      * apply isaprop_is_functor.
        exact (homset_property (mk_cat structY)).
    + cbn.
      intros ? ? ? ? ? ? ? ? ? ? structW ? ? ?.
      use total2_paths_f.
      * reflexivity.
      * apply isaprop_is_functor.
        exact (homset_property (mk_cat structW)).
Defined.

Definition ob_disp_categories_to_category
           (C : ob (total_precategory disp_categories)) : category :=
  mk_cat (pr2 C).

Coercion ob_disp_categories_to_category : ob >-> category.

Lemma ob_disp_categories_weq_category :
  weq (ob (total_precategory disp_categories)) category.
Proof.
  unfold category.
  apply invweq.
  do 3 (eapply weqcomp; [apply weqtotal2asstor|]).
  do 2 (apply weqfibtototal; intro).
  eapply weqcomp; [apply weqtotal2asstor|].
  do 3 (apply weqfibtototal; intro).
  apply idweq.
Defined.

(** The function we calculate in the above proof is exactly
    [ob_disp_categories_to_category]. *)
Lemma ob_disp_categories_to_category_is_weq : isweq ob_disp_categories_to_category.
Proof.
  exact (pr2 ob_disp_categories_weq_category).
Defined.

(** *** [disp_univalent_categories]: The displayed category of univalent categories *)

Definition disp_univalent_categories : disp_precat (total_precategory disp_categories).
Proof.
  use disp_full_sub.
  intros C.
  exact (make_hProp _ (isaprop_is_univalent (ob_disp_categories_to_category C))).
Defined.

Definition ob_disp_univalent_categories_weq_univalent_category :
  weq (ob (total_precategory disp_univalent_categories)) univalent_category.
Proof.
  apply invweq; unfold univalent_category, is_univalent.
  intermediate_weq (∑ C : category, (∏ a b : C, isweq (λ p : a = b, idtoiso p))).
  - apply invweq; eapply weqcomp; [apply weqtotal2asstor|].
    apply weqfibtototal; intro.
    apply invweq; apply weqdirprodcomm.
  - apply invweq.
    use weqbandf.
    + use tpair.
      * apply ob_disp_categories_to_category.
      * (* The [abstract] is for performance reasons, i.e. the [cbn] below *)
        abstract (apply ob_disp_categories_to_category_is_weq).
    + intro C; cbn.
      apply invweq.
      unfold is_univalent; cbn.
      apply WeakEquivalences.dirprod_with_contr_r.
      apply iscontraprop1.
      * apply isaprop_has_homsets.
      * apply (homset_property (ob_disp_categories_to_category C)).
Defined.

(** *** [disp_thin_categories]: The displayed category of thin categories (posets) *)

Definition is_thin (C : precategory) : hProp := homtype_hlevel 1 C.

Definition disp_thin_categories : disp_precat (total_precategory disp_categories).
Proof.
  use disp_full_sub.
  (** TODO: why isn't this coercion firing? *)
  intros C; exact (is_thin (ob_disp_categories_to_category C)).
Defined.