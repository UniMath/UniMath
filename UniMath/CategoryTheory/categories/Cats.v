(** * The (pre)category of (pre)categories

This file defines the (pre)category of 𝒰-small (pre)categories, i.e.
(pre)categories that fit within some fixed universe.

Author: Langston Barrett (@siddharthist), Feb 2018
*)

(** ** Contents:

- Definitions
  - The precategory of 𝒰-small precategories (for fixed U) ([precat_precat])
  - The precategory of 𝒰-small categories ([cat_precat])
  - The precategory of 𝒰-small univalent categories ([univalent_cat_precat])
  - The category of 𝒰-small set categories ([setcat_cat])
- Colimits
  - Initial objects
    - Initial precategory ([InitialPrecat])
    - Initial category ([InitialCat])
    - Initial univalent category ([InitialUniCat])
- Limits
  - Terminal objects
    - Terminal precategory ([TerminalPrecat])
    - Terminal category ([TerminalCat])
    - Terminal univalent category ([TerminalUniCat])
    - Terminal setcategory ([TerminalSetCat])
  - Products
    - Product category ([ProductsCat])
  - Notes on equalizers
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.

(* Basic category theory *)
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.catiso.

(* Subcategories *)
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Subcategory.Limits.

(* (Co)limits *)
Require Import UniMath.CategoryTheory.categories.StandardCategories. (* unit *)
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.ProductCategory.

Local Open Scope cat.
Local Open Scope functions.

(** ** Definitions *)

(** *** The precategory of 𝒰-small precategories (for fixed 𝒰) ([precat_precat]) *)

Definition precat_precat : precategory.
Proof.
  use make_precategory_one_assoc.
  - use tpair; use tpair; cbn.
    + exact precategory.
    + exact functor.
    + exact functor_identity.
    + exact @functor_composite.
  - repeat split; intros.
    + apply functor_identity_right.
    + apply pathsinv0, functor_assoc.
Defined.

(** *** The precategory of 𝒰-small categories ([cat_precat]) *)

Definition cat_precat_subtype : hsubtype precat_precat :=
  λ C : precategory, make_hProp _ (isaprop_has_homsets C).

(*
(** A subcategory can be coerced to a precategory, see [carrier_of_sub_precategory]. *)
Definition cat_precat : sub_precategories precat_precat :=
  full_sub_precategory cat_precat_subtype.
*)
(** It's not the case that [cat_precat] has homsets. *)

(** *** The precategory of 𝒰-small univalent categories ([univalent_cat_precat]) *)

(*
Definition univalent_cat_precat_subtype : hsubtype precat_precat :=
  λ C : precategory, make_hProp _ (isaprop_is_univalent C).
*)
(*
Definition univalent_cat_precat : sub_precategories precat_precat :=
  full_sub_precategory univalent_cat_precat_subtype.
*)
(** This can also be seen as a subcategory of [cat_precat].
    An isommorphism between them would be useful because it is easier to prove
    e.g. that [cat_precat] has products, and then inherit them in
    [univalent_cat_precat]. *)
(*
Definition univalent_cat_precat_subtype' : hsubtype cat_precat :=
  λ C : category, make_hProp _ (isaprop_is_univalent C).
 *)
(*
Definition univalent_cat_precat' : sub_precategories cat_precat :=
  full_sub_precategory univalent_cat_precat_subtype'.
*)
(** Two copies of a proposition are as good as one.
    This is like the structural rule of contraction. *)
Local Lemma dirprod_with_prop (A : UU) (isa : isaprop A) : A × A ≃ A.
Proof.
  apply weqpr1, iscontraprop1; assumption.
Defined.

(** A variation on the above theme *)
Local Lemma dirprod_with_prop' (A B : UU) (isa : isaprop A) : A × B × A ≃ B × A.
Proof.
  intermediate_weq ((A × B) × A).
  apply invweq, weqtotal2asstor.
  intermediate_weq (A × (A × B)).
  apply weqdirprodcomm.
  intermediate_weq ((A × A) × B).
  apply invweq, weqtotal2asstor.
  intermediate_weq (A × B).
  apply weqdirprodf.
  - apply dirprod_with_prop; assumption.
  - apply idweq.
  - apply weqdirprodcomm.
Defined.

(*
Lemma univalent_cat_precat_subcat_weq :
  univalent_cat_precat ≃ univalent_cat_precat'.
Proof.
  (** To get to the actual issue, it helps to do a lot of unfolding. *)
  cbn; unfold sub_ob; cbn.
  unfold univalent_cat_precat_subtype, univalent_cat_precat_subtype', carrier; cbn.
  unfold sub_ob, cat_precat_subtype.
  unfold sub_precategory_predicate_objects; cbn.
  unfold cat_precat_subtype, carrier; cbn.
  apply invweq.
  intermediate_weq (∑ x : precategory, has_homsets x × is_univalent x).
  - apply weqtotal2asstor.
  - unfold is_univalent.
    apply weqfibtototal; intro.
    apply dirprod_with_prop'.
    apply isaprop_has_homsets.
Defined.
 *)

(** *** The category of 𝒰-small set categories ([setcat_cat]) *)

(** **** The precategory of 𝒰-small categories with objects of hlevel n and homtypes
         of hlevel m. *)

Definition hlevel_precat_subtype : nat → nat → hsubtype precat_precat :=
  object_homtype_hlevel.

(*
Definition hlevel_precat (n m : nat) : sub_precategories precat_precat :=
  full_sub_precategory (hlevel_precat_subtype n m).
*)
(** **** Setcategories, the case where n = m = 2. *)

(*
Definition setcat_precat : sub_precategories precat_precat := hlevel_precat 2 2.
 *)

(*
Lemma has_homsets_setcat_precat : has_homsets setcat_precat.
Proof.
  intros X Y; apply isaset_total2.
  - apply functor_isaset.
    + apply isaset_mor.
    + apply isaset_ob.
  - intro.
    change isaset with (isofhlevel 2).
    apply isofhlevelcontr, iscontrunit.
Defined.
 *)
(*
Definition setcat_cat : category := make_category _ has_homsets_setcat_precat.
 *)


(*
(** ** Colimits *)

(** *** Initial objects *)

(** **** Initial precategory ([InitialPrecat]) *)

Definition InitialPrecat : Initial precat_precat.
Proof.
  use make_Initial.
  - cbn; exact empty_category.
  - intros ?; apply iscontr_functor_from_empty.
Defined.

(** **** Initial category ([InitialCat]) *)

Definition InitialCat : Initial cat_precat.
Proof.
  use (initial_in_full_subcategory _ InitialPrecat).
  apply homset_property.
Defined.

(** **** Initial univalent category ([InitialUniCat]) *)

Definition InitialUniCat : Initial univalent_cat_precat.
Proof.
  use (initial_in_full_subcategory _ InitialPrecat).
  apply univalent_category_is_univalent.
Defined.

(** **** Initial set category ([InitialSetCat]) *)

Definition InitialSetCat : Initial setcat_cat.
Proof.
  use (initial_in_full_subcategory _ InitialPrecat).
  split.
  - apply hlevelntosn, isapropempty.
  - intros a; induction a.
Defined.

(** ** Limits *)

(** *** Terminal objects *)

(** **** Terminal (pre)category ([TerminalPrecat]) *)

Definition TerminalPrecat : Terminal precat_precat.
Proof.
  use make_Terminal.
  - cbn; exact unit_category.
  - intros ?; apply iscontr_functor_to_unit.
Defined.

(** **** Terminal category ([TerminalCat]) *)

Definition TerminalCat : Terminal cat_precat.
Proof.
  use (terminal_in_full_subcategory _ TerminalPrecat).
  apply homset_property.
Defined.

(** **** Terminal univalent category ([TerminalUniCat]) *)

Definition TerminalUniCat : Terminal univalent_cat_precat.
Proof.
  use (terminal_in_full_subcategory _ TerminalPrecat).
  apply univalent_category_is_univalent.
Defined.

(** **** Terminal setcategory ([TerminalSetCat]) *)

Definition TerminalSetCat : Terminal setcat_cat.
Proof.
  use (terminal_in_full_subcategory _ TerminalPrecat).
  split.
  - apply isofhlevelcontr, iscontrunit.
  - intros a b.
    apply isofhlevelcontr; cbn.
    apply isapropunit.
Defined.

(** *** Products *)

(** **** Product category ([ProductsCat]) *)

(** We essentially proved the universal property in [functor_into_product_weq],
    an equivalence between A → (product_category B) and (∏ i : I, A → (B i)).
  *)
Definition ProductsCat {I : UU} : Products I cat_precat.
Proof.
  intros f; cbn in *.
  use make_Product.
  - exact (product_category f).
  - intro i.
    use morphism_in_full_subcat.
    exact (pr_functor I (pr1 ∘ f) i).
  - unfold funcomp; cbn.
    intros other_prod other_proj.
    apply (@iscontrweqf (hfiber functor_into_product_weq (λ i, pr1 (other_proj i)))).
    + unfold hfiber.
      unfold sub_precategory_morphisms, sub_precategory_predicate_morphisms; cbn.
      (* Use `Set Printing Coercions.` to understand the types here. *)
      unfold carrier, hProptoType; cbn.
      intermediate_weq
        (∑ x : (pr1 (pr1 other_prod)) ⟶ product_precategory_data (λ x : I, pr1 (f x)),
          ∏ i, x ∙ pr_functor I (λ x0 : I, pr1 (f x0)) i = pr1 (other_proj i)).
      * use weqfibtototal; intro; cbn.
        apply weqtoforallpaths.
      * apply invweq.
        intermediate_weq
          (∑ ff : pr1 (pr1 other_prod) ⟶ product_precategory_data (λ x : I, pr1 (f x)),
            ∏ i : I, ff ∙ pr_functor I (λ x : I, pr1 (f x)) i,, tt = other_proj i).
        {
          refine (weqfp (make_weq pr1 _) _).
          apply isweqpr1.
          intros ?.
          apply iscontrunit.
        }
        {
          apply weqfibtototal; intro.
          apply weqonsecfibers; intro.
          use make_weq.
          * intros eq; exact (maponpaths pr1 eq).
          * refine (isweqmaponpaths (make_weq pr1 _) _ _).
            apply isweqpr1.
            intros.
            apply iscontrunit.
        }
  + apply weqproperty.
Defined.
*)
(** *)
