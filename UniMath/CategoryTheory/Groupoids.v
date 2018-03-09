(** * Groupoids

  Author: Langston Barrett (@siddharthist), March 2018 *)

(** ** Contents

  - Definitions
    - Pregroupoid
    - Groupoid
    - Univalent groupoid
  - An alternative characterization of univalence for groupouds
  - Lemmas
  - Subgroupoids

 *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.LogicalEquivalence.Types.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

(** ** Definitions *)

(** A precategory is a pregroupoid when all of its arrows are [iso]s. *)
Definition is_pregroupoid (C : precategory) :=
  ∏ (x y : C) (f : x --> y), is_iso f.

Lemma isaprop_is_pregroupoid (C : category) : isaprop (is_pregroupoid C).
Proof.
  do 3 (apply impred; intro).
  apply isaprop_is_iso.
Defined.

Definition pregroupoid : UU := ∑ C : precategory, is_pregroupoid C.

(** Constructors, accessors, and coersions *)
Definition mk_pregroupoid (C : precategory) (is : is_pregroupoid C) : pregroupoid :=
  (C,, is).
Definition pregroupoid_to_precategory : pregroupoid -> precategory := pr1.
Definition pregroupoid_is_pregroupoid :
  ∏ gpd : pregroupoid, is_pregroupoid (pr1 gpd) := pr2.
Coercion pregroupoid_to_precategory : pregroupoid >-> precategory.

(** A category is a groupoid when all of its arrows are [iso]s. *)
Definition groupoid : UU := ∑ C : category, is_pregroupoid C.

(** Constructors, accessors, and coersions *)
Definition mk_groupoid (C : category) (is : is_pregroupoid C) : groupoid := (C,, is).
Definition groupoid_to_category : groupoid -> category := pr1.
Definition groupoid_is_pregroupoid :
  ∏ gpd : groupoid, is_pregroupoid (pr1 gpd) := pr2.
Coercion groupoid_to_category : groupoid >-> category.

Definition univalent_groupoid : UU := ∑ C : univalent_category, is_pregroupoid C.

(** Constructors, accessors, and coersions *)
Definition mk_univalent_groupoid (C : univalent_category) (is : is_pregroupoid C) :
  univalent_groupoid := (C,, is).
Definition univalent_groupoid_to_univalent_category :
  univalent_groupoid -> univalent_category := pr1.
Definition univalent_groupoid_is_pregroupoid :
  ∏ gpd : univalent_groupoid, is_pregroupoid (pr1 gpd) := pr2.
Coercion univalent_groupoid_to_univalent_category :
  univalent_groupoid >-> univalent_category.

(** An alternative characterization of univalence for groupoids *)
Definition is_univalent_pregroupoid (pgpd : pregroupoid) :=
  (∏ a b : ob pgpd, isweq (fun path : a = b => idtomor a b path)) ×
  has_homsets pgpd.

(** The morphism part of an isomorphism is an inclusion. *)
Lemma morphism_from_iso_is_incl (C : category) (a b : ob C) :
  isincl (morphism_from_iso C a b).
Proof.
  intro g.
  apply (isofhlevelweqf _ (ezweqpr1 _ _)).
  apply isaprop_is_iso.
Qed.

(** The alternative characterization implies the normal one. *)
Lemma is_univalent_pregroupoid_is_univalent {pgpd : pregroupoid} :
  is_univalent_pregroupoid pgpd -> is_univalent pgpd.
Proof.
  intros ig.
  split.
  - intros a b.
    use (isofhlevelff 0 idtoiso (morphism_from_iso _ _ _)).
    + use (isweqhomot (idtomor _ _)).
      * intro p; destruct p; reflexivity.
      * apply ig.
    + apply (morphism_from_iso_is_incl (pr1 pgpd,, pr2 ig)).
  - exact (pr2 ig).
Qed.

(** ** Lemmas *)

(** In a pregroupoid, the hom-types are equivalent to the type of isomorphisms. *)
Lemma pregroupoid_hom_weq_iso {pgpd : pregroupoid} (a b : pgpd) : a --> b ≃ iso a b.
Proof.
  use weq_iso.
  - intros f; refine (f,, _); apply pregroupoid_is_pregroupoid.
  - apply pr1.
  - reflexivity.
  - intros f.
    apply subtypeEquality'.
    * reflexivity.
    * apply isaprop_is_iso.
Defined.

(** If D is a groupoid, then a functor category into it is as well. *)
Lemma is_pregroupoid_functor_cat {C : precategory} {D : category}
  (gr_D : is_pregroupoid D)
  : is_pregroupoid (functor_category C D).
Proof.
  intros F G α; apply functor_iso_if_pointwise_iso.
  intros c; apply gr_D.
Defined.

(** ** Subgroupoids *)

(** Every category has a subgroupoid of all the objects and only the [iso]s. *)
Definition maximal_subgroupoid {C : precategory} : pregroupoid.
Proof.
  use mk_pregroupoid.
  - use mk_precategory; use tpair.
    + use tpair.
      * exact (ob C).
      * exact (λ a b, ∑ f : a --> b, is_iso f).
    + unfold precategory_id_comp; cbn.
      use dirprodpair.
      * exact (λ a, identity a,, identity_is_iso _ _).
      * intros ? ? ? f g; exact (pr1 g ∘ pr1 f,, is_iso_comp_of_isos f g).
    + use dirprodpair;
        intros;
        apply subtypeEquality'.
      * apply id_left.
      * apply isaprop_is_iso.
      * apply id_right.
      * apply isaprop_is_iso.
    + intros ? ? ? ? ? ? ?; cbn in *; apply subtypeEquality'.
      * apply assoc.
      * apply isaprop_is_iso.
  - intros ? ? f; use (is_iso_qinv f).
    + exact (iso_inv_from_iso f).
    + use dirprodpair; apply subtypeEquality'.
      * apply iso_inv_after_iso.
      * apply isaprop_is_iso.
      * apply iso_after_iso_inv.
      * apply isaprop_is_iso.
Defined.
