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
  - Discrete categories

 *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

(** ** Definitions *)

(** A precategory is a pregroupoid when all of its arrows are [iso]s. *)
Definition is_pregroupoid (C : precategory) :=
  ∏ (x y : C) (f : x --> y), is_iso f.

Lemma isaprop_is_pregroupoid (C : precategory) : isaprop (is_pregroupoid C).
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
Definition groupoid_to_pregroupoid :
  groupoid → pregroupoid := λ gpd, mk_pregroupoid gpd (groupoid_is_pregroupoid gpd).
Coercion groupoid_to_pregroupoid : groupoid >-> pregroupoid.

Definition univalent_groupoid : UU := ∑ C : univalent_category, is_pregroupoid C.

(** Constructors, accessors, and coersions *)
Definition mk_univalent_groupoid (C : univalent_category) (is : is_pregroupoid C) :
  univalent_groupoid := (C,, is).
Definition univalent_groupoid_to_univalent_category :
  univalent_groupoid -> univalent_category := pr1.
Coercion univalent_groupoid_to_univalent_category :
  univalent_groupoid >-> univalent_category.
Definition univalent_groupoid_is_pregroupoid :
  ∏ ugpd : univalent_groupoid, is_pregroupoid (pr1 ugpd) := pr2.
Definition univalent_groupoid_to_groupoid :
  univalent_groupoid -> groupoid :=
  λ ugpd, mk_groupoid ugpd (univalent_groupoid_is_pregroupoid ugpd).
Coercion univalent_groupoid_to_groupoid :
  univalent_groupoid >-> groupoid.

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
Lemma pregroupoid_hom_weq_iso {pgpd : pregroupoid} (a b : pgpd) : (a --> b) ≃ iso a b.
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

Lemma pregroupoid_hom_weq_iso_idtoiso {pgpd : pregroupoid} (a : pgpd) :
  pregroupoid_hom_weq_iso a a (identity a) = idtoiso (idpath a).
Proof.
  apply subtypeEquality'.
  - reflexivity.
  - apply isaprop_is_iso.
Defined.

Lemma pregroupoid_hom_weq_iso_comp {pgpd : pregroupoid} {a b c : ob pgpd}
      (f : a --> b) (g : b --> c) :
  iso_comp (pregroupoid_hom_weq_iso _ _ f) (pregroupoid_hom_weq_iso _ _ g) =
  (pregroupoid_hom_weq_iso _ _ (f · g)).
Proof.
  apply subtypeEquality'.
  - reflexivity.
  - apply isaprop_is_iso.
Defined.

(** If D is a groupoid, then a functor category into it is as well. *)
Lemma is_pregroupoid_functor_cat {C : precategory} {D : category}
  (gr_D : is_pregroupoid D)
  : is_pregroupoid (functor_category C D).
Proof.
  intros F G α; apply functor_iso_if_pointwise_iso.
  intros c; apply gr_D.
Defined.

(** In a univalent groupoid, arrows are equivalent to paths *)
Lemma univalent_groupoid_arrow_weq_path {ugpd : univalent_groupoid} {a b : ob ugpd} :
  (a --> b) ≃ a = b.
Proof.
  intermediate_weq (iso a b).
  - apply (@pregroupoid_hom_weq_iso ugpd).
  - apply invweq; use weqpair.
    + exact idtoiso.
    + apply univalent_category_is_univalent.
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

(** ** Discrete categories *)

(** See [Categories.categories.StandardCategories] for a proof that any discrete
    category is equivalent to the path groupoid of its objects. *)

(** A discrete category is a univalent [pregroupoid] with an underlying [setcategory].
    Why? In this case, all arrows must be identities: every arrow has an inverse,
    and isos induce equality (by univalence).
 *)
Definition is_discrete (C : precategory) :=
  (is_setcategory C × is_pregroupoid C × is_univalent C).

Definition discrete_category : UU := ∑ C : precategory, is_discrete C.
Definition mk_discrete_category :
  ∏ C : precategory, is_discrete C → discrete_category := tpair is_discrete.
Definition discrete_category_to_univalent_groupoid :
  discrete_category -> univalent_groupoid :=
  λ disc, mk_univalent_groupoid
            (mk_category (pr1 disc) (dirprod_pr2 (dirprod_pr2 (pr2 disc))))
            (dirprod_pr1 (dirprod_pr2 (pr2 disc))).
Coercion discrete_category_to_univalent_groupoid :
  discrete_category >-> univalent_groupoid.
Definition discrete_category_is_discrete :
  ∏ C : discrete_category, is_discrete C := pr2.
Definition discrete_category_is_setcategory :
  ∏ C : discrete_category, is_setcategory C := λ C, dirprod_pr1 (pr2 C).

Lemma isaprop_is_discrete (C : precategory) : isaprop (is_discrete C).
Proof.
  apply isapropdirprod; [|apply isapropdirprod].
  - apply isaprop_is_setcategory.
  - apply isaprop_is_pregroupoid.
  - apply isaprop_is_univalent.
Defined.

(** In a discrete category, hom-types are propositions. *)
Lemma discrete_category_hom_prop {disc : discrete_category} {a b : ob disc} :
  isaprop (a --> b).
Proof.
  apply (@isofhlevelweqf _ (a = b)).
  - apply invweq, (@univalent_groupoid_arrow_weq_path disc).
  - apply (isaset_ob (_ ,, discrete_category_is_setcategory _)).
Defined.

(** A functor between discrete categories is given by a function
    on their objects. *)
Lemma discrete_functor {C D : discrete_category} (f : ob C → ob D) :
  functor C D.
Proof.
  use mk_functor.
  - use mk_functor_data.
    + apply f.
    + intros a b atob.
      pose (aeqb := @univalent_groupoid_arrow_weq_path C _ _ atob).
      exact (transportf (λ z, _ ⟦ f a, z ⟧) (maponpaths f aeqb) (identity _)).
  - split.
    + intro; apply discrete_category_hom_prop.
    + intros ? ? ? ? ?; apply discrete_category_hom_prop.
Defined.

Definition discrete_cat_nat_trans {C : precategory} {D : discrete_category}
  {F G : functor C D} (t : ∏ x : ob C, F x --> G x) : is_nat_trans F G t.
Proof.
  intros ? ? ?; apply discrete_category_hom_prop.
Defined.
