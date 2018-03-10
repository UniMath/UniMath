(** * Actions

    Author: Langston Barrett (@siddharthist)
 *)

(** ** Contents
    - Strutures on morphisms
      - Endomorphisms and the endomorphism monoid
      - Automorphisms and the automorphism group
      - The endomorphism ring in an additive category
    - Algebraic structures as categories
      - Lemmas about categories with one object ([contr_cat])
      - Monoids as categories ([monoid_weq_contr_category])
      - Groups as groupoids
    - Actions
      - Monoid (group) actions
      - Ring actions
 *)

(** TODO:
 1. Rephrase definitions, prove equivalences with the originals:
   - Modules as abelian groups with a ring  action
   - Group actions (Ktheory/GroupAction) as sets with a group action
 2. Category of actions
 3. Actions as functors, equivariant maps as natural transformations,
    categories of actions as functor categories. Prerequisites:
   - Groups as single object categories
   - Rings as single object categories
 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.catiso.

(* For the endomorphism ring  *)
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.

(* For the symmetric group *)
Require Import UniMath.CategoryTheory.categories.category_hset.

Local Open Scope cat.

(** ** Structures on morphisms *)

(** *** Endomorphisms and the endomorphism monoid *)

(** Endomorphisms of X are arrows X --> X *)
Definition endomorphisms {C : precategory} (X : ob C) : UU := (X --> X).

(** When the hom-types of C are sets, we can form the endomorphism monoid *)
Definition endomorphism_monoid {C : category} (X : ob C) : monoid.
Proof.
  use monoidpair.
  - use setwithbinoppair.
    + use hSetpair.
      * exact (X --> X).
      * apply homset_property.
    + exact (@compose C X X X).
  - use dirprodpair.
    + exact (fun x x' x'' => !(@assoc C _ _ _ _ x x' x'')).
    + refine (identity X,, _).
      split.
      * exact (@id_left C X X).
      * exact (@id_right C X X).
Defined.

(** ** Algebraic structures as categories *)

(** *** Lemmas about categories with one object *)

Definition contr_cat : UU := ∑ C : category, iscontr (ob C).
Definition contr_cat_cat : contr_cat -> category := pr1.
Coercion contr_cat_cat : contr_cat >-> category.
Definition contr_cat_iscontr : ∏ C : contr_cat, iscontr (ob C) := pr2.
Definition contr_cat_center (C : contr_cat) : ob C :=
  iscontrpr1 (contr_cat_iscontr C).

Section ContrCatLemmas.

  Context {C D : contr_cat}.

  Lemma contr_cat_hom_weq :
    ∏ a b : ob C, (a --> b) ≃ (contr_cat_center C --> contr_cat_center C).
  Proof.
    intros a b.
    pose (aeqcenter := iscontr_uniqueness (contr_cat_iscontr C) a).
    pose (beqcenter := iscontr_uniqueness (contr_cat_iscontr C) b).
    use weq_iso.
    (** Construct the arrows using a double transport *)
    - intros cab.
      pose (tocenter := transportf (λ x, C ⟦ a, x ⟧) beqcenter cab).
      exact (transportf (λ x, C ⟦ x, contr_cat_center C ⟧) aeqcenter tocenter).
    - intros ccc.
      pose (froma := transportf (λ x, C ⟦ x, contr_cat_center C ⟧) (!aeqcenter) ccc).
      exact (transportf (λ x, C ⟦ a, x ⟧) (!beqcenter) froma).
    - intros x; cbn.
      (* We use abstract to make the rewrite-heavy proof opaque *)
      abstract (rewrite (transport_f_f _ (aeqcenter) (! aeqcenter));
                rewrite pathsinv0r; cbn; unfold idfun;
                rewrite (transport_f_f _ (beqcenter) (! beqcenter));
                rewrite pathsinv0r; cbn; unfold idfun;
                reflexivity).
    - intros x; cbn.
      abstract (rewrite (transport_f_f _ (! beqcenter) (beqcenter));
                rewrite pathsinv0l; cbn; unfold idfun;
                rewrite (transport_f_f _ (! aeqcenter) (aeqcenter));
                rewrite pathsinv0l; cbn; unfold idfun;
                reflexivity).
  Defined.

  Definition contr_cat_functor_data
             (f : C ⟦ contr_cat_center C, contr_cat_center C ⟧ ->
                  D ⟦ contr_cat_center D, contr_cat_center D ⟧) : functor_data C D.
  Proof.
    use mk_functor_data.
    - apply weqcontrcontr; apply contr_cat_iscontr.
    - intros a b g.
      apply f.
      apply (contr_cat_hom_weq a b); assumption.
  Defined.

  Lemma contr_cat_fully_faithful_to_isiso {F : functor C D} (ff : fully_faithful F) :
    is_catiso F.
  Proof.
    use dirprodpair; [assumption|].
    apply isweqcontrcontr; apply contr_cat_iscontr.
  Defined.

  Lemma contr_cat_eq {F : functor C D} (ff : fully_faithful F) : C = D.
  Proof.
    apply subtypeEquality'.
    - apply catiso_to_category_path.
      use tpair.
      + exact F.
      + apply contr_cat_fully_faithful_to_isiso; assumption.
    - apply isapropiscontr.
  Defined.

End ContrCatLemmas.

(** *** Monoids as categories*)

Local Open Scope multmonoid_scope.

Definition monoid_to_category (Mon : monoid) : contr_cat.
Proof.
  use tpair.
  - use makecategory.
    + exact unit.
    + intros; exact Mon.
    + intros; apply setproperty.
    + intros; exact (unel Mon).
    + intros; exact (f * g).
    + intros; apply lunax.
    + intros; apply runax.
    + intros; cbn; symmetry; apply assocax.
  - apply iscontrunit.
Defined.

Definition contr_category_to_monoid (C : category) (is : iscontr (ob C)) : monoid.
Proof.
  pose (center := iscontrpr1 is).
  use monoidpair.
  - use setwithbinoppair.
    + use hSetpair.
      * use (center --> center).
      * apply homset_property.
    + exact (@compose _ center center center).
  - use mk_ismonoidop.
    + unfold isassoc; symmetry; apply assoc.
    + use isunitalpair.
      * apply identity.
      * use isunitpair;
          [ unfold islunit; apply id_left | unfold isrunit; apply id_right ].
Defined.

(** The above functions constitute a weak equivalence. *)
Lemma monoid_weq_contr_category : monoid ≃ contr_cat.
Proof.
  use weq_iso.
  - exact monoid_to_category.
  - exact (uncurry contr_category_to_monoid).
  - (** By univalence for monoids, it suffices to show that they are isomorphic *)
    intros Mon; apply monoid_univalence.
    use tpair.
    + apply idweq.
    + use dirprodpair.
      * intros ? ?; apply idpath.
      * apply idpath.
  - intros contrcat.
    use contr_cat_eq.
    + use mk_functor.
      * apply contr_cat_functor_data.
        apply idfun.
      * use dirprodpair; cbn.
        { unfold functor_idax.
          intros a; cbn in *.
          abstract (induction a; reflexivity).
        }
        {
          unfold functor_compax.
          intros a b c.
          abstract (induction a, b, c; reflexivity).
        }
   + unfold fully_faithful.
     intros a b.
     abstract (induction a, b; exact (idisweq _)).
Defined.

(** *** Groups as categories*)

(** The automorphism group is a submonoid of the endomorphism monoid *)

(** When the hom-types of C are sets, we can form the automorphism grp *)
Definition automorphism_grp {C : category} (X : ob C) : gr :=
  gr_invertible_elements (endomorphism_monoid X).

Example symmetric_grp (X : hSet) := @automorphism_grp hset_category X.

(** *** The endomorphism ring in an additive category *)

Definition endomorphism_rng {C : Additive}
           (_ : ob (categoryWithAbgrops_category C)) : rng.
Proof.
  (** The multiplication operation is composition, we reuse the proof
      from the endomorphism monoid. The addition operation is the addition
      on homsets, we extract this with to_binop *)
  pose (end_monoid := @endomorphism_monoid (categoryWithAbgrops_category C) X).
  refine ((pr1 (pr1 end_monoid),,
          dirprodpair (to_binop X X) (pr2 (pr1 end_monoid))),, _).

  split; split.
  (** We know by assumption on C that + is an abgrop.*)
  - exact (to_isabgrop _ _).
  (** We already proved this *)
  - exact (pr2 end_monoid).
  (** By assumption on C *)
  - intros f g h; apply (to_premor_monoid C _ _ _ h).
  - intros f g h; apply (to_postmor_monoid C _ _ _ h).
Defined.

(** ** Actions *)

Section Actions.
  (** Fix a category to act on *)
  Context {C : category}.

  Definition contr_cat_action (CC : contr_cat) (X : ob C) :=
    functor CC (monoid_weq_contr_category (endomorphism_monoid X)).

  (** An equivariant map, or intertwiner, is simply a natural transformation *)
  Definition equivariant_map {CC : contr_cat} {X : ob C}
                             (actA : contr_cat_action CC X)
                             (actB : contr_cat_action CC X) : UU :=
    nat_trans (functor_data_from_functor _ _ actA)
              (functor_data_from_functor _ _ actB).
End Actions.

(** *** Monoid (group) actions *)

(** A monoid action is a functor from the monoid (viewed as a category)
 *)
Definition monaction {C : category} (Mon : monoid) (X : ob C) :=
  contr_cat_action (monoid_weq_contr_category Mon) X.

(** *** Ring actions *)
