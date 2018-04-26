(** * Actions

    Author: Langston Barrett (@siddharthist)
 *)

(** ** Contents
    - Strutures on morphisms
      - Endomorphisms and the endomorphism monoid ([endomorphism_monoid])
      - Automorphisms and the automorphism group ([automorphism_grp])
      - The endomorphism ring in an additive category ([endomorphism_ring])
    - Algebraic structures as categories
      - Lemmas about categories with one object ([contr_cat])
      - Monoids
        - Monoids as categories ([monoid_weq_contr_category])
        - Monoid morphisms as functors ([monoid_fun_weq_functor])
      - Groups
        - Groups as groupoids
        - Group morphisms as functors
      - Rings
    - Actions
      - As homomorphisms
        - Monoid (group) actions ([monaction_as_morphism])
        - Ring actions ([ringaction_as_morphism])
      - As functors
        - Equivariant maps
        - Monoid (group) actions ([monaction])
        - Ring actions
    - Theory
        - Translation groupoid ([translation_groupoid])
 *)

(** TODO:
 1. Rephrase definitions, prove equivalences with the originals:
   - Modules as abelian groups with a ring  action
   - Group actions (Ktheory/GroupAction) as sets with a group action
 2. Prove equivalence of rings as one-object categories
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

(** The automorphism group is a submonoid of the endomorphism monoid *)

(** When the hom-types of C are sets, we can form the automorphism grp *)
Definition automorphism_grp {C : category} (X : ob C) : gr :=
  gr_merely_invertible_elements (endomorphism_monoid X).

Example symmetric_grp (X : hSet) := @automorphism_grp hset_category X.

(** *** The endomorphism ring in an additive category *)

Definition endomorphism_ring {C : Additive}
           (_ : ob (categoryWithAbgrops_category C)) : ring.
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

(** ** Algebraic structures as categories *)

(** *** Lemmas about categories with one object *)

Definition contr_cat : UU := ∑ C : category, iscontr (ob C).
Definition contr_cat_cat : contr_cat -> category := pr1.
Coercion contr_cat_cat : contr_cat >-> category.
Definition contr_cat_iscontr : ∏ C : contr_cat, iscontr (ob C) := pr2.
Definition contr_cat_center (C : contr_cat) : ob C :=
  iscontrpr1 (contr_cat_iscontr C).

Section ContrCatLemmas.

  Context {C : contr_cat}.

  (** The hom-set between any two objects in a contractible category is
      equivalent to the hom-set of endomorphisms of the center (b/c both objects
      are, in fact, equal to the center). *)
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

  Context {D : contr_cat}.

  (** A functor between contractible categories is fully specified by its mapping
      of the endomorphisms of the center. *)
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

  (** Any fully faithful functor between contractible categories is an isomorphism. *)
  Lemma contr_cat_fully_faithful_to_isiso {F : functor C D} (ff : fully_faithful F) :
    is_catiso F.
  Proof.
    use dirprodpair; [assumption|].
    apply isweqcontrcontr; apply contr_cat_iscontr.
  Defined.

  (** Two contractible categories are equal if there is a fully faithful
      functor between them. *)
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

(** *** Monoids *)

Local Open Scope multmonoid_scope.

(** **** Monoids as categories ([monoid_weq_contr_category]) *)

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
        { unfold functor_compax.
          intros a b c.
          abstract (induction a, b, c; reflexivity).
        }
   + unfold fully_faithful.
     intros a b.
     abstract (induction a, b; exact (idisweq _)).
Defined.

(** **** Monoid morphisms as functors ([monoid_fun_weq_functor]) *)

(** Monoid morphism --> functor *)
Definition monoidfun_to_functor {Mon1 Mon2 : monoid} (monfun : monoidfun Mon1 Mon2) :
  functor (monoid_weq_contr_category Mon1) (monoid_weq_contr_category Mon2).
Proof.
  use mk_functor.
  - apply contr_cat_functor_data.
    exact monfun.
  - use dirprodpair.
    + intros a.
      abstract (induction a;
                apply monoidfununel).
    + intros a b c ? ?.
      abstract (induction a, b, c;
                apply monoidfunmul).
Defined.

(** Throwaway lemma: transport intertwines composition *)
Local Lemma transport_compose {C : precategory} {a b : ob C} {p : a = b}
           (f : a --> a) (g : a --> a) :
  transportf (λ x, C ⟦ x, b ⟧) p (transportf (λ x, C ⟦ a, x ⟧) p f) ·
  transportf (λ x, C ⟦ x, b ⟧) p (transportf (λ x, C ⟦ a, x ⟧) p g)
  = transportf (λ x, C ⟦ x, b ⟧) p (transportf (λ x, C ⟦ a, x ⟧) p (f · g)).
Proof.
  induction p; reflexivity.
Defined.

(** Throwaway lemma: transport intertwines identity *)
Local Lemma transport_identity {C : precategory} {a b : ob C} {p : a = b} :
  transportf (λ x, C ⟦ x, b ⟧) p (transportf (λ x, C ⟦ a, x ⟧) p (identity a)) =
  identity b.
Proof.
  induction p; reflexivity.
Defined.

(** Functor --> monoid morphism *)
Definition functor_to_monoidfun {CC1 CC2 : contr_cat} (funct : functor CC1 CC2) :
  monoidfun (invmap monoid_weq_contr_category CC1)
            (invmap monoid_weq_contr_category CC2).
Proof.
  use monoidfunconstr.
  - cbn in *.
    intros endo.
    apply (contr_cat_hom_weq (funct (iscontrpr1 (pr2 CC1)))
                             (funct (iscontrpr1 (pr2 CC1)))).
    exact (# funct endo).
  - use mk_ismonoidfun.
    + intros a b; cbn.
      abstract (rewrite functor_comp;
                rewrite <- transport_compose;
                reflexivity).
    + abstract (cbn; rewrite functor_id_id; [|reflexivity];
                rewrite transport_identity;
                reflexivity).
Defined.

(** The above functions constitute a weak equivalence. *)
Lemma monoid_fun_weq_functor {Mon1 Mon2 : monoid} :
      (monoidfun Mon1 Mon2) ≃
      functor (monoid_weq_contr_category Mon1) (monoid_weq_contr_category Mon2).
Proof.
  use weq_iso.
  - exact monoidfun_to_functor.
  - exact functor_to_monoidfun.
  - intros mfun.
    apply monoidfun_paths.
    reflexivity.
  - intros funct.
    apply functor_eq; [apply homset_property|].
    use functor_data_eq.
    + intros ?.
      exact (!(pr2 iscontrunit _)).
    + intros c1 c2 ?.
      (** Compare to proof of [contr_cat_hom_weq] *)
      abstract (induction c1, c2; cbn;
                do 2 (rewrite (transport_f_f _ (isProofIrrelevantUnit _ _)
                                             (! (isProofIrrelevantUnit _ _)) _);
                      rewrite pathsinv0r; cbn; unfold idfun);
                reflexivity).
Defined.

(** *** Groups *)

(** **** Groups as groupoids *)

(** **** Group morphisms as functors *)

(** ** Actions *)

(** *** As homomorphisms *)

(** **** Monoid (group) actions *)

Definition monaction_as_morphism {C : category} (Mon : monoid) (X : ob C) : UU :=
  monoidfun Mon (endomorphism_monoid X).
Identity Coercion id_monaction :  monaction_as_morphism >-> monoidfun.

(** Let f and g be actions of M on objects X and Y, respectively. An
    _equivariant map_ h from f to g is one that intertwines the actions of M,
    that is, for any m : M,

    <<
      X -- f m --> X
      |            |
      h            h
      V            V
      Y -- g m --> Y
    >>

    i.e. f m · h = h · g m.
 *)

Definition monaction_equivariant_map
           {C : category} {M : monoid} {X Y : ob C}
           (actX : monaction_as_morphism M X)
           (actY : monaction_as_morphism M Y) : UU :=
  ∑ f : X --> Y, ∏ m, actX m · f = f · actY m.

(** **** Ring actions *)

Definition ringaction_as_morphism {C : Additive} (R : ring) (X : ob C) :=
  ringfun R (endomorphism_ring X).

(** *** As functors *)

(** **** Equivariant maps (intertwiners) *)

Definition contr_cat_action (CC : contr_cat) (C : category) : UU := (CC ⟶ C).
Identity Coercion id_contr_cat_action : contr_cat_action >-> functor.

Section FunctorActions.
  Context {CC : contr_cat} {C : category}
          (actA : contr_cat_action CC C) (actB : contr_cat_action CC C).

  (** Now we can provide a uniform definition of equivariant maps for monoids,
      groups, and rings: equivariant map, or intertwiner, is simply a natural
      transformation. *)
  Definition equivariant_map : UU :=
    nat_trans (functor_data_from_functor _ _ actA)
              (functor_data_from_functor _ _ actB).

  Definition equivariant_map' : UU :=
    ∑ f : actA (contr_cat_center CC) --> actB (contr_cat_center CC),
    ∏ g : CC ⟦ contr_cat_center CC, contr_cat_center CC ⟧,
      # actA g · f = f · # actB g.

End FunctorActions.

(** **** Monoid (group) actions *)

(** A monoid action is a functor from the monoid (viewed as a category)
    to the target category. *)
Definition monaction_functor (Mon : monoid) (C : category) :=
  contr_cat_action (monoid_weq_contr_category Mon) C.

(** **** Ring actions *)

(** ** Theory *)

(** *** Translation groupoid ([translation_groupoid]) *)

Definition translation_groupoid_precat {CC : contr_cat}
           (F : contr_cat_action CC hset_category) : precategory.
Proof.
  pose (center := contr_cat_center CC).
  use mk_precategory.
  - use precategory_data_pair.
    + use precategory_ob_mor_pair.
      * exact (pr1 (F center)).
      * intros x1 x2; exact (∑ c : CC ⟦center, center⟧, # F c x1 = x2).
    + intros c; exists (identity center).
      refine (@eqtohomot _ _ (# F (identity center)) (idfun _) _ c).
      apply (functor_id F center).
    + intros a b c f g.
      cbn in *.
      exists (pr1 f · pr1 g).
      refine (maponpaths (λ z, z _) (functor_comp F (pr1 f) (pr1 g)) @ _); cbn.
      refine (maponpaths _ (pr2 f) @ _).
      exact (pr2 g).
  - use dirprodpair.
    + use dirprodpair;
        intros ? ? ?;
        apply subtypeEquality'.
      * apply id_left.
      * apply setproperty.
      * apply id_right.
      * apply setproperty.
    + cbn.
      intros a b c d f g h.
      apply subtypeEquality'; [|apply setproperty].
      apply assoc.
Defined.
