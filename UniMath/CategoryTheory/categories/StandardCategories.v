(** * Standard categories *)
(** ** Contents:

- The path groupoid ([path_groupoid])
- Discrete categories
  - Characterization of discrete categories
- The discrete univalent_category on n objects ([cat_n])
  - The category with one object ([unit_category])
  - The category with no objects ([empty_category])
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.catiso.

Local Open Scope cat.

Definition compose' { C:precategory_data } { a b c:ob C }
  (g:b --> c) (f:a --> b) : a --> c.
Proof. intros. exact (compose f g). Defined.

(** ** The path/fundamental groupoid of a type *)

(** The pregroupoid with points in X as objects and paths as morphisms *)
Definition path_pregroupoid (X:UU) : pregroupoid.
  use mk_pregroupoid.
  - use mk_precategory_one_assoc; use tpair.
    + exact (X,, λ x y, x = y).
    + use dirprodpair.
      * exact (λ _, idpath _).
      * intros a b c; exact pathscomp0.
    + use dirprodpair.
      * reflexivity.
      * intros; apply pathscomp0rid.
    + intros ? ? ? ? ? ?; apply path_assoc.
  - intros x y path.
    use (is_iso_qinv path); cbn in *.
    + exact (!path).
    + use dirprodpair.
      * apply pathsinv0r.
      * apply pathsinv0l.
Defined.

(** If X [isofhlevel] 3, then in particular, its path types are sets *)
Definition has_homsets_path_pregroupoid {X : UU} (iobj : isofhlevel 3 X) :
  has_homsets (path_pregroupoid X).
Proof.
  intros ? ? ? ? ? ?.
  apply iobj.
Defined.

Definition path_groupoid (X : UU) (iobj : isofhlevel 3 X) : groupoid.
Proof.
  use mk_groupoid.
  - use category_pair.
    + exact (path_pregroupoid X).
    + apply (has_homsets_path_pregroupoid); assumption.
  - apply (pregroupoid_is_pregroupoid (path_pregroupoid X)).
Defined.

(** In this case, the path pregroupoid is further univalent. *)
Lemma is_univalent_path_pregroupoid (X : UU) (iobj : isofhlevel 3 X) :
  is_univalent_pregroupoid (path_pregroupoid X).
Proof.
  split.
  - intros a b.
    assert (k : idfun (a = b) ~ idtomor a b).
           { intro p; destruct p; reflexivity. }
    apply (isweqhomot _ _ k). apply idisweq.
  - apply has_homsets_path_pregroupoid; assumption.
Defined.

Lemma is_univalent_path_groupoid (X:UU) (i : isofhlevel 3 X) :
  is_univalent (path_groupoid X i).
Proof.
  intros; split.
  - apply is_univalent_pregroupoid_is_univalent,
          is_univalent_path_pregroupoid; assumption.
  - apply i.
Defined.

Definition path_univalent_groupoid {X : UU} (i3 : isofhlevel 3 X) :
  univalent_groupoid :=
  mk_univalent_groupoid (univalent_category_pair _ (is_univalent_path_groupoid X i3))
                        (groupoid_is_pregroupoid _).

Definition path_groupoid_hset (X : hSet) : univalent_groupoid :=
  (path_univalent_groupoid (isofhlevelssnset 1 _ (setproperty X))).

(** When X is a set, its path pregroupoid is the discrete category on its elements. *)
Definition path_groupoid_hset_is_discrete (X : hSet) :
  is_discrete (path_groupoid_hset X).
Proof.
  split; split.
  - apply setproperty.
  - apply homset_property.
  - apply pregroupoid_is_pregroupoid.
  - apply univalent_category_is_univalent.
Defined.

Definition discrete_category_hset (X : hSet) : discrete_category :=
  mk_discrete_category (path_groupoid_hset X) (path_groupoid_hset_is_discrete X).

(** To define a functor out of a path pregroupoid, it suffices to give
    its values on objects. Compare to [functor_discrete_categories]. *)
Lemma functor_path_pregroupoid
      {X : UU} {D : precategory} (f : X → ob D) :
  functor (path_pregroupoid X) D.
Proof.
  use mk_functor.
  - use mk_functor_data.
    + apply f.
    + intros a b aeqb.
      exact (transportf (λ z, D ⟦ f a, z ⟧) (maponpaths f aeqb) (identity _)).
  - split.
    + intro; reflexivity.
    + intros a b c g h; cbn.
      refine (maponpaths (λ p, transportf _ p _) (maponpathscomp0 _ _ _) @ _).
      refine (!transport_f_f _ (maponpaths f g) (maponpaths f h) _ @ _).
      abstract (induction h; cbn; unfold idfun; apply pathsinv0; apply id_right).
Defined.

(** A natural transformation of functors out of a path groupoid is given by any
    family of morphisms *)
Definition is_nat_trans_discrete_precategory
           {X : UU} {D : precategory} (Dhom : has_homsets D)
           {f g : functor_precategory (path_pregroupoid X) D Dhom}
           (F : ∏ x : X, (pr1 f) x --> (pr1 g) x)
  : is_nat_trans (pr1 f) (pr1 g) F.
Proof.
  intros x y h; cbn in h.
  induction h.
  change (idpath x) with (identity x).
  assert (k := ! functor_id f x).
  unfold functor_data_from_functor in k.
  induction k.
  assert (k := ! functor_id g x).
  unfold functor_data_from_functor in k.
  induction k.
  intermediate_path (F x).
  - apply id_left.
  - apply pathsinv0. apply id_right.
Qed.

(** *** Characterization of discrete categories *)

(** Discrete categories are isomorphic to the path groupoid on their set of objects.
    This is analogous to the statement that any skeletal groupoid is discrete. *)

Lemma discrete_category_iso_path_groupoid (C : discrete_category) :
  catiso C (discrete_category_hset
              (setcategory_objects_set (_,, discrete_category_is_setcategory C))).
Proof.
  use tpair.
  - use mk_functor.
    + use mk_functor_data.
      * exact (idfun _).
      * intros a b f.
        apply isotoid.
        -- apply univalent_category_is_univalent.
        -- exact (@pregroupoid_hom_weq_iso C _ _ f).
    + use dirprodpair.
      * intro; apply setproperty.
      * intros ? ? ? ? ?; apply setproperty.
  - use dirprodpair.
    + intros a b.
      use isweq_iso.
      * intros f.
        apply idtoiso.
        assumption.
      * intro; apply discrete_category_hom_prop.
      * intro; apply setproperty.
   + apply idisweq.
Defined.

(** ** The discrete univalent_category on n objects ([cat_n]) *)

Require Import UniMath.Combinatorics.StandardFiniteSets.

Definition cat_n (n:nat): univalent_groupoid.
  apply path_groupoid_hset; use hSetpair.
  - exact (stn n).
  - apply isasetstn.
Defined.

Lemma is_discrete_cat_n (n : nat) : is_discrete (cat_n n).
Proof.
  apply path_groupoid_hset_is_discrete.
Defined.

(** ** The category with one object ([unit_category]) *)

Definition unit_category : univalent_category.
Proof.
  use path_univalent_groupoid.
  - exact unit.
  - do 2 (apply hlevelntosn). apply isapropunit.
Defined.

Section FunctorToUnit.
  Context (A : precategory).

  Definition functor_to_unit_data : functor_data A unit_category.
  Proof.
    use mk_functor_data.
    - exact tounit.
    - exact (λ _ _ _, idpath _ ).
  Defined.

  Definition is_functor_to_unit : is_functor functor_to_unit_data.
  Proof.
    split.
    - intro. apply idpath.
    - intros ? ? ? ? ?; apply idpath.
  Qed.

  Definition functor_to_unit : functor A _ := mk_functor _ is_functor_to_unit.

  Lemma iscontr_functor_to_unit : iscontr (functor A unit_category).
  Proof.
    use iscontrpair.
    - exact functor_to_unit.
    - intro F.
      apply functor_eq.
      + apply (homset_property unit_category).
      + use total2_paths_f.
        * apply funextsec. intro. cbn.
          apply proofirrelevance.
          apply isapropunit.
        * do 3 (apply funextsec; intro).
          apply proofirrelevance.
          simpl.
          apply hlevelntosn.
          apply isapropunit.
  Qed.
End FunctorToUnit.

(** ** The category with no objects ([empty_category]) *)

Definition empty_category : univalent_category.
Proof.
  use path_univalent_groupoid.
  - exact empty.
  - do 2 (apply hlevelntosn). apply isapropempty.
Defined.

Section FunctorFromEmpty.
  Context (A : precategory).

  Definition functor_from_empty_data : functor_data empty_category A.
  Proof.
    use mk_functor_data.
    - exact fromempty.
    - intros empt ?; induction empt.
  Defined.

  Definition is_functor_from_empty : is_functor functor_from_empty_data.
  Proof.
    use tpair; intro a; induction a.
  Defined.

  Definition functor_from_empty : functor empty_category A :=
    mk_functor _ is_functor_from_empty.

  (** Compare to [isaprop_is_functor]. For a functor from the empty_category,
      it's not necessary that the codomain has homsets. *)
  Lemma isaprop_is_functor_from_empty
        (F : functor_data empty_category A) : isaprop (is_functor F).
  Proof.
    apply isapropdirprod.
    - unfold functor_idax.
      apply impred; intro e; induction e.
    - unfold functor_compax.
      apply impred; intro e; induction e.
  Defined.

  Lemma iscontr_functor_from_empty : iscontr (functor empty_category A).
  Proof.
    use iscontrpair.
    - exact functor_from_empty.
    - intro F.
      use total2_paths_f.
      + use total2_paths_f;
          apply funextsec; intro empt; induction empt.
      + apply proofirrelevance, isaprop_is_functor_from_empty.
  Defined.
End FunctorFromEmpty.

(* *)
