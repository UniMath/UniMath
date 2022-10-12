(** * Standard categories *)
(** ** Contents:

- The path groupoid ([path_groupoid])
- Discrete categories
  - Characterization of discrete categories
- The discrete univalent_category on n objects ([cat_n])
  - The category with one object ([unit_category])
  - The category with no objects ([empty_category])
  - The directed interval
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.catiso.

Local Open Scope cat.

Definition compose' { C:precategory_data } { a b c:ob C }
  (g:b --> c) (f:a --> b) : a --> c.
Proof. intros. exact (compose f g). Defined.

(** ** The path/fundamental groupoid of a type *)

(** The pregroupoid with points in X as objects and paths as morphisms *)
Definition path_pregroupoid (X:UU) (iobj : isofhlevel 3 X) : pregroupoid.
  use make_pregroupoid.
  - use tpair.
    {
    use make_precategory_one_assoc; use tpair.
    + exact (X,, λ x y, x = y).
    + use make_dirprod.
      * exact (λ _, idpath _).
      * intros a b c; exact pathscomp0.
    + use make_dirprod.
      * reflexivity.
      * intros; apply pathscomp0rid.
    + intros ? ? ? ? ? ?; apply path_assoc.
    }
    intros ? ? ? ? ? ?.
    apply iobj.
  - intros x y path.
    exists (!path).
    split.
    + apply pathsinv0r.
    + apply pathsinv0l.
Defined.

(** If X [isofhlevel] 3, then in particular, its path types are sets *)
Definition has_homsets_path_pregroupoid {X : UU} (iobj : isofhlevel 3 X) :
  has_homsets (path_pregroupoid X iobj).
Proof.
  apply homset_property.
Defined.

Definition path_groupoid (X : UU) (iobj : isofhlevel 3 X) : groupoid.
Proof.
  use make_groupoid.
  - use make_category.
    + exact (path_pregroupoid X iobj).
    + apply (has_homsets_path_pregroupoid); assumption.
  - apply (pregroupoid_is_pregroupoid (path_pregroupoid X iobj)).
Defined.

(** In this case, the path pregroupoid is further univalent. *)
Lemma is_univalent_path_pregroupoid (X : UU) (iobj : isofhlevel 3 X) :
  is_univalent_pregroupoid (path_pregroupoid X iobj).
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
  apply is_univalent_pregroupoid_is_univalent,
          is_univalent_path_pregroupoid; assumption.
Defined.

Definition path_univalent_groupoid
           {X : UU}
           (i3 : isofhlevel 3 X)
  : univalent_groupoid.
Proof.
  use make_univalent_groupoid.
  - exact (make_univalent_category _ (is_univalent_path_groupoid X i3)).
  - apply (groupoid_is_pregroupoid _).
Defined.

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
  make_discrete_category (path_groupoid_hset X) (path_groupoid_hset_is_discrete X).

(** To define a functor out of a path pregroupoid, it suffices to give
    its values on objects. Compare to [functor_discrete_categories]. *)
Lemma functor_path_pregroupoid
      {X : UU} {D : category} (i : isofhlevel 3 X) (f : X → ob D) :
  functor (path_pregroupoid X i) D.
Proof.
  use make_functor.
  - use make_functor_data.
    + apply f.
    + intros a b aeqb.
      exact (transportf (λ z, D ⟦ f a, z ⟧) (maponpaths f aeqb) (identity _)).
  - split.
    + intro; reflexivity.
    + intros a b c g h; cbn.
      refine (maponpaths (λ p, transportf _ p _) (maponpathscomp0 _ _ _) @ _).
      refine (!transport_f_f _ (maponpaths f g) (maponpaths f h) _ @ _).
      abstract (induction h; cbn; apply pathsinv0; apply id_right).
Defined.

(** A natural transformation of functors out of a path groupoid is given by any
    family of morphisms *)
Definition is_nat_trans_discrete_precategory
           {X : UU} {i : isofhlevel 3 X}  {D : category}
           {f g : functor_category (path_pregroupoid X i) D}
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

Definition nat_trans_functor_path_pregroupoid
           {X : UU} {i : isofhlevel 3 X} {D : category} {F G : functor (path_pregroupoid X i) D}
           (ϕ : ∏ x : X, F x --> G x) : nat_trans F G.
Proof.
use make_nat_trans.
- intros z; apply (ϕ z).
- apply (is_nat_trans_discrete_precategory).
Defined.


(** *** Characterization of discrete categories *)

(** Discrete categories are isomorphic to the path groupoid on their set of objects.
    This is analogous to the statement that any skeletal groupoid is discrete. *)

Lemma discrete_category_iso_path_groupoid (C : discrete_category) :
  catiso C (discrete_category_hset
              (setcategory_objects_set (_,, discrete_category_is_setcategory C))).
Proof.
  use tpair.
  - use make_functor.
    + use make_functor_data.
      * exact (idfun _).
      * intros a b f.
        apply isotoid.
        -- apply univalent_category_is_univalent.
        -- exact (@pregroupoid_hom_weq_iso C _ _ f).
    + use make_dirprod.
      * intro; apply setproperty.
      * intros ? ? ? ? ?; apply setproperty.
  - use make_dirprod.
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
  apply path_groupoid_hset; use make_hSet.
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
    use make_functor_data.
    - exact tounit.
    - exact (λ _ _ _, idpath _ ).
  Defined.

  Definition is_functor_to_unit : is_functor functor_to_unit_data.
  Proof.
    split.
    - intro. apply idpath.
    - intros ? ? ? ? ?; apply idpath.
  Qed.

  Definition functor_to_unit : functor A _ := make_functor _ is_functor_to_unit.

  Lemma iscontr_functor_to_unit : iscontr (functor A unit_category).
  Proof.
    use make_iscontr.
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

(**
 Functors from the unit category
 *)
Definition functor_from_unit_data
           {C : category}
           (x : C)
  : functor_data unit_category C.
Proof.
  use make_functor_data.
  - exact (λ _, x).
  - exact (λ _ _ _, identity _).
Defined.

Definition functor_from_unit_is_functor
           {C : category}
           (x : C)
  : is_functor (functor_from_unit_data x).
Proof.
  split.
  - intro ; apply idpath.
  - intro ; intros ; cbn.
    rewrite id_left.
    apply idpath.
Qed.

Definition functor_from_unit
           {C : category}
           (x : C)
  : unit_category ⟶ C.
Proof.
  use make_functor.
  - exact (functor_from_unit_data x).
  - exact (functor_from_unit_is_functor x).
Defined.

Definition nat_trans_from_unit_is_nat_trans
           {C : category}
           {x y : C}
           (f : x --> y)
  : is_nat_trans
      (functor_from_unit x)
      (functor_from_unit y)
      (λ _, f).
Proof.
  intro ; intros ; cbn.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Definition nat_trans_from_unit
           {C : category}
           {x y : C}
           (f : x --> y)
  : functor_from_unit x ⟹ functor_from_unit y.
Proof.
  use make_nat_trans.
  - exact (λ _, f).
  - exact (nat_trans_from_unit_is_nat_trans f).
Defined.

Definition unit_category_nat_trans
           {C : category}
           (F G : C ⟶ unit_category)
  : F ⟹ G.
Proof.
  use make_nat_trans.
  - exact (λ _, pr1 (isapropunit _ _)).
  - abstract
      (intro ; intros ;
       apply isasetunit).
Defined.

Lemma nat_trans_to_unit_eq
      {X : category}
      (F G : X ⟶ unit_category)
      (α β : F ⟹ G)
  : α = β.
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - intro z. apply isasetunit.
Qed.

(** Morphisms are the same as certain natural transformations *)
Definition nat_trans_from_unit_weq_morphisms
           {C : category}
           (x y : C)
  : x --> y ≃ (functor_from_unit x ⟹ functor_from_unit y).
Proof.
  use make_weq.
  - exact nat_trans_from_unit.
  - use isweq_iso.
    + exact (λ n, n tt).
    + abstract
        (intro f ;
         apply idpath).
    + abstract
        (intros n ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intro z ; cbn ;
         induction z ;
         apply idpath).
Defined.

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
    use make_functor_data.
    - exact fromempty.
    - intros empt ?; induction empt.
  Defined.

  Definition is_functor_from_empty : is_functor functor_from_empty_data.
  Proof.
    use tpair; intro a; induction a.
  Defined.

  Definition functor_from_empty : functor empty_category A :=
    make_functor _ is_functor_from_empty.

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
    use make_iscontr.
    - exact functor_from_empty.
    - intro F.
      use total2_paths_f.
      + use total2_paths_f;
          apply funextsec; intro empt; induction empt.
      + apply proofirrelevance, isaprop_is_functor_from_empty.
  Defined.
End FunctorFromEmpty.

(** Natural transformations for the empty category *)
Definition nat_trans_from_empty
           {C : category}
           (F G : empty_category ⟶ C)
  : nat_trans F G.
Proof.
  use make_nat_trans.
  - exact (λ z, fromempty z).
  - exact (λ z, fromempty z).
Defined.

Definition nat_trans_to_empty
           {C₁ C₂ : category}
           (F : C₁ ⟶ empty_category)
           (G : empty_category ⟶ C₂)
           (H : C₁ ⟶ C₂)
  : H ⟹ F ∙ G.
Proof.
  use make_nat_trans.
  - exact (λ x, fromempty (F x)).
  - exact (λ x y f, fromempty (F x)).
Defined.

Definition nat_trans_to_empty_is_nat_z_iso
           {C₁ C₂ : category}
           (F : C₁ ⟶ empty_category)
           (G : empty_category ⟶ C₂)
           (H : C₁ ⟶ C₂)
  : is_nat_z_iso (nat_trans_to_empty F G H).
Proof.
  intro x.
  exact (fromempty (F x)).
Defined.

(* Directed interval category *)
Definition directed_interval_precategory_ob_mor
  : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact bool.
  - intros x y.
    induction x ; induction y.
    + exact unit.
    + exact unit.
    + exact empty.
    + exact unit.
Defined.

Definition directed_interval_precategory_data
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact directed_interval_precategory_ob_mor.
  - intro x.
    induction x.
    + exact tt.
    + exact tt.
  - intros x y z f g.
    induction x ; induction y ; induction z ; cbn in *.
    + exact tt.
    + exact tt.
    + exact tt.
    + exact tt.
    + exact f.
    + exact tt.
    + exact g.
    + exact tt.
Defined.

Definition directed_interval_precategory_is_precategory
  : is_precategory directed_interval_precategory_data.
Proof.
  use make_is_precategory_one_assoc.
  - intros x y f.
    induction x ; induction y ; cbn in *.
    + apply isapropunit.
    + apply isapropunit.
    + exact (fromempty f).
    + apply isapropunit.
  - intros x y f.
    induction x ; induction y ; cbn in *.
    + apply isapropunit.
    + apply isapropunit.
    + exact (fromempty f).
    + apply isapropunit.
  - intros w x y z f g h.
    induction w ; induction x ; induction y ; induction z ; cbn in * ; try (apply idpath).
    exact (fromempty f).
Qed.

Definition directed_interval_precategory
  : precategory.
Proof.
  use make_precategory.
  - exact directed_interval_precategory_data.
  - exact directed_interval_precategory_is_precategory.
Defined.

Definition directed_interval_category_has_homprops
           (x y : directed_interval_precategory_ob_mor)
  : isaprop (x --> y).
Proof.
  induction x ; induction y.
  - apply isapropunit.
  - apply isapropunit.
  - apply isapropempty.
  - apply isapropunit.
Qed.

Definition directed_interval_category_has_homsets
  : has_homsets directed_interval_precategory_ob_mor.
Proof.
  intros x y.
  apply isasetaprop.
  exact (directed_interval_category_has_homprops x y).
Qed.

Definition directed_interval_category
  : category.
Proof.
  use make_category.
  - exact directed_interval_precategory.
  - exact directed_interval_category_has_homsets.
Defined.

Definition is_univalent_directed_interval
  : is_univalent directed_interval_category.
Proof.
  intros x y.
  use isweqimplimpl.
  - intro f.
    induction x ; induction y ; cbn in *.
    + apply idpath.
    + apply (fromempty (inv_from_z_iso f)).
    + apply (fromempty (pr1 f)).
    + apply idpath.
  - apply isasetbool.
  - use (isaprop_total2 (_ ,, _) (λ _, _ ,, _)).
    + apply directed_interval_category_has_homprops.
    + intro.
      apply isaprop_is_z_isomorphism.
Qed.

Definition directed_interval
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact directed_interval_category.
  - exact is_univalent_directed_interval.
Defined.
