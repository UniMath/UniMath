(** * Category of monoids *)
(** ** Contents
- Precategory of monoids
- Category of monoids
- Forgetful functor to [HSET]
- Free functor from [HSET]
- Free/forgetful adjunction
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.Algebra.Free_Monoids_and_Groups.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.IteratedBinaryOperations.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.Adjunctions.

Local Open Scope cat.

(** ** Precategory of monoids *)

Section def_monoid_precategory.

  Definition monoid_fun_space (A B : monoid) : hSet :=
    hSetpair (monoidfun A B) (isasetmonoidfun A B).

  Definition monoid_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) monoid (λ A B : monoid, monoid_fun_space A B).

  Definition monoid_precategory_data : precategory_data :=
    precategory_data_pair
      monoid_precategory_ob_mor (λ (X : monoid), ((idmonoidiso X) : monoidfun X X))
      (fun (X Y Z : monoid) (f : monoidfun X Y) (g : monoidfun Y Z) => monoidfuncomp f g).

  Local Lemma monoid_id_left {X Y : monoid} (f : monoidfun X Y) :
    monoidfuncomp (idmonoidiso X) f = f.
  Proof.
    use monoidfun_paths. use idpath.
  Defined.
  Opaque monoid_id_left.

  Local Lemma monoid_id_right {X Y : monoid} (f : monoidfun X Y) :
    monoidfuncomp f (idmonoidiso Y) = f.
  Proof.
    use monoidfun_paths. use idpath.
  Defined.
  Opaque monoid_id_right.

  Local Lemma monoid_assoc (X Y Z W : monoid) (f : monoidfun X Y) (g : monoidfun Y Z)
        (h : monoidfun Z W) :
    monoidfuncomp f (monoidfuncomp g h) = monoidfuncomp (monoidfuncomp f g) h.
  Proof.
    use monoidfun_paths. use idpath.
  Defined.
  Opaque monoid_assoc.

  Lemma is_precategory_monoid_precategory_data : is_precategory monoid_precategory_data.
  Proof.
   use mk_is_precategory_one_assoc.
    - intros a b f. use monoid_id_left.
    - intros a b f. use monoid_id_right.
    - intros a b c d f g h. use monoid_assoc.
  Qed.

  Definition monoid_precategory : precategory :=
    mk_precategory monoid_precategory_data is_precategory_monoid_precategory_data.

  Lemma has_homsets_monoid_precategory : has_homsets monoid_precategory.
  Proof.
    intros X Y. use isasetmonoidfun.
  Qed.

End def_monoid_precategory.


(** ** Category of monoids *)
Section def_monoid_category.

  (** ** (monoidiso X Y) ≃ (iso X Y) *)

  Lemma monoid_iso_is_equiv (A B : ob monoid_precategory) (f : iso A B) : isweq (pr1 (pr1 f)).
  Proof.
    use isweq_iso.
    - exact (pr1monoidfun _ _ (inv_from_iso f)).
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (iso_inv_after_iso f)) x).
      intros x0. use isapropismonoidfun.
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (iso_after_iso_inv f)) x).
      intros x0. use isapropismonoidfun.
  Defined.
  Opaque monoid_iso_is_equiv.

  Lemma monoid_iso_equiv (X Y : ob monoid_precategory) : iso X Y -> monoidiso X Y.
  Proof.
    intro f.
    use monoidisopair.
    - exact (weqpair (pr1 (pr1 f)) (monoid_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma monoid_equiv_is_iso (X Y : ob monoid_precategory) (f : monoidiso X Y) :
    @is_iso monoid_precategory X Y (monoidfunconstr (pr2 f)).
  Proof.
    use is_iso_qinv.
    - exact (monoidfunconstr (pr2 (invmonoidiso f))).
    - use mk_is_inverse_in_precat.
      + use monoidfun_paths. use funextfun. intros x. use homotinvweqweq.
      + use monoidfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque monoid_equiv_is_iso.

  Lemma monoid_equiv_iso (X Y : ob monoid_precategory) : monoidiso X Y -> iso X Y.
  Proof.
    intros f. exact (@isopair monoid_precategory X Y (monoidfunconstr (pr2 f))
                              (monoid_equiv_is_iso X Y f)).
  Defined.

  Lemma monoid_iso_equiv_is_equiv (X Y : monoid_precategory) : isweq (monoid_iso_equiv X Y).
  Proof.
    use isweq_iso.
    - exact (monoid_equiv_iso X Y).
    - intros x. use eq_iso. use monoidfun_paths. use idpath.
    - intros y. use monoidiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque monoid_iso_equiv_is_equiv.

  Definition monoid_iso_equiv_weq (X Y : ob monoid_precategory) : (iso X Y) ≃ (monoidiso X Y).
  Proof.
    use weqpair.
    - exact (monoid_iso_equiv X Y).
    - exact (monoid_iso_equiv_is_equiv X Y).
  Defined.

  Lemma monoid_equiv_iso_is_equiv (X Y : ob monoid_precategory) : isweq (monoid_equiv_iso X Y).
  Proof.
    use isweq_iso.
    - exact (monoid_iso_equiv X Y).
    - intros y. use monoidiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use eq_iso. use monoidfun_paths. use idpath.
  Defined.
  Opaque monoid_equiv_iso_is_equiv.

  Definition monoid_equiv_weq_iso (X Y : ob monoid_precategory) : (monoidiso X Y) ≃ (iso X Y).
  Proof.
    use weqpair.
    - exact (monoid_equiv_iso X Y).
    - exact (monoid_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of monoids *)

  Definition monoid_precategory_isweq (X Y : ob monoid_precategory) :
    isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (iso X Y)
           (pr1weq (weqcomp (monoid_univalence X Y) (monoid_equiv_weq_iso X Y)))
           _ _ (weqproperty (weqcomp (monoid_univalence X Y) (monoid_equiv_weq_iso X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
  Defined.
  Opaque monoid_precategory_isweq.

  Definition monoid_precategory_is_univalent : is_univalent monoid_precategory.
  Proof.
    use mk_is_univalent.
    - intros X Y. exact (monoid_precategory_isweq X Y).
    - exact has_homsets_monoid_precategory.
  Defined.

  Definition monoid_category : univalent_category :=
    mk_category monoid_precategory monoid_precategory_is_univalent.

End def_monoid_category.

(** ** Forgetful functor to [HSET] *)

Definition monoid_forgetful_functor : functor monoid_precategory HSET.
Proof.
  use mk_functor.
  - use mk_functor_data.
    + intro; exact (pr1setwithbinop (pr1monoid ltac:(assumption))).
    + intros ? ? f; exact (pr1monoidfun _ _ f).
  - split.
    + (** Identity axiom *)
      intro; reflexivity.
    + (** Composition axiom *)
      intros ? ? ? ? ?; reflexivity.
Defined.

Lemma monoid_forgetful_functor_is_faithful : faithful monoid_forgetful_functor.
Proof.
  unfold faithful.
  intros ? ?.
  apply isinclpr1.
  apply isapropismonoidfun.
Defined.

(** ** Free functor from [HSET] *)

Definition monoid_free_functor : functor HSET monoid_precategory.
Proof.
  use mk_functor.
  - use mk_functor_data.
    + intros s; exact (free_monoid s).
    + intros ? ? f; exact (free_monoidfun f).
  - split.
    + (** Identity axiom *)
      intros ?.
      abstract (apply monoidfun_paths, funextfun; intro; apply map_idfun).
    + (** Composition axiom *)
      intros ? ? ? ? ?.
      abstract (apply monoidfun_paths, funextfun, (free_monoidfun_comp_homot f g)).
Defined.

(** ** Free/forgetful adjunction *)

(** The unit of this adjunction is the singleton function [x ↦ x::nil] *)
Definition monoid_free_forgetful_unit :
  nat_trans (functor_identity _)
            (functor_composite monoid_free_functor monoid_forgetful_functor).
Proof.
  use mk_nat_trans.
  - intros ? x; exact (cons x Lists.nil).
  - intros ? ? ?.
    abstract (apply funextfun; intro; reflexivity).
Defined.

(** This amounts to naturality of the counit: mapping commutes with folding *)
Lemma iterop_list_mon_map {m n : monoid} (f : monoidfun m n) :
  ∏ l, ((iterop_list_mon ∘ map (pr1monoidfun m n f)) l =
        (pr1monoidfun _ _ f ∘ iterop_list_mon) l)%functions.
Proof.
  apply list_ind.
  - apply pathsinv0, monoidfununel.
  - intros x xs H.
    unfold funcomp in *.
    refine (maponpaths iterop_list_mon (map_cons _ _ _) @ _).
    refine (iterop_list_mon_step _ _ @ _).
    refine (_ @ !maponpaths _ (iterop_list_mon_step _ _)).
    refine (_ @ !binopfunisbinopfun f _ _).
    apply maponpaths.
    assumption.
Qed.

(** The counit of this adjunction is the "folding" function
    [[a, b, …, z] ↦ a · b · ⋯ · z]

    (This is known to Haskell programmers as [mconcat].) *)
Definition monoid_free_forgetful_counit :
  nat_trans (functor_composite monoid_forgetful_functor monoid_free_functor )
            (functor_identity _).
Proof.
  use mk_nat_trans.
  - intros ?.
    use tpair.
    + intro; apply iterop_list_mon; assumption.
    + split.
      * intros ? ?; apply iterop_list_mon_concatenate.
      * reflexivity.
  - intros ? ? f; apply monoidfun_paths.
    apply funextfun; intro; simpl in *.
    apply (iterop_list_mon_map f).
Defined.

Definition monoid_free_forgetful_adjunction_data :
  adjunction_data HSET monoid_precategory .
Proof.
  use tpair; [|use tpair]. (* TODO: there should be a constructor for this *)
  - exact monoid_free_functor.
  - exact monoid_forgetful_functor.
  - split.
    + exact monoid_free_forgetful_unit.
    + exact monoid_free_forgetful_counit.
Defined.

Lemma monoid_free_forgetful_adjunction :
  form_adjunction' monoid_free_forgetful_adjunction_data.
Proof.
  split; intro.
  - apply monoidfun_paths.
    apply funextfun.
    simpl; unfold funcomp.
    unfold homot; apply list_ind; [reflexivity|].
    intros x xs ?.
    unfold funcomp.
    rewrite map_cons.
    (* For some reason, the unifier needs a lot of help here... *)
    refine (iterop_list_mon_step ((cons _ _) : pr1hSet (free_monoid _))
                                  (map (λ z, cons z Lists.nil) xs) @ _).
    apply maponpaths; assumption.
  - reflexivity.
Qed.