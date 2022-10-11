(** * Category of commrings *)
(** ** Contents
- Precategory of commrings
- Category of commrings
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.RigsAndRings.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Local Open Scope cat.


(** * Category of commrings *)
Section def_commring_precategory.

  Definition commring_fun_space (A B : commring) : hSet := make_hSet (ringfun A B) (isasetrigfun A B).

  Definition commring_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) commring (λ A B : commring, commring_fun_space A B).

  Definition commring_precategory_data : precategory_data :=
    make_precategory_data
      commring_precategory_ob_mor (λ (X : commring), (rigisotorigfun (idrigiso X)))
      (fun (X Y Z : commring) (f : ringfun X Y) (g : ringfun Y Z) => rigfuncomp f g).

  Local Lemma commring_id_left (X Y : commring) (f : ringfun X Y) :
    rigfuncomp (rigisotorigfun (idrigiso X)) f = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque commring_id_left.

  Local Lemma commring_id_right (X Y : commring) (f : ringfun X Y) :
    rigfuncomp f (rigisotorigfun (idrigiso Y)) = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque commring_id_right.

  Local Lemma commring_assoc (X Y Z W : commring) (f : ringfun X Y) (g : ringfun Y Z)
        (h : ringfun Z W) : rigfuncomp f (rigfuncomp g h) = rigfuncomp (rigfuncomp f g) h.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque commring_assoc.

  Lemma is_precategory_commring_precategory_data : is_precategory commring_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros a b f. use commring_id_left.
    - intros a b f. use commring_id_right.
    - intros a b c d f g h. use commring_assoc.
  Qed.

  Definition commring_precategory : precategory :=
    make_precategory commring_precategory_data is_precategory_commring_precategory_data.

  Lemma has_homsets_commring_precategory : has_homsets commring_precategory.
  Proof.
    intros X Y. use isasetrigfun.
  Qed.

End def_commring_precategory.


(** * Category of commrings *)
Section def_commring_category.

  Definition commring_category : category := make_category _ has_homsets_commring_precategory.

  (** ** (ringiso X Y) ≃ (z_iso X Y) *)

  Lemma commring_iso_is_equiv (A B : ob commring_category) (f : z_iso A B) : isweq (pr1 (pr1 f)).
  Proof.
    use isweq_iso.
    - exact (pr1rigfun _ _ (inv_from_z_iso f)).
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (z_iso_inv_after_z_iso f)) x).
      intros x0. use isapropisrigfun.
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (z_iso_after_z_iso_inv f)) x).
      intros x0. use isapropisrigfun.
  Defined.
  Opaque commring_iso_is_equiv.

  Lemma commring_iso_equiv (X Y : ob commring_category) :
    z_iso X Y -> ringiso (X : commring) (Y : commring).
  Proof.
    intro f.
    use make_ringiso.
    - exact (make_weq (pr1 (pr1 f)) (commring_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma commring_equiv_is_z_iso (X Y : ob commring_category)
        (f : ringiso (X : commring) (Y : commring)) :
    @is_z_isomorphism commring_category X Y (ringfunconstr (pr2 f)).
  Proof.
    exists (ringfunconstr (pr2 (invrigiso f))).
    use make_is_inverse_in_precat.
    - use rigfun_paths. use funextfun. intros x. use homotinvweqweq.
    - use rigfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque commring_equiv_is_z_iso.

  Lemma commring_equiv_iso (X Y : ob commring_category) :
    ringiso (X : commring) (Y : commring) -> z_iso X Y.
  Proof.
    intros f. exact (_,,commring_equiv_is_z_iso X Y f).
  Defined.

  Lemma commring_iso_equiv_is_equiv (X Y : commring_category) : isweq (commring_iso_equiv X Y).
  Proof.
    use isweq_iso.
    - exact (commring_equiv_iso X Y).
    - intros x. use z_iso_eq. use rigfun_paths. apply idpath.
    - intros y. use rigiso_paths. use subtypePath.
      + intros x0. use isapropisweq.
      + apply idpath.
  Defined.
  Opaque commring_iso_equiv_is_equiv.

  Definition commring_iso_equiv_weq (X Y : ob commring_category) :
    weq (z_iso X Y) (ringiso (X : commring) (Y : commring)).
  Proof.
    use make_weq.
    - exact (commring_iso_equiv X Y).
    - exact (commring_iso_equiv_is_equiv X Y).
  Defined.

  Lemma commring_equiv_iso_is_equiv (X Y : ob commring_category) : isweq (commring_equiv_iso X Y).
  Proof.
    use isweq_iso.
    - exact (commring_iso_equiv X Y).
    - intros y. use rigiso_paths. use subtypePath.
      + intros x0. use isapropisweq.
      + apply idpath.
    - intros x. use z_iso_eq. use rigfun_paths. apply idpath.
  Defined.
  Opaque commring_equiv_iso_is_equiv.

  Definition commring_equiv_weq_iso (X Y : ob commring_category) :
    (ringiso (X : commring) (Y : commring)) ≃ (z_iso X Y).
  Proof.
    use make_weq.
    - exact (commring_equiv_iso X Y).
    - exact (commring_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of commrings *)

  Definition commring_category_isweq (X Y : ob commring_category) :
    isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (z_iso X Y)
           (pr1weq (weqcomp (commring_univalence X Y) (commring_equiv_weq_iso X Y)))
           _ _ (weqproperty (weqcomp (commring_univalence X Y) (commring_equiv_weq_iso X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - apply idpath.
    - use proofirrelevance. use isaprop_is_z_isomorphism.
  Defined.
  Opaque commring_category_isweq.



  Definition commring_category_is_univalent : is_univalent commring_category.
  Proof.
    intros X Y. exact (commring_category_isweq X Y).
  Defined.

  Definition commring_univalent_category : univalent_category :=
    make_univalent_category commring_category commring_category_is_univalent.

End def_commring_category.
