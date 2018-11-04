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
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.RigsAndRings.

Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.


(** * Category of commrings *)
Section def_commring_precategory.

  Definition commring_fun_space (A B : commring) : hSet := hSetpair (ringfun A B) (isasetrigfun A B).

  Definition commring_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) commring (λ A B : commring, commring_fun_space A B).

  Definition commring_precategory_data : precategory_data :=
    precategory_data_pair
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
    use mk_is_precategory_one_assoc.
    - intros a b f. use commring_id_left.
    - intros a b f. use commring_id_right.
    - intros a b c d f g h. use commring_assoc.
  Qed.

  Definition commring_precategory : precategory :=
    mk_precategory commring_precategory_data is_precategory_commring_precategory_data.

  Lemma has_homsets_commring_precategory : has_homsets commring_precategory.
  Proof.
    intros X Y. use isasetrigfun.
  Qed.

End def_commring_precategory.


(** * Category of commrings *)
Section def_commring_category.

  (** ** (ringiso X Y) ≃ (iso X Y) *)

  Lemma commring_iso_is_equiv (A B : ob commring_precategory) (f : iso A B) : isweq (pr1 (pr1 f)).
  Proof.
    use isweq_iso.
    - exact (pr1rigfun _ _ (inv_from_iso f)).
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (iso_inv_after_iso f)) x).
      intros x0. use isapropisrigfun.
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (iso_after_iso_inv f)) x).
      intros x0. use isapropisrigfun.
  Defined.
  Opaque commring_iso_is_equiv.

  Lemma commring_iso_equiv (X Y : ob commring_precategory) :
    iso X Y -> ringiso (X : commring) (Y : commring).
  Proof.
    intro f.
    use ringisopair.
    - exact (weqpair (pr1 (pr1 f)) (commring_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma commring_equiv_is_iso (X Y : ob commring_precategory)
        (f : ringiso (X : commring) (Y : commring)) :
    @is_iso commring_precategory X Y (ringfunconstr (pr2 f)).
  Proof.
    use is_iso_qinv.
    - exact (ringfunconstr (pr2 (invrigiso f))).
    - use mk_is_inverse_in_precat.
      + use rigfun_paths. use funextfun. intros x. use homotinvweqweq.
      + use rigfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque commring_equiv_is_iso.

  Lemma commring_equiv_iso (X Y : ob commring_precategory) :
    ringiso (X : commring) (Y : commring) -> iso X Y.
  Proof.
    intros f. exact (@isopair commring_precategory X Y (ringfunconstr (pr2 f))
                              (commring_equiv_is_iso X Y f)).
  Defined.

  Lemma commring_iso_equiv_is_equiv (X Y : commring_precategory) : isweq (commring_iso_equiv X Y).
  Proof.
    use isweq_iso.
    - exact (commring_equiv_iso X Y).
    - intros x. use eq_iso. use rigfun_paths. use idpath.
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque commring_iso_equiv_is_equiv.

  Definition commring_iso_equiv_weq (X Y : ob commring_precategory) :
    weq (iso X Y) (ringiso (X : commring) (Y : commring)).
  Proof.
    use weqpair.
    - exact (commring_iso_equiv X Y).
    - exact (commring_iso_equiv_is_equiv X Y).
  Defined.

  Lemma commring_equiv_iso_is_equiv (X Y : ob commring_precategory) : isweq (commring_equiv_iso X Y).
  Proof.
    use isweq_iso.
    - exact (commring_iso_equiv X Y).
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use eq_iso. use rigfun_paths. use idpath.
  Defined.
  Opaque commring_equiv_iso_is_equiv.

  Definition commring_equiv_weq_iso (X Y : ob commring_precategory) :
    (ringiso (X : commring) (Y : commring)) ≃ (iso X Y).
  Proof.
    use weqpair.
    - exact (commring_equiv_iso X Y).
    - exact (commring_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of commrings *)

  Definition commring_precategory_isweq (X Y : ob commring_precategory) :
    isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (iso X Y)
           (pr1weq (weqcomp (commring_univalence X Y) (commring_equiv_weq_iso X Y)))
           _ _ (weqproperty (weqcomp (commring_univalence X Y) (commring_equiv_weq_iso X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
  Defined.
  Opaque commring_precategory_isweq.

  Definition commring_precategory_is_univalent : is_univalent commring_precategory.
  Proof.
    use mk_is_univalent.
    - intros X Y. exact (commring_precategory_isweq X Y).
    - exact has_homsets_commring_precategory.
  Defined.

  Definition commring_category : univalent_category :=
    mk_category commring_precategory commring_precategory_is_univalent.

End def_commring_category.
