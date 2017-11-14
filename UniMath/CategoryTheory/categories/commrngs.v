(** * Category of commrngs *)
(** ** Contents
- Precategory of commrngs
- Category of commrngs
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.Rigs_and_Rings.

Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.


(** * Category of commrngs *)
Section def_commrng_precategory.

  Definition commrng_fun_space (A B : commrng) : hSet := hSetpair (rngfun A B) (isasetrigfun A B).

  Definition commrng_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) commrng (λ A B : commrng, commrng_fun_space A B).

  Definition commrng_precategory_data : precategory_data :=
    precategory_data_pair
      commrng_precategory_ob_mor (λ (X : commrng), (rigisotorigfun (idrigiso X)))
      (fun (X Y Z : commrng) (f : rngfun X Y) (g : rngfun Y Z) => rigfuncomp f g).

  Local Lemma commrng_id_left (X Y : commrng) (f : rngfun X Y) :
    rigfuncomp (rigisotorigfun (idrigiso X)) f = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque commrng_id_left.

  Local Lemma commrng_id_right (X Y : commrng) (f : rngfun X Y) :
    rigfuncomp f (rigisotorigfun (idrigiso Y)) = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque commrng_id_right.

  Local Lemma commrng_assoc (X Y Z W : commrng) (f : rngfun X Y) (g : rngfun Y Z)
        (h : rngfun Z W) : rigfuncomp f (rigfuncomp g h) = rigfuncomp (rigfuncomp f g) h.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque commrng_assoc.

  Lemma is_precategory_commrng_precategory_data : is_precategory commrng_precategory_data.
  Proof.
    use mk_is_precategory.
    - intros a b f. use commrng_id_left.
    - intros a b f. use commrng_id_right.
    - intros a b c d f g h. use commrng_assoc.
  Qed.

  Definition commrng_precategory : precategory :=
    mk_precategory commrng_precategory_data is_precategory_commrng_precategory_data.

  Lemma has_homsets_commrng_precategory : has_homsets commrng_precategory.
  Proof.
    intros X Y. use isasetrigfun.
  Qed.

End def_commrng_precategory.


(** * Category of commrngs *)
Section def_commrng_category.

  (** ** (rngiso X Y) ≃ (iso X Y) *)

  Lemma commrng_iso_is_equiv (A B : ob commrng_precategory) (f : iso A B) : isweq (pr1 (pr1 f)).
  Proof.
    use gradth.
    - exact (pr1rigfun _ _ (inv_from_iso f)).
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (iso_inv_after_iso f)) x).
      intros x0. use isapropisrigfun.
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (iso_after_iso_inv f)) x).
      intros x0. use isapropisrigfun.
  Defined.
  Opaque commrng_iso_is_equiv.

  Lemma commrng_iso_equiv (X Y : ob commrng_precategory) :
    iso X Y -> rngiso (X : commrng) (Y : commrng).
  Proof.
    intro f.
    use rngisopair.
    - exact (weqpair (pr1 (pr1 f)) (commrng_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma commrng_equiv_is_iso (X Y : ob commrng_precategory)
        (f : rngiso (X : commrng) (Y : commrng)) :
    @is_iso commrng_precategory X Y (rngfunconstr (pr2 f)).
  Proof.
    use is_iso_qinv.
    - exact (rngfunconstr (pr2 (invrigiso f))).
    - use mk_is_inverse_in_precat.
      + use rigfun_paths. use funextfun. intros x. use homotinvweqweq.
      + use rigfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque commrng_equiv_is_iso.

  Lemma commrng_equiv_iso (X Y : ob commrng_precategory) :
    rngiso (X : commrng) (Y : commrng) -> iso X Y.
  Proof.
    intros f. exact (@isopair commrng_precategory X Y (rngfunconstr (pr2 f))
                              (commrng_equiv_is_iso X Y f)).
  Defined.

  Lemma commrng_iso_equiv_is_equiv (X Y : commrng_precategory) : isweq (commrng_iso_equiv X Y).
  Proof.
    use gradth.
    - exact (commrng_equiv_iso X Y).
    - intros x. use eq_iso. use rigfun_paths. use idpath.
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque commrng_iso_equiv_is_equiv.

  Definition commrng_iso_equiv_weq (X Y : ob commrng_precategory) :
    weq (iso X Y) (rngiso (X : commrng) (Y : commrng)).
  Proof.
    use weqpair.
    - exact (commrng_iso_equiv X Y).
    - exact (commrng_iso_equiv_is_equiv X Y).
  Defined.

  Lemma commrng_equiv_iso_is_equiv (X Y : ob commrng_precategory) : isweq (commrng_equiv_iso X Y).
  Proof.
    use gradth.
    - exact (commrng_iso_equiv X Y).
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use eq_iso. use rigfun_paths. use idpath.
  Defined.
  Opaque commrng_equiv_iso_is_equiv.

  Definition commrng_equiv_iso_weq (X Y : ob commrng_precategory) :
    (rngiso (X : commrng) (Y : commrng)) ≃ (iso X Y).
  Proof.
    use weqpair.
    - exact (commrng_equiv_iso X Y).
    - exact (commrng_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of commrngs *)

  Definition commrng_precategory_isweq (X Y : ob commrng_precategory) :
    isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (iso X Y)
           (pr1weq (weqcomp (commrng_univalence X Y) (commrng_equiv_iso_weq X Y)))
           _ _ (weqproperty (weqcomp (commrng_univalence X Y) (commrng_equiv_iso_weq X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
  Defined.
  Opaque commrng_precategory_isweq.

  Definition commrng_precategory_is_univalent : is_univalent commrng_precategory.
  Proof.
    use mk_is_univalent.
    - intros X Y. exact (commrng_precategory_isweq X Y).
    - exact has_homsets_commrng_precategory.
  Defined.

  Definition commrng_category : univalent_category :=
    mk_category commrng_precategory commrng_precategory_is_univalent.

End def_commrng_category.
