(** * Rngs category *)
(** ** Contents
- Precategory of rngs
- Category of rngs
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


(** * Precategory of rngs *)
Section def_rng_precategory.

  Definition rng_fun_space (A B : rng) : hSet := hSetpair (rngfun A B) (isasetrigfun A B).

  Definition rng_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) rng (λ A B : rng, rng_fun_space A B).

  Definition rng_precategory_data : precategory_data :=
    precategory_data_pair
      rng_precategory_ob_mor (λ (X : rng), (rigisotorigfun (idrigiso X)))
      (fun (X Y Z : rng) (f : rngfun X Y) (g : rngfun Y Z) => rigfuncomp f g).

  Local Lemma rng_id_left (X Y : rng) (f : rngfun X Y) :
    rigfuncomp (rigisotorigfun (idrigiso X)) f = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque rng_id_left.

  Local Lemma rng_id_right (X Y : rng) (f : rngfun X Y) :
    rigfuncomp f (rigisotorigfun (idrigiso Y)) = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque rng_id_right.

  Local Lemma rng_assoc (X Y Z W : rng) (f : rngfun X Y) (g : rngfun Y Z) (h : rngfun Z W) :
    rigfuncomp f (rigfuncomp g h) = rigfuncomp (rigfuncomp f g) h.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque rng_assoc.

  Lemma is_precategory_rng_precategory_data : is_precategory rng_precategory_data.
  Proof.
    use mk_is_precategory.
    - intros a b f. use rng_id_left.
    - intros a b f. use rng_id_right.
    - intros a b c d f g h. use rng_assoc.
  Qed.

  Definition rng_precategory : precategory :=
    mk_precategory rng_precategory_data is_precategory_rng_precategory_data.

  Lemma has_homsets_rng_precategory : has_homsets rng_precategory.
  Proof.
    intros X Y. use isasetrigfun.
  Qed.

End def_rng_precategory.


(** * Category of rngs *)
Section def_rng_category.

  (** ** (rngiso X Y) ≃ (iso X Y) *)

  Lemma rng_iso_is_equiv (A B : ob rng_precategory) (f : iso A B) : isweq (pr1 (pr1 f)).
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
  Opaque rng_iso_is_equiv.

  Lemma rng_iso_equiv (X Y : ob rng_precategory) : iso X Y -> rngiso (X : rng) (Y : rng).
  Proof.
    intro f.
    use rngisopair.
    - exact (weqpair (pr1 (pr1 f)) (rng_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma rng_equiv_is_iso (X Y : ob rng_precategory) (f : rngiso (X : rng) (Y : rng)) :
    @is_iso rng_precategory X Y (rngfunconstr (pr2 f)).
  Proof.
    use is_iso_qinv.
    - exact (rngfunconstr (pr2 (invrigiso f))).
    - use mk_is_inverse_in_precat.
      + use rigfun_paths. use funextfun. intros x. use homotinvweqweq.
      + use rigfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque rng_equiv_is_iso.

  Lemma rng_equiv_iso (X Y : ob rng_precategory) : rngiso (X : rng) (Y : rng) -> iso X Y.
  Proof.
    intros f. exact (@isopair rng_precategory X Y (rngfunconstr (pr2 f))
                              (rng_equiv_is_iso X Y f)).
  Defined.

  Lemma rng_iso_equiv_is_equiv (X Y : rng_precategory) : isweq (rng_iso_equiv X Y).
  Proof.
    use gradth.
    - exact (rng_equiv_iso X Y).
    - intros x. use eq_iso. use rigfun_paths. use idpath.
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque rng_iso_equiv_is_equiv.

  Definition rng_iso_equiv_weq (X Y : ob rng_precategory) :
    weq (iso X Y) (rngiso (X : rng) (Y : rng)).
  Proof.
    use weqpair.
    - exact (rng_iso_equiv X Y).
    - exact (rng_iso_equiv_is_equiv X Y).
  Defined.

  Lemma rng_equiv_iso_is_equiv (X Y : ob rng_precategory) : isweq (rng_equiv_iso X Y).
  Proof.
    use gradth.
    - exact (rng_iso_equiv X Y).
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use eq_iso. use rigfun_paths. use idpath.
  Defined.
  Opaque rng_equiv_iso_is_equiv.

  Definition rng_equiv_iso_weq (X Y : ob rng_precategory) :
    (rngiso (X : rng) (Y : rng)) ≃ (iso X Y).
  Proof.
    use weqpair.
    - exact (rng_equiv_iso X Y).
    - exact (rng_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of rngs *)

  Definition rng_precategory_isweq (X Y : ob rng_precategory) : isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (iso X Y)
           (pr1weq (weqcomp (rng_univalence X Y) (rng_equiv_iso_weq X Y)))
           _ _ (weqproperty (weqcomp (rng_univalence X Y) (rng_equiv_iso_weq X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
  Defined.
  Opaque rng_precategory_isweq.

  Definition rng_precategory_is_univalent : is_univalent rng_precategory.
  Proof.
    use mk_is_univalent.
    - intros X Y. exact (rng_precategory_isweq X Y).
    - exact has_homsets_rng_precategory.
  Defined.

  Definition rng_category : univalent_category :=
    mk_category rng_precategory rng_precategory_is_univalent.

End def_rng_category.
