(** * Rings category *)
(** ** Contents
- Precategory of rings
- Category of rings
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.RigsAndRings.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Local Open Scope cat.


(** * Precategory of rings *)
Section def_ring_precategory.

  Definition ring_fun_space (A B : ring) : hSet := hSetpair (ringfun A B) (isasetrigfun A B).

  Definition ring_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) ring (λ A B : ring, ring_fun_space A B).

  Definition ring_precategory_data : precategory_data :=
    precategory_data_pair
      ring_precategory_ob_mor (λ (X : ring), (rigisotorigfun (idrigiso X)))
      (fun (X Y Z : ring) (f : ringfun X Y) (g : ringfun Y Z) => rigfuncomp f g).

  Local Lemma ring_id_left (X Y : ring) (f : ringfun X Y) :
    rigfuncomp (rigisotorigfun (idrigiso X)) f = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque ring_id_left.

  Local Lemma ring_id_right (X Y : ring) (f : ringfun X Y) :
    rigfuncomp f (rigisotorigfun (idrigiso Y)) = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque ring_id_right.

  Local Lemma ring_assoc (X Y Z W : ring) (f : ringfun X Y) (g : ringfun Y Z) (h : ringfun Z W) :
    rigfuncomp f (rigfuncomp g h) = rigfuncomp (rigfuncomp f g) h.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque ring_assoc.

  Lemma is_precategory_ring_precategory_data : is_precategory ring_precategory_data.
  Proof.
    use mk_is_precategory_one_assoc.
    - intros a b f. use ring_id_left.
    - intros a b f. use ring_id_right.
    - intros a b c d f g h. use ring_assoc.
  Qed.

  Definition ring_precategory : precategory :=
    mk_precategory ring_precategory_data is_precategory_ring_precategory_data.

  Lemma has_homsets_ring_precategory : has_homsets ring_precategory.
  Proof.
    intros X Y. use isasetrigfun.
  Qed.

End def_ring_precategory.


(** * Category of rings *)
Section def_ring_category.

  (** ** (ringiso X Y) ≃ (iso X Y) *)

  Lemma ring_iso_is_equiv (A B : ob ring_precategory) (f : iso A B) : isweq (pr1 (pr1 f)).
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
  Opaque ring_iso_is_equiv.

  Lemma ring_iso_equiv (X Y : ob ring_precategory) : iso X Y -> ringiso (X : ring) (Y : ring).
  Proof.
    intro f.
    use ringisopair.
    - exact (weqpair (pr1 (pr1 f)) (ring_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma ring_equiv_is_iso (X Y : ob ring_precategory) (f : ringiso (X : ring) (Y : ring)) :
    @is_iso ring_precategory X Y (ringfunconstr (pr2 f)).
  Proof.
    use is_iso_qinv.
    - exact (ringfunconstr (pr2 (invrigiso f))).
    - use mk_is_inverse_in_precat.
      + use rigfun_paths. use funextfun. intros x. use homotinvweqweq.
      + use rigfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque ring_equiv_is_iso.

  Lemma ring_equiv_iso (X Y : ob ring_precategory) : ringiso (X : ring) (Y : ring) -> iso X Y.
  Proof.
    intros f. exact (@isopair ring_precategory X Y (ringfunconstr (pr2 f))
                              (ring_equiv_is_iso X Y f)).
  Defined.

  Lemma ring_iso_equiv_is_equiv (X Y : ring_precategory) : isweq (ring_iso_equiv X Y).
  Proof.
    use isweq_iso.
    - exact (ring_equiv_iso X Y).
    - intros x. use eq_iso. use rigfun_paths. use idpath.
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque ring_iso_equiv_is_equiv.

  Definition ring_iso_equiv_weq (X Y : ob ring_precategory) :
    weq (iso X Y) (ringiso (X : ring) (Y : ring)).
  Proof.
    use weqpair.
    - exact (ring_iso_equiv X Y).
    - exact (ring_iso_equiv_is_equiv X Y).
  Defined.

  Lemma ring_equiv_iso_is_equiv (X Y : ob ring_precategory) : isweq (ring_equiv_iso X Y).
  Proof.
    use isweq_iso.
    - exact (ring_iso_equiv X Y).
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use eq_iso. use rigfun_paths. use idpath.
  Defined.
  Opaque ring_equiv_iso_is_equiv.

  Definition ring_equiv_weq_iso (X Y : ob ring_precategory) :
    (ringiso (X : ring) (Y : ring)) ≃ (iso X Y).
  Proof.
    use weqpair.
    - exact (ring_equiv_iso X Y).
    - exact (ring_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of rings *)

  Definition ring_precategory_isweq (X Y : ob ring_precategory) : isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (iso X Y)
           (pr1weq (weqcomp (ring_univalence X Y) (ring_equiv_weq_iso X Y)))
           _ _ (weqproperty (weqcomp (ring_univalence X Y) (ring_equiv_weq_iso X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
  Defined.
  Opaque ring_precategory_isweq.

  Definition ring_precategory_is_univalent : is_univalent ring_precategory.
  Proof.
    use mk_is_univalent.
    - intros X Y. exact (ring_precategory_isweq X Y).
    - exact has_homsets_ring_precategory.
  Defined.

  Definition ring_category : univalent_category :=
    mk_category ring_precategory ring_precategory_is_univalent.

End def_ring_category.