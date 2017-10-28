(** * Category of commrigs *)
(** ** Contents
- Precategory of commrigs
- Category of commrigs
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


(** * Precategory of commrigs *)
Section def_commrig_precategory.

  Definition commrig_fun_space (A B : commrig) : hSet := hSetpair (rigfun A B) (isasetrigfun A B).

  Definition commrig_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) commrig (λ A B : commrig, commrig_fun_space A B).

  Definition commrig_precategory_data : precategory_data :=
    precategory_data_pair
      commrig_precategory_ob_mor (λ (X : commrig), (rigisotorigfun (idrigiso X)))
      (fun (X Y Z : commrig) (f : rigfun X Y) (g : rigfun Y Z) => rigfuncomp f g).

  Local Lemma commrig_id_left (X Y : commrig) (f : rigfun X Y) :
    rigfuncomp (rigisotorigfun (idrigiso X)) f = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque commrig_id_left.

  Local Lemma commrig_id_commright (X Y : commrig) (f : rigfun X Y) :
    rigfuncomp f (rigisotorigfun (idrigiso Y)) = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque commrig_id_commright.

  Local Lemma commrig_assoc (X Y Z W : commrig) (f : rigfun X Y) (g : rigfun Y Z) (h : rigfun Z W) :
    rigfuncomp f (rigfuncomp g h) = rigfuncomp (rigfuncomp f g) h.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque commrig_assoc.

  Lemma is_precategory_commrig_precategory_data : is_precategory commrig_precategory_data.
  Proof.
    use mk_is_precategory.
    - intros a b f. use commrig_id_left.
    - intros a b f. use commrig_id_commright.
    - intros a b c d f g h. use commrig_assoc.
  Qed.

  Definition commrig_precategory : precategory :=
    mk_precategory commrig_precategory_data is_precategory_commrig_precategory_data.

  Lemma has_homsets_commrig_precategory : has_homsets commrig_precategory.
  Proof.
    intros X Y. use isasetrigfun.
  Qed.

End def_commrig_precategory.


(** * Category of commrigs *)
Section def_commrig_category.

  (** ** (rigiso X Y) ≃ (iso X Y) *)

  Lemma commrig_iso_is_equiv (A B : ob commrig_precategory) (f : iso A B) : isweq (pr1 (pr1 f)).
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
  Opaque commrig_iso_is_equiv.

  Lemma commrig_iso_equiv (X Y : ob commrig_precategory) :
    iso X Y -> rigiso (X : commrig) (Y : commrig).
  Proof.
    intro f.
    use rigisopair.
    - exact (weqpair (pr1 (pr1 f)) (commrig_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma commrig_equiv_is_iso (X Y : ob commrig_precategory)
        (f : rigiso (X : commrig) (Y : commrig)) :
    @is_iso commrig_precategory X Y (rigfunconstr (pr2 f)).
  Proof.
    use is_iso_qinv.
    - exact (rigfunconstr (pr2 (invrigiso f))).
    - use mk_is_inverse_in_precat.
      + use rigfun_paths. use funextfun. intros x. use homotinvweqweq.
      + use rigfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque commrig_equiv_is_iso.

  Lemma commrig_equiv_iso (X Y : ob commrig_precategory) :
    rigiso (X : commrig) (Y : commrig) -> iso X Y.
  Proof.
    intros f. exact (@isopair commrig_precategory X Y (rigfunconstr (pr2 f))
                              (commrig_equiv_is_iso X Y f)).
  Defined.

  Lemma commrig_iso_equiv_is_equiv (X Y : commrig_precategory) : isweq (commrig_iso_equiv X Y).
  Proof.
    use gradth.
    - exact (commrig_equiv_iso X Y).
    - intros x. use eq_iso. use rigfun_paths. use idpath.
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque commrig_iso_equiv_is_equiv.

  Definition commrig_iso_equiv_weq (X Y : ob commrig_precategory) :
    weq (iso X Y) (rigiso (X : commrig) (Y : commrig)).
  Proof.
    use weqpair.
    - exact (commrig_iso_equiv X Y).
    - exact (commrig_iso_equiv_is_equiv X Y).
  Defined.

  Lemma commrig_equiv_iso_is_equiv (X Y : ob commrig_precategory) : isweq (commrig_equiv_iso X Y).
  Proof.
    use gradth.
    - exact (commrig_iso_equiv X Y).
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use eq_iso. use rigfun_paths. use idpath.
  Defined.
  Opaque commrig_equiv_iso_is_equiv.

  Definition commrig_equiv_iso_weq (X Y : ob commrig_precategory) :
    (rigiso (X : commrig) (Y : commrig)) ≃ (iso X Y).
  Proof.
    use weqpair.
    - exact (commrig_equiv_iso X Y).
    - exact (commrig_equiv_iso_is_equiv X Y).
  Defined.

  (** ** Category of commrigs *)

  Definition commrig_precategory_isweq (X Y : ob commrig_precategory) :
    isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (iso X Y)
           (pr1weq (weqcomp (commrig_univalence X Y) (commrig_equiv_iso_weq X Y)))
           _ _ (weqproperty (weqcomp (commrig_univalence X Y) (commrig_equiv_iso_weq X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
  Defined.
  Opaque commrig_precategory_isweq.

  Definition commrig_precategory_is_univalent : is_univalent commrig_precategory.
  Proof.
    use mk_is_univalent.
    - intros X Y. exact (commrig_precategory_isweq X Y).
    - exact has_homsets_commrig_precategory.
  Defined.

  Definition commrig_category : univalent_category :=
    mk_category commrig_precategory commrig_precategory_is_univalent.

End def_commrig_category.
