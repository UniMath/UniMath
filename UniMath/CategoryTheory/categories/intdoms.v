(** * Category of intdoms *)
(** ** Contents
- Precategory of intdoms
- Category of intdoms
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Domains_and_Fields.

Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.


(** * Precategory of intdoms *)
Section def_intdom_precategory.

  Definition intdom_fun_space (A B : intdom) : hSet := hSetpair (rngfun A B) (isasetrigfun A B).

  Definition intdom_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) intdom (λ A B : intdom, intdom_fun_space A B).

  Definition intdom_precategory_data : precategory_data :=
    precategory_data_pair
      intdom_precategory_ob_mor (λ (X : intdom), (rigisotorigfun (idrigiso X)))
      (fun (X Y Z : intdom) (f : rngfun X Y) (g : rngfun Y Z) => rigfuncomp f g).

  Local Lemma intdom_id_left (X Y : intdom) (f : rngfun X Y) :
    rigfuncomp (rigisotorigfun (idrigiso X)) f = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque intdom_id_left.

  Local Lemma intdom_id_right (X Y : intdom) (f : rngfun X Y) :
    rigfuncomp f (rigisotorigfun (idrigiso Y)) = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque intdom_id_right.

  Local Lemma intdom_assoc (X Y Z W : intdom) (f : rngfun X Y) (g : rngfun Y Z) (h : rngfun Z W) :
    rigfuncomp f (rigfuncomp g h) = rigfuncomp (rigfuncomp f g) h.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque intdom_assoc.

  Lemma is_precategory_intdom_precategory_data : is_precategory intdom_precategory_data.
  Proof.
    use mk_is_precategory.
    - intros a b f. use intdom_id_left.
    - intros a b f. use intdom_id_right.
    - intros a b c d f g h. use intdom_assoc.
  Qed.

  Definition intdom_precategory : precategory :=
    mk_precategory intdom_precategory_data is_precategory_intdom_precategory_data.

  Lemma has_homsets_intdom_precategory : has_homsets intdom_precategory.
  Proof.
    intros X Y. use isasetrigfun.
  Qed.

End def_intdom_precategory.


(** * Category of intdoms *)
Section def_intdom_category.

  (** ** (rigiso X Y) ≃ (iso X Y) *)

  Lemma intdom_iso_is_equiv (A B : ob intdom_precategory) (f : iso A B) : isweq (pr1 (pr1 f)).
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
  Opaque intdom_iso_is_equiv.

  Lemma intdom_iso_equiv (X Y : ob intdom_precategory) : iso X Y -> rngiso (X : intdom) (Y : intdom).
  Proof.
    intro f.
    use rngisopair.
    - exact (weqpair (pr1 (pr1 f)) (intdom_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma intdom_equiv_is_iso (X Y : ob intdom_precategory) (f : rngiso (X : intdom) (Y : intdom)) :
    @is_iso intdom_precategory X Y (rngfunconstr (pr2 f)).
  Proof.
    use is_iso_qinv.
    - exact (rngfunconstr (pr2 (invrigiso f))).
    - use mk_is_inverse_in_precat.
      + use rigfun_paths. use funextfun. intros x. use homotinvweqweq.
      + use rigfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque intdom_equiv_is_iso.

  Lemma intdom_equiv_iso (X Y : ob intdom_precategory) : rngiso (X : intdom) (Y : intdom) -> iso X Y.
  Proof.
    intros f. exact (@isopair intdom_precategory X Y (rngfunconstr (pr2 f))
                              (intdom_equiv_is_iso X Y f)).
  Defined.

  Lemma intdom_iso_equiv_is_equiv (X Y : intdom_precategory) : isweq (intdom_iso_equiv X Y).
  Proof.
    use gradth.
    - exact (intdom_equiv_iso X Y).
    - intros x. use eq_iso. use rigfun_paths. use idpath.
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque intdom_iso_equiv_is_equiv.

  Definition intdom_iso_equiv_weq (X Y : ob intdom_precategory) :
    weq (iso X Y) (rngiso (X : intdom) (Y : intdom)).
  Proof.
    use weqpair.
    - exact (intdom_iso_equiv X Y).
    - exact (intdom_iso_equiv_is_equiv X Y).
  Defined.

  Lemma intdom_equiv_iso_is_equiv (X Y : ob intdom_precategory) :
    isweq (intdom_equiv_iso X Y).
  Proof.
    use gradth.
    - exact (intdom_iso_equiv X Y).
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use eq_iso. use rigfun_paths. use idpath.
  Defined.
  Opaque intdom_equiv_iso_is_equiv.

  Definition intdom_equiv_iso_weq (X Y : ob intdom_precategory) :
    (rngiso (X : intdom) (Y : intdom)) ≃ (iso X Y).
  Proof.
    use weqpair.
    - exact (intdom_equiv_iso X Y).
    - exact (intdom_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of intdoms *)

  Definition intdom_precategory_isweq (X Y : ob intdom_precategory) :
    isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (iso X Y)
           (pr1weq (weqcomp (intdom_univalence X Y) (intdom_equiv_iso_weq X Y)))
           _ _ (weqproperty (weqcomp (intdom_univalence X Y) (intdom_equiv_iso_weq X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
  Defined.
  Opaque intdom_precategory_isweq.

  Definition intdom_precategory_is_univalent : is_univalent intdom_precategory.
  Proof.
    use mk_is_univalent.
    - intros X Y. exact (intdom_precategory_isweq X Y).
    - exact has_homsets_intdom_precategory.
  Defined.

  Definition intdom_category : univalent_category :=
    mk_category intdom_precategory intdom_precategory_is_univalent.

End def_intdom_category.
