(** * Category of flds *)
(** ** Contents
- Precategory of flds
- Category of flds
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

(** * Precategory of flds *)
Section def_fld_precategory.

  Definition fld_fun_space (A B : fld) : hSet := hSetpair (rngfun A B) (isasetrigfun A B).

  Definition fld_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) fld (λ A B : fld, fld_fun_space A B).

  Definition fld_precategory_data : precategory_data :=
    precategory_data_pair
      fld_precategory_ob_mor (λ (X : fld), (rigisotorigfun (idrigiso X)))
      (fun (X Y Z : fld) (f : rngfun X Y) (g : rngfun Y Z) => rigfuncomp f g).

  Local Lemma fld_id_left (X Y : fld) (f : rngfun X Y) :
    rigfuncomp (rigisotorigfun (idrigiso X)) f = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque fld_id_left.

  Local Lemma fld_id_right (X Y : fld) (f : rngfun X Y) :
    rigfuncomp f (rigisotorigfun (idrigiso Y)) = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque fld_id_right.

  Local Lemma fld_assoc (X Y Z W : fld) (f : rngfun X Y) (g : rngfun Y Z) (h : rngfun Z W) :
    rigfuncomp f (rigfuncomp g h) = rigfuncomp (rigfuncomp f g) h.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque fld_assoc.

  Lemma is_precategory_fld_precategory_data : is_precategory fld_precategory_data.
  Proof.
    use mk_is_precategory.
    - intros a b f. use fld_id_left.
    - intros a b f. use fld_id_right.
    - intros a b c d f g h. use fld_assoc.
  Qed.

  Definition fld_precategory : precategory :=
    mk_precategory fld_precategory_data is_precategory_fld_precategory_data.

  Lemma has_homsets_fld_precategory : has_homsets fld_precategory.
  Proof.
    intros X Y. use isasetrigfun.
  Qed.

End def_fld_precategory.


(** * Category of flds *)
Section def_fld_category.

  (** ** (rigiso X Y) ≃ (iso X Y) *)

  Lemma fld_iso_is_equiv (A B : ob fld_precategory) (f : iso A B) : isweq (pr1 (pr1 f)).
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
  Opaque fld_iso_is_equiv.

  Lemma fld_iso_equiv (X Y : ob fld_precategory) : iso X Y -> rngiso (X : fld) (Y : fld).
  Proof.
    intro f.
    use rngisopair.
    - exact (weqpair (pr1 (pr1 f)) (fld_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma fld_equiv_is_iso (X Y : ob fld_precategory) (f : rngiso (X : fld) (Y : fld)) :
    @is_iso fld_precategory X Y (rngfunconstr (pr2 f)).
  Proof.
    use is_iso_qinv.
    - exact (rngfunconstr (pr2 (invrigiso f))).
    - use mk_is_inverse_in_precat.
      + use rigfun_paths. use funextfun. intros x. use homotinvweqweq.
      + use rigfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque fld_equiv_is_iso.

  Lemma fld_equiv_iso (X Y : ob fld_precategory) : rngiso (X : fld) (Y : fld) -> iso X Y.
  Proof.
    intros f. exact (@isopair fld_precategory X Y (rngfunconstr (pr2 f))
                              (fld_equiv_is_iso X Y f)).
  Defined.

  Lemma fld_iso_equiv_is_equiv (X Y : fld_precategory) : isweq (fld_iso_equiv X Y).
  Proof.
    use gradth.
    - exact (fld_equiv_iso X Y).
    - intros x. use eq_iso. use rigfun_paths. use idpath.
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque fld_iso_equiv_is_equiv.

  Definition fld_iso_equiv_weq (X Y : ob fld_precategory) :
    weq (iso X Y) (rngiso (X : fld) (Y : fld)).
  Proof.
    use weqpair.
    - exact (fld_iso_equiv X Y).
    - exact (fld_iso_equiv_is_equiv X Y).
  Defined.

  Lemma fld_equiv_iso_is_equiv (X Y : ob fld_precategory) : isweq (fld_equiv_iso X Y).
  Proof.
    use gradth.
    - exact (fld_iso_equiv X Y).
    - intros y. use rigiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use eq_iso. use rigfun_paths. use idpath.
  Defined.
  Opaque fld_equiv_iso_is_equiv.

  Definition fld_equiv_iso_weq (X Y : ob fld_precategory) :
    (rngiso (X : fld) (Y : fld)) ≃ (iso X Y).
  Proof.
    use weqpair.
    - exact (fld_equiv_iso X Y).
    - exact (fld_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of flds *)

  Definition fld_precategory_isweq (X Y : ob fld_precategory) : isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (iso X Y)
           (pr1weq (weqcomp (fld_univalence X Y) (fld_equiv_iso_weq X Y)))
           _ _ (weqproperty (weqcomp (fld_univalence X Y) (fld_equiv_iso_weq X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
  Defined.
  Opaque fld_precategory_isweq.

  Definition fld_precategory_is_univalent : is_univalent fld_precategory.
  Proof.
    use mk_is_univalent.
    - intros X Y. exact (fld_precategory_isweq X Y).
    - exact has_homsets_fld_precategory.
  Defined.

  Definition fld_category : univalent_category := mk_category fld_precategory fld_precategory_is_univalent.

End def_fld_category.
