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
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Domains_and_Fields.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Local Open Scope cat.

(** * Precategory of flds *)
Section def_fld_precategory.

  Definition fld_fun_space (A B : fld) : hSet := make_hSet (ringfun A B) (isasetrigfun A B).

  Definition fld_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) fld (λ A B : fld, fld_fun_space A B).

  Definition fld_precategory_data : precategory_data :=
    make_precategory_data
      fld_precategory_ob_mor (λ (X : fld), (rigisotorigfun (idrigiso X)))
      (fun (X Y Z : fld) (f : ringfun X Y) (g : ringfun Y Z) => rigfuncomp f g).

  Local Lemma fld_id_left (X Y : fld) (f : ringfun X Y) :
    rigfuncomp (rigisotorigfun (idrigiso X)) f = f.
  Proof.
    use rigfun_paths. apply idpath.
  Defined.
  Opaque fld_id_left.

  Local Lemma fld_id_right (X Y : fld) (f : ringfun X Y) :
    rigfuncomp f (rigisotorigfun (idrigiso Y)) = f.
  Proof.
    use rigfun_paths. apply idpath.
  Defined.
  Opaque fld_id_right.

  Local Lemma fld_assoc (X Y Z W : fld) (f : ringfun X Y) (g : ringfun Y Z) (h : ringfun Z W) :
    rigfuncomp f (rigfuncomp g h) = rigfuncomp (rigfuncomp f g) h.
  Proof.
    use rigfun_paths. apply idpath.
  Defined.
  Opaque fld_assoc.

  Lemma is_precategory_fld_precategory_data : is_precategory fld_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros a b f. use fld_id_left.
    - intros a b f. use fld_id_right.
    - intros a b c d f g h. use fld_assoc.
  Qed.

  Definition fld_precategory : precategory :=
    make_precategory fld_precategory_data is_precategory_fld_precategory_data.

  Lemma has_homsets_fld_precategory : has_homsets fld_precategory.
  Proof.
    intros X Y. use isasetrigfun.
  Qed.

End def_fld_precategory.


(** * Category of flds *)
Section def_fld_category.

  Definition fld_category : category := make_category _ has_homsets_fld_precategory.

  (** ** (rigiso X Y) ≃ (z_iso X Y) *)

  Lemma fld_iso_is_equiv (A B : ob fld_category) (f : z_iso A B) : isweq (pr1 (pr1 f)).
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
  Opaque fld_iso_is_equiv.

  Lemma fld_iso_equiv (X Y : ob fld_category) : z_iso X Y -> ringiso (X : fld) (Y : fld).
  Proof.
    intro f.
    use make_ringiso.
    - exact (make_weq (pr1 (pr1 f)) (fld_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma fld_equiv_is_z_iso (X Y : ob fld_category) (f : ringiso (X : fld) (Y : fld)) :
    @is_z_isomorphism fld_category X Y (ringfunconstr (pr2 f)).
  Proof.
    exists (ringfunconstr (pr2 (invrigiso f))).
    use make_is_inverse_in_precat.
    - use rigfun_paths. use funextfun. intros x. use homotinvweqweq.
    - use rigfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque fld_equiv_is_z_iso.

  Lemma fld_equiv_iso (X Y : ob fld_category) : ringiso (X : fld) (Y : fld) -> z_iso X Y.
  Proof.
    intros f. exact (_,,fld_equiv_is_z_iso X Y f).
  Defined.

  Lemma fld_iso_equiv_is_equiv (X Y : fld_category) : isweq (fld_iso_equiv X Y).
  Proof.
    use isweq_iso.
    - exact (fld_equiv_iso X Y).
    - intros x. use eq_z_iso. use rigfun_paths. apply idpath.
    - intros y. use rigiso_paths. use subtypePath.
      + intros x0. use isapropisweq.
      + apply idpath.
  Defined.
  Opaque fld_iso_equiv_is_equiv.

  Definition fld_iso_equiv_weq (X Y : ob fld_category) :
    weq (z_iso X Y) (ringiso (X : fld) (Y : fld)).
  Proof.
    use make_weq.
    - exact (fld_iso_equiv X Y).
    - exact (fld_iso_equiv_is_equiv X Y).
  Defined.

  Lemma fld_equiv_iso_is_equiv (X Y : ob fld_category) : isweq (fld_equiv_iso X Y).
  Proof.
    use isweq_iso.
    - exact (fld_iso_equiv X Y).
    - intros y. use rigiso_paths. use subtypePath.
      + intros x0. use isapropisweq.
      + apply idpath.
    - intros x. use eq_z_iso. use rigfun_paths. apply idpath.
  Defined.
  Opaque fld_equiv_iso_is_equiv.

  Definition fld_equiv_weq_iso (X Y : ob fld_category) :
    (ringiso (X : fld) (Y : fld)) ≃ (z_iso X Y).
  Proof.
    use make_weq.
    - exact (fld_equiv_iso X Y).
    - exact (fld_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of flds *)

  Definition fld_category_isweq (X Y : ob fld_category) : isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (z_iso X Y)
           (pr1weq (weqcomp (fld_univalence X Y) (fld_equiv_weq_iso X Y)))
           _ _ (weqproperty (weqcomp (fld_univalence X Y) (fld_equiv_weq_iso X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - apply idpath.
    - use proofirrelevance. use isaprop_is_z_isomorphism.
  Defined.
  Opaque fld_category_isweq.


  Definition fld_category_is_univalent : is_univalent fld_category.
  Proof.
    intros X Y. exact (fld_category_isweq X Y).
  Defined.

  Definition fld_univalent_category : univalent_category
    := make_univalent_category fld_category fld_category_is_univalent.

End def_fld_category.
