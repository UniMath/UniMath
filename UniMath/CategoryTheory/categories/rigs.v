(** * Rigs category *)
(** ** Contents
- Precategory of rigs
- Category of rigs
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


(** * Precategory of rigs *)
Section def_rig_precategory.

  Definition rig_fun_space (A B : rig) : hSet := make_hSet (rigfun A B) (isasetrigfun A B).

  Definition rig_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) rig (λ A B : rig, rig_fun_space A B).

  Definition rig_precategory_data : precategory_data :=
    make_precategory_data
      rig_precategory_ob_mor (λ (X : rig), (rigisotorigfun (idrigiso X)))
      (fun (X Y Z : rig) (f : rigfun X Y) (g : rigfun Y Z) => rigfuncomp f g).

  Local Definition rig_id_left (X Y : rig) (f : rigfun X Y) :
    rigfuncomp (rigisotorigfun (idrigiso X)) f = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque rig_id_left.

  Local Definition rig_id_right (X Y : rig) (f : rigfun X Y) :
    rigfuncomp f (rigisotorigfun (idrigiso Y)) = f.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque rig_id_right.

  Local Definition rig_assoc (X Y Z W : rig) (f : rigfun X Y) (g : rigfun Y Z) (h : rigfun Z W) :
    rigfuncomp f (rigfuncomp g h) = rigfuncomp (rigfuncomp f g) h.
  Proof.
    use rigfun_paths. use idpath.
  Defined.
  Opaque rig_assoc.

  Lemma is_precategory_rig_precategory_data : is_precategory rig_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros a b f. use rig_id_left.
    - intros a b f. use rig_id_right.
    - intros a b c d f g h. use rig_assoc.
  Qed.

  Definition rig_precategory : precategory :=
    make_precategory rig_precategory_data is_precategory_rig_precategory_data.

  Lemma has_homsets_rig_precategory : has_homsets rig_precategory.
  Proof.
    intros X Y. use isasetrigfun.
  Qed.

End def_rig_precategory.


(** * Category of rigs *)
Section def_rig_category.

  Definition rig_category : category := make_category _ has_homsets_rig_precategory.

  (** ** (rigiso X Y) ≃ (iso X Y) *)

  Lemma rig_iso_is_equiv (A B : ob rig_category) (f : z_iso A B) : isweq (pr1 (pr1 f)).
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
  Opaque rig_iso_is_equiv.

  Lemma rig_iso_equiv (X Y : ob rig_category) : z_iso X Y -> rigiso (X : rig) (Y : rig).
  Proof.
    intro f.
    use make_rigiso.
    - exact (make_weq (pr1 (pr1 f)) (rig_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma rig_equiv_is_z_iso (X Y : ob rig_category) (f : rigiso (X : rig) (Y : rig)) :
    @is_z_isomorphism rig_precategory X Y (rigfunconstr (pr2 f)).
  Proof.
    exists (rigfunconstr (pr2 (invrigiso f))).
    use make_is_inverse_in_precat.
    - use rigfun_paths. use funextfun. intros x. use homotinvweqweq.
    - use rigfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque rig_equiv_is_z_iso.

  Lemma rig_equiv_z_iso (X Y : ob rig_category) : rigiso (X : rig) (Y : rig) -> z_iso X Y.
  Proof.
    intros f.
    exists (rigfunconstr (pr2 f)).
    exact (rig_equiv_is_z_iso X Y f).
  Defined.

  Lemma rig_iso_equiv_is_equiv (X Y : rig_category) : isweq (rig_iso_equiv X Y).
  Proof.
    use isweq_iso.
    - exact (rig_equiv_z_iso X Y).
    - intros x. use z_iso_eq. use rigfun_paths. use idpath.
    - intros y. use rigiso_paths. use subtypePath.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque rig_iso_equiv_is_equiv.

  Definition rig_iso_equiv_weq (X Y : ob rig_category) :
    weq (z_iso X Y) (rigiso (X : rig) (Y : rig)).
  Proof.
    use make_weq.
    - exact (rig_iso_equiv X Y).
    - exact (rig_iso_equiv_is_equiv X Y).
  Defined.

  Lemma rig_equiv_iso_is_equiv (X Y : ob rig_category) : isweq (rig_equiv_z_iso X Y).
  Proof.
    use isweq_iso.
    - exact (rig_iso_equiv X Y).
    - intros y. use rigiso_paths. use subtypePath.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use z_iso_eq. use rigfun_paths. use idpath.
  Defined.
  Opaque rig_equiv_iso_is_equiv.

  Definition rig_equiv_weq_iso (X Y : ob rig_category) :
    (rigiso (X : rig) (Y : rig)) ≃ (z_iso X Y).
  Proof.
    use make_weq.
    - exact (rig_equiv_z_iso X Y).
    - exact (rig_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of rigs *)

  Definition rig_category_isweq (X Y : ob rig_category) : isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (z_iso X Y)
           (pr1weq (weqcomp (rig_univalence X Y) (rig_equiv_weq_iso X Y)))
           _ _ (weqproperty (weqcomp (rig_univalence X Y)
                                     (rig_equiv_weq_iso X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_z_isomorphism.
  Defined.
  Opaque rig_category_isweq.


  Definition rig_category_is_univalent : is_univalent rig_category.
  Proof.
    intros X Y. exact (rig_category_isweq X Y).
  Defined.

  Definition rig_univalent_category : univalent_category :=
    make_univalent_category rig_category rig_category_is_univalent.

End def_rig_category.
