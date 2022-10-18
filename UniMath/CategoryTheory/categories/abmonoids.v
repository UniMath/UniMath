(** * Category of abmonoids *)
(** ** Contents
- Precategory of abmonoids
- Category of abmonoids
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Local Open Scope cat.


(** * Precategory of abmonoids *)
Section def_abmonoid_precategory.

  Definition abmonoid_fun_space (A B : abmonoid) : hSet :=
    make_hSet (monoidfun A B) (isasetmonoidfun A B).

  Definition abmonoid_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) abmonoid (λ A B : abmonoid, abmonoid_fun_space A B).

  Definition abmonoid_precategory_data : precategory_data :=
    make_precategory_data
      abmonoid_precategory_ob_mor (λ (X : abmonoid), ((idmonoidiso X) : monoidfun X X))
      (fun (X Y Z : abmonoid) (f : monoidfun X Y) (g : monoidfun Y Z) => monoidfuncomp f g).

  Local Lemma abmonoid_id_left (X Y : abmonoid) (f : monoidfun X Y) :
    monoidfuncomp (idmonoidiso X) f = f.
  Proof.
    use monoidfun_paths. use idpath.
  Defined.
  Opaque abmonoid_id_left.

  Local Lemma abmonoid_id_right (X Y : abmonoid) (f : monoidfun X Y) :
    monoidfuncomp f (idmonoidiso Y) = f.
  Proof.
    use monoidfun_paths. use idpath.
  Defined.
  Opaque abmonoid_id_right.

  Local Lemma abmonoid_assoc (X Y Z W : abmonoid) (f : monoidfun X Y)
             (g : monoidfun Y Z) (h : monoidfun Z W) :
    monoidfuncomp f (monoidfuncomp g h) = monoidfuncomp (monoidfuncomp f g) h.
  Proof.
    use monoidfun_paths. use idpath.
  Defined.
  Opaque abmonoid_assoc.

  Lemma is_precategory_abmonoid_precategory_data : is_precategory abmonoid_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros a b f. use abmonoid_id_left.
    - intros a b f. use abmonoid_id_right.
    - intros a b c d f g h. use abmonoid_assoc.
  Qed.

  Definition abmonoid_precategory : precategory :=
    make_precategory abmonoid_precategory_data is_precategory_abmonoid_precategory_data.

  Lemma has_homsets_abmonoid_precategory : has_homsets abmonoid_precategory.
  Proof.
    intros X Y. use isasetmonoidfun.
  Qed.

End def_abmonoid_precategory.


(** * Category of abmonoids *)
Section def_abmonoid_category.

  Definition abmonoid_category : category := make_category _ has_homsets_abmonoid_precategory.

  (** ** (monoidsiso X Y) ≃ (iso X Y) *)

  Lemma abmonoid_iso_is_equiv (A B : ob abmonoid_category) (f : z_iso A B) : isweq (pr1 (pr1 f)).
  Proof.
    use isweq_iso.
    - exact (pr1monoidfun _ _ (inv_from_z_iso f)).
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (z_iso_inv_after_z_iso f)) x).
      intros x0. use isapropismonoidfun.
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (z_iso_after_z_iso_inv f)) x).
      intros x0. use isapropismonoidfun.
  Defined.
  Opaque abmonoid_iso_is_equiv.

  Lemma abmonoid_iso_equiv (X Y : ob abmonoid_category) :
    z_iso X Y -> monoidiso (X : abmonoid) (Y : abmonoid).
  Proof.
    intro f.
    use make_monoidiso.
    - exact (make_weq (pr1 (pr1 f)) (abmonoid_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma abmonoid_equiv_is_z_iso (X Y : ob abmonoid_category)
        (f : monoidiso (X : abmonoid) (Y : abmonoid)) :
    @is_z_isomorphism abmonoid_category X Y (monoidfunconstr (pr2 f)).
  Proof.
    exists (monoidfunconstr (pr2 (invmonoidiso f))).
    use make_is_inverse_in_precat.
    - use monoidfun_paths. use funextfun. intros x. use homotinvweqweq.
    - use monoidfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque abmonoid_equiv_is_z_iso.

  Lemma abmonoid_equiv_z_iso (X Y : ob abmonoid_category) :
    monoidiso (X : abmonoid) (Y : abmonoid) -> z_iso X Y.
  Proof.
    intros f.
    exists (monoidfunconstr (pr2 f)).
    exact (abmonoid_equiv_is_z_iso X Y f).
  Defined.

  Lemma abmonoid_iso_equiv_is_equiv (X Y : ob abmonoid_category) :
    isweq (abmonoid_iso_equiv X Y).
  Proof.
    use isweq_iso.
    - exact (abmonoid_equiv_z_iso X Y).
    - intros x. use z_iso_eq. use monoidfun_paths. use idpath.
    - intros y. use monoidiso_paths. use subtypePath.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque abmonoid_iso_equiv_is_equiv.

  Definition abmonoid_iso_equiv_weq (X Y : ob abmonoid_category) :
    weq (z_iso X Y) (monoidiso (X : abmonoid) (Y : abmonoid)).
  Proof.
    use make_weq.
    - exact (abmonoid_iso_equiv X Y).
    - exact (abmonoid_iso_equiv_is_equiv X Y).
  Defined.

  Lemma abmonoid_equiv_iso_is_equiv (X Y : ob abmonoid_category) :
    isweq (abmonoid_equiv_z_iso X Y).
  Proof.
    use isweq_iso.
    - exact (abmonoid_iso_equiv X Y).
    - intros y. use monoidiso_paths. use subtypePath.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use z_iso_eq. use monoidfun_paths. use idpath.
  Defined.
  Opaque abmonoid_equiv_iso_is_equiv.

  Definition abmonoid_equiv_weq_iso (X Y : ob abmonoid_category) :
    (monoidiso (X : abmonoid) (Y : abmonoid)) ≃ (z_iso X Y).
  Proof.
    use make_weq.
    - exact (abmonoid_equiv_z_iso X Y).
    - exact (abmonoid_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of abmonoids *)

  Definition abmonoid_category_isweq (X Y : ob abmonoid_category) :
    isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (z_iso X Y)
           (pr1weq (weqcomp (abmonoid_univalence X Y) (abmonoid_equiv_weq_iso X Y)))
           _ _ (weqproperty (weqcomp (abmonoid_univalence X Y) (abmonoid_equiv_weq_iso X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_z_isomorphism.
  Defined.
  Opaque abmonoid_category_isweq.



  Definition abmonoid_category_is_univalent : is_univalent abmonoid_category.
  Proof.
    intros X Y. exact (abmonoid_category_isweq X Y).
  Defined.

  Definition abmonoid_univalent_category : univalent_category :=
    make_univalent_category abmonoid_category abmonoid_category_is_univalent.

End def_abmonoid_category.
