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
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.


(** * Precategory of abmonoids *)
Section def_abmonoid_precategory.

  Definition abmonoid_fun_space (A B : abmonoid) : hSet :=
    hSetpair (monoidfun A B) (isasetmonoidfun A B).

  Definition abmonoid_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) abmonoid (λ A B : abmonoid, abmonoid_fun_space A B).

  Definition abmonoid_precategory_data : precategory_data :=
    precategory_data_pair
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
    use mk_is_precategory.
    - intros a b f. use abmonoid_id_left.
    - intros a b f. use abmonoid_id_right.
    - intros a b c d f g h. use abmonoid_assoc.
  Qed.

  Definition abmonoid_precategory : precategory :=
    mk_precategory abmonoid_precategory_data is_precategory_abmonoid_precategory_data.

  Lemma has_homsets_abmonoid_precategory : has_homsets abmonoid_precategory.
  Proof.
    intros X Y. use isasetmonoidfun.
  Qed.

End def_abmonoid_precategory.


(** * Category of abmonoids *)
Section def_abmonoid_category.

  (** ** (monoidsiso X Y) ≃ (iso X Y) *)

  Lemma abmonoid_iso_is_equiv (A B : ob abmonoid_precategory) (f : iso A B) : isweq (pr1 (pr1 f)).
  Proof.
    use gradth.
    - exact (pr1monoidfun _ _ (inv_from_iso f)).
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (iso_inv_after_iso f)) x).
      intros x0. use isapropismonoidfun.
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (iso_after_iso_inv f)) x).
      intros x0. use isapropismonoidfun.
  Defined.
  Opaque abmonoid_iso_is_equiv.

  Lemma abmonoid_iso_equiv (X Y : ob abmonoid_precategory) :
    iso X Y -> monoidiso (X : abmonoid) (Y : abmonoid).
  Proof.
    intro f.
    use monoidisopair.
    - exact (weqpair (pr1 (pr1 f)) (abmonoid_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma abmonoid_equiv_is_iso (X Y : ob abmonoid_precategory)
        (f : monoidiso (X : abmonoid) (Y : abmonoid)) :
    @is_iso abmonoid_precategory X Y (monoidfunconstr (pr2 f)).
  Proof.
    use is_iso_qinv.
    - exact (monoidfunconstr (pr2 (invmonoidiso f))).
    - use mk_is_inverse_in_precat.
      + use monoidfun_paths. use funextfun. intros x. use homotinvweqweq.
      + use monoidfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque abmonoid_equiv_is_iso.

  Lemma abmonoid_equiv_iso (X Y : ob abmonoid_precategory) :
    monoidiso (X : abmonoid) (Y : abmonoid) -> iso X Y.
  Proof.
    intros f. exact (@isopair abmonoid_precategory X Y (monoidfunconstr (pr2 f))
                              (abmonoid_equiv_is_iso X Y f)).
  Defined.

  Lemma abmonoid_iso_equiv_is_equiv (X Y : ob abmonoid_precategory) :
    isweq (abmonoid_iso_equiv X Y).
  Proof.
    use gradth.
    - exact (abmonoid_equiv_iso X Y).
    - intros x. use eq_iso. use monoidfun_paths. use idpath.
    - intros y. use monoidiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque abmonoid_iso_equiv_is_equiv.

  Definition abmonoid_iso_equiv_weq (X Y : ob abmonoid_precategory) :
    weq (iso X Y) (monoidiso (X : abmonoid) (Y : abmonoid)).
  Proof.
    use weqpair.
    - exact (abmonoid_iso_equiv X Y).
    - exact (abmonoid_iso_equiv_is_equiv X Y).
  Defined.

  Lemma abmonoid_equiv_iso_is_equiv (X Y : ob abmonoid_precategory) :
    isweq (abmonoid_equiv_iso X Y).
  Proof.
    use gradth.
    - exact (abmonoid_iso_equiv X Y).
    - intros y. use monoidiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use eq_iso. use monoidfun_paths. use idpath.
  Defined.
  Opaque abmonoid_equiv_iso_is_equiv.

  Definition abmonoid_equiv_iso_weq (X Y : ob abmonoid_precategory) :
    (monoidiso (X : abmonoid) (Y : abmonoid)) ≃ (iso X Y).
  Proof.
    use weqpair.
    - exact (abmonoid_equiv_iso X Y).
    - exact (abmonoid_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of abmonoids *)

  Definition abmonoid_precategory_isweq (X Y : ob abmonoid_precategory) :
    isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (iso X Y)
           (pr1weq (weqcomp (abmonoid_univalence X Y) (abmonoid_equiv_iso_weq X Y)))
           _ _ (weqproperty (weqcomp (abmonoid_univalence X Y) (abmonoid_equiv_iso_weq X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
  Defined.
  Opaque abmonoid_precategory_isweq.

  Definition abmonoid_precategory_is_univalent : is_univalent abmonoid_precategory.
  Proof.
    use mk_is_univalent.
    - intros X Y. exact (abmonoid_precategory_isweq X Y).
    - exact has_homsets_abmonoid_precategory.
  Defined.

  Definition abmonoid_category : univalent_category :=
    mk_category abmonoid_precategory abmonoid_precategory_is_univalent.

End def_abmonoid_category.
