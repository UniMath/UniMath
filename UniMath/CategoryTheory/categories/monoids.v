(** * Category of monoids *)
(** ** Contents
- Precategory of monoids
- Category of monoids
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.


(** * Precategory of monoids *)
Section def_monoid_precategory.

  Definition monoid_fun_space (A B : monoid) : hSet :=
    hSetpair (monoidfun A B) (isasetmonoidfun A B).

  Definition monoid_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) monoid (λ A B : monoid, monoid_fun_space A B).

  Definition monoid_precategory_data : precategory_data :=
    precategory_data_pair
      monoid_precategory_ob_mor (λ (X : monoid), ((idmonoidiso X) : monoidfun X X))
      (fun (X Y Z : monoid) (f : monoidfun X Y) (g : monoidfun Y Z) => monoidfuncomp f g).

  Local Lemma monoid_id_left {X Y : monoid} (f : monoidfun X Y) :
    monoidfuncomp (idmonoidiso X) f = f.
  Proof.
    use monoidfun_paths. use idpath.
  Defined.
  Opaque monoid_id_left.

  Local Lemma monoid_id_right {X Y : monoid} (f : monoidfun X Y) :
    monoidfuncomp f (idmonoidiso Y) = f.
  Proof.
    use monoidfun_paths. use idpath.
  Defined.
  Opaque monoid_id_right.

  Local Lemma monoid_assoc (X Y Z W : monoid) (f : monoidfun X Y) (g : monoidfun Y Z)
        (h : monoidfun Z W) :
    monoidfuncomp f (monoidfuncomp g h) = monoidfuncomp (monoidfuncomp f g) h.
  Proof.
    use monoidfun_paths. use idpath.
  Defined.
  Opaque monoid_assoc.

  Lemma is_precategory_monoid_precategory_data : is_precategory monoid_precategory_data.
  Proof.
    use mk_is_precategory.
    - intros a b f. use monoid_id_left.
    - intros a b f. use monoid_id_right.
    - intros a b c d f g h. use monoid_assoc.
  Qed.

  Definition monoid_precategory : precategory :=
    mk_precategory monoid_precategory_data is_precategory_monoid_precategory_data.

  Lemma has_homsets_monoid_precategory : has_homsets monoid_precategory.
  Proof.
    intros X Y. use isasetmonoidfun.
  Qed.

End def_monoid_precategory.


(** * Category of monoids *)
Section def_monoid_category.

  (** ** (monoidiso X Y) ≃ (iso X Y) *)

  Lemma monoid_iso_is_equiv (A B : ob monoid_precategory) (f : iso A B) : isweq (pr1 (pr1 f)).
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
  Opaque monoid_iso_is_equiv.

  Lemma monoid_iso_equiv (X Y : ob monoid_precategory) : iso X Y -> monoidiso X Y.
  Proof.
    intro f.
    use monoidisopair.
    - exact (weqpair (pr1 (pr1 f)) (monoid_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma monoid_equiv_is_iso (X Y : ob monoid_precategory) (f : monoidiso X Y) :
    @is_iso monoid_precategory X Y (monoidfunconstr (pr2 f)).
  Proof.
    use is_iso_qinv.
    - exact (monoidfunconstr (pr2 (invmonoidiso f))).
    - use mk_is_inverse_in_precat.
      + use monoidfun_paths. use funextfun. intros x. use homotinvweqweq.
      + use monoidfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque monoid_equiv_is_iso.

  Lemma monoid_equiv_iso (X Y : ob monoid_precategory) : monoidiso X Y -> iso X Y.
  Proof.
    intros f. exact (@isopair monoid_precategory X Y (monoidfunconstr (pr2 f))
                              (monoid_equiv_is_iso X Y f)).
  Defined.

  Lemma monoid_iso_equiv_is_equiv (X Y : monoid_precategory) : isweq (monoid_iso_equiv X Y).
  Proof.
    use gradth.
    - exact (monoid_equiv_iso X Y).
    - intros x. use eq_iso. use monoidfun_paths. use idpath.
    - intros y. use monoidiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque monoid_iso_equiv_is_equiv.

  Definition monoid_iso_equiv_weq (X Y : ob monoid_precategory) : (iso X Y) ≃ (monoidiso X Y).
  Proof.
    use weqpair.
    - exact (monoid_iso_equiv X Y).
    - exact (monoid_iso_equiv_is_equiv X Y).
  Defined.

  Lemma monoid_equiv_iso_is_equiv (X Y : ob monoid_precategory) : isweq (monoid_equiv_iso X Y).
  Proof.
    use gradth.
    - exact (monoid_iso_equiv X Y).
    - intros y. use monoidiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use eq_iso. use monoidfun_paths. use idpath.
  Defined.
  Opaque monoid_equiv_iso_is_equiv.

  Definition monoid_equiv_iso_weq (X Y : ob monoid_precategory) : (monoidiso X Y) ≃ (iso X Y).
  Proof.
    use weqpair.
    - exact (monoid_equiv_iso X Y).
    - exact (monoid_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of monoids *)

  Definition monoid_precategory_isweq (X Y : ob monoid_precategory) :
    isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (iso X Y)
           (pr1weq (weqcomp (monoid_univalence X Y) (monoid_equiv_iso_weq X Y)))
           _ _ (weqproperty (weqcomp (monoid_univalence X Y) (monoid_equiv_iso_weq X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
  Defined.
  Opaque monoid_precategory_isweq.

  Definition monoid_precategory_is_univalent : is_univalent monoid_precategory.
  Proof.
    use mk_is_univalent.
    - intros X Y. exact (monoid_precategory_isweq X Y).
    - exact has_homsets_monoid_precategory.
  Defined.

  Definition monoid_category : univalent_category :=
    mk_category monoid_precategory monoid_precategory_is_univalent.

End def_monoid_category.
