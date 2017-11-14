(** * Category of grs *)
(** ** Contents
- Precategory of grs
- Category of grs
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.functor_categories.


(** * Precategory of grs *)
Section def_gr_precategory.

  Definition gr_fun_space (A B : gr) : hSet := hSetpair (monoidfun A B) (isasetmonoidfun A B).

  Definition gr_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) gr (λ A B : gr, gr_fun_space A B).

  Definition gr_precategory_data : precategory_data :=
    precategory_data_pair
      gr_precategory_ob_mor (λ (X : gr), ((idmonoidiso X) : monoidfun X X))
      (fun (X Y Z : gr) (f : monoidfun X Y) (g : monoidfun Y Z) => monoidfuncomp f g).

  Local Lemma gr_id_left (X Y : gr) (f : monoidfun X Y) : monoidfuncomp (idmonoidiso X) f = f.
  Proof.
    use monoidfun_paths. use idpath.
  Defined.
  Opaque gr_id_left.

  Local Lemma gr_id_right (X Y : gr) (f : monoidfun X Y) : monoidfuncomp f (idmonoidiso Y) = f.
  Proof.
    use monoidfun_paths. use idpath.
  Defined.
  Opaque gr_id_right.

  Local Lemma gr_assoc (X Y Z W : gr) (f : monoidfun X Y) (g : monoidfun Y Z) (h : monoidfun Z W) :
    monoidfuncomp f (monoidfuncomp g h) = monoidfuncomp (monoidfuncomp f g) h.
  Proof.
    use monoidfun_paths. use idpath.
  Defined.
  Opaque gr_assoc.

  Lemma is_precategory_gr_precategory_data : is_precategory gr_precategory_data.
  Proof.
    use mk_is_precategory.
    - intros a b f. use gr_id_left.
    - intros a b f. use gr_id_right.
    - intros a b c d f g h. use gr_assoc.
  Qed.

  Definition gr_precategory : precategory :=
    mk_precategory gr_precategory_data is_precategory_gr_precategory_data.

  Lemma has_homsets_gr_precategory : has_homsets gr_precategory.
  Proof.
    intros X Y. use isasetmonoidfun.
  Qed.

End def_gr_precategory.


(** * Category of grs *)
Section def_gr_category.

  (** ** (monoidiso X Y) ≃ (iso X Y) *)

  Lemma gr_iso_is_equiv (A B : ob gr_precategory) (f : iso A B) : isweq (pr1 (pr1 f)).
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
  Opaque gr_iso_is_equiv.

  Lemma gr_iso_equiv (X Y : ob gr_precategory) : iso X Y -> monoidiso (X : gr) (Y : gr).
  Proof.
    intro f.
    use monoidisopair.
    - exact (weqpair (pr1 (pr1 f)) (gr_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma gr_equiv_is_iso (X Y : ob gr_precategory) (f : monoidiso (X : gr) (Y : gr)) :
    @is_iso gr_precategory X Y (monoidfunconstr (pr2 f)).
  Proof.
    use is_iso_qinv.
    - exact (monoidfunconstr (pr2 (invmonoidiso f))).
    - use mk_is_inverse_in_precat.
      + use monoidfun_paths. use funextfun. intros x. use homotinvweqweq.
      + use monoidfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque gr_equiv_is_iso.

  Lemma gr_equiv_iso (X Y : ob gr_precategory) : monoidiso (X : gr) (Y : gr) -> iso X Y.
  Proof.
    intros f. exact (@isopair gr_precategory X Y (monoidfunconstr (pr2 f))
                              (gr_equiv_is_iso X Y f)).
  Defined.

  Lemma gr_iso_equiv_is_equiv (X Y : gr_precategory) : isweq (gr_iso_equiv X Y).
  Proof.
    use gradth.
    - exact (gr_equiv_iso X Y).
    - intros x. use eq_iso. use monoidfun_paths. use idpath.
    - intros y. use monoidiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque gr_iso_equiv_is_equiv.

  Definition gr_iso_equiv_weq (X Y : ob gr_precategory) :
    weq (iso X Y) (monoidiso (X : gr) (Y : gr)).
  Proof.
    use weqpair.
    - exact (gr_iso_equiv X Y).
    - exact (gr_iso_equiv_is_equiv X Y).
  Defined.

  Lemma gr_equiv_iso_is_equiv (X Y : ob gr_precategory) : isweq (gr_equiv_iso X Y).
  Proof.
    use gradth.
    - exact (gr_iso_equiv X Y).
    - intros y. use monoidiso_paths. use subtypeEquality.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use eq_iso. use monoidfun_paths. use idpath.
  Defined.
  Opaque gr_equiv_iso_is_equiv.

  Definition gr_equiv_iso_weq (X Y : ob gr_precategory) :
    (monoidiso (X : gr) (Y : gr)) ≃ (iso X Y).
  Proof.
    use weqpair.
    - exact (gr_equiv_iso X Y).
    - exact (gr_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of grs *)

  Definition gr_precategory_isweq (X Y : ob gr_precategory) : isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (iso X Y)
           (pr1weq (weqcomp (gr_univalence X Y) (gr_equiv_iso_weq X Y)))
           _ _ (weqproperty (weqcomp (gr_univalence X Y) (gr_equiv_iso_weq X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_iso.
  Defined.
  Opaque gr_precategory_isweq.

  Definition gr_precategory_is_univalent : is_univalent gr_precategory.
  Proof.
    use mk_is_univalent.
    - intros X Y. exact (gr_precategory_isweq X Y).
    - exact has_homsets_gr_precategory.
  Defined.

  Definition gr_category : univalent_category := mk_category gr_precategory gr_precategory_is_univalent.

End def_gr_category.
