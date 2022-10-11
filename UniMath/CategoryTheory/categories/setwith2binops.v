(** * Category of setswith2binops *)
(** ** Contents
- setwith2binops precategory
- setwith2binops category
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Local Open Scope cat.


(** * Precategory of setwith2binops  *)
Section def_setwith2binop_precategory.

  Definition setwith2binop_fun_space (A B : setwith2binop) : hSet :=
    make_hSet (twobinopfun A B) (isasettwobinopfun A B).

  Definition setwith2binop_precategory_ob_mor : precategory_ob_mor :=
    tpair (λ ob : UU, ob -> ob -> UU) setwith2binop
          (λ A B : setwith2binop, setwith2binop_fun_space A B).

  Definition setwith2binop_precategory_data : precategory_data :=
    make_precategory_data
      setwith2binop_precategory_ob_mor
      (λ (X : setwith2binop), ((idtwobinopiso X) : twobinopfun X X))
      (fun (X Y Z : setwith2binop) (f : twobinopfun X Y) (g : twobinopfun Y Z)
       => twobinopfuncomp f g).

  Local Lemma setwith2binop_id_left (X Y : setwith2binop) (f : twobinopfun X Y) :
    twobinopfuncomp (idtwobinopiso X) f = f.
  Proof.
    use twobinopfun_paths. use idpath.
  Defined.
  Opaque setwith2binop_id_left.

  Local Lemma setwith2binop_id_right (X Y : setwith2binop) (f : twobinopfun X Y) :
    twobinopfuncomp f (idtwobinopiso Y) = f.
  Proof.
    use twobinopfun_paths. use idpath.
  Defined.
  Opaque setwith2binop_id_right.

  Local Lemma setwith2binop_assoc (X Y Z W : setwith2binop) (f : twobinopfun X Y)
             (g : twobinopfun Y Z) (h : twobinopfun Z W) :
    twobinopfuncomp f (twobinopfuncomp g h) = twobinopfuncomp (twobinopfuncomp f g) h.
  Proof.
    use twobinopfun_paths. use idpath.
  Defined.
  Opaque setwith2binop_assoc.

  Lemma is_precategory_setwith2binop_precategory_data :
    is_precategory setwith2binop_precategory_data.
  Proof.
    use make_is_precategory.
    - intros a b f. use setwith2binop_id_left.
    - intros a b f. use setwith2binop_id_right.
    - intros a b c d f g h. use setwith2binop_assoc.
    - intros a b c d f g h. apply pathsinv0, setwith2binop_assoc.
  Defined.

  Definition setwith2binop_precategory : precategory :=
    make_precategory setwith2binop_precategory_data is_precategory_setwith2binop_precategory_data.

  Lemma has_homsets_setwith2binop_precategory : has_homsets setwith2binop_precategory.
  Proof.
    intros X Y. use isasettwobinopfun.
  Qed.

End def_setwith2binop_precategory.


(** * Category of setwith2binops *)
Section def_setwith2binop_category.

  Definition setwith2binop_category : category
    := make_category _ has_homsets_setwith2binop_precategory.

  (** ** (twobinopiso X Y) ≃ (iso X Y) *)

  Lemma setwith2binop_iso_is_equiv (A B : ob setwith2binop_category) (f : z_iso A B) :
    isweq (pr1 (pr1 f)).
  Proof.
    use isweq_iso.
    - exact (pr1twobinopfun _ _ (inv_from_z_iso f)).
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (z_iso_inv_after_z_iso f)) x).
      intros x0. use isapropistwobinopfun.
    - intros x.
      use (toforallpaths _ _ _ (subtypeInjectivity _ _ _ _ (z_iso_after_z_iso_inv f)) x).
      intros x0. use isapropistwobinopfun.
  Defined.
  Opaque setwith2binop_iso_is_equiv.

  Lemma setwith2binop_iso_equiv (X Y : ob setwith2binop_category) : z_iso X Y -> twobinopiso X Y.
  Proof.
    intro f.
    use make_twobinopiso.
    - exact (make_weq (pr1 (pr1 f)) (setwith2binop_iso_is_equiv X Y f)).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma setwith2binop_equiv_is_z_iso (X Y : ob setwith2binop_category) (f : twobinopiso X Y) :
    @is_z_isomorphism setwith2binop_precategory X Y (make_twobinopfun (pr1 (pr1 f)) (pr2 f)).
  Proof.
    exists (make_twobinopfun (pr1 (pr1 (invtwobinopiso f))) (pr2 (invtwobinopiso f))).
    split.
    - use twobinopfun_paths. use funextfun. intros x. use homotinvweqweq.
    - use twobinopfun_paths. use funextfun. intros y. use homotweqinvweq.
  Defined.
  Opaque setwith2binop_equiv_is_z_iso.

  Lemma setwith2binop_equiv_iso (X Y : ob setwith2binop_category) : twobinopiso X Y -> z_iso X Y.
  Proof.
    intros f. exact (_,,setwith2binop_equiv_is_z_iso X Y f).
  Defined.

  Lemma setwith2binop_iso_equiv_is_equiv (X Y : setwith2binop_category) :
    isweq (setwith2binop_iso_equiv X Y).
  Proof.
    use isweq_iso.
    - exact (setwith2binop_equiv_iso X Y).
    - intros x. use z_iso_eq. use twobinopfun_paths. use idpath.
    - intros y. use twobinopiso_paths. use subtypePath.
      + intros x0. use isapropisweq.
      + use idpath.
  Defined.
  Opaque setwith2binop_iso_equiv_is_equiv.

  Definition setwith2binop_iso_equiv_weq (X Y : ob setwith2binop_category) :
    (z_iso X Y) ≃ (twobinopiso X Y).
  Proof.
    use make_weq.
    - exact (setwith2binop_iso_equiv X Y).
    - exact (setwith2binop_iso_equiv_is_equiv X Y).
  Defined.

  Lemma setwith2binop_equiv_iso_is_equiv (X Y : ob setwith2binop_category) :
    isweq (setwith2binop_equiv_iso X Y).
  Proof.
    use isweq_iso.
    - exact (setwith2binop_iso_equiv X Y).
    - intros y. use twobinopiso_paths. use subtypePath.
      + intros x0. use isapropisweq.
      + use idpath.
    - intros x. use z_iso_eq. use twobinopfun_paths. use idpath.
  Defined.
  Opaque setwith2binop_equiv_iso_is_equiv.

  Definition setwith2binop_equiv_weq_iso (X Y : ob setwith2binop_category) :
    (twobinopiso X Y) ≃ (z_iso X Y).
  Proof.
    use make_weq.
    - exact (setwith2binop_equiv_iso X Y).
    - exact (setwith2binop_equiv_iso_is_equiv X Y).
  Defined.


  (** ** Category of setwith2binops *)

  Definition setwith2binop_category_isweq (X Y : ob setwith2binop_category) :
    isweq (λ p : X = Y, idtoiso p).
  Proof.
    use (@isweqhomot
           (X = Y) (z_iso X Y)
           (pr1weq (weqcomp (setwith2binop_univalence X Y) (setwith2binop_equiv_weq_iso X Y)))
           _ _ (weqproperty (weqcomp (setwith2binop_univalence X Y)
                                     (setwith2binop_equiv_weq_iso X Y)))).
    intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use total2_paths_f.
    - use idpath.
    - use proofirrelevance. use isaprop_is_z_isomorphism.
  Defined.
  Opaque setwith2binop_category_isweq.



  Definition setwith2binop_category_is_univalent : is_univalent setwith2binop_category.
  Proof.
    intros X Y. exact (setwith2binop_category_isweq X Y).
  Defined.

  Definition setwith2binop_univalent_category : univalent_category :=
    make_univalent_category setwith2binop_category setwith2binop_category_is_univalent.

End def_setwith2binop_category.
