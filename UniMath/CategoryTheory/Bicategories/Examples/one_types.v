(**
The bicategory of 1-types.

Authors: Dan Frumin, Niels van der Weide

Ported from: https://github.com/nmvdw/groupoids
*)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.equiv_to_adjequiv.
Require Import UniMath.CategoryTheory.Bicategories.adjoint_unique.

Definition one_type
  := ∑ (A : Type), isofhlevel 3 A.

Definition one_type_to_type : one_type -> UU := pr1.
Coercion one_type_to_type : one_type >-> UU.

(** The bicategory *)
Definition one_type_bicat_data
  : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact one_type.
  - exact (λ X Y, X → Y).
  - exact (λ _ _ f g, f = g).
  - exact (λ _ x, x).
  - exact (λ _ _ _ f g x, g(f x)).
  - reflexivity.
  - cbn ; intros X Y f g h p q.
    exact (p @ q).
  - cbn ; intros X Y Z f g h p.
    exact (maponpaths (λ φ x, φ (f x)) p).
  - cbn ; intros X Y Z f g h p.
    exact (maponpaths (λ φ x, h(φ x)) p).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Definition one_type_bicat_laws
  : prebicat_laws one_type_bicat_data.
Proof.
  repeat (use tpair).
  - intros X Y f g p ; cbn in *.
    reflexivity.
  - intros X Y f g p ; cbn in *.
    apply pathscomp0rid.
  - intros X Y f g h k p q r.
    apply path_assoc.
  - reflexivity.
  - reflexivity.
  - intros X Y Z f g h i p q ; cbn in *.
    induction p, q ; cbn.
    reflexivity.
  - intros X Y Z f g h i p q ; cbn in *.
    induction p, q ; cbn.
    reflexivity.
  - intros X Y f g p ; cbn in *.
    induction p ; cbn.
    reflexivity.
  - intros X Y f g p ; cbn in *.
    induction p ; cbn.
    reflexivity.
  - intros W X Y Z f g h i p ; cbn in *.
      induction p ; cbn.
      reflexivity.
  - intros W X Y Z f g h i p ; cbn in *.
    induction p ; cbn.
    reflexivity.
  - intros W X Y Z f g h i p ; cbn in *.
    induction p ; cbn.
    reflexivity.
  - intros X Y Z f g h i p q ; cbn in *.
    induction p, q ; cbn.
    reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros V W X Y Z f g h i ; cbn in *.
    reflexivity.
Qed.

Definition one_types
  : bicat.
Proof.
  use build_bicategory.
  - exact one_type_bicat_data.
  - exact one_type_bicat_laws.
  - intros X Y f g ; cbn in *.
    exact (impredfun 3 X Y (pr2 Y) f g).
Defined.

(** Each 2-cell is an iso *)
Definition one_type_2cell_iso
           {X Y : one_types}
           {f g : one_types⟦X,Y⟧}
           (α : f ==> g)
  : is_invertible_2cell α.
Proof.
  refine (!α ,, _).
  split ; cbn.
  - apply pathsinv0r.
  - apply pathsinv0l.
Defined.

(** It is univalent *)
Definition one_types_is_univalent_2_1
  : is_univalent_2_1 one_types.
Proof.
  intros X Y f g.
  use isweq_iso.
  - intros α.
    induction α as [p Hp].
    exact p.
  - intros p.
    induction p ; cbn.
    reflexivity.
  - intros p.
    induction p as [p Hp].
    induction p ; cbn in *.
    use subtypeEquality' ; cbn.
    + reflexivity.
    + exact (@isaprop_is_invertible_2cell one_types X Y f f (idpath f)).
Defined.

Definition adjoint_equivalence_is_weq
           {X Y : one_types}
           (f : one_types⟦X,Y⟧)
           (Hf : is_internal_left_adjoint_internal_equivalence f)
  : isweq f.
Proof.
  use isweq_iso.
  - exact (internal_right_adjoint Hf).
  - intros x.
    exact (eqtohomot (!(internal_unit Hf)) x).
  - intros x.
    exact (eqtohomot (internal_counit Hf) x).
Defined.

Definition weq_is_adjoint_equivalence_help
           {X Y : one_types}
           (f : one_types⟦X,Y⟧)
           (Hf : isweq f)
  : internal_equivalence X Y.
Proof.
  use tpair.
  - refine (f ,, invmap (f ,, Hf) ,, _).
    split.
    + apply funextsec.
      intros x.
      exact (!(homotinvweqweq (f ,, Hf) x)).
    + apply funextsec.
      intros x.
      exact (homotweqinvweq (f ,, Hf) x).
  - split ; apply one_type_2cell_iso.
Defined.

Definition weq_is_adjoint_equivalence
           {X Y : one_types}
           (f : one_types⟦X,Y⟧)
           (Hf : isweq f)
  : is_internal_left_adjoint_internal_equivalence f
  := equiv_to_isadjequiv (weq_is_adjoint_equivalence_help f Hf).

Definition adjoint_equivalence_to_weq
           (X Y : one_types)
  : internal_adjoint_equivalence X Y → weq (pr1 X) (pr1 Y).
Proof.
  intros Hf.
  refine (internal_left_adjoint Hf ,, _).
  apply adjoint_equivalence_is_weq.
  apply Hf.
Defined.

Definition weq_to_adjoint_equivalence
           (X Y : one_types)
  : weq (pr1 X) (pr1 Y) → internal_adjoint_equivalence X Y.
Proof.
  intros Hf.
  refine (pr1weq Hf ,, _).
  apply weq_is_adjoint_equivalence.
  apply Hf.
Defined.

Definition weq_to_adjoint_equivalence_is_weq
           (X Y : one_types)
  : isweq (weq_to_adjoint_equivalence X Y).
Proof.
  use isweq_iso.
  - exact (adjoint_equivalence_to_weq X Y).
  - intros f.
    use subtypeEquality'.
    + reflexivity.
    + apply isapropisweq.
  - intros f.
    apply path_internal_adjoint_equivalence.
    + apply one_types_is_univalent_2_1.
    + reflexivity.
Defined.

Definition one_types_is_univalent_2_0
  : is_univalent_2_0 one_types.
Proof.
  intros X Y.
  apply (isweqhomot
           (weq_to_adjoint_equivalence X Y ∘ pr1 (UA_for_HLevels 3 X Y))%functions
           (idtoiso_2_0 X Y)).
  - intros p.
    induction p ; cbn.
    apply path_internal_adjoint_equivalence.
    + apply one_types_is_univalent_2_1.
    + reflexivity.
  - apply twooutof3c.
    + apply UA_for_HLevels.
    + exact (weq_to_adjoint_equivalence_is_weq X Y).
Defined.

Definition one_types_is_univalent_2
  : is_univalent_2 one_types.
Proof.
  split.
  - exact one_types_is_univalent_2_0.
  - exact one_types_is_univalent_2_1.
Defined.