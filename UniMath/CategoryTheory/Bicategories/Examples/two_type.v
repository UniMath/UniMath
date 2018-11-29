(**
The fundamental groupoid of a 2-type.

Authors: Dan Frumin, Niels van der Weide

Ported from: https://github.com/nmvdw/groupoids
 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.equiv_to_adjequiv.
Require Import UniMath.CategoryTheory.Bicategories.adjoint_unique.
Local Open Scope bicategory_scope.

Section TwoTypeBiGroupoid.
  Variable (X : Type)
           (HX : isofhlevel 4 X).

  Definition two_type_bicat_data
    : prebicat_data.
  Proof.
    use build_prebicat_data.
    - exact X.
    - exact (λ x y, x = y).
    - exact (λ _ _ p q, p = q).
    - exact (fun _ => idpath _).
    - exact (λ _ _ _ p q, p @ q).
    - exact (λ _ _ p, idpath p).
    - exact (λ _ _ _ _ _ q₁ q₂, q₁ @ q₂).
    - exact (λ _ _ _ p _ _ r, maponpaths (λ s, p @ s) r).
    - exact (λ _ _ _ _ _ q r, maponpaths (λ s, s @ q) r).
    - exact (λ _ _ p, idpath p).
    - exact (λ _ _ p, idpath p).
    - exact (λ _ _ p, pathscomp0rid p).
    - exact (λ _ _ p, !(pathscomp0rid p)).
    - exact (λ _ _ _ _ p q r, path_assoc p q r).
    - exact (λ _ _ _ _ p q r, !(path_assoc p q r)).
  Defined.


  Definition two_type_bicat_laws
    : prebicat_laws two_type_bicat_data.
  Proof.
    repeat (use tpair) ; try reflexivity.
    - intros ; cbn in *.
      apply pathscomp0rid.
    - intros ; cbn in *.
      apply path_assoc.
    - intros ; cbn in *.
      symmetry.
      apply maponpathscomp0.
    - intros ; cbn in *.
      rewrite maponpathscomp0.
      reflexivity.
    - intros x y p₁ p₂ q ; cbn in *.
      induction q ; cbn.
      reflexivity.
    - intros x y p₁ p₂ q ; cbn in *.
      induction q ; cbn.
      exact (!(pathscomp0rid _)).
    - intros w x y z p₁ p₂ p₃ p₄ q ; cbn in *.
      induction q ; cbn.
      exact (!(pathscomp0rid _)).
    - intros w x y z p₁ p₂ p₃ p₄ q ; cbn in *.
      induction q ; cbn.
      exact (!(pathscomp0rid _)).
    - intros w x y z p₁ p₂ p₃ p₄ q ; cbn in *.
      induction q ; cbn.
      exact ((pathscomp0rid _)).
    - intros w x y z p₁ p₂ p₃ p₄ q ; cbn in *.
      induction q ; cbn.
      exact ((pathscomp0rid _)).
    - intros x y p ; cbn in *.
      apply pathsinv0r.
    - intros x y p ; cbn in *.
      apply pathsinv0l.
    - intros w x y z p₁ p₂ p₃ ; cbn in *.
      apply pathsinv0r.
    - intros w x y z p₁ p₂ p₃ ; cbn in *.
      apply pathsinv0l.
    - intros x y z p q ; cbn in *.
      induction p ; cbn.
      reflexivity.
    - intros v w x y z p₁ p₂ p₃ p₄ ; cbn in *.
      induction p₁, p₂, p₃, p₄ ; cbn.
      reflexivity.
  Qed.

  Definition fundamental_bigroupoid
    : bicat.
  Proof.
    use build_bicategory.
    - exact two_type_bicat_data.
    - exact two_type_bicat_laws.
    - intros x y p₁ p₂ ; cbn in *.
      exact (HX x y p₁ p₂).
  Defined.

  (** Each 2-cell is an iso *)
  Definition fundamental_groupoid_2cell_iso
             {x y : fundamental_bigroupoid}
             {p₁ p₂ : fundamental_bigroupoid⟦x,y⟧}
             (s : p₁ ==> p₂)
    : is_invertible_2cell s.
  Proof.
    refine (!s ,, _).
    split ; cbn.
    - apply pathsinv0r.
    - apply pathsinv0l.
  Defined.

  (** Each 1-cell is an adjoint equivalence *)
  Definition fundamental_bigroupoid_1cell_equivalence
             {x y : fundamental_bigroupoid}
             (p : fundamental_bigroupoid⟦x,y⟧)
    : left_equivalence p.
  Proof.
    use tpair.
    - refine (!p ,, _).
      split ; cbn.
      + exact (! (pathsinv0r p)).
      + exact (pathsinv0l p).
    - split ; cbn.
      + apply fundamental_groupoid_2cell_iso.
      + apply fundamental_groupoid_2cell_iso.
  Defined.

  Definition fundamental_bigroupoid_1cell_adj_equiv
             {x y : fundamental_bigroupoid}
             (p : fundamental_bigroupoid⟦x,y⟧)
    : left_adjoint_equivalence p
    := equiv_to_isadjequiv p (fundamental_bigroupoid_1cell_equivalence p).

  (** It is univalent *)
  Definition fundamental_bigroupoid_is_univalent_2_1
    : is_univalent_2_1 fundamental_bigroupoid.
  Proof.
    intros x y p₁ p₂.
    use isweq_iso ; cbn in *.
    - intros q.
      apply q.
    - intros q.
      induction q ; cbn.
      reflexivity.
    - intros q.
      induction q as [q Hq].
      induction q ; cbn.
      use subtypeEquality' ; cbn.
      + reflexivity.
      + exact (@isaprop_is_invertible_2cell fundamental_bigroupoid x y p₁ p₁ (idpath p₁)).
  Defined.

  Definition fundamental_bigroupoid_is_univalent_2_0
    : is_univalent_2_0 fundamental_bigroupoid.
  Proof.
    intros x y.
    use isweq_iso.
    - intros p.
      apply p.
    - intros p ; cbn in *.
      induction p ; cbn.
      reflexivity.
    - intros p ; cbn in *.
      apply path_internal_adjoint_equivalence.
      + apply fundamental_bigroupoid_is_univalent_2_1.
      + cbn in *.
        induction (pr1 p) ; cbn.
        reflexivity.
  Defined.
End TwoTypeBiGroupoid.
