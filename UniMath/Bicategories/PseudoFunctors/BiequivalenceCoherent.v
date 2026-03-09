(**

 Coherent biequivalences

 The notion of biequivalence in the file `PseudoFunctors.Biequivalence` is incoherent. A
 biequivalence from `B₁` to `B₂` consists of pseudofunctors `F` from `B₁` to ` B₂` and `G`
 from `B₂` to `B₁` and pseudotransformations from `F · G` to the identity and from `G · F`
 to the identity that are adjoint equivalences. These two pseudotransformations witness
 that `F` and `G` are inverses in a suitable sense.

 However, what is missing to make this notion fully coherent, are, for instance, the
 triangle equations. These are witnessed by invertible modifications satisfying suitable
 coherences (see Definition 2.1 in "Biequivalences in tricategories" and see Section 5 in
 "A coherent approach to pseudomonads"). In this file, we construct a coherent biequivalence
 from a biequivalence. Note that we only construct the necessary invertible 2-cells, and we
 do not show that they are natural in a suitable (i.e., an invertible modification), and we
 do not prove any further coherences.

 Our construction is a variation of the usual construction used to refine equivalences. More
 specifically, both pseudofunctors and the unit are left the same, but we define a new counit.

 References
 - "Biequivalences in tricategories" by Gurski
 - "A coherent approach to pseudomonads" by Lack

 Contents
 1. The refined counit
 2. The invertible2-cell witnessing the first triangle law
 3. The invertible 2-cell witnessing the second triangle law
 4. The refined biequivalence

                                                                                         *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Properties.ClosedUnderInvertibles.
Require Import UniMath.Bicategories.Morphisms.Properties.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Modifications.Examples.Unitality.

Local Open Scope cat.

Section CoherentBiequivalence.
  Context {B₁ B₂ : bicat}
          (HB₁ : is_univalent_2 B₁)
          (HB₂ : is_univalent_2 B₂)
          (biequiv : biequivalence B₁ B₂).

  Let L : psfunctor B₁ B₂ := biequiv.
  Let R : psfunctor B₂ B₁ := inv_psfunctor_of_is_biequivalence biequiv.
  Let η : pstrans (comp_psfunctor R L) (id_psfunctor _)
    := unit_of_is_biequivalence biequiv.
  Let ηinv : pstrans (id_psfunctor _) (comp_psfunctor R L)
    := invunit_of_is_biequivalence biequiv.
  Let ε : pstrans (comp_psfunctor L R) (id_psfunctor _)
    := counit_of_is_biequivalence biequiv.
  Let εinv : pstrans (id_psfunctor _) (comp_psfunctor L R)
    := invcounit_of_is_biequivalence biequiv.
  Let ηinvη : invertible_modification (ηinv · η) (id₁ _)
    := unitcounit_of_is_biequivalence biequiv.
  Let ηηinv : invertible_modification (η · ηinv) (id₁ _)
    := unitunit_of_is_biequivalence biequiv.
  Let εεinv : invertible_modification (ε · εinv) (id₁ _)
    := counitunit_of_is_biequivalence biequiv.
  Let εinvε : invertible_modification (εinv · ε) (id₁ _)
    := counitcounit_of_is_biequivalence biequiv.

  (** * 1. The refined counit *)
  Definition coherent_counit_biequiv
    : pstrans (comp_psfunctor L R) (id_psfunctor _)
    := linvunitor_pstrans _
       · right_whisker (comp_psfunctor L R) εinv
       · rassociator_pstrans _ _ _
       · left_whisker L (lassociator_pstrans _ _ _)
       · left_whisker L (right_whisker R η)
       · left_whisker L (lunitor_pstrans _)
       · ε.

  Definition coherent_counit_biequiv_ob
             (x : B₂)
    : invertible_2cell
        (coherent_counit_biequiv x)
        (εinv (L(R x)) · #L(η(R x)) · ε x).
  Proof.
    cbn.
    refine (rwhisker_of_invertible_2cell _ _).
    refine (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 (inv_of_invertible_2cell (psfunctor_id L _)))
              _).
    refine (comp_of_invertible_2cell
              (runitor_invertible_2cell _)
              _).
    refine (rwhisker_of_invertible_2cell _ _).
    refine (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 (inv_of_invertible_2cell (psfunctor_id L _)))
              _).
    refine (comp_of_invertible_2cell
              (runitor_invertible_2cell _)
              _).
    refine (comp_of_invertible_2cell
              (runitor_invertible_2cell _)
              _).
    apply lunitor_invertible_2cell.
  Defined.

  Definition coherent_counit_biequiv_ob_adj_equiv
             (x : B₂)
    : left_adjoint_equivalence (coherent_counit_biequiv x).
  Proof.
    use (left_adjoint_equivalence_invertible
           _
           (coherent_counit_biequiv_ob x)).
    use comp_left_adjoint_equivalence.
    - use comp_left_adjoint_equivalence.
      + exact (inv_left_adjoint_equivalence
                 (pointwise_adjequiv
                    _
                    (is_biequivalence_adjoint_counit biequiv)
                    (L(R x)))).
      + use psfunctor_preserves_adjequiv'.
        exact (pointwise_adjequiv _ (is_biequivalence_adjoint_unit biequiv) (R x)).
    - exact (pointwise_adjequiv _ (is_biequivalence_adjoint_counit biequiv) x).
  Defined.

  (** * 2. The invertible2-cell witnessing the first triangle law *)
  Definition coherent_counit_biequiv_triangle_1_help
             (x : B₁)
    : invertible_2cell
        (id₁ _)
        (ηinv (R(L x)) · #R(#L(η x)))
    := comp_of_invertible_2cell
         (inv_of_invertible_2cell (invertible_modcomponent_of ηηinv x))
         (inv_of_invertible_2cell (psnaturality_of ηinv (η x))).

  Definition coherent_counit_biequiv_triangle_1_help_2
             (x : B₁)
    : invertible_2cell
        (# L (η (R (L x))) · ε (L x))
        (ε (L(R(L x))) · #L(η x)).
  Proof.
    refine (comp_of_invertible_2cell
              _
              (inv_of_invertible_2cell (psnaturality_of ε (#L(η x))))).
    refine (rwhisker_of_invertible_2cell _ _).
    use (psfunctor_inv2cell L).
    refine (comp_of_invertible_2cell
              (rinvunitor_invertible_2cell _)
              _).
    refine (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 (coherent_counit_biequiv_triangle_1_help x))
              _).
    refine (comp_of_invertible_2cell
              (lassociator_invertible_2cell _ _ _)
              _).
    refine (comp_of_invertible_2cell
              (rwhisker_of_invertible_2cell _ (invertible_modcomponent_of ηηinv _))
              _).
    apply lunitor_invertible_2cell.
  Defined.

  Definition coherent_counit_biequiv_triangle_1
             (x : B₁)
    : invertible_2cell
        (coherent_counit_biequiv (L x))
        (#L(η x)).
  Proof.
    refine (comp_of_invertible_2cell
              (coherent_counit_biequiv_ob (L x))
              _).
    refine (comp_of_invertible_2cell
              (rassociator_invertible_2cell _ _ _)
              _).
    refine (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 (coherent_counit_biequiv_triangle_1_help_2 x))
              _).
    refine (comp_of_invertible_2cell
              (lassociator_invertible_2cell _ _ _)
              _).
    refine (comp_of_invertible_2cell
              (rwhisker_of_invertible_2cell
                 _
                 (invertible_modcomponent_of εinvε (L(R(L x)))))
              _).
    apply lunitor_invertible_2cell.
  Defined.

  (** * 3. The invertible 2-cell witnessing the second triangle law *)
  Definition coherent_counit_biequiv_triangle_2_unit_lem
             (x : B₁)
    : invertible_2cell
        (#R(#L(η x)))
        (η(R(L x))).
  Proof.
    refine (comp_of_invertible_2cell
              _
              (runitor_invertible_2cell _)).
    refine (comp_of_invertible_2cell
              _
              (lwhisker_of_invertible_2cell
                 _
                 (inv_of_invertible_2cell
                    (coherent_counit_biequiv_triangle_1_help x)))).
    refine (comp_of_invertible_2cell
              _
              (rassociator_invertible_2cell _ _ _)).
    refine (comp_of_invertible_2cell
              (linvunitor_invertible_2cell _)
              _).
    refine (rwhisker_of_invertible_2cell _ _).
    exact (inv_of_invertible_2cell (invertible_modcomponent_of ηηinv _)).
  Defined.

  Definition coherent_counit_biequiv_triangle_2_counit_lem
             (x : B₂)
    : invertible_2cell
        (#L(#R(ε x)))
        (ε(L(R x))).
  Proof.
    refine (comp_of_invertible_2cell
              (rinvunitor_invertible_2cell _)
              _).
    refine (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 (inv_of_invertible_2cell
                    (invertible_modcomponent_of εεinv _)))
              _).
    refine (comp_of_invertible_2cell
              (lassociator_invertible_2cell _ _ _)
              _).
    refine (comp_of_invertible_2cell
              (rwhisker_of_invertible_2cell
                 _
                 (inv_of_invertible_2cell (psnaturality_of ε (ε x))))
              _).
    refine (comp_of_invertible_2cell
              (rassociator_invertible_2cell _ _ _)
              _).
    refine (comp_of_invertible_2cell
              _
              (runitor_invertible_2cell _)).
    refine (lwhisker_of_invertible_2cell _ _).
    exact (invertible_modcomponent_of εεinv _).
  Defined.

  Definition coherent_counit_biequiv_triangle_2
             (x : B₂)
    : invertible_2cell
        (#R (coherent_counit_biequiv x))
        (η (R x)).
  Proof.
    refine (comp_of_invertible_2cell
              (psfunctor_inv2cell R (coherent_counit_biequiv_ob x))
              _).
    refine (comp_of_invertible_2cell
              (inv_of_invertible_2cell (psfunctor_comp R _ _))
              _).
    refine (comp_of_invertible_2cell
              (rwhisker_of_invertible_2cell
                 _
                 (inv_of_invertible_2cell (psfunctor_comp R _ _)))
              _).
    refine (comp_of_invertible_2cell
              (rwhisker_of_invertible_2cell
                 _
                 (lwhisker_of_invertible_2cell
                    _
                    (coherent_counit_biequiv_triangle_2_unit_lem _)))
              _).
    refine (comp_of_invertible_2cell
              (rassociator_invertible_2cell _ _ _)
              _).
    refine (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 (psnaturality_of η (#R(ε x))))
              _).
    refine (comp_of_invertible_2cell
              (lassociator_invertible_2cell _ _ _)
              _).
    refine (comp_of_invertible_2cell
              _
              (lunitor_invertible_2cell _)).
    refine (rwhisker_of_invertible_2cell _ _).
    refine (comp_of_invertible_2cell
              (psfunctor_comp R _ _)
              _).
    refine (comp_of_invertible_2cell
              _
              (inv_of_invertible_2cell (psfunctor_id R _))).
    refine (psfunctor_inv2cell R _).
    refine (comp_of_invertible_2cell
              _
              (invertible_modcomponent_of εinvε _)).
    refine (lwhisker_of_invertible_2cell _ _).
    apply coherent_counit_biequiv_triangle_2_counit_lem.
  Defined.

  (** * 4. The refined biequivalence *)
  Definition to_coherent_biequiv_unit_counit
    : is_biequivalence_unit_counit L R
    := η ,, coherent_counit_biequiv.

  Definition to_coherent_biequiv_adjoint
    : is_biequivalence_adjoints
        to_coherent_biequiv_unit_counit.
  Proof.
    split.
    - exact (is_biequivalence_adjoint_unit biequiv).
    - use (pointwise_adjequiv_to_adjequiv HB₂).
      exact coherent_counit_biequiv_ob_adj_equiv.
  Defined.

  Definition to_coherent_biequiv
    : biequivalence B₁ B₂
    := L
       ,,
       R
       ,,
       to_coherent_biequiv_unit_counit
       ,,
       to_coherent_biequiv_adjoint.

  Definition coherent_counit_biequiv_triangle_2_alt
             (x : B₂)
    : invertible_2cell
        (identity _)
        (η (R x)
         · #R (invcounit_of_is_biequivalence to_coherent_biequiv x)).
  Proof.
    refine (comp_of_invertible_2cell
              _
              (rwhisker_of_invertible_2cell
                 _
                 (coherent_counit_biequiv_triangle_2 x))).
    refine (comp_of_invertible_2cell
              _
              (inv_of_invertible_2cell (psfunctor_comp R _ _))).
    refine (comp_of_invertible_2cell
              (psfunctor_id R _)
              _).
    refine (psfunctor_inv2cell R _).
    exact (inv_of_invertible_2cell
             (invertible_modcomponent_of
                (counitunit_of_is_biequivalence to_coherent_biequiv)
                x)).
  Defined.
End CoherentBiequivalence.

Definition coherent_is_biequivalence_adjoints
           {B₁ B₂ : bicat}
           (univ_2_B₁ : is_univalent_2 B₁)
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit G F}
           (a : is_biequivalence_adjoints e)
  : biequivalence B₂ B₁.
Proof.
  use to_coherent_biequiv.
  - exact univ_2_B₁.
  - exact (G ,, F ,, e ,, a).
Defined.

Definition coherent_is_biequivalence_adjoints_triangle_2_alt
           {B₁ B₂ : bicat}
           (univ_2_B₁ : is_univalent_2 B₁)
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit G F}
           (a : is_biequivalence_adjoints e)
           (x : B₁)
  : invertible_2cell
      (identity _)
      (unit_of_is_biequivalence
         (coherent_is_biequivalence_adjoints univ_2_B₁ a)
         (F x)
       · #F (invcounit_of_is_biequivalence
               (coherent_is_biequivalence_adjoints univ_2_B₁ a)
               x)).
Proof.
  exact (coherent_counit_biequiv_triangle_2_alt
           univ_2_B₁
           (G ,, F ,, e ,, a)
           x).
Defined.
