(********************************************************************

 Cleaving properties

 There are several definitions of cleaving of bicategories, namely
 local (op)cleavings and global cleavings. If we assume that the
 involed (displayed) bicategories are univalent, then we can show
 that these notions are propositional

 Contents
 1. Propositionality of preservation of cartesian cells
 2. Propositionality of local (op)cleavings
 3. Propositionality of global cleavings

 ********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Opposite.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Cartesians.
Require Import UniMath.Bicategories.DisplayedBicats.EquivalenceBetweenCartesians.

Local Open Scope cat.

(**
 1. Propositionality of preservation of cartesian cells
 *)
Definition isaprop_lwhisker_cartesian
           {B : bicat}
           (D : disp_bicat B)
  : isaprop (lwhisker_cartesian D).
Proof.
  do 15 (use impred ; intro).
  apply isaprop_is_cartesian_2cell.
Qed.

Definition isaprop_rwhisker_cartesian
           {B : bicat}
           (D : disp_bicat B)
  : isaprop (rwhisker_cartesian D).
Proof.
  do 15 (use impred ; intro).
  apply isaprop_is_cartesian_2cell.
Qed.

Definition isaprop_lwhisker_opcartesian
           {B : bicat}
           (D : disp_bicat B)
  : isaprop (lwhisker_opcartesian D).
Proof.
  do 15 (use impred ; intro).
  apply isaprop_is_opcartesian_2cell.
Qed.

Definition isaprop_rwhisker_opcartesian
           {B : bicat}
           (D : disp_bicat B)
  : isaprop (rwhisker_opcartesian D).
Proof.
  do 15 (use impred ; intro).
  apply isaprop_is_opcartesian_2cell.
Qed.

(**
 2. Propositionality of local (op)cleavings
 *)
Definition isaprop_local_cleaving
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (D : disp_bicat B)
           (HD : disp_univalent_2_1 D)
  : isaprop (local_cleaving D).
Proof.
  use (isofhlevelweqb 1 (local_fib_weq_local_cleaving D)).
  use impred ; intro x.
  use impred ; intro y.
  use impred ; intro xx.
  use impred ; intro yy.
  use (@isaprop_cleaving (univ_hom HB x y)).
  use is_univalent_disp_disp_hom.
  exact HD.
Defined.

Definition isaprop_local_opcleaving
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (D : disp_bicat B)
           (HD : disp_univalent_2_1 D)
  : isaprop (local_opcleaving D).
Proof.
  use (isofhlevelweqb 1 (local_opfib_weq_local_opcleaving D)).
  unfold local_opfib.
  use impred ; intro x.
  use impred ; intro y.
  use impred ; intro xx.
  use impred ; intro yy.
  use (isofhlevelweqb 1 (opcleaving_weq_cleaving _)).
  use (@isaprop_cleaving (op_unicat (univ_hom HB x y))).
  apply is_univalent_op_disp_cat.
  apply is_univalent_disp_disp_hom.
  exact HD.
Defined.

(**
 3. Propositionality of global cleavings
 *)
Definition eq_cartesian_lift
           {B : bicat}
           (D : disp_bicat B)
           (HD : disp_univalent_2_1 D)
           {x y : B}
           {yy : D y}
           {f : x --> y}
           (ℓ₁ ℓ₂ : ∑ (xx : D x) (ff : xx -->[ f ] yy), cartesian_1cell D ff)
           (p₁ : pr1 ℓ₁ = pr1 ℓ₂)
           (p₂ : transportf (λ z, z -->[ f ] yy) p₁ (pr12 ℓ₁) = pr12 ℓ₂)
  : ℓ₁ = ℓ₂.
Proof.
  induction ℓ₁ as [ xx₁ [ ff₁ Hff₁ ]].
  induction ℓ₂ as [ xx₂ [ ff₂ Hff₂ ]].
  cbn in *.
  induction p₁ ; cbn in *.
  induction p₂ ; cbn in *.
  do 2 apply maponpaths.
  apply isaprop_cartesian_1cell.
  apply HD.
Defined.

Definition eq_cartesian_lift_from_adjequiv_transport
           {B : bicat}
           (HB : is_univalent_2 B)
           {D : disp_bicat B}
           (HD : disp_univalent_2 D)
           {x y : B}
           (f : x --> y)
           (yy : D y)
           {xx₁ xx₂ : D x}
           (p : xx₁ = xx₂)
           (ff : xx₂ -->[ f] yy)
  : transportb
      (λ z, z -->[ f ] yy)
      p
      ff
    =
    transportf
      (λ z, _ -->[ z ] _)
      (isotoid_2_1 (pr2 HB) (lunitor_invertible_2cell _))
      (disp_idtoiso_2_0 _ (idpath _) _ _ p ;; ff)%mor_disp.
Proof.
  induction p.
  cbn.
  refine (!_).
  refine (disp_isotoid_2_1
            _
            (pr2 HD)
            (isotoid_2_1 (pr2 HB) (lunitor_invertible_2cell f))
            _ _
            (transportf
               (λ z, disp_invertible_2cell z _ _)
               _
               (disp_invertible_2cell_lunitor ff))).
  use subtypePath.
  {
    intro.
    apply isaprop_is_invertible_2cell.
  }
  cbn.
  rewrite idtoiso_2_1_isotoid_2_1.
  apply idpath.
Qed.

Definition eq_cartesian_lift_from_adjequiv
           {B : bicat}
           (HB : is_univalent_2 B)
           (D : disp_bicat B)
           (HD : disp_univalent_2 D)
           {x y : B}
           {yy : D y}
           {f : x --> y}
           (ℓ₁ ℓ₂ : ∑ (xx : D x) (ff : xx -->[ f ] yy), cartesian_1cell D ff)
           (e : disp_adjoint_equivalence
                  (internal_adjoint_equivalence_identity x)
                  (pr1 ℓ₁)
                  (pr1 ℓ₂))
           (γ : disp_invertible_2cell
                  (lunitor_invertible_2cell _)
                  (e ;; pr12 ℓ₂)
                  (pr12 ℓ₁))
  : ℓ₁ = ℓ₂.
Proof.
  use eq_cartesian_lift.
  - apply HD.
  - exact (disp_isotoid_2_0 (pr1 HD) e).
  - pose (disp_isotoid_2_1
            _
            (pr2 HD)
            (isotoid_2_1 (pr2 HB) (lunitor_invertible_2cell _))
            _ _
            (transportb
               (λ z, disp_invertible_2cell z _ _)
               (idtoiso_2_1_isotoid_2_1 _ _)
               γ))
      as p.
    use (@transportf_transpose_left _ (λ z, z -->[ f ] yy)).
    refine (!_).
    refine (_ @ p) ; clear p.
    refine (eq_cartesian_lift_from_adjequiv_transport HB HD _ _ _ _ @ _).
    apply maponpaths.
    apply maponpaths_2.
    rewrite disp_idtoiso_2_0_isotoid_2_0.
    apply idpath.
Qed.

Definition isaprop_global_cleaving
           {B : bicat}
           (HB : is_univalent_2 B)
           (D : disp_bicat B)
           (HD : disp_univalent_2 D)
  : isaprop (global_cleaving D).
Proof.
  use impred ; intro x.
  use impred ; intro y.
  use impred ; intro xx.
  use impred ; intro f.
  use invproofirrelevance.
  intros ℓ₁ ℓ₂.
  use eq_cartesian_lift_from_adjequiv.
  - apply HB.
  - apply HD.
  - refine (map_between_cartesian_1cell (pr2 HB) (pr12 ℓ₁) (pr22 ℓ₂) ,, _).
    refine (transportf
              (λ z, disp_left_adjoint_equivalence z _)
              _
              (pr2 (disp_adj_equiv_between_cartesian_1cell (pr2 HB) (pr22 ℓ₁) (pr22 ℓ₂)))).
    use unique_internal_adjoint_equivalence.
    apply HB.
  - cbn.
    apply map_between_cartesian_1cell_commute.
Defined.
