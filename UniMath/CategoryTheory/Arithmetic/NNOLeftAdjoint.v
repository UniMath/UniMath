(**

 Left adjoints and NNOs

 Every left adjoint that preserves terminal objects maps natural numbes objects to natural
 numbers objects. We can use this as a method to construct natural numbers in some category.
 In this file, we give this construction.

 Content
 1. The natural numbers objects with zero and successor
 2. Recursion
 3. The NNO

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Arithmetic.NNO.

Local Open Scope cat.

Section LeftAdjointNNO.
  Context {C₁ C₂ : category}
          (R : C₁ ⟶ C₂)
          (HR : is_right_adjoint R)
          (L := left_adjoint HR)
          (η := unit_from_right_adjoint HR)
          (ε := counit_from_right_adjoint HR)
          (T₁ : Terminal C₁)
          (T₂ : Terminal C₂)
          (HT : preserves_terminal L)
          (N : NNO T₂).

  Let RT : preserves_terminal R
    := right_adjoint_preserves_terminal L (is_left_adjoint_left_adjoint HR).

  (** * 1. The natural numbers objects with zero and successor *)
  Definition left_adjoint_on_NNO_Z
    : T₁ --> L N
    := inv_from_z_iso (preserves_terminal_to_z_iso L HT T₂ T₁) · #L (zeroNNO _ N).

  Definition left_adjoint_on_NNO_S
    : L N --> L N
    := #L (sucNNO _ N).

  (** * 2. Recursion *)
  Section Recursion.
    Context {x : C₁}
            (zx : T₁ --> x)
            (sx : x --> x).

    Definition left_adjoint_on_NNO_rec
      : L N --> x.
    Proof.
      refine (#L _ · ε x).
      use NNO_mor.
      - refine (_ · #R zx).
        exact (inv_from_z_iso (preserves_terminal_to_z_iso R RT T₁ T₂)).
      - exact (#R sx).
    Defined.

    Proposition left_adjoint_on_NNO_rec_Z
      : left_adjoint_on_NNO_Z · left_adjoint_on_NNO_rec = zx.
    Proof.
      unfold left_adjoint_on_NNO_Z, left_adjoint_on_NNO_rec.
      cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- (functor_comp L).
        apply maponpaths.
        apply NNO_mor_Z.
      }
      rewrite functor_comp.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        exact (nat_trans_ax ε _ _ zx).
      }
      rewrite !assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply TerminalArrowEq.
    Qed.

    Proposition left_adjoint_on_NNO_rec_S
      : left_adjoint_on_NNO_S · left_adjoint_on_NNO_rec
        =
        left_adjoint_on_NNO_rec · sx.
    Proof.
      unfold left_adjoint_on_NNO_S, left_adjoint_on_NNO_rec.
      cbn.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        rewrite <- (functor_comp L).
        apply maponpaths.
        apply NNO_mor_S.
      }
      rewrite !functor_comp.
      rewrite !assoc'.
      apply maponpaths.
      exact (nat_trans_ax ε _ _ sx).
    Qed.

    Proposition left_adjoint_on_NNO_rec_unique
                {φ : L N --> x}
                (pz : left_adjoint_on_NNO_Z · φ = zx)
                (ps : left_adjoint_on_NNO_S · φ = φ · sx)
      : φ = left_adjoint_on_NNO_rec.
    Proof.
      refine (!(id_left _) @ _ @ id_left _).
      etrans.
      {
        apply maponpaths_2.
        exact (!(pr122 HR N) : _ = #L (η N) · ε (L N)).
      }
      etrans.
      {
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        exact (!(nat_trans_ax ε _ _ φ)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (!(pr122 HR N) : _ = #L (η N) · ε (L N)).
      }
      etrans.
      {
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        exact (!(nat_trans_ax ε _ _ left_adjoint_on_NNO_rec)).
      }
      rewrite !assoc.
      apply maponpaths_2.
      refine (!(functor_comp L _ (#R _)) @ _).
      refine (_ @ functor_comp L _ (#R _)).
      apply maponpaths.
      use NNO_mor_unique.
      - refine (_ · #R zx).
        exact (inv_from_z_iso (preserves_terminal_to_z_iso R RT T₁ T₂)).
      - exact (#R sx).
      - rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (nat_trans_ax η).
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!(functor_comp R _ _) @ _).
          apply maponpaths.
          unfold left_adjoint_on_NNO_rec.
          rewrite assoc.
          apply maponpaths_2.
          refine (!(functor_comp L _ _) @ _).
          apply maponpaths.
          apply NNO_mor_Z.
        }
        etrans.
        {
          do 2 apply maponpaths.
          rewrite functor_comp.
          rewrite !assoc'.
          apply maponpaths.
          apply (nat_trans_ax ε).
        }
        rewrite !functor_comp.
        rewrite !assoc.
        apply maponpaths_2.
        apply (TerminalArrowEq (T := preserves_terminal_to_terminal R RT T₁)).
      - rewrite <- pz.
        rewrite functor_comp.
        rewrite !assoc.
        apply maponpaths_2.
        unfold left_adjoint_on_NNO_Z.
        rewrite functor_comp.
        refine (nat_trans_ax η _ _ _ @ _).
        rewrite !assoc.
        apply maponpaths_2.
        apply (TerminalArrowEq
                 (T := preserves_terminal_to_terminal
                         _ RT
                         (preserves_terminal_to_terminal _ HT T₂))).
      - rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (nat_trans_ax η).
        }
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          refine (!(functor_comp R _ _) @ _).
          apply maponpaths.
          unfold left_adjoint_on_NNO_rec.
          rewrite assoc.
          apply maponpaths_2.
          refine (!(functor_comp L _ _) @ _).
          apply maponpaths.
          apply NNO_mor_S.
        }
        etrans.
        {
          apply maponpaths.
          rewrite functor_comp.
          rewrite !assoc'.
          apply maponpaths.
          apply (nat_trans_ax ε).
        }
        rewrite !functor_comp.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!(functor_comp R _ _) @ _).
        apply idpath.
      - rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply (nat_trans_ax η).
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!(functor_comp R _ _) @ _ @ functor_comp R _ _).
        apply maponpaths.
        exact ps.
    Qed.
  End Recursion.

  (** * 3. The NNO *)
  Definition left_adjoint_on_NNO
    : NNO T₁.
  Proof.
    use make_NNO.
    - exact (L N).
    - exact left_adjoint_on_NNO_Z.
    - exact left_adjoint_on_NNO_S.
    - intros x zx sx.
      use make_iscontr.
      + simple refine (_ ,, _ ,, _).
        * exact (left_adjoint_on_NNO_rec zx sx).
        * apply left_adjoint_on_NNO_rec_Z.
        * apply left_adjoint_on_NNO_rec_S.
      + abstract
          (intros [ φ [ pz ps ]] ;
           use subtypePath ;
           [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           cbn ;
           exact (left_adjoint_on_NNO_rec_unique zx sx pz ps)).
  Defined.
End LeftAdjointNNO.
