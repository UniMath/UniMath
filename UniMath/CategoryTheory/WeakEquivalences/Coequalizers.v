(**

   Behaviour Of Weak Equivalences And Coequalizers

   In this file, we show that weak equivalences preserve and reflect coequalizers.
   Furthermore, we show that the transport of a coequalizer preservation functor, along a weak equivalence, is again coequalizer preserving.

   Contents.
   1. Preservation [weak_equiv_preserves_coequalizers, weak_equiv_preserves_chosen_coequalizers]
   2. Reflection [weak_equiv_reflects_coequalizers]
   3. Lift Preservation [weak_equiv_lifts_preserves_coequalizers]

   Remark: These results are an immediate consequence of the fact that the dual statement hold and that the opposite of a weak equivalence is again a weak equivalence.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Opp.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Opp.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Equalizers.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Equalizers.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.Equalizers.

Local Open Scope cat.

(** * 1. Preservation *)
Proposition weak_equiv_preserves_coequalizers
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F)
  : preserves_coequalizer F.
Proof.
  use (invweq (preserves_coequalizer_opp F)).
  use weak_equiv_preserves_equalizers.
  apply opp_is_weak_equiv.
  exact Fw.
Qed.

Corollary weak_equiv_preserves_chosen_coequalizers
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F) (BE : Coequalizers C)
  : preserves_chosen_coequalizer BE F.
Proof.
  intros x y f g p.
  use (weak_equiv_preserves_coequalizers Fw).
  - apply CoequalizerEqAr.
  - apply isCoequalizer_Coequalizer.
Qed.

(** * 2. Reflection *)
Section WeakEquivReflectsCoequalizers.

  Context
    {C D : category}
      {F : C ⟶ D} (Fw : is_weak_equiv F)
      {x y e : C}
      {f₁ f₂ : C⟦x, y⟧}
      {h : C⟦y, e⟧}
      {p : f₁ · h = f₂ · h}.

  Local Definition p_func : # F f₁ · # F h = # F f₂ · # F h.
  Proof.
    do 2 rewrite <- functor_comp.
    apply maponpaths.
    exact p.
  Qed.
  Lemma weak_equiv_reflects_coequalizers
    : isCoequalizer (#F f₁) (#F f₂) (#F h) p_func → isCoequalizer f₁ f₂ h p.
  Proof.
    intro F_coeq.
    use (weak_equiv_reflects_equalizers (opp_is_weak_equiv Fw)).
    { apply p. }
    apply F_coeq.
  Qed.

End WeakEquivReflectsCoequalizers.

(** * 3. Lift Preservation *)
Section WeakEquivLiftPreservationCoequalizers.

  Context {C1 : category}
    (C2 C3 : univalent_category)
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (Gw : is_weak_equiv G)
    (Feq : preserves_coequalizer F).

  Let oC₂ : univalent_category
      := C2^opp ,, op_is_univalent C2.
  Let oC₃ : univalent_category
      := C3^opp ,, op_is_univalent C3.

  Proposition weak_equiv_lifts_preserves_coequalizers
    : preserves_coequalizer H.
  Proof.
    use (invweq (preserves_coequalizer_opp H)).
    set (oF_pe := pr1weq (preserves_coequalizer_opp F) Feq).
    use (weak_equiv_lifts_preserves_equalizers oC₂ oC₃
           (F := functor_op F) _ (opp_is_weak_equiv Gw) oF_pe).
    exact (nat_z_iso_inv (make_nat_z_iso _ _ _ (op_nt_is_z_iso α (pr2 α)))).
  Qed.

End WeakEquivLiftPreservationCoequalizers.
