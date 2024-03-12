(***********************************************************************************

 Iterated slice categories

 The slice construction can be iterated. More specifically, if we have a category `C`,
 an object `y : C`, and a morphism `f : x --> y`, then we can consider the slice
 category `C/y/f`. This slice category is equivalent to a simpler one, namely `C/x`.
 In this file, we construct this equivalence. In addition, if `C` has pullbacks, then
 we characterize the fiber functor of the iterated slice category via the fiber functor
 of the ordinary slice category. This allows us to conclude that preservation of colimits
 for the pullback functor of the iterated slice category follows from preservation of
 colimits for the pullback functor of ordinary slice categories

 Contents
 1. Iterated slice categories
 2. Pullbacks in iterated slice categories
 3. Preservation of colimits by pullback in the iterated slice

 ***********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.PreservationProperties.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodColimits.

Local Open Scope cat.

(** * 1. Iterated slice categories *)
Section IteratedSlice.
  Context {C : category}
          {y : C}
          (xf : C/y).

  Let x : C := cod_dom xf.
  Let f : x --> y := cod_mor xf.

  Definition from_iterated_slice_data
    : functor_data (C/y/xf) (C/x).
  Proof.
    use make_functor_data.
    - exact (λ h, make_cod_fib_ob (dom_mor (cod_mor h))).
    - simple refine (λ h₁ h₂ p, make_cod_fib_mor _ _).
      + exact (dom_mor (dom_mor p)).
      + abstract
          (cbn ;
           pose (maponpaths pr1 (mor_eq p)) as q ;
           cbn in q ;
           rewrite transportf_cod_disp in q ;
           exact q).
  Defined.

  Proposition is_functor_from_iterated_slice_data
    : is_functor from_iterated_slice_data.
  Proof.
    split.
    - intros h.
      use eq_mor_cod_fib ; cbn.
      apply idpath.
    - intros h₁ h₂ h₃ p q.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      simpl.
      etrans.
      {
        apply maponpaths.
        apply comp_in_cod_fib.
      }
      rewrite comp_in_cod_fib.
      apply idpath.
  Qed.

  Definition from_iterated_slice
    : (C/y/xf) ⟶ (C/x).
  Proof.
    use make_functor.
    - exact from_iterated_slice_data.
    - exact is_functor_from_iterated_slice_data.
  Defined.

  Definition to_iterated_slice_data
    : functor_data (C / x) (C / y / xf).
  Proof.
    use make_functor_data.
    - simple refine (λ h, make_cod_fib_ob _).
      + use make_cod_fib_ob.
        * exact (cod_dom h).
        * exact (cod_mor h · f).
      + use make_cod_fib_mor.
        * exact (cod_mor h).
        * abstract
            (cbn ;
             apply idpath).
    - simple refine (λ h₁ h₂ p, make_cod_fib_mor _ _).
      + use make_cod_fib_mor.
        * exact (dom_mor p).
        * abstract
            (cbn ;
             rewrite !assoc ;
             rewrite (mor_eq p) ;
             apply idpath).
      + abstract
          (use eq_mor_cod_fib ;
           rewrite comp_in_cod_fib ;
           cbn ;
           exact (mor_eq p)).
  Defined.

  Proposition is_functor_to_iterated_slice_data
    : is_functor to_iterated_slice_data.
  Proof.
    split.
    - intros h.
      use eq_mor_cod_fib.
      use eq_mor_cod_fib ; cbn.
      apply idpath.
    - intros h₁ h₂ h₃ p q.
      use eq_mor_cod_fib.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      etrans.
      {
        simpl.
        apply comp_in_cod_fib.
      }
      refine (!_).
      etrans.
      {
        apply comp_in_cod_fib.
      }
      cbn.
      apply idpath.
  Qed.

  Definition to_iterated_slice
    : (C/x) ⟶ (C/y/xf).
  Proof.
    use make_functor.
    - exact to_iterated_slice_data.
    - exact is_functor_to_iterated_slice_data.
  Defined.

  Definition iterated_slice_unit
    : functor_identity _
      ⟹
      from_iterated_slice ∙ to_iterated_slice.
  Proof.
    use make_nat_trans.
    - simple refine (λ h, make_cod_fib_mor _ _).
      + use make_cod_fib_mor.
        * apply identity.
        * abstract
            (cbn ;
             rewrite id_left ;
             exact (mor_eq (cod_mor h))).
      + abstract
          (use eq_mor_cod_fib ;
           rewrite comp_in_cod_fib ;
           cbn ;
           apply id_left).
    - abstract
        (intros h₁ h₂ p ;
         use eq_mor_cod_fib ;
         use eq_mor_cod_fib ;
         rewrite !comp_in_cod_fib ;
         cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Definition iterated_slice_counit
    : to_iterated_slice ∙ from_iterated_slice
      ⟹
      functor_identity _.
  Proof.
    use make_nat_trans.
    - simple refine (λ h, make_cod_fib_mor _ _).
      + apply identity.
      + abstract
          (cbn ;
           apply id_left).
    - abstract
        (intros h₁ h₂ p ;
         use eq_mor_cod_fib ;
         rewrite !comp_in_cod_fib ;
         cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Definition iterated_slice_equivalence_of_cats
    : equivalence_of_cats (C/y/xf) (C/x).
  Proof.
    use make_equivalence_of_cats.
    - use make_adjunction_data.
      + exact from_iterated_slice.
      + exact to_iterated_slice.
      + exact iterated_slice_unit.
      + exact iterated_slice_counit.
    - use make_forms_equivalence.
      + intro h.
        use is_z_iso_fiber_from_is_z_iso_disp.
        use is_z_iso_disp_codomain.
        use is_z_iso_fiber_from_is_z_iso_disp.
        use is_z_iso_disp_codomain.
        cbn.
        apply is_z_isomorphism_identity.
      + intro h.
        use is_z_iso_fiber_from_is_z_iso_disp.
        use is_z_iso_disp_codomain.
        cbn.
        apply is_z_isomorphism_identity.
  Defined.

  Definition from_iterated_slice_adj_equivalence_of_cats
    : adj_equivalence_of_cats from_iterated_slice
    := adjointification iterated_slice_equivalence_of_cats.
End IteratedSlice.

(** * 2. Pullbacks in iterated slice categories *)
Section IteratedSlicePB.
  Context {C : category}
          (PB : Pullbacks C)
          {y₁ y₂ : C}
          {xf₁ xf₂ : C/y₁}
          (h : xf₁ --> xf₂).

  Let PB₁ : Pullbacks (C/y₁) := codomain_fiberwise_pullbacks PB _.

  Definition iterated_slice_pb_nat_trans_data
    : nat_trans_data
        (cod_pb PB₁ h ∙ from_iterated_slice xf₁)
        (from_iterated_slice xf₂ ∙ cod_pb PB (dom_mor h)).
  Proof.
    intros g.
    use make_cod_fib_mor.
    - apply identity.
    - abstract
        (apply id_left).
  Defined.

  Proposition iterated_slice_pb_nat_trans_laws
    : is_nat_trans _ _ iterated_slice_pb_nat_trans_data.
  Proof.
    intros g₁ g₂ p.
    use eq_mor_cod_fib.
    rewrite !comp_in_cod_fib.
    refine (id_right _ @ _ @ !(id_left _)).
    cbn -[cod_pb].
    etrans.
    {
      apply maponpaths.
      exact (maponpaths dom_mor (cod_fiber_functor_on_mor PB₁ h p)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (cod_fiber_functor_on_mor PB (dom_mor h) _).
    }
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    - refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _ @ !(PullbackArrow_PullbackPr1 _ _ _ _ _)).
      rewrite comp_in_cod_fib.
      cbn.
      apply idpath.
    - exact (PullbackArrow_PullbackPr2 _ _ _ _ _ @ !(PullbackArrow_PullbackPr2 _ _ _ _ _)).
  Qed.

  Definition iterated_slice_pb_nat_trans
    : cod_pb PB₁ h ∙ from_iterated_slice xf₁
      ⟹
      from_iterated_slice xf₂ ∙ cod_pb PB (dom_mor h).
  Proof.
    use make_nat_trans.
    - exact iterated_slice_pb_nat_trans_data.
    - exact iterated_slice_pb_nat_trans_laws.
  Defined.

  Definition iterated_slice_pb_nat_z_iso
    : nat_z_iso
        (cod_pb PB₁ h ∙ from_iterated_slice xf₁)
        (from_iterated_slice xf₂ ∙ cod_pb PB (dom_mor h)).
  Proof.
    use make_nat_z_iso.
    - exact iterated_slice_pb_nat_trans.
    - intro k.
      use is_z_iso_fiber_from_is_z_iso_disp.
      use is_z_iso_disp_codomain.
      cbn.
      apply is_z_isomorphism_identity.
  Defined.

  (** * 3. Preservation of colimits by pullback in the iterated slice *)
  Definition preserves_initial_cod_pb_iterated
             (H : preserves_initial (cod_pb PB (dom_mor h)))
    : preserves_initial (cod_pb PB₁ h)
    := preserves_initial_equivalence_b
         _ _
         (from_iterated_slice_adj_equivalence_of_cats _)
         (from_iterated_slice_adj_equivalence_of_cats _)
         (cod_pb PB₁ h)
         (cod_pb PB (dom_mor h))
         iterated_slice_pb_nat_z_iso
         H.

  Definition preserves_bincoproduct_cod_pb_iterated
             (H : preserves_bincoproduct (cod_pb PB (dom_mor h)))
    : preserves_bincoproduct (cod_pb PB₁ h)
    := preserves_bincoproduct_equivalence_b
         _ _
         (from_iterated_slice_adj_equivalence_of_cats _)
         (from_iterated_slice_adj_equivalence_of_cats _)
         (cod_pb PB₁ h)
         (cod_pb PB (dom_mor h))
         iterated_slice_pb_nat_z_iso
         H.
End IteratedSlicePB.
