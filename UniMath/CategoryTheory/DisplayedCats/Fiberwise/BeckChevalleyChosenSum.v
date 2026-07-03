(**

 Beck-Chevalley conditions for chosen pullbacks (dependent sums)

 Beck-Chevalley conditions for dependent sums are defined for arbitrary pullbacks. More
 specifically, we express that some morphism is an isomorphism for every pullback square
 in the base. One can use a more convenient formulation in concrete examples, because in
 concrete examples one can take advantage from how the pullback are defined precisely.
 Rather than requiring the Beck-Chevalley for all pullback squares in the base, it suffices
 to only require the Beck-Chevalley condition for the chosen pullback squares. In this
 file, we prove this statement.

 The proof goes in two steps. First, we show that the Beck-Chevalley condition is
 preserved under adjoint equivalences. If one assumes univalence, then this follows
 immediately, but we need this statement for both univalent and non-univalent categories.
 The proof is a calculation using adjunctions, and it involves naturality and triangle
 equations. The second step is instantiating this statement to dependent sums in fibrations,
 and concluding that the Beck-Chevalley condition holds for all pullbacks if it holds for
 the chosen ones.

 Contents
 1. The Beck-Chevalley condition is preserved under adjoint equivalence
 2. The Beck-Chevalley condition for chosen pullbacks

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Reflections.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.MoreFibrations.FiberEquivalence.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

(** * 1. The Beck-Chevalley condition is preserved under adjoint equivalence *)
Section BeckChevalleyAdjEquiv.
  Context {C₁ C₂ C₃ C₄ C₄' : category}
          {F : C₁ ⟶ C₂}
          {G : C₁ ⟶ C₃}
          {H : C₃ ⟶ C₄}
          {K : C₂ ⟶ C₄}
          {H' : C₃ ⟶ C₄'}
          {K' : C₂ ⟶ C₄'}
          (HF : is_right_adjoint F)
          (HH : is_right_adjoint H)
          (HH' : is_right_adjoint H')
          (τ : nat_z_iso (F ∙ K) (G ∙ H))
          (τ' : nat_z_iso (F ∙ K') (G ∙ H'))
          (E : C₄ ⟶ C₄')
          (HE : adj_equivalence_of_cats E)
          (θH : nat_z_iso (H ∙ E) H')
          (θK : nat_z_iso (K ∙ E) K').

  Definition left_beck_chevalley_adj_equiv_equality
    : UU
    := ∏ (x : C₁), # E (τ x) · θH (G x) = θK (F x) · τ' x.

  Context (p : left_beck_chevalley_adj_equiv_equality).

  (**
     Notation for the components of the adjunctions
   *)
  Context (FL := left_adjoint HF)
          (η₁ := unit_from_right_adjoint HF)
          (ε₁ := counit_from_right_adjoint HF)
          (HL := left_adjoint HH)
          (η₂ := unit_from_right_adjoint HH)
          (ε₂ := counit_from_right_adjoint HH)
          (HL' := left_adjoint HH')
          (η₂' := unit_from_right_adjoint HH')
          (ε₂' := counit_from_right_adjoint HH')
          (E' := adj_equivalence_inv HE)
          (ηE := unit_nat_z_iso_from_adj_equivalence_of_cats HE)
          (εE := counit_nat_z_iso_from_adj_equivalence_of_cats HE).

  Let θH' : nat_z_iso (H' ∙ E') H
    := nat_z_iso_comp
         (post_whisker_nat_z_iso
            (nat_z_iso_inv θH)
            E')
         (pre_whisker_nat_z_iso H (nat_z_iso_inv ηE)).

  Lemma left_beck_chevalley_equiv_lemma_eq
        (x : C₃)
    : θH' x
      =
      #E' (inv_from_z_iso (nat_z_iso_pointwise_z_iso θH x))
      · inv_from_z_iso (nat_z_iso_pointwise_z_iso ηE (H x)).
  Proof.
    apply idpath.
  Qed.

  Definition left_beck_chevalley_nat_trans_adj_equiv_iso
             (y : C₄)
    : HL y --> HL' (E y).
  Proof.
    use (φ_adj_inv (pr2 HH)).
    exact (ηE _ · #E' (η₂' (E y)) · θH' _).
  Defined.

  Definition left_beck_chevalley_nat_trans_adj_equiv_inv
             (y : C₄)
    : HL' (E y) --> HL y.
  Proof.
    exact (#HL' (#E (η₂ _) · (θH (HL y))) · ε₂' (HL y)).
  Defined.

  Lemma left_beck_chevalley_nat_trans_adj_equiv_inv_left
        (y : C₄)
    : #HL' (#E (η₂ y) · θH (HL y))
      · ε₂' (HL y)
      · #HL (ηE y · #E' (η₂' (E y)) · θH' (HL' (E y)))
      · ε₂ (HL' (E y))
      =
      identity (HL' (E y)).
  Proof.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      exact (nat_trans_ax ε₂' _ _ (_ · _)).
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      exact (!(functor_comp HL' _ _)).
    }
    refine (_ @ pr122 HH' (E y)).
    apply maponpaths_2.
    apply maponpaths.
    rewrite (functor_comp H').
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      apply (nat_trans_ax θH).
    }
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (!(functor_comp E _ _)).
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply maponpaths.
      refine (!_).
      apply (nat_trans_ax η₂).
    }
    cbn -[ηE θH'].
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (nat_trans_ax θH).
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      exact (!(functor_comp E _ _)).
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths_2.
      do 4 apply maponpaths.
      apply (pr222 HH (HL' (E y))).
    }
    rewrite id_right.
    rewrite (functor_comp E (ηE y)).
    refine (_ @ id_left _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply (pr1 (pr221 HE)).
    }
    refine (!_).
    rewrite !assoc'.
    apply maponpaths.
    refine (!(id_left _) @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      exact (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso εE (E y))).
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite (functor_comp E).
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply (nat_trans_ax (nat_z_iso_inv εE)).
    }
    rewrite !assoc'.
    refine (_ @ id_right _).
    apply maponpaths.
    rewrite left_beck_chevalley_equiv_lemma_eq.
    rewrite functor_comp.
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply (nat_trans_ax (nat_z_iso_inv εE)).
    }
    refine (_ @ z_iso_after_z_iso_inv (nat_z_iso_pointwise_z_iso θH _)).
    apply maponpaths_2.
    refine (_ @ id_right _).
    rewrite !assoc'.
    apply maponpaths.
    rewrite functor_on_inv_from_z_iso.
    refine (!_).
    use z_iso_inv_on_left.
    rewrite id_left.
    refine (_ @ id_right _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      exact (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso εE _)).
    }
    refine (_ @ id_left _).
    rewrite !assoc.
    apply maponpaths_2.
    cbn -[εE ηE].
    exact (pr1 (pr221 HE) (H (HL' (E y)))) .
  Qed.

  Lemma left_beck_chevalley_nat_trans_adj_equiv_inv_right
        (y : C₄)
    : #HL (ηE y · #E' (η₂' (E y)) · θH' (HL' (E y)))
      · ε₂ (HL' (E y))
      · #HL' (#E (η₂ y) · θH (HL y))
      · ε₂' (HL y)
      =
      identity (HL y).
  Proof.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      apply (nat_trans_ax ε₂).
    }
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!(functor_comp HL _ _) @ _).
      apply maponpaths.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply (nat_trans_ax θH').
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply (functor_comp E').
        }
        apply maponpaths.
        refine (!_).
        apply (nat_trans_ax η₂').
      }
      rewrite !functor_comp.
      rewrite !assoc.
      etrans.
      {
        do 3 apply maponpaths_2.
        refine (!_).
        apply (nat_trans_ax ηE).
      }
      rewrite left_beck_chevalley_equiv_lemma_eq.
      rewrite !assoc'.
      do 2 apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- !functor_comp.
      apply idpath.
    }
    rewrite !(functor_comp HL).
    rewrite !assoc'.
    refine (_ @ pr122 HH y).
    apply maponpaths.
    etrans.
    {
      do 3 apply maponpaths.
      refine (!_).
      apply (nat_trans_ax ε₂).
    }
    refine (_ @ id_left _).
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- !(functor_comp HL).
    refine (!(functor_comp HL _ _) @ _).
    refine (_ @ functor_id HL _).
    apply maponpaths.
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply (nat_trans_ax (nat_z_iso_inv ηE)).
    }
    refine (_ @ z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso ηE _)).
    apply maponpaths.
    refine (_ @ id_left _).
    rewrite !assoc.
    apply maponpaths_2.
    refine (!(functor_comp E' _ _) @ _ @ functor_id E' _).
    apply maponpaths.
    cbn.
    refine (_ @ z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso θH _)).
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (nat_trans_ax (nat_z_iso_inv θH)).
    }
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply (pr2 HH').
  Qed.

  Proposition is_z_iso_left_beck_chevalley_nat_trans_adj_equiv_iso_laws
              (y : C₄)
    : is_inverse_in_precat
        (left_beck_chevalley_nat_trans_adj_equiv_iso y)
        (left_beck_chevalley_nat_trans_adj_equiv_inv y).
  Proof.
    split.
    - unfold left_beck_chevalley_nat_trans_adj_equiv_iso,
        left_beck_chevalley_nat_trans_adj_equiv_inv,
        φ_adj_inv.
      refine (_ @ left_beck_chevalley_nat_trans_adj_equiv_inv_right y).
      rewrite !assoc.
      apply idpath.
    - unfold left_beck_chevalley_nat_trans_adj_equiv_iso,
        left_beck_chevalley_nat_trans_adj_equiv_inv,
        φ_adj_inv.
      refine (_ @ left_beck_chevalley_nat_trans_adj_equiv_inv_left y).
      rewrite !assoc.
      apply idpath.
  Qed.

  Definition is_z_iso_left_beck_chevalley_nat_trans_adj_equiv_iso
             (y : C₄)
    : is_z_isomorphism (left_beck_chevalley_nat_trans_adj_equiv_iso y).
  Proof.
    use make_is_z_isomorphism.
    - exact (left_beck_chevalley_nat_trans_adj_equiv_inv y).
    - exact (is_z_iso_left_beck_chevalley_nat_trans_adj_equiv_iso_laws y).
  Defined.

  Lemma left_beck_chevalley_nat_trans_adj_equiv_eq_lemma
        (x : C₂)
    : #HL (#K (η₁ x))
      · #HL (τ (FL x))
      · ε₂ (G (FL x))
      =
      #HL (ηE (K x) · #E' (η₂' (E (K x))) · θH' (HL' (E (K x))))
      · ε₂ (HL' (E (K x)))
      · #HL' (θK x)
      · #HL' (# K' (η₁ x))
      · #HL' (τ' (FL x))
      · ε₂' (G (FL x)).
  Proof.
    refine (!_).
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (functor_comp HL').
        }
        refine (!_).
        apply (functor_comp HL').
      }
      refine (!_).
      exact (nat_trans_ax
               ε₂
               _ _
               (#HL' (θK x · #K' (η₁ x) · τ' (FL x)) · ε₂' (G (FL x)))).
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- functor_comp.
    etrans.
    {
      refine (!_).
      apply (functor_comp HL).
    }
    apply maponpaths.
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply (nat_trans_ax θH').
    }
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        refine (!_).
        apply (functor_comp E').
      }
      apply maponpaths.
      rewrite (functor_comp H').
      rewrite assoc.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (nat_trans_ax η₂').
      }
      refine (assoc' (_ · _) _ _ @ _).
      apply maponpaths.
      apply (pr2 HH').
    }
    rewrite id_right.
    etrans.
    {
      rewrite assoc.
      apply maponpaths_2.
      rewrite functor_comp.
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply (nat_trans_ax θK).
      }
      rewrite functor_comp.
      rewrite assoc.
      apply maponpaths_2.
      refine (!_).
      apply (nat_trans_ax ηE).
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite left_beck_chevalley_equiv_lemma_eq.
    rewrite !assoc.
    refine (!_).
    use z_iso_inv_on_left.
    rewrite functor_on_inv_from_z_iso.
    refine (!_).
    use z_iso_inv_on_left.
    cbn -[ηE].
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply (nat_trans_ax ηE).
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!(functor_comp E' _ _) @ _ @ functor_comp E' _ _).
    apply maponpaths.
    apply p.
  Qed.

  Proposition left_beck_chevalley_nat_trans_adj_equiv_eq
              (x : C₂)
    : left_beck_chevalley_nat_trans HF HH τ x
      =
      left_beck_chevalley_nat_trans_adj_equiv_iso _
      · #HL' (θK x)
      · left_beck_chevalley_nat_trans HF HH' τ' x.
  Proof.
    rewrite !left_beck_chevalley_nat_trans_ob.
    rewrite !assoc.
    apply left_beck_chevalley_nat_trans_adj_equiv_eq_lemma.
  Qed.

  Proposition left_beck_chevalley_nat_trans_adj_equiv_eq'
              (x : C₂)
    : left_beck_chevalley_nat_trans HF HH' τ' x
      =
      #HL' (inv_from_z_iso (nat_z_iso_pointwise_z_iso θK x))
      · left_beck_chevalley_nat_trans_adj_equiv_inv _
      · left_beck_chevalley_nat_trans HF HH τ x.
  Proof.
    rewrite left_beck_chevalley_nat_trans_adj_equiv_eq.
    refine (!_).
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      apply is_z_iso_left_beck_chevalley_nat_trans_adj_equiv_iso_laws.
    }
    rewrite id_left.
    rewrite !assoc.
    rewrite <- functor_comp.
    rewrite z_iso_after_z_iso_inv.
    rewrite functor_id.
    apply id_left.
  Qed.

  Proposition left_beck_chevalley_adj_equiv
              {x : C₂}
              (Hx : is_z_isomorphism (left_beck_chevalley_nat_trans HF HH τ x))
    : is_z_isomorphism (left_beck_chevalley_nat_trans HF HH' τ' x).
  Proof.
    use (is_z_isomorphism_path (!(left_beck_chevalley_nat_trans_adj_equiv_eq' x))).
    use is_z_isomorphism_comp.
    - use is_z_isomorphism_comp.
      + use functor_on_is_z_isomorphism.
        apply is_z_iso_inv_from_z_iso.
      + exact (is_z_iso_inv_from_z_iso
                 (_ ,, is_z_iso_left_beck_chevalley_nat_trans_adj_equiv_iso _)).
    - exact Hx.
  Defined.

  Proposition left_beck_chevalley_adj_equiv'
              {x : C₂}
              (Hx : is_z_isomorphism (left_beck_chevalley_nat_trans HF HH' τ' x))
    : is_z_isomorphism (left_beck_chevalley_nat_trans HF HH τ x).
  Proof.
    use (is_z_isomorphism_path (!(left_beck_chevalley_nat_trans_adj_equiv_eq x))).
    use is_z_isomorphism_comp.
    - use is_z_isomorphism_comp.
      + apply is_z_iso_left_beck_chevalley_nat_trans_adj_equiv_iso.
      + use functor_on_is_z_isomorphism.
        apply (nat_z_iso_pointwise_z_iso θK x).
    - exact Hx.
  Defined.
End BeckChevalleyAdjEquiv.

(** * 2. The Beck-Chevalley condition for chosen pullbacks *)
Definition has_dependent_sums_chosen
           {C : category}
           (PB : Pullbacks C)
           {D : disp_cat C}
           (HD : cleaving D)
  : UU
  := ∑ (L : ∏ (x y : C) (f : x --> y), dependent_sum HD f),
     ∏ (w x y : C)
       (f : x --> w)
       (g : y --> w)
       (P := PB _ _ _ f g),
     left_beck_chevalley
       HD
       _ _ _ _
       (PullbackSqrCommutes _)
       (L _ _ f)
       (L _ _ (PullbackPr2 P)).

Definition make_has_dependent_sums_chosen
           {C : category}
           (PB : Pullbacks C)
           {D : disp_cat C}
           (HD : cleaving D)
           (L : ∏ (x y : C) (f : x --> y), dependent_sum HD f)
           (H : ∏ (w x y : C)
                  (f : x --> w)
                  (g : y --> w)
                  (P := PB _ _ _ f g),
                left_beck_chevalley
                  HD
                  _ _ _ _
                  (PullbackSqrCommutes _)
                  (L _ _ f)
                  (L _ _ (PullbackPr2 P)))
  : has_dependent_sums_chosen PB HD
  := L ,, H.

Section DependentSumWithChosenPB.
  Context {C : category}
          (PB : Pullbacks C)
          {D : disp_cat C}
          (HD : cleaving D)
          (H : has_dependent_sums_chosen PB HD)
          {w x y z : C}
          {f : x --> w}
          {g : y --> w}
          {h : z --> y}
          {k : z --> x}
          (p : k · f = h · g)
          (Hp : isPullback p).

  Let PBfg : Pullback f g := make_Pullback _ Hp.
  Let PBfg' : Pullback f g := PB w x y f g.

  Definition has_dependent_sums_chosen_to_dependent_sum_adjequiv
    : D[{PBfg}] ⟶ D[{PBfg'}].
  Proof.
    use (fiber_functor_from_cleaving D HD).
    exact (z_iso_from_Pullback_to_Pullback (PB w x y f g) PBfg).
  Defined.

  Definition has_dependent_sums_chosen_to_dependent_sum_left
    : nat_z_iso
        (fiber_functor_from_cleaving D HD h
         ∙ has_dependent_sums_chosen_to_dependent_sum_adjequiv)
        (fiber_functor_from_cleaving D HD (PullbackPr2 (PB w x y f g))).
  Proof.
    refine (nat_z_iso_comp
              (fiber_functor_from_cleaving_comp_nat_z_iso HD _ _)
              (fiber_functor_on_eq_nat_z_iso HD _)).
    apply (PullbackArrow_PullbackPr2 PBfg).
  Defined.

  Definition has_dependent_sums_chosen_to_dependent_sum_right
    : nat_z_iso
        (fiber_functor_from_cleaving D HD k
         ∙ has_dependent_sums_chosen_to_dependent_sum_adjequiv)
        (fiber_functor_from_cleaving D HD (PullbackPr1 (PB w x y f g))).
  Proof.
    refine (nat_z_iso_comp
              (fiber_functor_from_cleaving_comp_nat_z_iso HD _ _)
              (fiber_functor_on_eq_nat_z_iso HD _)).
    apply (PullbackArrow_PullbackPr1 PBfg).
  Defined.

  Local Arguments transportf {X P x x' e} _.

  Proposition has_dependent_sums_chosen_to_dependent_sum_eq
    : left_beck_chevalley_adj_equiv_equality
        (comm_nat_z_iso HD f g h k p)
        (comm_nat_z_iso HD _ _ _ _ (PullbackSqrCommutes PBfg'))
        has_dependent_sums_chosen_to_dependent_sum_adjequiv
        has_dependent_sums_chosen_to_dependent_sum_left
        has_dependent_sums_chosen_to_dependent_sum_right.
  Proof.
    intro ww.
    cbn -[fiber_functor_from_cleaving_comp_nat_z_iso
            fiber_functor_on_eq_nat_z_iso
            fiber_functor_from_cleaving comm_nat_z_iso].
    rewrite mor_disp_transportf_prewhisker.
    rewrite mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    use (cartesian_factorisation_unique
           (cartesian_lift_is_cartesian _ _ (HD _ _ _ _))).
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !assoc_disp_var.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    etrans.
    {
      do 3 apply maponpaths.
      apply fiber_functor_on_eq_comm.
    }
    rewrite !mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    etrans.
    {
      do 2 apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    unfold transportb.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    etrans.
    {
      cbn -[comm_nat_z_iso].
      rewrite !assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        apply comm_nat_z_iso_ob.
      }
      cbn -[fiber_functor_on_eq].
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite !assoc_disp_var.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      do 4 apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths.
      apply maponpaths_2.
      apply comm_nat_z_iso_ob.
    }
    etrans.
    {
      cbn -[fiber_functor_on_eq].
      unfold transportb.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite !assoc_disp_var.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      do 5 apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    use (cartesian_factorisation_unique
           (cartesian_lift_is_cartesian _ _ (HD _ _ _ _))).
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !assoc_disp_var.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    etrans.
    {
      do 5 apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    etrans.
    {
      do 4 apply maponpaths.
      apply fiber_functor_on_eq_comm.
    }
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc_disp.
      apply maponpaths.
      apply maponpaths_2.
      apply fiber_functor_on_eq_comm.
    }
    unfold transportb.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    etrans.
    {
      rewrite !assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      apply idpath.
    }
    refine (!_).
    rewrite cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    etrans.
    {
      do 3 apply maponpaths.
      apply fiber_functor_on_eq_comm.
    }
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    rewrite !assoc_disp_var.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.
End DependentSumWithChosenPB.

Definition has_dependent_sums_chosen_to_dependent_sum
           {C : category}
           (PB : Pullbacks C)
           {D : disp_cat C}
           (HD : cleaving D)
           (H : has_dependent_sums_chosen PB HD)
  : has_dependent_sums HD.
Proof.
  refine (pr1 H ,, _).
  intros w x y z f g h k p Hp xx.
  pose (PBfg := make_Pullback _ Hp).
  simple refine (left_beck_chevalley_adj_equiv'
                   _
                   _
                   _
                   _
                   _
                   _
                   _
                   _
                   _
                   _
                   (pr2 H w x y f g xx)).
  - exact (has_dependent_sums_chosen_to_dependent_sum_adjequiv PB HD p Hp).
  - apply fiber_functor_cleaving_of_z_iso_adj_equiv.
  - apply has_dependent_sums_chosen_to_dependent_sum_left.
  - apply has_dependent_sums_chosen_to_dependent_sum_right.
  - apply has_dependent_sums_chosen_to_dependent_sum_eq.
Defined.
