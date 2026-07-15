(**

 Beck-Chevalley conditions for chosen pullbacks

 Beck-Chevalley conditions for dependent products are defined for arbitrary pullbacks. More
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
 equations. The second step is instantiating this statement to dependent products in fibrations,
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
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
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
          (HF : is_left_adjoint F)
          (HH : is_left_adjoint H)
          (HH' : is_left_adjoint H')
          (τ : nat_z_iso (G ∙ H) (F ∙ K))
          (τ' : nat_z_iso (G ∙ H') (F ∙ K'))
          (E : C₄ ⟶ C₄')
          (HE : adj_equivalence_of_cats E)
          (θH : nat_z_iso (H ∙ E) H')
          (θK : nat_z_iso (K ∙ E) K').

  Definition right_beck_chevalley_adj_equiv_equality
    : UU
    := ∏ (x : C₁), #E (τ x) · θK (F x) = θH (G x) · τ' x.

  Context (p : right_beck_chevalley_adj_equiv_equality).

  (**
     Notation for the components of the adjunctions
   *)
  Context (FR := right_adjoint HF)
          (η₁ := unit_from_left_adjoint HF)
          (ε₁ := counit_from_left_adjoint HF)
          (HR := right_adjoint HH)
          (η₂ := unit_from_left_adjoint HH)
          (ε₂ := counit_from_left_adjoint HH)
          (HR' := right_adjoint HH')
          (η₂' := unit_from_left_adjoint HH')
          (ε₂' := counit_from_left_adjoint HH')
          (E' := adj_equivalence_inv HE)
          (ηE := unit_nat_z_iso_from_adj_equivalence_of_cats HE)
          (εE := counit_nat_z_iso_from_adj_equivalence_of_cats HE).

  Let θH' : nat_z_iso H (H' ∙ E')
    := nat_z_iso_comp
         (pre_whisker_nat_z_iso H ηE)
         (post_whisker_nat_z_iso θH E').

  Lemma right_beck_chevalley_equiv_lemma_eq
        (x : C₃)
    : θH' x = ηE (H x) · #E' (θH x).
  Proof.
    apply idpath.
  Qed.

  Definition right_beck_chevalley_nat_trans_adj_equiv_iso
             (y : C₄)
    : HR' (E y) --> HR y.
  Proof.
    use (φ_adj (pr2 HH)).
    exact (θH' _ · #E' (ε₂' _) · nat_z_iso_inv ηE y).
  Defined.

  Proposition right_beck_chevalley_nat_trans_adj_equiv_iso_eq
              (y : C₄)
    : right_beck_chevalley_nat_trans_adj_equiv_iso y
      =
      η₂ (HR' _) · #HR (ηE (H (HR' _)) · #E' (θH _) · #E' (ε₂' _) · nat_z_iso_inv ηE y).
  Proof.
    apply idpath.
  Qed.

  Definition right_beck_chevalley_nat_trans_adj_equiv_inv
             (y : C₄)
    : HR y --> HR' (E y)
    := η₂' _ · #HR' (nat_z_iso_inv θH (HR y)) · #HR' (#E (ε₂ y)).

  Lemma right_beck_chevalley_nat_trans_adj_equiv_inv_left
        (y : C₄)
    : η₂' (HR y)
      · #HR' (inv_from_z_iso (nat_z_iso_pointwise_z_iso θH (HR y)))
      · #HR' (#E (ε₂ y))
      · η₂ (HR' (E y))
      · #HR (θH' (HR' (E y))
             · #E' (ε₂' (E y))
             · inv_from_z_iso (nat_z_iso_pointwise_z_iso ηE y))
      =
      identity _.
  Proof.
    rewrite right_beck_chevalley_equiv_lemma_eq.
    rewrite !functor_comp.
    rewrite !assoc.
    refine (!_).
    use (z_iso_inv_on_left _ _ _ _ (functor_on_z_iso HR (nat_z_iso_pointwise_z_iso ηE y))).
    cbn -[ε₂' η₂ η₂' ηE].
    rewrite id_left.
    rewrite !assoc'.
    etrans.
    {
      rewrite !assoc.
      do 3 apply maponpaths_2.
      apply (nat_trans_ax η₂ _ _ (_ · _)).
    }
    cbn -[ε₂' η₂ η₂' ηE].
    fold HR.
    refine (_ @ id_left _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (!(pr222 HH y : η₂ _ · #HR (ε₂ _) = _)).
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite <- !functor_comp.
    refine (!(functor_comp HR _ _) @ _).
    apply maponpaths.
    refine (nat_trans_ax ηE _ _ _ @ _).
    refine (!_).
    etrans.
    {
      rewrite !assoc.
      apply maponpaths_2.
      apply (nat_trans_ax ηE).
    }
    rewrite !assoc'.
    apply maponpaths.
    cbn -[ε₂' η₂ η₂' ηE].
    refine (!(functor_comp E' _ _) @ _).
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply (nat_trans_ax θH).
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply (functor_comp H').
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply (nat_trans_ax ε₂').
      }
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply (pr122 HH' (HR y)).
      }
      exact (id_left (_ · _)).
    }
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso θH (HR y))).
  Qed.

  Lemma right_beck_chevalley_nat_trans_adj_equiv_inv_right
        (y : C₄)
    : η₂ (HR' (E y))
      · #HR (θH' (HR' (E y))
             · #E' (ε₂' (E y))
             · inv_from_z_iso (nat_z_iso_pointwise_z_iso ηE y))
      · η₂' (HR y)
      · #HR' (nat_z_iso_inv θH (HR y))
      · #HR' (# E (ε₂ y))
      =
      identity _.
  Proof.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply (nat_trans_ax η₂' _ _ (_ · _) : _ · _ = _ · #HR' _).
    }
    rewrite !assoc'.
    refine (_ @ (pr222 HH' (E y) : η₂' _ · #HR' (ε₂' _) = _)).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      exact (!(functor_comp HR' _ _)).
    }
    refine (!(functor_comp HR' _ _) @ _).
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply functor_comp.
      }
      rewrite !assoc'.
      apply maponpaths.
      exact (nat_trans_ax (nat_z_iso_inv θH) _ _ _ : _ = _ · #E(#H _)).
    }
    etrans.
    {
      rewrite !assoc'.
      do 2 apply maponpaths.
      refine (!(functor_comp E) _ _ @ _).
      apply maponpaths.
      exact (nat_trans_ax ε₂ _ _ _ : _ = ε₂ _ · (_ · _)).
    }
    rewrite !functor_comp.
    rewrite !assoc.
    refine (!_).
    use (z_iso_inv_on_left _ _ _ _ (functor_on_z_iso E (nat_z_iso_pointwise_z_iso ηE y))).
    cbn -[ε₂' η₂ η₂' ηE nat_z_iso_inv].
    etrans.
    {
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply (nat_trans_ax (nat_z_iso_inv θH)).
      }
      rewrite !assoc'.
      apply maponpaths.
      refine (!(functor_comp E _ _) @ _).
      apply maponpaths.
      exact (pr122 HH (HR' (E y))).
    }
    rewrite functor_id.
    rewrite id_right.
    rewrite !assoc'.
    use (z_iso_inv_on_right _ _ _ (nat_z_iso_pointwise_z_iso θH (HR' (E y)))).
    cbn -[ε₂' η₂ η₂' ηE].
    etrans.
    {
      apply maponpaths_2.
      refine (functor_comp E _ _ @ _).
      apply maponpaths_2.
      pose proof (maponpaths
                    (λ z, z · inv_from_z_iso (nat_z_iso_pointwise_z_iso εE _))
                    (pr1 (pr221 HE) (H (HR' (E y)))))
        as q.
      refine (_ @ q).
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso εE _)).
      }
      apply id_right.
    }
    rewrite id_left.
    rewrite !assoc'.
    etrans.
    {
      rewrite <- !functor_comp.
      refine (!_).
      apply (nat_trans_ax (nat_z_iso_inv εE)).
    }
    refine (assoc' _ _ _ @ _).
    do 2 apply maponpaths.
    pose proof (maponpaths
                  (λ z, z · inv_from_z_iso (nat_z_iso_pointwise_z_iso εE _))
                  (pr1 (pr221 HE) y))
      as q.
    refine (_ @ !q @ _).
    - rewrite id_left.
      apply idpath.
    - rewrite assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      exact (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso εE _)).
  Qed.

  Proposition is_z_iso_right_beck_chevalley_nat_trans_adj_equiv_iso_laws
              (y : C₄)
    : is_inverse_in_precat
        (right_beck_chevalley_nat_trans_adj_equiv_iso y)
        (right_beck_chevalley_nat_trans_adj_equiv_inv y).
  Proof.
    split.
    - unfold right_beck_chevalley_nat_trans_adj_equiv_iso,
        right_beck_chevalley_nat_trans_adj_equiv_inv,
        φ_adj.
      refine (_ @ right_beck_chevalley_nat_trans_adj_equiv_inv_right y).
      rewrite !assoc.
      apply idpath.
    - unfold right_beck_chevalley_nat_trans_adj_equiv_iso,
        right_beck_chevalley_nat_trans_adj_equiv_inv,
        φ_adj.
      refine (_ @ right_beck_chevalley_nat_trans_adj_equiv_inv_left y).
      rewrite !assoc.
      apply idpath.
  Qed.

  Definition is_z_iso_right_beck_chevalley_nat_trans_adj_equiv_iso
             (y : C₄)
    : is_z_isomorphism (right_beck_chevalley_nat_trans_adj_equiv_iso y).
  Proof.
    use make_is_z_isomorphism.
    - exact (right_beck_chevalley_nat_trans_adj_equiv_inv y).
    - exact (is_z_iso_right_beck_chevalley_nat_trans_adj_equiv_iso_laws y).
  Defined.

  Lemma right_beck_chevalley_nat_trans_adj_equiv_eq_lemma
        (x : C₂)
    : η₂ (G (FR x))
      · #HR (τ (FR x))
      · #HR (# K (ε₁ x))
      =
      η₂' (G (FR x))
      · #HR' (τ' (FR x))
      · #HR' (# K' (ε₁ x))
      · #HR' (inv_from_z_iso (nat_z_iso_pointwise_z_iso θK x))
      · right_beck_chevalley_nat_trans_adj_equiv_iso (K x).
  Proof.
    refine (!_).
    rewrite right_beck_chevalley_nat_trans_adj_equiv_iso_eq.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      exact (nat_trans_ax η₂ _ _ (_ · _) : _ = _ · #HR (#H _)).
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!(functor_comp HR _ _) @ _ @ functor_comp HR _ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      apply right_beck_chevalley_equiv_lemma_eq.
    }
    rewrite <- !functor_comp.
    rewrite !assoc.
    refine (!_).
    use (z_iso_inv_on_left _ _ _ _ (nat_z_iso_pointwise_z_iso ηE (K x))).
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (nat_trans_ax ηE _ _ _ : _ = _ · #E' (#E (#H _))).
    }
    refine (!_).
    etrans.
    {
      exact (nat_trans_ax ηE _ _ (_ · _) : _ = _ · #E' (#E _)).
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!(functor_comp E' _ _)).
    }
    refine (!(functor_comp E' _ _) @ _).
    apply maponpaths.
    etrans.
    {
      rewrite !assoc.
      apply maponpaths_2.
      apply (nat_trans_ax θH).
    }
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply functor_comp.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        refine (!_).
        apply (functor_comp HR').
      }
      etrans.
      {
        apply maponpaths.
        exact (nat_trans_ax ε₂' _ _ _ : _ = _ · (_ · _)).
      }
      rewrite !assoc.
      etrans.
      {
        do 3 apply maponpaths_2.
        apply (pr122 HH').
      }
      rewrite id_left.
      apply idpath.
    }
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (!(p (FR x))).
    }
    rewrite !assoc'.
    rewrite functor_comp.
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply (nat_trans_ax θK).
    }
    rewrite !assoc'.
    refine (_ @ id_right _).
    apply maponpaths.
    exact (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso θK x)).
  Qed.

  Proposition right_beck_chevalley_nat_trans_adj_equiv_eq
              (x : C₂)
    : right_beck_chevalley_nat_trans HF HH τ x
      =
      right_beck_chevalley_nat_trans HF HH' τ' x
      · #HR' (inv_from_z_iso (nat_z_iso_pointwise_z_iso θK x))
      · right_beck_chevalley_nat_trans_adj_equiv_iso _.
  Proof.
    rewrite !right_beck_chevalley_nat_trans_ob.
    apply right_beck_chevalley_nat_trans_adj_equiv_eq_lemma.
  Qed.

  Proposition right_beck_chevalley_nat_trans_adj_equiv_eq'
              (x : C₂)
    : right_beck_chevalley_nat_trans HF HH' τ' x
      =
      right_beck_chevalley_nat_trans HF HH τ x
      · right_beck_chevalley_nat_trans_adj_equiv_inv _
      · #HR' (θK x).
  Proof.
    rewrite right_beck_chevalley_nat_trans_adj_equiv_eq.
    refine (!_).
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply is_z_iso_right_beck_chevalley_nat_trans_adj_equiv_iso_laws.
    }
    rewrite id_right.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (functor_comp HR').
    }
    rewrite z_iso_after_z_iso_inv.
    rewrite functor_id.
    apply id_right.
  Qed.

  Proposition right_beck_chevalley_adj_equiv
              {x : C₂}
              (Hx : is_z_isomorphism (right_beck_chevalley_nat_trans HF HH τ x))
    : is_z_isomorphism (right_beck_chevalley_nat_trans HF HH' τ' x).
  Proof.
    use (is_z_isomorphism_path (!(right_beck_chevalley_nat_trans_adj_equiv_eq' x))).
    use is_z_isomorphism_comp.
    - use is_z_isomorphism_comp.
      + exact Hx.
      + exact (is_z_iso_inv_from_z_iso
                 (_ ,, is_z_iso_right_beck_chevalley_nat_trans_adj_equiv_iso _)).
    - use functor_on_is_z_isomorphism.
      apply (nat_z_iso_pointwise_z_iso θK x).
  Defined.

  Proposition right_beck_chevalley_adj_equiv'
              {x : C₂}
              (Hx : is_z_isomorphism (right_beck_chevalley_nat_trans HF HH' τ' x))
    : is_z_isomorphism (right_beck_chevalley_nat_trans HF HH τ x).
  Proof.
    use (is_z_isomorphism_path (!(right_beck_chevalley_nat_trans_adj_equiv_eq x))).
    use is_z_isomorphism_comp.
    - use is_z_isomorphism_comp.
      + exact Hx.
      + use functor_on_is_z_isomorphism.
        apply (nat_z_iso_pointwise_z_iso (nat_z_iso_inv θK) x).
    - cbn.
      exact (is_z_iso_right_beck_chevalley_nat_trans_adj_equiv_iso (K x)).
  Defined.
End BeckChevalleyAdjEquiv.

(** * 2. The Beck-Chevalley condition for chosen pullbacks *)
Definition has_dependent_products_chosen
           {C : category}
           (PB : Pullbacks C)
           {D : disp_cat C}
           (HD : cleaving D)
  : UU
  := ∑ (R : ∏ (x y : C) (f : x --> y), dependent_product HD f),
     ∏ (w x y : C)
       (f : x --> w)
       (g : y --> w)
       (P := PB _ _ _ f g),
     right_beck_chevalley
       HD
       _ _ _ _
       (PullbackSqrCommutes _)
       (R _ _ f)
       (R _ _ (PullbackPr2 P)).

Definition make_has_dependent_products_chosen
           {C : category}
           (PB : Pullbacks C)
           {D : disp_cat C}
           (HD : cleaving D)
           (R : ∏ (x y : C) (f : x --> y), dependent_product HD f)
           (H : ∏ (w x y : C)
                  (f : x --> w)
                  (g : y --> w)
                  (P := PB _ _ _ f g),
                right_beck_chevalley
                  HD
                  _ _ _ _
                  (PullbackSqrCommutes _)
                  (R _ _ f)
                  (R _ _ (PullbackPr2 P)))
  : has_dependent_products_chosen PB HD
  := R ,, H.

Section DependentProdWithChosenPB.
  Context {C : category}
          (PB : Pullbacks C)
          {D : disp_cat C}
          (HD : cleaving D)
          (H : has_dependent_products_chosen PB HD)
          {w x y z : C}
          {f : x --> w}
          {g : y --> w}
          {h : z --> y}
          {k : z --> x}
          (p : k · f = h · g)
          (Hp : isPullback p).

  Let PBfg : Pullback f g := make_Pullback _ Hp.
  Let PBfg' : Pullback f g := PB w x y f g.

  Definition has_dependent_products_chosen_to_dependent_prod_adjequiv
    : D[{PBfg}] ⟶ D[{PBfg'}].
  Proof.
    use (fiber_functor_from_cleaving D HD).
    exact (z_iso_from_Pullback_to_Pullback (PB w x y f g) PBfg).
  Defined.

  Definition has_dependent_products_chosen_to_dependent_prod_left
    : nat_z_iso
        (fiber_functor_from_cleaving D HD h
         ∙ has_dependent_products_chosen_to_dependent_prod_adjequiv)
        (fiber_functor_from_cleaving D HD (PullbackPr2 (PB w x y f g))).
  Proof.
    refine (nat_z_iso_comp
              (fiber_functor_from_cleaving_comp_nat_z_iso HD _ _)
              (fiber_functor_on_eq_nat_z_iso HD _)).
    apply (PullbackArrow_PullbackPr2 PBfg).
  Defined.

  Definition has_dependent_products_chosen_to_dependent_prod_right
    : nat_z_iso
        (fiber_functor_from_cleaving D HD k
         ∙ has_dependent_products_chosen_to_dependent_prod_adjequiv)
        (fiber_functor_from_cleaving D HD (PullbackPr1 (PB w x y f g))).
  Proof.
    refine (nat_z_iso_comp
              (fiber_functor_from_cleaving_comp_nat_z_iso HD _ _)
              (fiber_functor_on_eq_nat_z_iso HD _)).
    apply (PullbackArrow_PullbackPr1 PBfg).
  Defined.

  Local Arguments transportf {X P x x' e} _.

  Proposition has_dependent_products_chosen_to_dependent_prod_eq
    : right_beck_chevalley_adj_equiv_equality
        (comm_nat_z_iso_inv HD f g h k p)
        (comm_nat_z_iso_inv HD _ _ _ _ (PullbackSqrCommutes (PB w x y f g)))
        has_dependent_products_chosen_to_dependent_prod_adjequiv
        has_dependent_products_chosen_to_dependent_prod_left
        has_dependent_products_chosen_to_dependent_prod_right.
  Proof.
    intro ww.
    cbn -[fiber_functor_from_cleaving_comp_nat_z_iso
            fiber_functor_on_eq_nat_z_iso
            fiber_functor_from_cleaving
            comm_nat_z_iso_inv].
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
      cbn -[comm_nat_z_iso_inv].
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
        apply comm_nat_z_iso_inv_ob.
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
      apply comm_nat_z_iso_inv_ob.
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
End DependentProdWithChosenPB.

Definition has_dependent_prods_chosen_to_dependent_prod
           {C : category}
           (PB : Pullbacks C)
           {D : disp_cat C}
           (HD : cleaving D)
           (H : has_dependent_products_chosen PB HD)
  : has_dependent_products HD.
Proof.
  refine (pr1 H ,, _).
  intros w x y z f g h k p Hp xx.
  pose (PBfg := make_Pullback _ Hp).
  pose (pr2 H w x y f g xx).
  simple refine (right_beck_chevalley_adj_equiv'
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
  - exact (has_dependent_products_chosen_to_dependent_prod_adjequiv PB HD p Hp).
  - apply fiber_functor_cleaving_of_z_iso_adj_equiv.
  - apply has_dependent_products_chosen_to_dependent_prod_left.
  - apply has_dependent_products_chosen_to_dependent_prod_right.
  - apply has_dependent_products_chosen_to_dependent_prod_eq.
Defined.
