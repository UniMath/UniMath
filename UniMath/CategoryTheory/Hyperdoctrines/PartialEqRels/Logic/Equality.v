(**

 Equality formulas

 We show how to interpret equality in the category of partial equivalence relations valued
 in a first order hyperdoctrine. The key idea is to interpret equality as the equivalence
 relation of a partial setoid.

 Content
 1. The equality formula
 2. Reflexivity
 3. Elimination of equality

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERBinProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.Logic.SubobjectDispCat.

Local Open Scope cat.
Local Open Scope hd.

(** * 1. The equality formula *)
Definition per_subobject_eq_form
           {H : first_order_hyperdoctrine}
           {A : partial_setoid H}
           (φ : per_subobject A)
  : form (prod_partial_setoid A A)
  := let a₁ := π₁ (tm_var (A ×h A)) in
     let a₂ := π₂ (tm_var (A ×h A)) in
     a₁ ~ a₂ ∧ φ [ a₁ ].

Arguments per_subobject_eq_form /.

Proposition per_subobject_eq_form_laws
            {H : first_order_hyperdoctrine}
            {A : partial_setoid H}
            (φ : per_subobject A)
  : per_subobject_laws (per_subobject_eq_form φ).
Proof.
  split.
  - cbn.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    hypersimplify.
    cbn.
    pose (Γ := 𝟙 ×h A ×h A).
    pose (a₁ := π₁ (π₂ (tm_var Γ))).
    pose (a₂ := π₂ (π₂ (tm_var Γ))).
    fold Γ a₁ a₂.
    use eq_in_prod_partial_setoid.
    + fold a₁ a₂.
      use weaken_left.
      exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
    + fold a₁ a₂.
      use weaken_left.
      exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
  - cbn.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    hypersimplify.
    cbn.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      exact (from_eq_in_prod_partial_setoid _ _ (hyperdoctrine_hyp _)).
    }
    use hyp_ltrans.
    use weaken_right.
    pose (Γ := (𝟙 ×h A ×h A) ×h A ×h A).
    pose (a₁ := π₁ (π₂ (tm_var Γ))).
    pose (a₂ := π₂ (π₂ (tm_var Γ))).
    pose (b₁ := π₁ (π₂ (π₁ (tm_var Γ)))).
    pose (b₂ := π₂ (π₂ (π₁ (tm_var Γ)))).
    fold Γ a₁ a₂ b₁ b₂.
    use conj_intro.
    + refine (partial_setoid_trans _ _ _).
      {
        use partial_setoid_sym.
        use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
      }
      refine (partial_setoid_trans _ _ _).
      {
        do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      }
      do 2 use weaken_right.
      apply hyperdoctrine_hyp.
    + refine (per_subobject_eq _ _ _).
      * use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
      * use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
Qed.

Definition per_subobject_equality
           {H : first_order_hyperdoctrine}
           {A : partial_setoid H}
           (φ : per_subobject A)
  : per_subobject (prod_partial_setoid A A).
Proof.
  use make_per_subobject.
  - exact (per_subobject_eq_form φ).
  - exact (per_subobject_eq_form_laws φ).
Defined.

(** * 2. Reflexivity *)
Proposition per_subobject_equality_refl
            {H : first_order_hyperdoctrine}
            {A : partial_setoid H}
            (φ : per_subobject A)
  : per_subobject_mor_law
      (id_partial_setoid_morphism A)
      φ
      (per_subobject_subst
         (pair_partial_setoid_morphism
            (id_partial_setoid_morphism A)
            (id_partial_setoid_morphism A))
         (per_subobject_equality φ)).
Proof.
  do 2 use forall_intro.
  use impl_intro.
  use weaken_right.
  use impl_intro.
  cbn.
  hypersimplify.
  pose (Γ := (𝟙 ×h A) ×h A).
  pose (a₁ := π₂ (tm_var Γ)).
  pose (a₂ := π₂ (π₁ (tm_var Γ))).
  fold Γ a₁ a₂.
  use exists_intro.
  {
    exact ⟨ a₁ , a₂ ⟩.
  }
  cbn.
  hypersimplify.
  fold a₁.
  repeat use conj_intro.
  - use weaken_left.
    exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
  - use weaken_left.
    use partial_setoid_sym.
    apply hyperdoctrine_hyp.
  - use weaken_left.
    use partial_setoid_sym.
    apply hyperdoctrine_hyp.
  - refine (per_subobject_eq _ _ _).
    + use weaken_left.
      apply hyperdoctrine_hyp.
    + use weaken_right.
      apply hyperdoctrine_hyp.
Qed.

(** * 3. Elimination of equality *)
Proposition per_subobject_equality_elim
            {H : first_order_hyperdoctrine}
            {A : partial_setoid H}
            {φ : per_subobject A}
            {ψ : per_subobject (prod_partial_setoid A A)}
            (p : per_subobject_mor_law
                   (id_partial_setoid_morphism A)
                   φ
                   (per_subobject_subst
                      (pair_partial_setoid_morphism
                         (id_partial_setoid_morphism A)
                         (id_partial_setoid_morphism A))
                      ψ))
  : per_subobject_mor_law
      (id_partial_setoid_morphism (prod_partial_setoid A A))
      (per_subobject_equality φ)
      ψ.
Proof.
  do 2 use forall_intro.
  use impl_intro.
  use weaken_right.
  use impl_intro.
  cbn.
  hypersimplify.
  pose (Γ := (𝟙 ×h A ×h A) ×h A ×h A).
  pose (a₁ := π₁ (π₂ (tm_var Γ))).
  pose (a₂ := π₂ (π₂ (tm_var Γ))).
  pose (b₁ := π₁ (π₂ (π₁ (tm_var Γ)))).
  pose (b₂ := π₂ (π₂ (π₁ (tm_var Γ)))).
  fold Γ a₁ a₂ b₁ b₂.
  rewrite (hyperdoctrine_pair_eta (π₂ (tm_var Γ))).
  rewrite (hyperdoctrine_pair_eta (π₂ (π₁ (tm_var Γ)))).
  fold b₁ b₂ a₁ a₂.
  refine (weaken_cut _ _).
  {
    use (per_subobject_mor p).
    - exact b₁.
    - exact b₂.
    - cbn.
      hypersimplify.
      use weaken_right.
      use weaken_left.
      apply hyperdoctrine_hyp.
    - do 2 use weaken_right.
      apply hyperdoctrine_hyp.
  }
  cbn.
  hypersimplify_form.
  use hyp_sym.
  refine (exists_elim _ _).
  {
    use weaken_left.
    apply hyperdoctrine_hyp.
  }
  rewrite conj_subst.
  use hyp_ltrans.
  use weaken_right.
  unfold Γ, a₁, a₂, b₁, b₂.
  hypersimplify.
  clear Γ a₁ a₂ b₁ b₂.
  pose (Γ := ((𝟙 ×h A ×h A) ×h A ×h A) ×h A ×h A).
  pose (a₁ := π₁ (π₂ (tm_var Γ))).
  pose (a₂ := π₂ (π₂ (tm_var Γ))).
  pose (b₁ := π₁ (π₂ (π₁ (tm_var Γ)))).
  pose (b₂ := π₂ (π₂ (π₁ (tm_var Γ)))).
  pose (c₁ := π₁ (π₂ (π₁ (π₁ (tm_var Γ))))).
  pose (c₂ := π₂ (π₂ (π₁ (π₁ (tm_var Γ))))).
  fold Γ a₁ a₂ b₁ b₂ c₁ c₂.
  rewrite (hyperdoctrine_pair_eta (π₂ (tm_var Γ))).
  fold a₁ a₂.
  use (per_subobject_eq ψ _ _).
  - exact ⟨ a₁ , a₂ ⟩.
  - use eq_in_prod_partial_setoid.
    + hypersimplify.
      refine (partial_setoid_trans _ _ _).
      {
        use weaken_right.
        do 2 use weaken_left.
        use partial_setoid_sym.
        apply hyperdoctrine_hyp.
      }
      refine (partial_setoid_trans _ _ _).
      {
        use weaken_left.
        use weaken_right.
        use weaken_left.
        use partial_setoid_sym.
        apply hyperdoctrine_hyp.
      }
      do 2 use weaken_left.
      refine (hyperdoctrine_cut _ _).
      {
        exact (eq_in_prod_partial_setoid_l _ _ (hyperdoctrine_hyp _)).
      }
      hypersimplify.
      apply hyperdoctrine_hyp.
    + hypersimplify.
      refine (partial_setoid_trans _ _ _).
      {
        use weaken_right.
        use weaken_left.
        use weaken_right.
        use partial_setoid_sym.
        apply hyperdoctrine_hyp.
      }
      do 2 use weaken_left.
      refine (hyperdoctrine_cut _ _).
      {
        exact (eq_in_prod_partial_setoid_r _ _ (hyperdoctrine_hyp _)).
      }
      hypersimplify.
      apply hyperdoctrine_hyp.
  - do 2 use weaken_right.
    apply hyperdoctrine_hyp.
Qed.
