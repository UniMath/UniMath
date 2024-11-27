(******************************************************************************************

 Derived laws in complete Heyting algebras

 This file is a collection of various derived laws for complete Heyting algebras. These
 are useful in various applications.

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.OrderTheory.Lattice.Bounded.
Require Import UniMath.OrderTheory.Lattice.Heyting.
Require Import UniMath.OrderTheory.Lattice.CompleteHeyting.

Local Open Scope heyting.

Proposition cha_min_le_min_l
            {H : complete_heyting_algebra}
            {x₁ x₂ : H}
            (p : x₁ ≤ x₂)
            (y : H)
  : (x₁ ∧ y) ≤ (x₂ ∧ y).
Proof.
  use cha_min_le_case.
  - refine (cha_le_trans _ p).
    apply cha_min_le_l.
  - apply cha_min_le_r.
Qed.

Proposition cha_min_le_min_r
            {H : complete_heyting_algebra}
            (x : H)
            {y₁ y₂ : H}
            (p : y₁ ≤ y₂)
  : (x ∧ y₁) ≤ (x ∧ y₂).
Proof.
  use cha_min_le_case.
  - apply cha_min_le_l.
  - refine (cha_le_trans _ p).
    apply cha_min_le_r.
Qed.

Proposition cha_max_le_max_l
            {H : complete_heyting_algebra}
            {x₁ x₂ : H}
            (p : x₁ ≤ x₂)
            (y : H)
  : (x₁ ∨ y) ≤ (x₂ ∨ y).
Proof.
  use cha_max_le_case.
  - refine (cha_le_trans p _).
    apply cha_max_le_l.
  - apply cha_max_le_r.
Qed.

Proposition cha_max_le_max_r
            {H : complete_heyting_algebra}
            (x : H)
            {y₁ y₂ : H}
            (p : y₁ ≤ y₂)
  : (x ∨ y₁) ≤ (x ∨ y₂).
Proof.
  use cha_max_le_case.
  - apply cha_max_le_l.
  - refine (cha_le_trans p _).
    apply cha_max_le_r.
Qed.

Proposition cha_curry
            {H : complete_heyting_algebra}
            (x y z : H)
  : (x ⇒ (y ⇒ z)) = (x ∧ y ⇒ z).
Proof.
  use cha_le_antisymm.
  - use cha_to_le_exp.
    rewrite <- cha_min_assoc.
    refine (cha_le_trans _ (cha_exp_eval y z)).
    use cha_min_le_min_l.
    apply cha_exp_eval.
  - use cha_to_le_exp.
    use cha_to_le_exp.
    rewrite cha_min_assoc.
    apply cha_exp_eval.
Qed.

Proposition cha_max_min_distributive
            {H : complete_heyting_algebra}
            (x y z : H)
  : (x ∧ (y ∨ z)) = ((x ∧ y) ∨ (x ∧ z)).
Proof.
  use cha_le_antisymm.
  - rewrite cha_min_comm.
    use cha_from_le_exp.
    use cha_max_le_case.
    + use cha_to_le_exp.
      rewrite cha_min_comm.
      use cha_max_le_l.
    + use cha_to_le_exp.
      rewrite cha_min_comm.
      use cha_max_le_r.
  - use cha_min_le_case.
    + use cha_max_le_case.
      * apply cha_min_le_l.
      * apply cha_min_le_l.
    + use cha_max_le_case.
      * refine (cha_le_trans (cha_min_le_r _ _) _).
        apply cha_max_le_l.
      * refine (cha_le_trans (cha_min_le_r _ _) _).
        apply cha_max_le_r.
Qed.

Proposition cha_min_max_distributive
            {H : complete_heyting_algebra}
            (x y z : H)
  : (x ∨ (y ∧ z)) = ((x ∨ y) ∧ (x ∨ z)).
Proof.
  rewrite (cha_max_min_distributive (x ∨ y) x z).
  rewrite (cha_min_comm (x ∨ y) x).
  rewrite cha_min_absorb.
  rewrite (cha_min_comm (x ∨ y) z).
  rewrite cha_max_min_distributive.
  rewrite (cha_min_comm z y).
  rewrite <- cha_max_assoc.
  apply maponpaths_2.
  rewrite (cha_min_comm z x).
  rewrite (cha_max_absorb x z).
  apply idpath.
Qed.

Proposition cha_frobenius
            {H : complete_heyting_algebra}
            {I : UU}
            (f : I → H)
            (x : H)
  : (x ∧ \/_{ i } f i) = \/_{ i } (x ∧ f i).
Proof.
  use cha_le_antisymm.
  - rewrite (cha_min_comm x (\/_{ i } f i)).
    use cha_from_le_exp.
    use cha_lub_le.
    intro i.
    use cha_to_le_exp.
    rewrite (cha_min_comm (f i) x).
    exact (cha_le_lub_pt (λ j, x ∧ f j) i).
  - use cha_lub_le.
    intro i ; cbn.
    use cha_min_le_min_r.
    apply cha_le_lub_pt.
Qed.

Proposition cha_not_top
            (H : complete_heyting_algebra)
  : ¬ ⊤ = (⊥ : H).
Proof.
  cbn.
  use cha_le_antisymm.
  - rewrite <- (cha_runit_min_bot (¬ ⊤)).
    use cha_exp_eval.
  - use cha_to_le_exp.
    use cha_min_le_l.
Qed.

Proposition cha_not_bot
            (H : complete_heyting_algebra)
  : ¬ ⊥ = (⊤ : H).
Proof.
  cbn.
  use cha_le_antisymm.
  - use cha_le_top.
  - use cha_to_le_exp.
    use cha_min_le_r.
Qed.

Proposition cha_not_not
            {H : complete_heyting_algebra}
            (x : H)
  : x ≤ ¬ ¬ x.
Proof.
  use cha_to_le_exp.
  rewrite cha_min_comm.
  use cha_exp_eval.
Qed.

Proposition cha_not_eval
            {H : complete_heyting_algebra}
            (x : H)
  : (¬x ∧ x) ≤ ⊥.
Proof.
  apply cha_exp_eval.
Qed.

Proposition cha_and_monotone
            {H : complete_heyting_algebra}
            {x₁ x₂ y₁ y₂ : H}
            (p : x₁ ≤ x₂)
            (q : y₁ ≤ y₂)
  : (x₁ ∧ y₁) ≤ (x₂ ∧ y₂).
Proof.
  use cha_min_le_case.
  - refine (cha_le_trans _ p).
    apply cha_min_le_l.
  - refine (cha_le_trans _ q).
    apply cha_min_le_r.
Qed.

Proposition cha_and_monotone_l
            {H : complete_heyting_algebra}
            {x₁ x₂ y : H}
            (p : x₁ ≤ x₂)
  : (x₁ ∧ y) ≤ (x₂ ∧ y).
Proof.
  use (cha_and_monotone p).
  apply cha_le_refl.
Qed.

Proposition cha_and_monotone_r
            {H : complete_heyting_algebra}
            {x y₁ y₂ : H}
            (q : y₁ ≤ y₂)
  : (x ∧ y₁) ≤ (x ∧ y₂).
Proof.
  refine (cha_and_monotone _ q).
  apply cha_le_refl.
Qed.

Proposition cha_not_antimonotone
            {H : complete_heyting_algebra}
            {x y : H}
            (p : y ≤ x)
  : ¬ x ≤ ¬ y.
Proof.
  use cha_to_le_exp.
  refine (cha_le_trans _ _).
  {
    exact (cha_and_monotone_r p).
  }
  use cha_exp_eval.
Qed.

Proposition cha_not_not_monotone
            {H : complete_heyting_algebra}
            {x y : H}
            (p : x ≤ y)
  : ¬ ¬ x ≤ ¬ ¬ y.
Proof.
  do 2 use cha_not_antimonotone.
  exact p.
Qed.

Proposition cha_not_not_not
            {H : complete_heyting_algebra}
            (x : H)
  : ¬ ¬ ¬ x = ¬ x.
Proof.
  use cha_le_antisymm.
  - use cha_to_le_exp.
    refine (cha_le_trans _ _).
    {
      refine (cha_and_monotone_r _).
      apply cha_not_not.
    }
    use cha_exp_eval.
  - apply cha_not_not.
Qed.

Proposition cha_not_not_lem
            {H : complete_heyting_algebra}
            (x : H)
  : ¬ ¬(x ∨ ¬ x) = ⊤.
Proof.
  use cha_le_antisymm.
  - apply cha_le_top.
  - use cha_to_le_exp.
    rewrite cha_lunit_min_top.
    refine (cha_le_trans _ (cha_not_eval (¬ x))).
    use cha_min_le_case.
    + use cha_to_le_exp.
      refine (cha_le_trans _ (cha_exp_eval (x ∨ ¬ x) _)).
      use cha_and_monotone_r.
      use cha_max_le_r.
    + use cha_to_le_exp.
      refine (cha_le_trans _ (cha_exp_eval (x ∨ ¬ x) _)).
      use cha_and_monotone_r.
      use cha_max_le_l.
Qed.

Proposition cha_disj_not
            {H : complete_heyting_algebra}
            (x y : H)
  : (¬x ∨ ¬y) ≤ ¬(x ∧ y).
Proof.
  use cha_max_le_case.
  - use cha_not_antimonotone.
    use cha_min_le_l.
  - use cha_not_antimonotone.
    use cha_min_le_r.
Qed.

Proposition cha_conj_not
            {H : complete_heyting_algebra}
            (x y : H)
  : (¬x ∧ ¬y) = ¬(x ∨ y).
Proof.
  use cha_le_antisymm.
  - use cha_to_le_exp.
    rewrite cha_min_comm.
    use cha_from_le_exp.
    use cha_max_le_case.
    + use cha_to_le_exp.
      refine (cha_le_trans _ _).
      {
        exact (cha_and_monotone_r (cha_min_le_l _ _)).
      }
      rewrite cha_min_comm.
      use cha_exp_eval.
    + use cha_to_le_exp.
      refine (cha_le_trans _ _).
      {
        exact (cha_and_monotone_r (cha_min_le_r _ _)).
      }
      rewrite cha_min_comm.
      use cha_exp_eval.
  - use cha_min_le_case.
    + use cha_to_le_exp.
      refine (cha_le_trans _ _).
      {
        refine (cha_and_monotone_r _).
        exact (cha_max_le_l x y).
      }
      use cha_exp_eval.
    + use cha_to_le_exp.
      refine (cha_le_trans _ _).
      {
        refine (cha_and_monotone_r _).
        exact (cha_max_le_r x y).
      }
      use cha_exp_eval.
Qed.

Proposition cha_not_not_conj
            {H : complete_heyting_algebra}
            (x y : H)
  : ¬ ¬(x ∧ y) = (¬ ¬ x ∧ ¬ ¬ y).
Proof.
  use cha_le_antisymm.
  - use cha_min_le_case.
    + use cha_not_not_monotone.
      apply cha_min_le_l.
    + use cha_not_not_monotone.
      apply cha_min_le_r.
  - use cha_to_le_exp.
    refine (cha_le_trans _ (cha_not_eval (¬ x))).
    use cha_min_le_case.
    + refine (cha_le_trans (cha_min_le_l _ _) _).
      use cha_min_le_l.
    + use cha_to_le_exp.
      refine (cha_le_trans _ (cha_not_eval (¬ y))).
      use cha_min_le_case.
      * refine (cha_le_trans (cha_min_le_l _ _) _).
        refine (cha_le_trans (cha_min_le_l _ _) _).
        use cha_min_le_r.
      * use cha_to_le_exp.
        refine (cha_le_trans _ (cha_not_eval (x ∧ y))).
        use cha_min_le_case.
        ** refine (cha_le_trans (cha_min_le_l _ _) _).
           refine (cha_le_trans (cha_min_le_l _ _) _).
           use cha_min_le_r.
        ** use cha_min_le_case.
           *** refine (cha_le_trans (cha_min_le_l _ _) _).
               use cha_min_le_r.
           *** use cha_min_le_r.
Qed.

Proposition cha_not_not_disj_not
            {H : complete_heyting_algebra}
            (x y : H)
  : ¬ ¬ (¬x ∨ ¬y) = ¬(x ∧ y).
Proof.
  use cha_le_antisymm.
  - rewrite <- (cha_not_not_not (x ∧ y)).
    use cha_not_not_monotone.
    apply cha_disj_not.
  - rewrite <- cha_conj_not.
    rewrite <- (cha_not_not_not (x ∧ y)).
    rewrite <- cha_not_not_conj.
    apply cha_le_refl.
Qed.

Proposition cha_glb_conj
            {H : complete_heyting_algebra}
            {I : UU}
            (f : I → H)
            (x : H)
  : (/\_{ i : I } f i ∧ x) ≤ /\_{ i : I } (f i ∧ x).
Proof.
  use cha_le_glb.
  intro i.
  use cha_and_monotone_l.
  use cha_glb_le.
  - exact i.
  - apply cha_le_refl.
Qed.
