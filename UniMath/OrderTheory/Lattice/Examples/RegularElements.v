Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.OrderTheory.Lattice.Bounded.
Require Import UniMath.OrderTheory.Lattice.Heyting.
Require Import UniMath.OrderTheory.Lattice.CompleteHeyting.

Local Open Scope heyting.

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




Definition is_regular_element
           {H : complete_heyting_algebra}
           (x : H)
  : hProp
  := (x = (¬ ¬ x)%heyting)%logic.

Proposition make_is_regular_element
            {H : complete_heyting_algebra}
            {x : H}
            (p : ¬ ¬ x ≤ x)
  : is_regular_element x.
Proof.
  use cha_le_antisymm.
  - apply cha_not_not.
  - exact p.
Qed.

Definition regular_element
           (H : complete_heyting_algebra)
  : UU
  := ∑ (x : H), is_regular_element x.

Definition make_regular_element
           {H : complete_heyting_algebra}
           (x : H)
           (Hx : is_regular_element x)
  : regular_element H
  := x ,, Hx.

Coercion regular_element_type
         {H : complete_heyting_algebra}
         (x : regular_element H)
  : H
  := pr1 x.

Proposition is_regular_regular_element
            {H : complete_heyting_algebra}
            (x : regular_element H)
  : ¬ ¬ x = x.
Proof.
  exact (!(pr2 x)).
Qed.

Proposition eq_regular_element
            {H : complete_heyting_algebra}
            {x y : regular_element H}
            (p : (x : H) = y)
  : x = y.
Proof.
  use subtypePath.
  {
    intro.
    apply propproperty.
  }
  exact p.
Qed.

Proposition isaset_regular_element
            (H : complete_heyting_algebra)
  : isaset (regular_element H).
Proof.
  use isaset_total2 ; [ apply setproperty | ].
  intro x.
  apply isasetaprop.
  apply propproperty.
Qed.

Definition set_of_regular_elements
           (H : complete_heyting_algebra)
  : hSet.
Proof.
  use make_hSet.
  - exact (regular_element H).
  - apply isaset_regular_element.
Defined.


Proposition cha_not_antimonotone_inv
            {H : complete_heyting_algebra}
            {x y : regular_element H}
            (p : ¬ x ≤ ¬ y)
  : y ≤ x.
Proof.
  pose (cha_not_antimonotone p) as q.
  rewrite !is_regular_regular_element in q.
  exact q.
Qed.


Definition top_regular_element
           (H : complete_heyting_algebra)
  : regular_element H.
Proof.
  use make_regular_element.
  - exact ⊤.
  - abstract
      (use make_is_regular_element ;
       rewrite cha_not_top ;
       rewrite cha_not_bot ;
       apply cha_le_refl).
Defined.

Definition bot_regular_element
           (H : complete_heyting_algebra)
  : regular_element H.
Proof.
  use make_regular_element.
  - exact ⊥.
  - abstract
      (use make_is_regular_element ;
       rewrite cha_not_bot ;
       rewrite cha_not_top ;
       apply cha_le_refl).
Defined.

Proposition not_not_is_regular_element
            {H : complete_heyting_algebra}
            (x : H)
  : ¬ ¬ x = ¬ ¬ ¬ ¬ x.
Proof.
  use make_is_regular_element.
  use cha_to_le_exp.
  refine (cha_le_trans _ (cha_exp_eval (¬ ¬ ¬ x) _)).
  use cha_min_le_case.
  - use cha_min_le_l.
  - refine (cha_le_trans (cha_min_le_r _ _) _).
    apply cha_not_not.
Qed.

Definition not_not_regular_element
           {H : complete_heyting_algebra}
           (x : H)
  : regular_element H.
Proof.
  use make_regular_element.
  - exact (¬ ¬ x).
  - apply not_not_is_regular_element.
Defined.

Definition not_regular_element
           {H : complete_heyting_algebra}
           (x : regular_element H)
  : regular_element H.
Proof.
  use make_regular_element.
  - exact (¬ x).
  - abstract
      (use make_is_regular_element ;
       rewrite cha_not_not_not ;
       apply cha_le_refl).
Defined.

Proposition is_regular_conj
            {H : complete_heyting_algebra}
            (x y : regular_element H)
  : is_regular_element (x ∧ y).
Proof.
  use make_is_regular_element.
  rewrite <- (is_regular_regular_element x).
  rewrite <- (is_regular_regular_element y).
  rewrite cha_conj_not.
  rewrite cha_not_not_not.
  apply cha_le_refl.
Qed.

Definition conj_regular_element
           {H : complete_heyting_algebra}
           (x y : regular_element H)
  : regular_element H.
Proof.
  use make_regular_element.
  - exact (x ∧ y).
  - apply is_regular_conj.
Defined.


Definition disj_regular_element
           {H : complete_heyting_algebra}
           (x y : regular_element H)
  : regular_element H
  := not_not_regular_element (x ∨ y).


Proposition is_regular_glb
            {H : complete_heyting_algebra}
            {I : UU}
            (f : I → regular_element H)
  : is_regular_element (/\_{ i : I } f i).
Proof.
  use make_is_regular_element.
  use cha_le_glb.
  intros i ; cbn.
  rewrite <- (is_regular_regular_element (f i)).
  use cha_not_antimonotone.
  use cha_not_antimonotone.
  exact (cha_glb_le_pt f i).
Qed.

Definition glb_regular_element
           {H : complete_heyting_algebra}
           {I : UU}
           (f : I → regular_element H)
  : regular_element H.
Proof.
  use make_regular_element.
  - exact (/\_{ i : I } f i).
  - apply is_regular_glb.
Defined.


Proposition regular_element_islatticeop
            (H : complete_heyting_algebra)
  : islatticeop
      (λ (x y : set_of_regular_elements H), conj_regular_element x y)
      (λ (x y : set_of_regular_elements H), disj_regular_element x y).
Proof.
  repeat split.
  - intros x y z ; use eq_regular_element ; cbn.
    apply cha_min_assoc.
  - intros x y ; use eq_regular_element ; cbn.
    apply cha_min_comm.
  - intros x y z ; use eq_regular_element ; cbn ; cbn in x, y, z.
    use cha_le_antisymm.
    + refine (cha_le_trans _ _) ;
        [ rewrite <- (is_regular_regular_element z)
        | rewrite <- (is_regular_regular_element x) ].
      {
        apply cha_le_refl.
      }
      rewrite !cha_not_not_disj_not.
      rewrite !cha_conj_not.
      use cha_not_not_monotone.
      rewrite cha_max_assoc.
      apply cha_le_refl.
    + refine (cha_le_trans _ _) ;
        [ rewrite <- (is_regular_regular_element x)
        | rewrite <- (is_regular_regular_element z) ].
      {
        apply cha_le_refl.
      }
      rewrite !cha_not_not_disj_not.
      rewrite !cha_conj_not.
      use cha_not_not_monotone.
      rewrite cha_max_assoc.
      apply cha_le_refl.
  - intros x y ; use eq_regular_element ; cbn.
    rewrite cha_max_comm.
    apply idpath.
  - intros x y ; use eq_regular_element ; cbn.
    use cha_le_antisymm.
    + apply cha_min_le_l.
    + use cha_min_le_case.
      {
        apply cha_le_refl.
      }
      rewrite <- cha_conj_not.
      refine (cha_le_trans _ _).
      {
        rewrite <- (is_regular_regular_element x).
        apply cha_le_refl.
      }
      use cha_not_antimonotone.
      use cha_min_le_l.
  - intros x y ; use eq_regular_element ; cbn.
    rewrite cha_max_absorb.
    rewrite is_regular_regular_element.
    apply idpath.
Qed.

Definition regular_element_lattice
           (H : complete_heyting_algebra)
  : lattice (set_of_regular_elements H).
Proof.
  use make_lattice.
  - exact (λ x y, conj_regular_element x y).
  - exact (λ x y, disj_regular_element x y).
  - exact (regular_element_islatticeop H).
Defined.

Proposition to_le_regular_element_lattice
            {H : complete_heyting_algebra}
            {x y : regular_element H}
            (p : x ≤ y)
  : Lle (regular_element_lattice H) x y.
Proof.
  cbn.
  use eq_regular_element.
  exact p.
Qed.

Proposition from_le_regular_element_lattice
            {H : complete_heyting_algebra}
            {x y : regular_element H}
            (p : Lle (regular_element_lattice H) x y)
  : x ≤ y.
Proof.
  exact (maponpaths pr1 p).
Qed.

Proposition regular_element_bounded_latticeop
            (H : complete_heyting_algebra)
  : bounded_latticeop
      (regular_element_lattice H)
      (bot_regular_element H)
      (top_regular_element H).
Proof.
  split.
  - intro x ; use eq_regular_element ; cbn.
    rewrite cha_lunit_max_bot.
    rewrite is_regular_regular_element.
    apply idpath.
  - intro x ; use eq_regular_element ; cbn.
    rewrite cha_lunit_min_top.
    apply idpath.
Qed.

Definition regular_element_bounded_lattice
           (H : complete_heyting_algebra)
  : bounded_lattice (set_of_regular_elements H).
Proof.
  use make_bounded_lattice.
  - exact (regular_element_lattice H).
  - exact (bot_regular_element H).
  - exact (top_regular_element H).
  - exact (regular_element_bounded_latticeop H).
Defined.

Proposition is_glb_glb_regular_element
            {H : complete_heyting_algebra}
            {I : UU}
            (f : I → regular_element H)
  : is_greatest_lowerbound_lattice
      (regular_element_lattice H)
      f
      (glb_regular_element f).
Proof.
  split.
  - intros i ; use eq_regular_element.
    exact (cha_glb_le_pt (λ j, (f j : H)) i).
  - intros x Hx ; use eq_regular_element ; cbn ; cbn in x.
    use (@cha_le_glb H I (λ j, (f j : H)) x).
    intros i ; cbn.
    exact (maponpaths pr1 (Hx i)).
Qed.

Definition regular_element_complete_lattice
           (H : complete_heyting_algebra)
  : is_complete_lattice (regular_element_bounded_lattice H).
Proof.
  use complete_lattice_from_glb.
  intros I f.
  refine (glb_regular_element f ,, _).
  apply is_glb_glb_regular_element.
Defined.

Definition lub_regular_element
           {H : complete_heyting_algebra}
           (I : UU)
           (f : I → regular_element H)
  : regular_element H
  := pr1 (regular_element_complete_lattice H I f).

Proposition le_lub_regular_element
            {H : complete_heyting_algebra}
            {I : UU}
            (f : I → regular_element H)
            (y : regular_element H)
            (i : I)
            (p : y ≤ f i)
  : y ≤ lub_regular_element I f.
Proof.
  refine (cha_le_trans p _).
  use from_le_regular_element_lattice.
  exact (pr12 (regular_element_complete_lattice H I f) i).
Qed.

Proposition lub_regular_element_le
            {H : complete_heyting_algebra}
            {I : UU}
            (f : I → regular_element H)
            (y : regular_element H)
            (p : ∏ (i : I), f i ≤ y)
  : lub_regular_element I f ≤ y.
Proof.
  use from_le_regular_element_lattice.
  refine (pr22 (regular_element_complete_lattice H I f) y _).
  intros i.
  use to_le_regular_element_lattice.
  apply p.
Qed.

Proposition lub_regular_element_pt_le
            {H : complete_heyting_algebra}
            {I : UU}
            (f f' : I → regular_element H)
            (p : ∏ (i : I), f i ≤ f' i)
  : lub_regular_element I f ≤ lub_regular_element I f'.
Proof.
  use lub_regular_element_le.
  intro i.
  use le_lub_regular_element.
  - exact i.
  - apply p.
Qed.

Proposition lub_regular_element_eq
            {H : complete_heyting_algebra}
            (I : UU)
            (f : I → regular_element H)
  : lub_regular_element I f
    =
    not_not_regular_element (\/_{ i : I } f i).
Proof.
  use eq_regular_element.
  use cha_le_antisymm.
  - cbn -[lub_regular_element].
    use cha_to_le_exp.
    refine (cha_le_trans _ (cha_exp_eval (¬ (\/_{ i } f i)) _)).
    use cha_and_monotone_l.
    refine (lub_regular_element_le f (not_not_regular_element (\/_{ i : I } f i)) _).
    intro i ; cbn.
    refine (cha_le_trans (cha_not_not _) _).
    use cha_not_not_monotone.
    exact (cha_le_lub_pt f i).
  - use cha_le_glb.
    intro i.
    induction i as [ x p ] ; cbn.
    rewrite <- (is_regular_regular_element x).
    use cha_not_not_monotone.
    use cha_lub_le.
    intro i ; cbn.
    use from_le_regular_element_lattice.
    apply p.
Qed.

Proposition conj_lub_regular_element
            {H : complete_heyting_algebra}
            {I : UU}
            (f : I → regular_element H)
            (y : regular_element H)
  : (lub_regular_element I f ∧ y)
    ≤
    lub_regular_element I (λ i, conj_regular_element (f i) y).
Proof.
  rewrite !lub_regular_element_eq ; cbn.
  rewrite <- (is_regular_regular_element y).
  rewrite <- cha_not_not_conj.
  rewrite is_regular_regular_element.
  use cha_not_not_monotone.
  rewrite (cha_min_comm _ y).
  rewrite cha_frobenius.
  use cha_lub_le.
  intro i.
  use cha_le_lub.
  - exact i.
  - cbn.
    rewrite (cha_min_comm y (f i)).
    apply cha_le_refl.
Qed.


Definition impl_regular_element
           {H : complete_heyting_algebra}
           (x y : regular_element H)
  : regular_element H
  := lub_regular_element (∑ (w : regular_element H), (w ∧ x) ≤ y) pr1.



Proposition regular_element_is_exponential
            {H : complete_heyting_algebra}
            (x y z : regular_element H)
  : Lle (regular_element_lattice H) z (impl_regular_element x y)
    <->
    Lle (regular_element_lattice H) (conj_regular_element z x) y.
Proof.
  split.
  - intro p.
    apply from_le_regular_element_lattice in p.
    use to_le_regular_element_lattice.
    cbn.
    refine (cha_le_trans _ _).
    {
      exact (cha_and_monotone_l p).
    }
    refine (cha_le_trans _ _).
    {
      apply conj_lub_regular_element.
    }
    refine (cha_le_trans _ _).
    {
      use (lub_regular_element_pt_le _ (λ _, y)).
      cbn.
      intro i.
      induction i as [ w Hw ] ; cbn.
      exact Hw.
    }
    use lub_regular_element_le.
    intro i ; cbn.
    apply cha_le_refl.
  - intro p.
    apply from_le_regular_element_lattice in p.
    use to_le_regular_element_lattice.
    cbn ; cbn in p.
    use cha_le_glb.
    intros i ; induction i as [ w q ] ; cbn.
    refine (cha_le_trans _ (cha_min_le_r z w)).
    assert ((z ∧ w) = z) as ->.
    {
      exact (maponpaths pr1 (q (z ,, p))).
    }
    apply cha_le_refl.
Qed.

Definition regular_element_exponential
           (H : complete_heyting_algebra)
  : exponential (regular_element_bounded_lattice H).
Proof.
  use make_exponential.
  - exact (λ x y, impl_regular_element x y).
  - exact regular_element_is_exponential.
Defined.

Definition regular_element_cha
           (H : complete_heyting_algebra)
  : complete_heyting_algebra.
Proof.
  use make_complete_heyting_algebra.
  - exact (set_of_regular_elements H).
  - exact (regular_element_bounded_lattice H).
  - exact (regular_element_complete_lattice H).
  - exact (regular_element_exponential H).
Defined.

#[local] Transparent complete_heyting_algebra_max.
#[local] Transparent complete_heyting_algebra_top.
#[local] Transparent complete_heyting_algebra_exp.

Proposition is_boolean_regular_element_cha
            (H : complete_heyting_algebra)
  : is_boolean_algebra (regular_element_cha H).
Proof.
  intros x.
  use eq_regular_element ; cbn in x.
  refine (_ @ cha_not_not_lem x).
  cbn -[Lle].
  use cha_le_antisymm.
  - use cha_not_not_monotone.
    use cha_max_le_max_r.
    use cha_glb_le.
    + refine (not_regular_element x ,, _).
      intro i.
      induction i as [ w Hw ].
      use to_le_regular_element_lattice ; cbn.
      use cha_to_le_exp.
      exact Hw.
    + cbn.
      apply cha_le_refl.
  - use cha_not_not_monotone.
    use cha_max_le_max_r.
    use cha_le_glb.
    intros i.
    induction i as [ w Hw ] ; cbn.
    refine (from_le_regular_element_lattice (Hw (not_regular_element x ,, _))).
    cbn.
    apply cha_not_eval.
Qed.
