(*********************************************************************************************

 Complete Heyting algebras

 Heyting algebras provide a framework in which one can interpret intuitionistic propositional
 logic. In complete Heyting algebras, one can also take suprema over arbitrary subsets, and
 this allows one to also interpret the existential quantifier. Since infima can be constructed
 from suprema, one can also interpret the universal quantifier.

 Under the hood there are universe levels in play here. When we phrase "complete", we need to
 indicate over which types it is complete. The easiest way to see this, is by working in
 predicative foundations. Suppose that we have universes `U` and `V` such that `U : V`. Then
 we can form the type of propositions in `U`, and this type lives in universe `V`. The resulting
 lattice of propositions would only be complete over types in `U` but not over types in `V`.
 Since UniMath uses impredicative foundations, the universe levels do not matter for
 propositions. However, it might matter for other examples. Note that similar considerations
 are relevant when defining directed complete partial orders, see the PhD thesis by Tom de Jong.

 References:
 - Appendix A in "Intuitionistic Set Theory" by John Bell
 - Section 3.1 in "Domain Theory in Constructive and Predicative Univalent Foundations" by Tom
   de Jong

 Content
 1. Complete Heyting algebra
 2. Operations of complete Heyting algebras
 3. Laws for complete Heyting algebras
 4. Greatest lower bounds for complete Heyting algebras
 5. Derived laws for complete Heyting algebras

 *********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.OrderTheory.Lattice.Bounded.
Require Import UniMath.OrderTheory.Lattice.Heyting.

Declare Scope heyting.
Delimit Scope heyting with heyting.
Local Open Scope heyting.

(** * 1. Complete Heyting algebra *)
Definition is_upperbound_lattice
           {X : hSet}
           (L : lattice X)
           {I : UU}
           (f : I → X)
           (x : X)
  : UU
  := ∏ (i : I), Lle L (f i) x.

Definition is_least_upperbound_lattice
           {X : hSet}
           (L : lattice X)
           {I : UU}
           (f : I → X)
           (x : X)
  : UU
  := is_upperbound_lattice L f x
     ×
     ∏ (y : X), is_upperbound_lattice L f y → Lle L x y.

Definition is_complete_lattice
           {X : hSet}
           (L : lattice X)
  : UU
  := ∏ (I : UU)
       (f : I → X),
     ∑ (x : X),
     is_least_upperbound_lattice L f x.

Definition complete_heyting_algebra
  : UU
  := ∑ (X : hSet)
       (L : bounded_lattice X),
     is_complete_lattice L
     ×
     exponential L.

Definition make_complete_heyting_algebra
           (X : hSet)
           (L : bounded_lattice X)
           (CL : is_complete_lattice L)
           (EL : exponential L)
  : complete_heyting_algebra
  := X ,, L ,, CL ,, EL.

Coercion complete_heyting_algebra_to_carrier
         (H : complete_heyting_algebra)
  : hSet.
Proof.
  exact (pr1 H).
Defined.

Coercion lattice_of_complete_heyting_algebra
         (H : complete_heyting_algebra)
  : bounded_lattice H.
Proof.
  exact (pr12 H).
Defined.

(** * 2. Operations of complete Heyting algebras *)
Definition complete_heyting_algebra_top
           (H : complete_heyting_algebra)
  : H
  := Ltop H.

Notation "⊤" := (complete_heyting_algebra_top _) : heyting.

Definition complete_heyting_algebra_bot
           (H : complete_heyting_algebra)
  : H
  := Lbot H.

Notation "⊥" := (complete_heyting_algebra_bot _) : heyting.

Definition complete_heyting_algebra_le
           {H : complete_heyting_algebra}
           (x y : H)
  : hProp
  := Lle H x y.

Notation "x ≤ y" := (complete_heyting_algebra_le x y) : heyting.

Definition complete_heyting_algebra_min
           {H : complete_heyting_algebra}
           (x y : H)
  : H
  := Lmin H x y.

Notation "x ∧ y" := (complete_heyting_algebra_min x y) : heyting.

Definition complete_heyting_algebra_max
           {H : complete_heyting_algebra}
           (x y : H)
  : H
  := Lmax H x y.

Notation "x ∨ y" := (complete_heyting_algebra_max x y) : heyting.

Definition complete_heyting_algebra_lub
           {H : complete_heyting_algebra}
           {I : UU}
           (f : I → H)
  : H
  := pr1 (pr122 H I f).

Notation "\/_{ i } f" := (complete_heyting_algebra_lub (λ i, f)) (at level 20, i binder)
    : heyting.

(**
   Note that one can also write `\/_{ i : I } f`
 *)

Definition complete_heyting_algebra_exp
           {H : complete_heyting_algebra}
           (x y : H)
  : H
  := pr222 H x y.

Notation "x ⇒ y" := (complete_heyting_algebra_exp x y) : heyting.

(** * 3. Laws for complete Heyting algebras *)

(**
   For the laws, we use `cha` as an abbreviation for 'complete Heyting algebra'.
   We did not do so for the operations, because there one can use the notation.
 *)
Proposition cha_min_assoc
            {H : complete_heyting_algebra}
            (x y z : H)
  : ((x ∧ y) ∧ z) = (x ∧ (y ∧ z)).
Proof.
  exact (isassoc_Lmin H x y z).
Qed.

Proposition cha_min_comm
            {H : complete_heyting_algebra}
            (x y : H)
  : (x ∧ y) = (y ∧ x).
Proof.
  exact (iscomm_Lmin H x y).
Qed.

Proposition cha_max_assoc
            {H : complete_heyting_algebra}
            (x y z : H)
  : ((x ∨ y) ∨ z) = (x ∨ (y ∨ z)).
Proof.
  exact (isassoc_Lmax H x y z).
Qed.

Proposition cha_max_comm
            {H : complete_heyting_algebra}
            (x y : H)
  : (x ∨ y) = (y ∨ x).
Proof.
  exact (iscomm_Lmax H x y).
Qed.

Proposition cha_min_absorb
            {H : complete_heyting_algebra}
            (x y : H)
  : (x ∧ (x ∨ y)) = x.
Proof.
  exact (Lmin_absorb H x y).
Qed.

Proposition cha_max_absorb
            {H : complete_heyting_algebra}
            (x y : H)
  : (x ∨ (x ∧ y)) = x.
Proof.
  exact (Lmax_absorb H x y).
Qed.

Proposition cha_min_id
            {H : complete_heyting_algebra}
            (x : H)
  : (x ∧ x) = x.
Proof.
  exact (Lmin_id H x).
Qed.

Proposition cha_max_id
            {H : complete_heyting_algebra}
            (x : H)
  : (x ∨ x) = x.
Proof.
  exact (Lmax_id H x).
Qed.

Proposition cha_le_refl
            {H : complete_heyting_algebra}
            (x : H)
  : x ≤ x.
Proof.
  exact (isrefl_Lle H x).
Qed.

Proposition cha_le_antisymm
            {H : complete_heyting_algebra}
            {x y : H}
            (p : x ≤ y)
            (q : y ≤ x)
  : x = y.
Proof.
  exact (isantisymm_Lle H x y p q).
Qed.

Proposition cha_le_trans
            {H : complete_heyting_algebra}
            {x y z : H}
            (p : x ≤ y)
            (q : y ≤ z)
  : x ≤ z.
Proof.
  exact (istrans_Lle H x y z p q).
Qed.

Proposition cha_min_le_l
            {H : complete_heyting_algebra}
            (x y : H)
  : (x ∧ y) ≤ x.
Proof.
  exact (Lmin_le_l H x y).
Qed.

Proposition cha_min_le_r
            {H : complete_heyting_algebra}
            (x y : H)
  : (x ∧ y) ≤ y.
Proof.
  exact (Lmin_le_r H x y).
Qed.

Proposition cha_min_le_case
            {H : complete_heyting_algebra}
            {x y z : H}
            (p : z ≤ x)
            (q : z ≤ y)
  : z ≤ (x ∧ y).
Proof.
  exact (Lmin_le_case H x y z p q).
Qed.

Proposition cha_max_le_l
            {H : complete_heyting_algebra}
            (x y : H)
  : x ≤ (x ∨ y).
Proof.
  exact (Lmax_le_l H x y).
Qed.

Proposition cha_max_le_r
            {H : complete_heyting_algebra}
            (x y : H)
  : y ≤ (x ∨ y).
Proof.
  exact (Lmax_le_r H x y).
Qed.

Proposition cha_max_le_case
            {H : complete_heyting_algebra}
            {x y z : H}
            (p : x ≤ z)
            (q : y ≤ z)
  : (x ∨ y) ≤ z.
Proof.
  exact (Lmax_le_case H x y z p q).
Qed.

Proposition cha_min_le_eq_l
            {H : complete_heyting_algebra}
            {x y : H}
            (p : x ≤ y)
  : (x ∧ y) = x.
Proof.
  exact (Lmin_le_eq_l H x y p).
Qed.

Proposition cha_min_le_eq_r
            {H : complete_heyting_algebra}
            {x y : H}
            (p : y ≤ x)
  : (x ∧ y) = y.
Proof.
  exact (Lmin_le_eq_r H x y p).
Qed.

Proposition cha_max_le_eq_l
            {H : complete_heyting_algebra}
            {x y : H}
            (p : y ≤ x)
  : (x ∨ y) = x.
Proof.
  exact (Lmax_le_eq_l H x y p).
Qed.

Proposition cha_max_le_eq_r
            {H : complete_heyting_algebra}
            {x y : H}
            (p : x ≤ y)
  : (x ∨ y) = y.
Proof.
  exact (Lmax_le_eq_r H x y p).
Qed.

Proposition cha_lunit_max_bot
            {H : complete_heyting_algebra}
            (x : H)
  : (⊥ ∨ x) = x.
Proof.
  exact (islunit_Lmax_Lbot H x).
Qed.

Proposition cha_runit_max_bot
            {H : complete_heyting_algebra}
            (x : H)
  : (x ∨ ⊥) = x.
Proof.
  rewrite cha_max_comm.
  apply cha_lunit_max_bot.
Qed.

Proposition cha_lunit_min_top
            {H : complete_heyting_algebra}
            (x : H)
  : (⊤ ∧ x) = x.
Proof.
  exact (islunit_Lmin_Ltop H x).
Qed.

Proposition cha_runit_min_bot
            {H : complete_heyting_algebra}
            (x : H)
  : (x ∧ ⊤) = x.
Proof.
  rewrite cha_min_comm.
  apply cha_lunit_min_top.
Qed.

Proposition cha_min_bot_l
            {H : complete_heyting_algebra}
            (x : H)
  : (⊥ ∧ x) = ⊥.
Proof.
  exact (Lmin_Lbot H x).
Qed.

Proposition cha_min_bot_r
            {H : complete_heyting_algebra}
            (x : H)
  : (x ∧ ⊥) = ⊥.
Proof.
  rewrite cha_min_comm.
  apply cha_min_bot_l.
Qed.

Proposition cha_max_top_l
            {H : complete_heyting_algebra}
            (x : H)
  : (⊤ ∨ x) = ⊤.
Proof.
  exact (Lmax_Ltop H x).
Qed.

Proposition cha_max_top_r
            {H : complete_heyting_algebra}
            (x : H)
  : (x ∨ ⊤) = ⊤.
Proof.
  rewrite cha_max_comm.
  apply cha_max_top_l.
Qed.

Proposition cha_to_le
            {H : complete_heyting_algebra}
            {x y : H}
            (p : (x ∧ y) = x)
  : x ≤ y.
Proof.
  exact p.
Qed.

Proposition cha_from_le
            {H : complete_heyting_algebra}
            {x y : H}
            (p : x ≤ y)
  : (x ∧ y) = x.
Proof.
  exact p.
Qed.

Proposition cha_bot_le
            {H : complete_heyting_algebra}
            (x : H)
  : ⊥ ≤ x.
Proof.
  use cha_to_le.
  apply cha_min_bot_l.
Qed.

Proposition cha_le_top
            {H : complete_heyting_algebra}
            (x : H)
  : x ≤ ⊤.
Proof.
  use cha_to_le.
  apply cha_runit_min_bot.
Qed.

Proposition cha_from_le_exp
            {H : complete_heyting_algebra}
            {x y z : H}
            (p : z ≤ (x ⇒ y))
  : (z ∧ x) ≤ y.
Proof.
  exact (pr1 (pr2 (pr222 H) x y z) p).
Qed.

Proposition cha_to_le_exp
            {H : complete_heyting_algebra}
            {x y z : H}
            (p : (z ∧ x) ≤ y)
  : z ≤ (x ⇒ y).
Proof.
  exact (pr2 (pr2 (pr222 H) x y z) p).
Qed.

Proposition cha_exp_eval
            {H : complete_heyting_algebra}
            (x y : H)
  : ((x ⇒ y) ∧ x) ≤ y.
Proof.
  use cha_from_le_exp.
  apply cha_le_refl.
Qed.

Proposition cha_le_lub_pt
            {H : complete_heyting_algebra}
            {I : UU}
            (f : I → H)
            (i : I)
  : f i ≤ \/_{ j } f j.
Proof.
  exact (pr12 (pr122 H I f) i).
Qed.

Proposition cha_le_lub
            {H : complete_heyting_algebra}
            {I : UU}
            (f : I → H)
            {x : H}
            {i : I}
            (p : x ≤ f i)
  : x ≤ \/_{ j } f j.
Proof.
  refine (cha_le_trans p _).
  apply cha_le_lub_pt.
Qed.

Proposition cha_lub_le
            {H : complete_heyting_algebra}
            {I : UU}
            {f : I → H}
            {x : H}
            (p : ∏ (i : I), f i ≤ x)
  : \/_{ j } f j ≤ x.
Proof.
  exact (pr22 (pr122 H I f) x p).
Qed.

(**
   The following commands prevent that the operations are unfolded by `cbn` or `simpl.
   Without them, the operations for complete Heyting algebras would be unfolded to the level
   of lattices, and then it would be more complicated to use the accessors/notation in this
   file.
 *)
#[global] Opaque complete_heyting_algebra_top.
#[global] Opaque complete_heyting_algebra_bot.
#[global] Opaque complete_heyting_algebra_le.
#[global] Opaque complete_heyting_algebra_min.
#[global] Opaque complete_heyting_algebra_max.
#[global] Opaque complete_heyting_algebra_lub.
#[global] Opaque complete_heyting_algebra_exp.

(** * 4. Greatest lower bounds for complete Heyting algebras *)
Definition complete_heyting_algebra_glb
           {H : complete_heyting_algebra}
           {I : UU}
           (f : I → H)
  : H
  := \/_{ i : ∑ (x : H), ∏ (i : I), x ≤ f i } pr1 i.

Notation "/\_{ i } f" := (complete_heyting_algebra_glb (λ i, f)) (at level 20, i binder)
    : heyting.

Proposition cha_glb_le_pt
            {H : complete_heyting_algebra}
            {I : UU}
            (f : I → H)
            (i : I)
  : /\_{ j } f j ≤ f i.
Proof.
  use cha_lub_le.
  intros x ; cbn.
  exact (pr2 x i).
Qed.

Proposition cha_glb_le
            {H : complete_heyting_algebra}
            {I : UU}
            (f : I → H)
            {x : H}
            {i : I}
            (p : f i ≤ x)
  : /\_{ j } f j ≤ x.
Proof.
  refine (cha_le_trans _ p).
  apply cha_glb_le_pt.
Qed.

Proposition cha_le_glb
            {H : complete_heyting_algebra}
            {I : UU}
            {f : I → H}
            {x : H}
            (p : ∏ (i : I), x ≤ f i)
  : x ≤ /\_{ j } f j.
Proof.
  unfold complete_heyting_algebra_glb.
  use cha_le_lub.
  - exact (x ,, p).
  - apply cha_le_refl.
Qed.

#[global] Opaque complete_heyting_algebra_glb.

(** * 5. Derived laws for complete Heyting algebras *)
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
