Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(* The presheaf data type *)
Definition presheaf_data (T : algebraic_theory_data) : UU
  := ∑ P : (finite_set_skeleton_category ⟶ HSET),
    ∏ m n, (P m : hSet) → (stn m → (T n : hSet)) → (P n : hSet).

Coercion presheaf_data_to_functor {T : algebraic_theory_data} (P : presheaf_data T)
  : finite_set_skeleton_category ⟶ HSET
  := pr1 P.

Definition action {T} {P : presheaf_data T} {m n} : (P m : hSet) → (stn m → (T n : hSet)) → (P n : hSet) := pr2 P m n.

Definition make_presheaf_data {T : algebraic_theory_data}
  (P : finite_set_skeleton_category ⟶ HSET)
  (action : ∏ m n, (P m : hSet) → (stn m → (T n : hSet)) → (P n : hSet))
  : presheaf_data T
  := (P ,, action).

(* The presheaf type *)
Definition is_assoc {T : algebraic_theory_data} (P : presheaf_data T) : UU
  := ∏ l m n (a : (P l : hSet)) f (g : stn m → (T n : hSet)), action (action a f) g = action a (λ i, (f i) • g).

Definition identity_projections {T : algebraic_theory_data} (P : presheaf_data T) : UU
  := ∏ n (a : (P n : hSet)), action a (λ i, pr i) = a.

Definition action_is_natural {T : algebraic_theory_data} (P : presheaf_data T) : UU
  := ∏ m m' n (x : finite_set_skeleton_category⟦m, m'⟧) a (f : stn m' → T n : hSet),
  action (# P x a) f = action a (λ i, f (x i)).

Definition is_presheaf {T : algebraic_theory_data} (P : presheaf_data T) : UU :=
  is_assoc P ×
  identity_projections P ×
  action_is_natural P.

Definition make_is_presheaf
  {T : algebraic_theory_data}
  (P : presheaf_data T)
  (H1 : is_assoc P)
  (H2 : identity_projections P)
  (H3 : action_is_natural P)
  : is_presheaf P
  := H1 ,, H2 ,, H3.

Definition presheaf (T : algebraic_theory_data) : UU := ∑
  (P : finite_set_skeleton_category ⟶ HSET)
  (action : ∏ m n, (P m : hSet) → (stn m → (T n : hSet)) → (P n : hSet)),
    is_presheaf (make_presheaf_data P action).

Coercion presheaf_to_presheaf_data {T : algebraic_theory_data} (P : presheaf T) : presheaf_data T := make_presheaf_data (pr1 P) (pr12 P).

Definition make_presheaf
  {T : algebraic_theory_data}
  (P : presheaf_data T)
  (H : is_presheaf P)
  : presheaf T
  := (pr1 P) ,, (pr2 P) ,, H.

Definition presheaf_is_assoc
  {T : algebraic_theory_data}
  (P : presheaf T)
  : is_assoc P
  := pr122 P.

Definition presheaf_identity_projections
  {T : algebraic_theory_data}
  (P : presheaf T)
  : identity_projections P
  := pr1 (pr222 P).

Definition presheaf_action_is_natural
  {T : algebraic_theory_data}
  (P : presheaf T)
  : action_is_natural P
  := pr2 (pr222 P).

Lemma isaprop_is_presheaf {T : algebraic_theory_data} (P : presheaf_data T) : isaprop (is_presheaf P).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply setproperty.
Qed.

Lemma presheaf_functor_uses_projections
  {T : algebraic_theory_data}
  (P : presheaf T)
  {m n : finite_set_skeleton_category}
  (a : finite_set_skeleton_category⟦m, n⟧)
  (x : P m : hSet)
  : #P a x = action x (λ i, pr (a i)).
Proof.
  rewrite <- (presheaf_identity_projections _ _ (#P _ _)).
  apply presheaf_action_is_natural.
Qed.

Definition presheaf_morphism {T : algebraic_theory_data} (P P' : presheaf_data T) : UU
  := ∑ (F: P ⟹ P') (HF: ∏ m n a f, F n (action a f) = action (F m a) f), unit.

Definition make_presheaf_morphism
  {T : algebraic_theory_data}
  {P P' : presheaf_data T}
  (F: P ⟹ P')
  (HF: ∏ m n a f, F n (action a f) = action (F m a) f)
  : presheaf_morphism P P'
  := F ,, HF ,, tt.

Definition make_presheaf_morphism'
  {T : algebraic_theory_data}
  {P P' : presheaf T}
  (F: ∏ n, (P n : hSet) → (P' n : hSet))
  (HF: ∏ m n a f, F n (action a f) = action (F m a) f)
  : presheaf_morphism P P'.
Proof.
  use make_presheaf_morphism.
  - use make_nat_trans.
    + exact F.
    + abstract (
        intros n n' a;
        use funextfun;
        intro x;
        cbn;
        rewrite (presheaf_functor_uses_projections P);
        rewrite (presheaf_functor_uses_projections P');
        apply HF
      ).
  - exact HF.
Defined.

Coercion presheaf_morphism_to_nat_trans
  {T : algebraic_theory_data}
  {P P' : presheaf_data T}
  (f : presheaf_morphism P P')
  : nat_trans P P'
  := pr1 f.

Definition presheaf_morphism_commutes_with_action
  {T : algebraic_theory_data}
  {P P' : presheaf_data T}
  (F : presheaf_morphism P P')
  {m n : nat}
  (t : (P m : hSet))
  (f : stn m → (T n : hSet))
  : F n (action t f) = action (F m t) f
  := pr12 F m n t f.

Lemma presheaf_morphism_eq
  {T : algebraic_theory_data}
  {P P' : presheaf_data T}
  (F F' : presheaf_morphism P P')
  (H : ∏ n, F n = F' n)
  : F = F'.
Proof.
  apply subtypePath.
  {
    intro.
    use isapropdirprod.
    + do 4 (apply impred_isaprop; intro).
      apply setproperty.
    + exact isapropunit.
  }
  apply nat_trans_eq.
  - apply homset_property.
  - exact H.
Qed.

Definition presheaf_data' (T : algebraic_theory_data) : UU
  := ∑ (P : nat → hSet),
    ∏ m n, P m → (stn m → (T n : hSet)) → P n.

Definition presheaf_data'_to_function
  {T : algebraic_theory_data}
  (P : presheaf_data' T)
  : nat → hSet
  := pr1 P.

Coercion presheaf_data'_to_function : presheaf_data' >-> Funclass.

Definition action'
  {T : algebraic_theory_data}
  {P : presheaf_data' T}
  {m n : nat}
  (f : P m)
  (g : stn m → (T n : hSet))
  : P n
  := pr2 P m n f g.

Definition make_presheaf_data'
  {T : algebraic_theory_data}
  (P : nat → hSet)
  (action : ∏ m n, P m → (stn m → (T n : hSet)) → P n)
  : presheaf_data' T
  := P ,, action.

Definition is_assoc' {T : algebraic_theory_data} (P : presheaf_data' T) : UU
  := ∏ l m n (a : P l) f (g : stn m → (T n : hSet)), action' (action' a f) g = action' a (λ i, (f i) • g).

Definition identity_projections' {T : algebraic_theory_data} (P : presheaf_data' T) : UU
  := ∏ n (a : P n), action' a pr = a.

Definition is_presheaf' {T : algebraic_theory_data}
  (P : presheaf_data' T)
  := is_assoc' P ×
    identity_projections' P.

Definition make_is_presheaf'
  {T : algebraic_theory_data}
  {P : presheaf_data' T}
  (H1 : is_assoc' P)
  (H2 : identity_projections' P)
  : is_presheaf' P
  := H1 ,, H2.

Section MakePresheaf'.

  Context {T : algebraic_theory}.
  Context (P : presheaf_data' T).
  Context (H : is_presheaf' P).

  Definition presheaf'_to_functor_data
    : functor_data finite_set_skeleton_category HSET.
  Proof.
    use make_functor_data.
    - exact P.
    - intros n n' a f.
      exact (action' f (λ i, pr (a i))).
  Defined.

  Lemma presheaf'_to_is_functor
    : is_functor presheaf'_to_functor_data.
  Proof.
    split.
    - intro n.
      use funextfun.
      intro t.
      apply (pr2 H).
    - intros l m n f g.
      use funextfun.
      intro h.
      refine (_ @ !pr1 H _ _ _ _ _ _).
      simpl.
      apply maponpaths.
      apply funextfun.
      intro i.
      symmetry.
      apply algebraic_theory_comp_projects_component.
  Qed.

  Definition presheaf'_to_presheaf_data
    : presheaf_data T.
  Proof.
    use make_presheaf_data.
    - use make_functor.
      + exact presheaf'_to_functor_data.
      + exact presheaf'_to_is_functor.
    - exact (pr2 P).
  Defined.

  Lemma presheaf'_to_is_presheaf
    : is_presheaf presheaf'_to_presheaf_data.
  Proof.
    use make_is_presheaf.
    - exact (pr1 H).
    - exact (pr2 H).
    - intros n n' n'' a f g.
      simpl.
      rewrite (pr1 H).
      apply maponpaths.
      apply funextfun.
      intro.
      apply algebraic_theory_comp_projects_component.
  Qed.

  Definition make_presheaf'
    : presheaf T
    := make_presheaf _ presheaf'_to_is_presheaf.

End MakePresheaf'.

Definition theory_presheaf_data
  (T : algebraic_theory)
  : presheaf_data T.
Proof.
  use make_presheaf_data.
  - exact T.
  - intros ? ? f g.
    exact (f • g).
Defined.

Lemma theory_is_presheaf
  (T : algebraic_theory)
  : is_presheaf (theory_presheaf_data T).
Proof.
  use make_is_presheaf.
  - apply algebraic_theory_comp_is_assoc.
  - apply algebraic_theory_comp_identity_projections.
  - apply algebraic_theory_comp_is_natural_l.
Qed.

Definition theory_presheaf
  (T : algebraic_theory)
  : presheaf T
  := make_presheaf _ (theory_is_presheaf T).

(* Definition yoneda_lemma
  (T : algebraic_theory)
  (X : presheaf T)
  : (presheaf_cat T)⟦⟧ *)
