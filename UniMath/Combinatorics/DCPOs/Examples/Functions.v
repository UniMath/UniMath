Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Posets.Basics.
Require Import UniMath.Combinatorics.Posets.MonotoneFunctions.
Require Import UniMath.Combinatorics.Posets.PointedPosets.
Require Import UniMath.Combinatorics.DCPOs.Core.DirectedSets.
Require Import UniMath.Combinatorics.DCPOs.Core.Basics.
Require Import UniMath.Combinatorics.DCPOs.Core.ScottContinuous.
Require Import UniMath.Combinatorics.DCPOs.Examples.Propositions.

Local Open Scope dcpo.

Section FunctionPartialOrder.
  Context (X : UU)
          {Y : hSet}
          (PY : PartialOrder Y).

  Definition funset_hrel
    : hrel (funset X Y)
    := λ f g, ∀ (x : X), PY (f x) (g x).

  Proposition isPartialOrder_funset_hrel
    : isPartialOrder funset_hrel.
  Proof.
    refine ((_ ,, _) ,, _).
    - intros P₁ P₂ P₃ p q x.
      exact (trans_PartialOrder PY (p x) (q x)).
    - intros P x.
      exact (refl_PartialOrder PY (P x)).
    - intros P₁ P₂ p q.
      use funextsec.
      intro x.
      use (antisymm_PartialOrder PY).
      + exact (p x).
      + exact (q x).
  Qed.

  Definition funset_PartialOrder
    : PartialOrder (funset X Y).
  Proof.
    use make_PartialOrder.
    - exact funset_hrel.
    - exact isPartialOrder_funset_hrel.
  Defined.

  Proposition is_monotone_app
              (x : X)
    : is_monotone funset_PartialOrder PY (λ f, f x).
  Proof.
    intros f g p.
    exact (p x).
  Qed.

  Definition app_monotone_function
             (x : X)
    : monotone_function funset_PartialOrder PY
    := (λ f, f x) ,, is_monotone_app x.
End FunctionPartialOrder.

Section FunctionDCPO.
  Context (X : UU)
          (D : dcpo).

  Proposition is_lub_funset_lub
              (E : directed_set (funset_PartialOrder X D))
    : is_least_upperbound
        (funset_PartialOrder X D)
        E
        (λ x, ⨆_{ E} app_monotone_function X D x).
  Proof.
    split.
    - intros i x.
      use less_than_dcpo_lub.
      + exact i.
      + apply refl_dcpo.
    - intros f Hf x.
      use dcpo_lub_is_least.
      intro i ; cbn.
      exact (Hf i x).
  Qed.

  Definition funset_lub
             (E : directed_set (funset_PartialOrder X D))
    : lub (funset_PartialOrder X D) E.
  Proof.
    use make_lub.
    - exact (λ x, ⨆_{E} app_monotone_function X D x).
    - apply is_lub_funset_lub.
  Defined.

  Definition directed_complete_funset_PartialOrder
    : directed_complete_poset (funset_PartialOrder X D)
    := λ I E HE, funset_lub (make_directed_set _ I E HE).

  Definition funset_dcpo_struct
    : dcpo_struct (funset X D).
  Proof.
    use make_dcpo_struct.
    - exact (funset_PartialOrder X D).
    - exact directed_complete_funset_PartialOrder.
  Defined.

  Definition funset_dcpo
    : dcpo
    := _ ,, funset_dcpo_struct.
End FunctionDCPO.

Definition funset_dcppo
           (X : UU)
           (D : dcppo)
  : dcppo.
Proof.
  refine (_ ,, funset_dcpo_struct X D ,, (λ _, ⊥_{D}) ,, _).
  abstract
    (intros f x ;
     apply is_min_bottom_dcppo).
Defined.

Definition hProp_dcppo
  : dcppo.
Proof.
  refine (_ ,, hProp_dcpo_struct ,, hfalse ,, _).
  abstract
    (intros P ;
     exact fromempty).
Defined.

Definition subtype_dcppo
           (X : UU)
  : dcppo
  := funset_dcppo X hProp_dcppo.
