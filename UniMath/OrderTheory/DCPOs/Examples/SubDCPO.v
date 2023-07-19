(*****************************************************************

 Sub DCPO

 If we have a DCPO and a predicate on it, then the subtype of the
 elements satisfying that predicate, is a DCPO if the predicate is
 closed under suprema.

 Contents
 1. The sub DCPO
 2. The first projection is continuous

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.Posets.PointedPosets.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.

Local Open Scope dcpo.

(**
 1. The sub DCPO
 *)
Section SubPartialOrder.
  Context {X : hSet}
          (PX : PartialOrder X)
          (P : X → hProp).

  Let S : hSet := (∑ (x : X), hProp_to_hSet (P x))%set.

  Definition sub_isPartialOrder
    : isPartialOrder (λ (x y : S), PX (pr1 x) (pr1 y)).
  Proof.
    repeat split.
    - intros x₁ x₂ x₃ p q.
      exact (trans_PartialOrder PX p q).
    - intros x.
      apply refl_PartialOrder.
    - intros x y p q.
      use subtypePath.
      {
        intro.
        apply propproperty.
      }
      exact (antisymm_PartialOrder PX p q).
  Qed.

  Definition sub_PartialOrder
    : PartialOrder S.
  Proof.
    use make_PartialOrder.
    - exact (λ x y, PX (pr1 x) (pr1 y)).
    - exact sub_isPartialOrder.
  Defined.

  Definition is_monotone_pr1_sub
    : is_monotone sub_PartialOrder PX pr1.
  Proof.
    intros x y p.
    exact p.
  Qed.

  Definition pr1_sub_monotone
    : monotone_function sub_PartialOrder PX
    := _ ,, is_monotone_pr1_sub.
End SubPartialOrder.

Section SubDCPO.
  Context (X : dcpo)
          (P : X → hProp)
          (HP : ∏ (D : directed_set X),
                (∏ (d : D), P (D d))
                →
                P (⨆ D)).

  Let S : hSet := (∑ (x : X), hProp_to_hSet (P x))%set.

  Definition sub_dcpo_lub
             (D : directed_set (sub_PartialOrder X P))
    : lub (sub_PartialOrder X P) D.
  Proof.
    pose (D' := directed_set_comp (pr1_sub_monotone X P) D).
    use make_lub.
    - refine (⨆ D' ,, HP D' _).
      abstract
        (intro d ;
         exact (pr2 (D d))).
    - split.
      + abstract
          (intro i ; cbn ;
           exact (less_than_dcpo_lub D' (pr1 (D i)) i (refl_dcpo _))).
      + abstract
          (intros x Hx ;
           use (dcpo_lub_is_least D') ;
           intro i ;
           apply (Hx i)).
  Defined.

  Definition sub_dcpo_struct
    : dcpo_struct S.
  Proof.
    use make_dcpo_struct.
    - exact (sub_PartialOrder X P).
    - intros I D HD.
      exact (sub_dcpo_lub (make_directed_set _ I D HD)).
  Defined.

  Definition sub_dcpo
    : dcpo
    := _ ,, sub_dcpo_struct.

  Proposition is_scott_continuous_pr1_sub
    : is_scott_continuous sub_dcpo X pr1.
  Proof.
    use make_is_scott_continuous.
    - exact (is_monotone_pr1_sub X P).
    - cbn.
      intro.
      apply idpath.
  Qed.

  (**
   2. The first projection is continuous
   *)
  Definition pr1_sub_scott_continuous
    : scott_continuous_map sub_dcpo X
    := _ ,, is_scott_continuous_pr1_sub.
End SubDCPO.
