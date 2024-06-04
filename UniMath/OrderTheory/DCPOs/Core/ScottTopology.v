(******************************************************************************

 The Scott topology

 We define the notions of Scott open and of Scott closed subsets of DCPOs. A
 Scott open set is upwards closed and inaccessible by least upperbounds, and
 Scott closed sets are downwards closed and closed under suprema. Note that
 to prove that the complement of a Scott closed set is Scott open, one needs
 the law of excluded middle (Lemma 2.9 in https://arxiv.org/pdf/2106.05064.pdf).
 We also prove some basic properties of these sets.

 References:
 - Section 2 in the chapter 'Domain Theory' of the Handbook for Logic in
   Computer Science, Volume 3 (https://www.cs.ox.ac.uk/files/298/handbook.pdf)
 - https://arxiv.org/pdf/2106.05064.pdf

 Contents
 1. Lower and upper sets
 2. Scott open and Scott closed sets
 3. Bundled definitions of Scott open and Scott closed sets
 4. Accessors for Scott open and Scott closed sets
 5. Lower sets are Scott closed
 6. Upper sets (with respect to the way-below relation) are Scott open
 7. Empty and top sets are Scott open
 8. Complements of Scott open sets

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.
Require Import UniMath.OrderTheory.DCPOs.Basis.Continuous.

Local Open Scope dcpo.

Section ScottTopology.
  Context {X : dcpo}.

  (**
   1. Lower and upper sets
   *)
  Definition is_lower_set
             (P : X → hProp)
    : hProp
    := (∀ (x y : X), P y ⇒ x ⊑ y ⇒ P x)%logic.

  Definition is_upper_set
             (P : X → hProp)
    : hProp
    := (∀ (x y : X), P x ⇒ x ⊑ y ⇒ P y)%logic.

  (**
   2. Scott open and Scott closed sets
   *)
  Definition is_lub_inaccessible
             (P : X → hProp)
    : hProp
    := (∀ (D : directed_set X), P(⨆ D) ⇒ ∃ (i : D), P(D i))%logic.

  Definition is_closed_under_lub
             (P : X → hProp)
    : hProp
    := (∀ (D : directed_set X), (∀ (i : D), P (D i)) ⇒ P(⨆ D))%logic.

  Definition is_scott_closed
             (P : X → hProp)
    : hProp
    := is_lower_set P ∧ is_closed_under_lub P.

  Definition is_scott_open
             (P : X → hProp)
    : hProp
    := is_upper_set P ∧ is_lub_inaccessible P.
End ScottTopology.

(**
 3. Bundled definitions of Scott open and Scott closed sets
 *)
Definition scott_open_set
           (X : dcpo)
  : UU
  := ∑ (P : X → hProp), is_scott_open P.

Definition scott_open_set_to_pred
           {X : dcpo}
           (P : scott_open_set X)
           (x : X)
  : hProp
  := pr1 P x.

Coercion scott_open_set_to_pred : scott_open_set >-> Funclass.

#[reversible=no] Coercion is_scott_open_scott_open_set
          {X : dcpo}
          (P : scott_open_set X)
  : is_scott_open P
  := pr2 P.

Definition scott_closed_set
           (X : dcpo)
  : UU
  := ∑ (P : X → hProp), is_scott_closed P.

Definition scott_closed_set_to_pred
           {X : dcpo}
           (P : scott_closed_set X)
           (x : X)
  : hProp
  := pr1 P x.

Coercion scott_closed_set_to_pred : scott_closed_set >-> Funclass.

#[reversible=no] Coercion is_scott_closed_scott_closed_set
          {X : dcpo}
          (P : scott_closed_set X)
  : is_scott_closed P
  := pr2 P.

(**
 4. Accessors for Scott open and Scott closed sets
 *)
Section ScottClosedAccessors.
  Context {X : dcpo}
          {P : X → hProp}
          (HP : is_scott_closed P).

  Proposition is_scott_closed_lower_set
              {x y : X}
              (Py : P y)
              (p : x ⊑ y)
    : P x.
  Proof.
    exact (pr1 HP x y Py p).
  Qed.

  Proposition is_scott_closed_lub
              (D : directed_set X)
              (HD : ∀ (i : D), P (D i))
    : P(⨆ D).
  Proof.
    exact (pr2 HP D HD).
  Qed.
End ScottClosedAccessors.

Section ScottOpenAccessors.
  Context {X : dcpo}
          {P : X → hProp}
          (HP : is_scott_open P).

  Proposition is_scott_open_upper_set
              {x y : X}
              (Py : P x)
              (p : x ⊑ y)
    : P y.
  Proof.
    exact (pr1 HP x y Py p).
  Qed.

  Proposition is_scott_open_lub_inaccessible
              (D : directed_set X)
              (HD : P(⨆ D))
    : ∃ (i : D), P (D i).
  Proof.
    exact (pr2 HP D HD).
  Qed.
End ScottOpenAccessors.

Section PropertiesScottTopology.
  Context {X : dcpo}.

  (**
   5. Lower sets are Scott closed
   *)
  Proposition lower_set_is_scott_closed
              (x : X)
    : is_scott_closed (λ y, y ⊑ x).
  Proof.
    split.
    - intros y₁ y₂ p q.
      exact (trans_dcpo q p).
    - intros D H.
      use dcpo_lub_is_least.
      exact H.
  Qed.

  (**
   6. Upper sets (with respect to the way-below relation) are Scott open
   *)
  Proposition upper_set_is_scott_open
              (CX : continuous_dcpo_struct X)
              (x : X)
    : is_scott_open (λ y, x ≪ y).
  Proof.
    split.
    - intros y₁ y₂ p q.
      exact (trans_way_below_le p q).
    - intros D p.
      assert (H := unary_interpolation CX p).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intro z.
      induction z as [ z [ q₁ q₂ ]].
      assert (H := q₂ D (refl_dcpo _)).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intro i.
      induction i as [ i r ].
      refine (hinhpr (i ,, _)).
      exact (trans_way_below_le q₁ r).
  Qed.

  (** * 7. Empty and top sets are Scott open *)
  Definition true_scott_open_set
    (A : dcpo)
    : scott_open_set A.
  Proof.
    simple refine (_ ,, _).
    - exact (λ _, htrue).
    - split.
      + abstract
          (intros x y p q ;
           exact tt).
      + abstract
          (intros D x ;
           assert (H := directed_set_el D) ;
           revert H ;
           use factor_through_squash_hProp ;
           intro d ;
           exact (hinhpr (d ,, tt))).
  Defined.

  Definition false_scott_open_set
    (A : dcpo)
    : scott_open_set A.
  Proof.
    simple refine (_ ,, _).
    - exact (λ _, hfalse).
    - split.
      + abstract (intros x y p q; exact (fromempty p)).
      + abstract (intros D p; exact (fromempty p)).
  Defined.

  (**
   8. Complements of Scott open sets
   *)
  Proposition complement_of_scott_open
              (P : X → hProp)
              (HP : is_scott_open P)
    : is_scott_closed (λ x, ¬(P x))%logic.
  Proof.
    split.
    - cbn ; intros x y p q H.
      apply p.
      use (pr1 HP x).
      + exact H.
      + exact q.
    - cbn ; intros D HD p.
      assert (H := is_scott_open_lub_inaccessible HP D p).
      revert H.
      use factor_through_squash.
      {
        apply isapropempty.
      }
      intro i.
      induction i as [ i Hi ].
      apply (HD i).
      exact Hi.
  Qed.
End PropertiesScottTopology.
