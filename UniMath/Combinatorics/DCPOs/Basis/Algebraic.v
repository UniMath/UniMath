(******************************************************************************

 Algebraic DCPOs

 Continuous DCPOs are those with a basis: every elements is the supremum of all
 elements that are way below it. The notion of algebraic DCPO is strong. It
 says that there is a basis consisting of only compact elements (which are the
 elements `x` such that `x ≪ x`).

 References:
 - Section 2 in https://www.cs.ox.ac.uk/files/298/handbook.pdf
 - Section 4.6 in https://tdejong.com/writings/phd-thesis.pdf

 Contents
 1. Compact elements
 2. Algebraic DCPOs (as structure)
 3. Algebraic DCPOs (as property)
 4. Algebraic DCPOs to continuous DCPOs

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.DCPOs.Core.DirectedSets.
Require Import UniMath.Combinatorics.DCPOs.Core.Basics.
Require Import UniMath.Combinatorics.DCPOs.Core.WayBelow.
Require Import UniMath.Combinatorics.DCPOs.Basis.Continuous.

Local Open Scope dcpo.

(**
 1. Compact elements
 *)
Definition is_compact_el
           {X : dcpo}
           (x : X)
  : hProp
  := x ≪ x.

Proposition is_compact_bot
            (X : dcppo)
  : is_compact_el (⊥_{X}).
Proof.
  apply bot_way_below.
Qed.

Definition compact_elements
           (X : dcpo)
  : UU
  := ∑ (x : X), is_compact_el x.

(**
 2. Algebraic DCPOs (as structure)
 *)
Definition algebraic_dcpo_struct
           (X : dcpo)
  : UU
  := ∏ (x : X),
     ∑ (D : directed_set X),
     (∏ (i : D), is_compact_el (D i))
     ×
     is_least_upperbound X D x.

Section AlgebraicDCPOAccessors.
  Context {X : dcpo}
          (AX : algebraic_dcpo_struct X).

  Definition compact_approximating_family
             (x : X)
    : directed_set X
    := pr1 (AX x).

  Proposition is_compact_approximating_family
              (x : X)
              (i : compact_approximating_family x)
    : is_compact_el (compact_approximating_family x i).
  Proof.
    exact (pr12 (AX x) i).
  Qed.

  Proposition compact_approximating_family_lub
              (x : X)
    : ⨆ (compact_approximating_family x) = x.
  Proof.
    use antisymm_dcpo.
    - use dcpo_lub_is_least.
      intro i.
      exact (pr122 (AX x) i).
    - use (is_least_upperbound_is_least (pr22 (AX x))).
      apply is_least_upperbound_is_upperbound.
      apply is_least_upperbound_dcpo_lub.
  Qed.

  Proposition compact_approximating_family_way_below
              (x : X)
              (i : compact_approximating_family x)
    : compact_approximating_family x i ≪ x.
  Proof.
    refine (trans_way_below_le (is_compact_approximating_family x i) _).
    exact (pr122 (AX x) i).
  Qed.
End AlgebraicDCPOAccessors.

(**
 3. Algebraic DCPOs (as property)
 *)
Definition is_algebraic_dcpo
           (X : dcpo)
  : hProp
  := ∥ algebraic_dcpo_struct X ∥.

(**
 4. Algebraic DCPOs to continuous DCPOs
 *)
Definition algebraic_dcpo_struct_to_continuous
           {X : dcpo}
           (AX : algebraic_dcpo_struct X)
  : continuous_dcpo_struct X.
Proof.
  intro x.
  refine (compact_approximating_family AX x ,, _ ,, _).
  - abstract
      (intro i ;
       apply compact_approximating_family_way_below).
  - abstract (apply AX).
Defined.
