(*****************************************************************

 Basic notions in DCPOs

 In this file, we define the basic notions on DCPOs. We define a
 notion of DCPO structure on sets, because such a notion is
 necessary when using displayed categories. We also give bundled
 definitions, and we provide the necessary lemmas and notations
 for them.

 Note: in the definition of `directed_complete_poset`, there is a
 quantification over all `I` of type `UU`. The universe levels are
 left implicit in Coq, so implicitly, there is an argument that
 indicates the universe level of `I`. This corresponds to how
 DCPOs are developed in Tom de Jong's thesis.

 Contents
 1. Upperbounds
 2. DCPO structures
 3. DCPOs
 4. Accessors for DCPOs
 5. Lemmas for least upperbounds
 6. Pointed DCPOs

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.Posets.PointedPosets.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.

Local Open Scope dcpo.

(**
 1. Upperbounds
 *)
Section Upperbounds.
  Context {X : hSet}
          (PX : PartialOrder X)
          {I : UU}
          (D : I → X).

  Definition is_upperbound
             (x : X)
    : hProp
    := ∀ (i : I), PX (D i) x.

  Definition is_least_upperbound
             (x : X)
    : hProp
    := (is_upperbound x ∧ ∀ (y : X), is_upperbound y ⇒ PX x y)%logic.

  Proposition is_least_upperbound_is_upperbound
              {x : X}
              (Hx : is_least_upperbound x)
    : is_upperbound x.
  Proof.
    exact (pr1 Hx).
  Qed.

  Proposition is_least_upperbound_is_least
              {x : X}
              (Hx : is_least_upperbound x)
              {y : X}
              (Hy : is_upperbound y)
    : PX x y.
  Proof.
    exact (pr2 Hx y Hy).
  Qed.

  Definition lub
    : UU
    := ∑ (x : X), is_least_upperbound x.

  Definition make_lub
             (x : X)
             (Hx : is_least_upperbound x)
    : lub
    := x ,, Hx.

  #[reversible=no] Coercion lub_to_el
           (x : lub)
    : X
    := pr1 x.

  Proposition lub_is_upperbound
              (x : lub)
    : is_upperbound x.
  Proof.
    exact (is_least_upperbound_is_upperbound (pr2 x)).
  Qed.

  Proposition lub_is_least
              (x : lub)
              (y : X)
              (Hy : is_upperbound y)
    : PX x y.
  Proof.
    exact (is_least_upperbound_is_least (pr2 x) Hy).
  Qed.

  Proposition eq_lub
              {x y : X}
              (Hx : is_least_upperbound x)
              (Hy : is_least_upperbound y)
    : x = y.
  Proof.
    pose (x' := (x ,, Hx) : lub).
    pose (y' := (y ,, Hy) : lub).
    use (antisymm_PartialOrder PX).
    - apply (lub_is_least x' y').
      exact (lub_is_upperbound y').
    - apply (lub_is_least y' x').
      exact (lub_is_upperbound x').
  Qed.

  Definition isaprop_lub
    : isaprop lub.
  Proof.
    use invproofirrelevance.
    intros x₁ x₂.
    use subtypePath.
    {
      intro ; apply propproperty.
    }
    use eq_lub.
    - exact (pr2 x₁).
    - exact (pr2 x₂).
  Qed.
End Upperbounds.

Arguments is_least_upperbound_is_upperbound {X PX I D x} Hx.
Arguments is_least_upperbound_is_least {X PX I D x} Hx.
Arguments lub_is_upperbound {X PX I D} x.
Arguments lub_is_least {X PX I D} x.

(**
 2. DCPO structures
 *)
Definition directed_complete_poset
           {X : hSet}
           (PX : PartialOrder X)
  : UU
  := ∏ (I : UU)
       (f : I → X),
     is_directed PX f
     →
     lub PX f.

Proposition isaprop_directed_complete_poset
            {X : hSet}
            (PX : PartialOrder X)
  : isaprop (directed_complete_poset PX).
Proof.
  repeat (use impred ; intro).
  apply isaprop_lub.
Qed.

Definition dcpo_struct (X : hSet)
  : UU
  := ∑ (PX : PartialOrder X), directed_complete_poset PX.

Definition make_dcpo_struct
           {X : hSet}
           (PX : PartialOrder X)
           (HX : directed_complete_poset PX)
  : dcpo_struct X
  := PX ,, HX.

Proposition isaset_dcpo_struct
            (X : hSet)
  : isaset (dcpo_struct X).
Proof.
  use isaset_total2.
  - apply isaset_PartialOrder.
  - intro.
    apply isasetaprop.
    apply isaprop_directed_complete_poset.
Qed.

#[reversible] Coercion dcpo_struct_to_PartialOrder
         {X : hSet}
         (DX : dcpo_struct X)
  : PartialOrder X
  := pr1 DX.

Definition dcpo_struct_lub
           {X : hSet}
           (DX : dcpo_struct X)
           {I : UU}
           (f : I → X)
           (Hf : is_directed DX f)
  : lub DX f
  := pr2 DX I f Hf.

(**
 3. DCPOs
 *)
Definition dcpo
  : UU
  := ∑ (X : hSet), dcpo_struct X.

#[reversible=no] Coercion dcpo_to_hSet (X : dcpo) : hSet := pr1 X.

#[reversible=no] Coercion dcpo_to_PartialOrder (X : dcpo) : PartialOrder X := pr12 X.

Definition dcpo_order {X : dcpo} (x y : X) : hProp := pr12 X x y.

Notation "x ⊑ y" := (dcpo_order x y) (no associativity, at level 70) : dcpo.
(* ⊑ - \sqsubseteq  *)

(**
 4. Accessors for DCPOs
 *)
Proposition refl_dcpo
            {X : dcpo}
            (x : X)
  : x ⊑ x.
Proof.
  apply refl_PartialOrder.
Qed.

Definition eq_to_le_dcpo
           {X : dcpo}
           {x y : X}
           (p : x = y)
  : x ⊑ y.
Proof.
  induction p.
  apply refl_dcpo.
Qed.

Proposition trans_dcpo
            {X : dcpo}
            {x y z : X}
            (p : x ⊑ y)
            (q : y ⊑ z)
  : x ⊑ z.
Proof.
  exact (trans_PartialOrder X p q).
Qed.

Proposition antisymm_dcpo
            {X : dcpo}
            {x y : X}
            (p : x ⊑ y)
            (q : y ⊑ x)
  : x = y.
Proof.
  exact (antisymm_PartialOrder X p q).
Qed.

Definition dcpo_lub
           {X : dcpo}
           (D : directed_set X)
  : X
  := pr22 X _ D (directed_set_is_directed D).

Notation "⨆ D" := (dcpo_lub D) (at level 20) : dcpo.
(* ⊔ - \sqcup *)
Notation "⨆_{ D } f" := (⨆ (f {{ D }})) (at level 20) : dcpo.

Definition make_dcpo_is_least_upperbound
           {X : dcpo}
           (D : directed_set X)
           (x : X)
           (H₁ : ∏ (i : D), D i ⊑ x)
           (H₂ : ∏ (x' : X), (∏ (i : D), D i ⊑ x') → x ⊑ x')
  : is_least_upperbound X D x.
Proof.
  split.
  - exact H₁.
  - exact H₂.
Qed.

Proposition is_least_upperbound_dcpo_lub
            {X : dcpo}
            (D : directed_set X)
  : is_least_upperbound X D (⨆ D).
Proof.
  apply (pr22 X _ D (directed_set_is_directed D)).
Qed.

Proposition less_than_dcpo_lub
            {X : dcpo}
            (D : directed_set X)
            (x : X)
            (i : D)
            (H : x ⊑ D i)
  : x ⊑ ⨆ D.
Proof.
  exact (trans_PartialOrder
           X
           H
           (is_least_upperbound_is_upperbound
              (is_least_upperbound_dcpo_lub D)
              i)).
Qed.

Proposition dcpo_lub_is_least
            {X : dcpo}
            (D : directed_set X)
            (x : X)
            (H : ∏ (i : D), D i ⊑ x)
  : ⨆ D ⊑ x.
Proof.
  exact (is_least_upperbound_is_least (is_least_upperbound_dcpo_lub D) x H).
Qed.

(**
 5. Lemmas for least upperbounds
 *)
Proposition const_lub
            {X : dcpo}
            (x : X)
            (I : UU)
            (i : ∥ I ∥)
  : ⨆ (const_directed_set X x I i) = x.
Proof.
  use antisymm_dcpo.
  - use dcpo_lub_is_least.
    intro j ; cbn.
    apply refl_dcpo.
  - revert i.
    use factor_dep_through_squash.
    {
      intro i.
      apply propproperty.
    }
    intro i ; cbn.
    use less_than_dcpo_lub.
    + exact i.
    + cbn.
      apply refl_dcpo.
Qed.

Proposition is_least_upperbound_dcpo_comp_lub
            {X Y : dcpo}
            (f : monotone_function X Y)
            (D : directed_set X)
  : is_least_upperbound Y (f{{D}}) (⨆_{ D } f).
Proof.
  apply is_least_upperbound_dcpo_lub.
Qed.

Proposition dcpo_lub_eq_pointwise
            {X Y : dcpo}
            (f f' : monotone_function X Y)
            (D : directed_set X)
            (H : ∏ (x : X), f x = f' x)
  : ⨆_{D} f = ⨆_{D} f'.
Proof.
  apply maponpaths.
  apply maponpaths_2.
  apply eq_monotone_function.
  exact H.
Qed.

(**
 6. Pointed DCPOs
 *)
Definition dcppo_struct
           (X : hSet)
  : UU
  := ∑ (DX : dcpo_struct X), bottom_element DX.

#[reversible] Coercion dcppo_struct_to_dcpo_struct
         {X : hSet}
         (DX : dcppo_struct X)
  : dcpo_struct X
  := pr1 DX.

#[reversible=no] Coercion dcppo_to_pointed_PartialOrder
         {X : hSet}
         (DX : dcppo_struct X)
  : pointed_PartialOrder X
  := pr11 DX ,, pr2 DX.

Proposition isaset_dcppo_struct
            (X : hSet)
  : isaset (dcppo_struct X).
Proof.
  use isaset_total2.
  - exact (isaset_dcpo_struct X).
  - intro.
    apply isasetaprop.
    apply isaprop_bottom_element.
Qed.

Definition dcppo
  : UU
  := ∑ (X : hSet), dcppo_struct X.

#[reversible=no] Coercion dcppo_to_dcpo
         (X : dcppo)
  : dcpo
  := pr1 X ,, pr12 X.

Definition bottom_dcppo
           (X : dcppo)
  : X
  := pr122 X.

Notation "⊥_{ X }" := (bottom_dcppo X) : dcpo.
(* ⊥ - \bot*)

Proposition is_min_bottom_dcppo
            {X : dcppo}
            (x : X)
  : ⊥_{ X } ⊑ x.
Proof.
  exact (pr222 X x).
Qed.
