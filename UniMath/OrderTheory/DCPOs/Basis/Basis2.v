(******************************************************************************

 Bases in DCPOs

 We define the notion of a basis of a DCPO. There are two possible approaches:
 1. A basis is given by a predicate on the elements of the DCPO
 2. We have a type of basis elements and a map from that type to the DCPO
 For both approaches, suitable requirements need to be demanded as well.

 We follow Section 4.7 in https://tdejong.com/writings/phd-thesis.pdf, and we
 use the second approach.

 We also study some properties of bases. First of all, we show that every
 continuous DCPO comes equipped with a bases and that every DCPO with a basis
 comes equipped with a continuity structure. Second, we look at the standard
 properties of continuous DCPOs and we reformulate them using the basis. For
 example, in a continuous DCPO the order relation can be characterized using
 the approximations (i.e., `x ⊑ y` if and only if for every `z` such that
 `z ≪ x`, we have `z ≪ y`). Another standard property would be interpolation:
 if we have `x ≪ y`, then we can find an element of the basis `x ≪ b ≪ y`.
 Lastly, we look at the mapping property of a DCPO with a basis. We look at
 three properties:
 1. Two maps are equal if they are equal on the basis
 2. We have `f x ⊑ g x` for every `x` if for every basis element `b` we have
   `f b ⊑ g b`
 3. If we have a monotone map from the basis to some DCPO `Y`, then we can
    extend that map to `X`.
 Note that the map from the third point is unique. The uniqueness would be
 guaranteed if the DCPO is algebraic, but not in general if the DCPO is only
 continuous.

 Contents
 1. Definition of a basis
 2. Accessors and builders for bases
 3. Bases versus continuity
 4. Approximation via bases
 5. Interpolation using bases
 6. Equality of maps via bases
 7. The order on maps via basis elements
 8. Constructing maps from their action on the basis

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.
Require Import UniMath.OrderTheory.DCPOs.Basis.Continuous.
Require Import UniMath.OrderTheory.DCPOs.Basis.Basis.

Section BasisProperties.
  Context {X : dcpo}
          (B : dcpo_basis X).


Proposition map_eq_on_basis_if_scott_continuous
              {Y : dcpo}
              {f g : X → Y}
              (p : ∏ (i : B), f (B i) = g (B i))
              (Hf : is_scott_continuous X Y f)
              (Hg : is_scott_continuous X Y g)
              (x : X)
    : f x = g x.
  Proof.

    exact (maponpaths
             (λ z, pr1 z x)
             (@scott_continuous_map_eq_on_basis Y (f ,, Hf) (g ,, Hg) p)).

  Qed.

End BasisProperties.
