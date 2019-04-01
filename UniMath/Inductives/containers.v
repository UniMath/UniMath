Require Export UniMath.Inductives.functors.


Definition Container (I J : UU) :=
  ∑ S : J -> UU,
        ∏ j, S j -> I -> UU.

Definition build_container {I J : UU}
           (S : J -> UU) (P : ∏ j, S j -> I -> UU) :
  Container I J :=
  S,, P.
Infix "◁" := build_container (at level 50).

Definition container_shapes {I J : UU} (c : Container I J) :
  J -> UU :=
  pr1 c.
Notation "c '.S'" := (container_shapes c) (at level 5).

Definition container_positions {I J : UU} (c : Container I J) :
  ∏ j, c.S j -> I -> UU :=
  pr2 c.
Notation "c '.P'" := (container_positions c) (at level 5).

Definition container_extension {I J} (c : Container I J) : functor I J.
Proof.
  use build_functor.
  - exact (λ X j, ∑ s : c.S j, ∏ i, c.P j s i -> X i).
  - cbn.
    exact (λ X Y f j x, tpair (λ s, ∏ i, c.P j s i -> Y i)
                              (pr1 x)
                              (λ i p, f i (pr2 x i p))).
  - reflexivity.
  - reflexivity.
Defined.
Notation "⟦ c ⟧" := (container_extension c).