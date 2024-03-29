Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Section Subtypes.

  Definition subtype_intersection
    (X : UU)
    (Y Y' : hsubtype X)
    : hsubtype X.
  Proof.
    intro x.
    exists (Y x × Y' x).
    abstract (
      apply isapropdirprod;
      apply propproperty
    ).
  Defined.

  Definition subtype_union
    (X : UU)
    (Y Y' : hsubtype X)
    : hsubtype X
    := λ x, Y x ∨ Y' x.

  Definition subtype_family_intersection
    (X I : UU)
    (Y : I → hsubtype X)
    : hsubtype X.
  Proof.
    intro x.
    exists (∏ i, Y i x).
    abstract (
      apply impred;
      intro i;
      apply propproperty
    ).
  Defined.

  Definition subtype_family_union
    (X I : UU)
    (Y : I → hsubtype X)
    : hsubtype X
    := λ x, ∃ i, Y i x.

End Subtypes.

Notation "X ∩ Y" :=
  (subtype_intersection _ X Y)
  (at level 50, left associativity).

Notation "X ∪ Y" :=
  (subtype_union _ X Y)
  (at level 51, left associativity).

Notation "⋂ Y" :=
  (subtype_family_intersection _ _ Y)
  (at level 52, no associativity).

Notation "⋃ Y" :=
  (subtype_family_union _ _ Y)
  (at level 52, no associativity).

Section Topology.

  Definition topological_space_data
    : UU
    := ∑ (X : hSet), hsubtype (hsubtype X).

  Coercion topological_space_data_to_set
    (X : topological_space_data)
    : hSet
    := pr1 X.

  Definition is_open
    {X : topological_space_data}
    (Y : hsubtype X)
    : hProp
    := pr2 X Y.

  Definition open
    (X : topological_space_data)
    : UU
    := carrier (is_open (X := X)).

  Coercion open_to_subtype
    {X : topological_space_data}
    (Y : open X)
    : hsubtype X
    := pr1 Y.

  Definition open_is_open
    {X : topological_space_data}
    (Y : open X)
    : is_open Y
    := pr2 Y.

  Definition total_is_open_ax
    (X : topological_space_data)
    : UU
    := is_open (λ (x : X), htrue).

  Definition empty_is_open_ax
    (X : topological_space_data)
    : UU
    := is_open (λ (x : X), hfalse).

  Definition union_is_open_ax
    (X : topological_space_data)
    (I : UU)
    (Y : I → open X)
    : UU
    := is_open (⋃ Y).

  Definition intersection_is_open_ax
    (X : topological_space_data)
    (Y Y' : open X)
    : UU
    := is_open (Y ∩ Y').

  Definition is_topological_space (X : topological_space_data) : UU :=
    (total_is_open_ax X) ×
    (empty_is_open_ax X) ×
    (∏ I Y, union_is_open_ax X I Y) ×
    (∏ Y Y', intersection_is_open_ax X Y Y').

  Definition topological_space
    : UU
    := ∑ X, is_topological_space X.

  Coercion topological_space_to_topological_space_data
    (X : topological_space)
    : topological_space_data
    := pr1 X.

  Definition total_is_open
    (X : topological_space)
    : total_is_open_ax X
    := pr1 (pr2 X).

  Definition total_open
    {X : topological_space}
    : open X
    := make_carrier _ _ (total_is_open X).

  Definition empty_is_open
    (X : topological_space)
    : empty_is_open_ax X
    := pr1 (pr2 (pr2 X)).

  Definition empty_open
    {X : topological_space}
    : open X
    := make_carrier _ _ (empty_is_open X).

  Definition union_is_open
    (X : topological_space)
    (I : UU)
    (Y : I → open X)
    : union_is_open_ax X I Y
    := pr1 (pr2 (pr2 (pr2 X))) I Y.

  Definition union_open
    {X : topological_space}
    {I : UU}
    (Y : I → open X)
    : open X
    := make_carrier _ _ (union_is_open X I Y).

  Definition intersection_is_open
    (X : topological_space)
    (Y Y' : open X)
    : intersection_is_open_ax X Y Y'
    := pr2 (pr2 (pr2 (pr2 X))) Y Y'.

  Definition intersection_open
    {X : topological_space}
    (Y Y' : open X)
    : open X
    := make_carrier _ _ (intersection_is_open X Y Y').

End Topology.

Definition discrete_topology
  (X : hSet)
  : topological_space.
Proof.
  use tpair.
  - exists X.
    exact (λ x, htrue).
  - repeat split.
Qed.

Definition indiscrete_topology
  (X : hSet)
  : topological_space.
Proof.
  use tpair.
  - exists X.
    intro U.
    use tpair.
    exact (∏ x y, U x <-> U y).
    abstract (
      do 2 (apply impred; intro);
      apply isapropdirprod;
      apply impredfun;
      apply propproperty
    ).
  - split; [|split;[|split]].
    + split; apply tounit.
    + split; apply fromempty.
    + intros I Y.
      split;
      apply hinhfun;
      intro H;
      induction H as [i H];
      exists i;
      exact (pr1 (open_is_open (Y i) _ _) H).
    + intros Y Y' x y;
      split;
      intro H;
      ( split;
        [ exact (pr1 (open_is_open Y _ _) (pr1 H))
        | exact (pr1 (open_is_open Y' _ _) (pr2 H)) ] ).
Qed.
