Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

(* Subtypes *)

Definition subtype_intersection
  (X : UU)
  (Y Y' : hsubtype X)
  : hsubtype X.
Proof.
  intro x.
  exists (Y x ∧ Y' x).
  abstract (
    apply isapropdirprod;
    apply propproperty
  ).
Defined.

Notation "X ∩ Y" :=
  (subtype_intersection _ X Y)
  (at level 50, left associativity).

Definition subtype_union
  (X : UU)
  (Y Y' : hsubtype X)
  : hsubtype X
  := λ x, Y x ∨ Y' x.

Notation "X ∪ Y" :=
  (subtype_union _ X Y)
  (at level 51, left associativity).

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

Notation "⋂ Y" :=
  (subtype_family_intersection _ _ Y)
  (at level 52, no associativity).

Definition subtype_family_union
  (X I : UU)
  (Y : I → hsubtype X)
  : hsubtype X
  := λ x, ∃ i, Y i x.

Notation "⋃ Y" :=
  (subtype_family_union _ _ Y)
  (at level 52, no associativity).

Definition total_subtype
  (X : UU)
  : hsubtype X
  := λ x, htrue.

Definition empty_subtype
  (X : UU)
  : hsubtype X
  := λ x, hfalse.

Definition subsubtype
  {X : UU}
  (Y Y' : hsubtype X)
  : UU
  := ∏ x, (Y x → Y' x).

Notation "Y ⊆ Y'" :=
  (subsubtype Y Y')
  (at level 70, no associativity).

Definition not_subsubtype
  {X : UU}
  (Y Y' : hsubtype X)
  : UU
  := ∑ x, Y x ∧ hneg (Y' x).

Notation "Y ⊈ Y'" :=
  (not_subsubtype Y Y')
  (at level 70, no associativity).

Lemma not_subsubtype_to_not_subsubtype
  {X : UU}
  (Y Y' : hsubtype X)
  : (Y ⊈ Y') → ¬ (Y ⊆ Y').
Proof.
  intros H1 H2.
  refine (pr2 (pr2 H1) _).
  apply H2, H1.
Qed.

Lemma subsubtype_to_not_not_subtype
  {X : UU}
  (Y Y' : hsubtype X)
  : (Y ⊆ Y') → ¬ (Y ⊈ Y').
Proof.
  intros H1 H2.
  exact (not_subsubtype_to_not_subsubtype _ _ H2 H1).
Qed.

Definition equivalent_subtypes
  {X : UU}
  (Y Y' : hsubtype X)
  : UU
  := Y ⊆ Y' × Y' ⊆ Y.

Notation "Y ≡ Y'" :=
  (equivalent_subtypes Y Y')
  (at level 70, no associativity).

Definition nonequivalent_subtypes
  {X : UU}
  (Y Y' : hsubtype X)
  : UU
  := (Y ⊈ Y') ⨿ (Y' ⊈ Y).

Notation "Y ≢ Y'" :=
  (nonequivalent_subtypes Y Y')
  (at level 70, no associativity).

Lemma nonequivalent_subtype_to_not_equivalent
  {X : UU}
  (Y Y' : hsubtype X)
  : (Y ≢ Y') → ¬ (Y ≡ Y').
Proof.
  intros H1 H2.
  induction H1 as [H1 | H1];
    refine (pr2 (pr2 H1) _);
    apply H2, H1.
Qed.

Lemma equivalent_subtype_to_not_nonequivalent
  {X : UU}
  (Y Y' : hsubtype X)
  : (Y ≡ Y') → ¬ (Y ≢ Y').
Proof.
  intros H1 H2.
  exact (nonequivalent_subtype_to_not_equivalent _ _ H2 H1).
Qed.

Definition subtype_subtype_weq
  {X : UU}
  (Y : hsubtype X)
  : hsubtype Y ≃ ∑ (Z : hsubtype X), Z ⊆ Y.
Proof.
  use weq_iso.
  - intro Z.
    use tpair.
    + intro x.
      exists (∑ (H : Y x), Z (x ,, H)).
      abstract apply isaprop_total2.
    + abstract exact (λ x, pr1).
  - intro Z.
    intro x.
    exact (pr1 Z (pr1 x)).
  - abstract (
      intro Z;
      apply funextfun;
      intro y;
      apply hPropUnivalence;
      [ intro z';
        refine (transportf _ _ (pr2 z'));
        apply propproperty
      | intro z;
        exact (pr2 y ,, z) ]
    ).
  - abstract (
      intro;
      apply subtypePairEquality;
      [ intro x;
        unfold subsubtype;
        apply impred;
        intro;
        apply impredfun;
        apply propproperty
      | apply funextfun;
        intro x;
        apply hPropUnivalence;
        [ intro z';
          exact (pr2 z')
        | intro z;
          exact (pr2 y _ z ,, z) ]]
    ).
Defined.

(* Topology *)

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
  := is_open (total_subtype X).

Arguments total_is_open_ax /.

Definition empty_is_open_ax
  (X : topological_space_data)
  : UU
  := is_open (empty_subtype X).

Arguments empty_is_open_ax /.

Definition union_is_open_ax
  (X : topological_space_data)
  (I : UU)
  (Y : I → open X)
  : UU
  := is_open (⋃ Y).

Arguments union_is_open_ax /.

Definition intersection_is_open_ax
  (X : topological_space_data)
  (Y Y' : open X)
  : UU
  := is_open (Y ∩ Y').

Arguments intersection_is_open_ax /.

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

Definition connected
  (X : topological_space)
  : UU
  := ∏ (Y Y' : open X),
    Y ∪ Y' ≡ total_subtype X →
    Y ∩ Y' ≡ empty_subtype X →
      ((Y ≡ total_subtype X) ⨿
      (Y' ≡ total_subtype X)).

Definition disconnected
  (X : topological_space)
  : UU
  := ∑ (Y Y' : open X),
    Y ∪ Y' ≡ total_subtype X ×
    Y ∩ Y' ≡ empty_subtype X ×
    Y ≢ total_subtype X ×
    Y' ≢ total_subtype X.

Lemma disconnected_to_not_connected
  (X : topological_space)
  : disconnected X → ¬ connected X.
Proof.
  intros H1 H2.
  unfold disconnected, connected in *.
  induction (H2 (pr1 H1) (pr1 (pr2 H1)) (pr1 (pr2 (pr2 H1))) (pr1 (pr2 (pr2 (pr2 H1))))) as [H3 | H3].
  - exact (nonequivalent_subtype_to_not_equivalent _ _ (pr1 (pr2 (pr2 (pr2 (pr2 H1))))) H3).
  - exact (nonequivalent_subtype_to_not_equivalent _ _ (pr2 (pr2 (pr2 (pr2 (pr2 H1))))) H3).
Qed.

Lemma connected_to_not_disconnected
  (X : topological_space)
  : connected X → ¬ disconnected X.
Proof.
  intros H1 H2.
  exact (disconnected_to_not_connected X H2 H1).
Qed.

(* Examples / constructions *)

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

Definition subspace_topology
  (X : topological_space)
  (Y : hsubtype X)
  : topological_space.
Proof.
  use tpair.
  - exists (carrier_subset Y).
    intro U.
    exact (∃ V : open X, pr1 (subtype_subtype_weq _ U) ≡ Y ∩ V).
  - repeat split.
    + apply hinhpr.
      exists total_open.
      split;
      exact (λ x y, y).
    + apply hinhpr.
      exists empty_open.
      split;
      exact (λ x y, y).
    + intros I Z.
      apply hinhpr.
      (* Stuck here *)
      admit.
    + intros Z Z'.
      induction Z as [Z HZ].
      induction Z' as [Z' HZ'].
      revert HZ HZ'.
      simpl.
      refine (hinhfun2 _).
      intros HZ HZ'.
      exists (intersection_open (pr1 HZ) (pr1 HZ')).
      * cbn.
        split;
          intros x Hx.
        -- refine (
            pr1 Hx ,,
            pr2 (pr1 (pr2 HZ) x (pr1 Hx ,, pr1 (pr2 Hx))) ,,
            pr2 (pr1 (pr2 HZ') x (pr1 Hx ,, pr2 (pr2 Hx)))
          ).
        -- exists (pr1 Hx).
          split.
          ++ refine (transportf _ _ (pr2 (pr2 (pr2 HZ) x (pr1 Hx ,, pr1 (pr2 Hx))))).
            apply propproperty.
          ++ refine (transportf _ _ (pr2 (pr2 (pr2 HZ') x (pr1 Hx ,, pr2 (pr2 Hx))))).
            apply propproperty.
Abort.
