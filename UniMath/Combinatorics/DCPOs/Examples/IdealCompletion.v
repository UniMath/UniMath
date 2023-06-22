(******************************************************************************

 The rounded ideal completion

 In this file, we study the rounded ideal completion. Given an abstract basis,
 the rounded ideal completion gives a continuous DCPO with that particular
 basis. If the basis is reflexive (a preorder), then the resulting DCPO is
 algebraic.

 Given an abstract basis, the rounded ideal completion is defined to be the
 DCPO whose inhabitants are ideal (i.e., directed lower sets of the basis). As
 such, there are some nuances regarding the universe level. Let's say, the
 basis lives in some universe U_ℓ. Then the ideal completion lives in the
 universe U_{ℓ⁺}. However, using propositional resizing, we can improve on this
 situation. This is because all propositions are equivalent to one in the
 lowest universe (which we call U_0). Then the rounded ideal completion lives
 in U_{max ℓ 1}.

 References:
 - Section 2.2.6 in https://www.cs.ox.ac.uk/files/298/handbook.pdf
 - Section 4.10 in https://tdejong.com/writings/phd-thesis.pdf

 Contents
 1. Abstract bases
 2. Preorder to abstract basis
 3. Ideals
 4. Rounded ideal completion
 5. Rounded ideal completion for reflexive bases

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Posets.
Require Import UniMath.Combinatorics.DCPOs.Core.DirectedSets.
Require Import UniMath.Combinatorics.DCPOs.Core.Basics.
Require Import UniMath.Combinatorics.DCPOs.Core.ScottContinuous.
Require Import UniMath.Combinatorics.DCPOs.Core.WayBelow.
Require Import UniMath.Combinatorics.DCPOs.Basis.Continuous.
Require Import UniMath.Combinatorics.DCPOs.Basis.Algebraic.
Require Import UniMath.Combinatorics.DCPOs.Basis.Basis.
Require Import UniMath.Combinatorics.DCPOs.Basis.CompactBasis.
Require Import UniMath.Combinatorics.DCPOs.Examples.Products.
Require Import UniMath.Combinatorics.DCPOs.Examples.SubDCPO.
Require Import UniMath.Combinatorics.DCPOs.Examples.Propositions.

Local Open Scope dcpo.

(**
 1. Abstract bases
 *)
Definition abstract_basis_data
  : UU
  := ∑ (X : UU), X → X → hProp.

Coercion type_of_abstract_basis_data
         (B : abstract_basis_data)
  : UU
  := pr1 B.

Definition rel_of_abstract_basis_data
           {B : abstract_basis_data}
           (b₁ b₂ : B)
  : hProp
  := pr2 B b₁ b₂.

Notation "b₁ ≺ b₂" := (rel_of_abstract_basis_data b₁ b₂) (at level 70).

Definition make_abstract_basis_data
           (X : Type)
           (R : X → X → UU)
           (HR : ∏ (x y : X), isaprop (R x y))
  : abstract_basis_data
  := X ,, λ x y, make_hProp (R x y) (HR x y).

Definition abstract_basis_laws
           (B : abstract_basis_data)
  : UU
  := (istrans (λ (b₁ b₂ : B), b₁ ≺ b₂)
     ×
     (∏ (a : B), ∃ (b : B), b ≺ a)
     ×
     (∏ (a₁ a₂ b : B), a₁ ≺ b → a₂ ≺ b → ∃ (a : B), a ≺ b × a₁ ≺ a × a₂ ≺ a))%type.

Definition abstract_basis
  : UU
  := ∑ (B : abstract_basis_data), abstract_basis_laws B.

Definition make_abstract_basis
           (B : abstract_basis_data)
           (HB : abstract_basis_laws B)
  : abstract_basis
  := B ,, HB.

Coercion abstract_basis_to_data
         (B : abstract_basis)
  : abstract_basis_data
  := pr1 B.

Proposition trans_abstract_basis
            {B : abstract_basis}
            {b₁ b₂ b₃ : B}
            (p : b₁ ≺ b₂)
            (q : b₂ ≺ b₃)
  : b₁ ≺ b₃.
Proof.
  exact (pr12 B b₁ b₂ b₃ p q).
Qed.

Proposition nullary_interpolation_abstract_basis
            {B : abstract_basis}
            (a : B)
  : ∃ (b : B), b ≺ a.
Proof.
  exact (pr122 B a).
Qed.

Proposition binary_interpolation_abstract_basis
            {B : abstract_basis}
            {a₁ a₂ b : B}
            (p : a₁ ≺ b)
            (q : a₂ ≺ b)
  : (∃ (a : B), a ≺ b × a₁ ≺ a × a₂ ≺ a)%type.
Proof.
  exact (pr222 B a₁ a₂ b p q).
Qed.

Definition is_reflexive_abstract_basis
           (B : abstract_basis)
  : UU
  := isrefl (λ (b₁ b₂ : B), b₁ ≺ b₂).

(**
 2. Preorder to abstract basis
 *)
Section PreorderToBasis.
  Context (X : PreorderedSet).

  Definition preorder_to_abstract_basis_data
    : abstract_basis_data.
  Proof.
    use make_abstract_basis_data.
    - exact X.
    - exact (λ x y, PreorderedSetRelation X x y).
    - intros x y.
      apply propproperty.
  Defined.

  Proposition preorder_to_abstract_basis_laws
    : abstract_basis_laws preorder_to_abstract_basis_data.
  Proof.
    repeat split.
    - apply istrans_po.
    - intros a.
      refine (hinhpr (a ,, _)).
      apply isrefl_po.
    - intros a₁ a₂ b p q.
      refine (hinhpr (b ,, _ ,, p ,, q)).
      apply isrefl_po.
  Qed.

  Definition preorder_to_abstract_basis
    : abstract_basis.
  Proof.
    use make_abstract_basis.
    - exact preorder_to_abstract_basis_data.
    - exact preorder_to_abstract_basis_laws.
  Defined.
End PreorderToBasis.

(**
 3. Ideals
 *)
Section Ideals.
  Context {B : abstract_basis}.

  Definition is_ideal
             (P : B → hProp)
    : hProp
    := ((∃ (b : B), P b)
       ∧
       (∀ (a₁ a₂ : B), P a₁ ⇒ P a₂ ⇒ ∃ (b : B), P b ∧ a₁ ≺ b ∧ a₂ ≺ b)
       ∧
       (∀ (a b : B), P b ⇒ a ≺ b ⇒ P a))%logic.

  Definition is_ideal_el
             {P : B → hProp}
             (HP : is_ideal P)
    : ∃ (b : B), P b
    := pr1 HP.

  Definition is_ideal_top
             {P : B → hProp}
             (HP : is_ideal P)
             {a₁ a₂ : B}
             (Ha₁ : P a₁)
             (Ha₂ : P a₂)
    : ∃ (b : B), P b ∧ a₁ ≺ b ∧ a₂ ≺ b
    := pr12 HP a₁ a₂ Ha₁ Ha₂.

  Definition is_ideal_lower_set
             {P : B → hProp}
             (HP : is_ideal P)
             {a b : B}
             (Hb : P b)
             (p : a ≺ b)
    : P a
    := pr22 HP a b Hb p.

  Proposition is_ideal_rounded
              {P : B → hProp}
              (HP : is_ideal P)
              {a : B}
              (Ha : P a)
    : ∃ (b : B), a ≺ b ∧ P b.
  Proof.
    assert (H := is_ideal_top HP Ha Ha).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros b.
    induction b as ( b & p₁ & p₂ & p₃ ).
    exact (hinhpr (b ,, p₂ ,, p₁)).
  Qed.
End Ideals.

(**
 4. Rounded ideal completion
 *)
Section RoundedIdealCompletion.
  Context (B : abstract_basis).

  Proposition lub_of_ideals
              (D : directed_set (funset_dcpo B hProp_dcpo))
              (HD : ∏ (d : D), is_ideal (D d))
    : is_ideal (⨆ D).
  Proof.
    simple refine (_ ,, _ ,, _).
    - assert (H := directed_set_el D).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intro d.
      assert (H := is_ideal_el (HD d)).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intro b.
      induction b as [ b p ].
      exact (hinhpr (b ,, hinhpr (d ,, p))).
    - intros a₁ a₂.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros Ha₁ ; cbn in Ha₁.
      induction Ha₁ as [ d₁ p₁ ].
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros Ha₂ ; cbn in Ha₂.
      induction Ha₂ as [ d₂ p₂ ].
      assert (H := directed_set_top D d₁ d₂).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intro H ; cbn in H.
      induction H as [ dt [ H₁ H₂ ]].
      assert (H := is_ideal_top (HD dt) (H₁ a₁ p₁) (H₂ a₂ p₂)).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros H.
      induction H as ( b & q₁ & q₂ & q₃ ).
      exact (hinhpr (b ,, hinhpr (dt ,, q₁) ,, q₂ ,, q₃)).
    - intros a b.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intros H q ; cbn in H.
      induction H as [ d p ] ; cbn.
      refine (hinhpr (d ,, _)).
      exact (is_ideal_lower_set (HD d) p q).
  Qed.

  Definition rounded_ideal_completion
    : dcpo
    := sub_dcpo
         (funset_dcpo B hProp_dcpo)
         is_ideal
         lub_of_ideals.

  Definition in_rounded_ideal
             (b : B)
             (I : rounded_ideal_completion)
    : hProp
    := pr1 I b.

  Local Notation "b ∈ I" := (in_rounded_ideal b I).

  Proposition is_ideal_principal_ideal
              (b : B)
    : is_ideal (λ a, a ≺ b).
  Proof.
    repeat split.
    - exact (nullary_interpolation_abstract_basis b).
    - intros a₁ a₂ p q.
      exact (binary_interpolation_abstract_basis p q).
    - intros a₁ a₂ p q.
      exact (trans_abstract_basis q p).
  Qed.

  Definition principal_ideal
    : B → rounded_ideal_completion
    := λ b, ((λ a, a ≺ b) ,, is_ideal_principal_ideal b).

  Proposition principal_ideal_monotone
              {b₁ b₂ : B}
              (p : b₁ ≺ b₂)
    : principal_ideal b₁ ≤ principal_ideal b₂.
  Proof.
    intros a q ; cbn in *.
    exact (trans_abstract_basis q p).
  Qed.

  Proposition to_way_below_ideal
              {I : rounded_ideal_completion}
              (b : B)
              (Hb : b ∈ I)
    : principal_ideal b ≪ I.
  Proof.
    assert (H := is_ideal_rounded (pr2 I) Hb).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro c.
    induction c as ( c & p₁ & p₂ ).
    intros D HD.
    assert (H := HD c p₂).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intro d ; cbn in d.
    induction d as [ d Hd ].
    refine (hinhpr (d ,, _)).
    cbn ; intros x Hx.
    use (is_ideal_lower_set (pr2 (D d)) Hd).
    exact (trans_abstract_basis Hx p₁).
  Qed.

  Proposition is_directed_below_ideal
              (I : rounded_ideal_completion)
    : is_directed
        rounded_ideal_completion
        (λ (b : ∑ b : B, b ∈ I), principal_ideal (pr1 b)).
  Proof.
    split.
    - exact (is_ideal_el (pr2 I)).
    - intros i j.
      assert (H := is_ideal_top (pr2 I) (pr2 i) (pr2 j)).
      revert H.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intro t.
      induction t as ( t & p₁ & p₂ & p₃ ).
      refine (hinhpr ((t ,, p₁) ,, _ ,, _)) ; cbn.
      + intros x q.
        exact (trans_abstract_basis q p₂).
      + intros x q.
        exact (trans_abstract_basis q p₃).
  Qed.

  Definition below_ideal_directed_set
             (I : rounded_ideal_completion)
    : directed_set rounded_ideal_completion.
  Proof.
    use make_directed_set.
    - exact (∑ (b : B), b ∈ I).
    - exact (λ b, principal_ideal (pr1 b)).
    - exact (is_directed_below_ideal I).
  Defined.

  Proposition rounded_ideal_supremum
              (I : rounded_ideal_completion)
    : I ≤ ⨆ below_ideal_directed_set I.
  Proof.
    intros x Hx.
    assert (H := is_ideal_rounded (pr2 I) Hx).
    revert H.
    use factor_through_squash.
    {
      apply propproperty.
    }
    intros b.
    induction b as [ b [ p₁ p₂ ]].
    exact (hinhpr ((b ,, p₂) ,, p₁)).
  Qed.

  Definition rounded_ideal_completion_basis_data
    : dcpo_basis_data rounded_ideal_completion.
  Proof.
    use make_dcpo_basis_data.
    - exact B.
    - exact principal_ideal.
  Defined.

  Proposition rounded_ideal_completion_basis_laws
    : dcpo_basis_laws
        rounded_ideal_completion
        rounded_ideal_completion_basis_data.
  Proof.
    intro I.
    split.
    - split.
      + assert (H := is_ideal_el (pr2 I)).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros b.
        induction b as [ b p ].
        refine (hinhpr (b ,, _)).
        apply to_way_below_ideal.
        exact p.
      + intros b₁ b₂.
        induction b₁ as [ b₁ p₁ ].
        induction b₂ as [ b₂ p₂ ].
        cbn -[way_below] in b₁, p₁, b₂, p₂.
        assert (H := p₁ _ (rounded_ideal_supremum I)).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros c₁.
        induction c₁ as ( ( c₁ & q₁ ) & s₁ ).
        assert (H := p₂ _ (rounded_ideal_supremum I)).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros c₂.
        induction c₂ as ( ( c₂ & q₂ ) & s₂ ).
        cbn in c₁, q₁, s₁, c₂, q₂, s₂.
        assert (H := is_ideal_top (pr2 I) q₁ q₂).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros t.
        induction t as ( t & r₁ & r₂ & r₃ ).
        simple refine (hinhpr ((t ,, _) ,, (_ ,, _))) ; cbn -[way_below].
        * apply to_way_below_ideal.
          exact r₁.
        * intros x v.
          refine (trans_abstract_basis _ r₂).
          use s₁.
          exact v.
        * intros x v.
          refine (trans_abstract_basis _ r₃).
          use s₂.
          exact v.
    - (* `I` is the supremum of all principal ideals way below `I` *)
      split.
      + intros b x p.
        induction b as [ b q ].
        cbn -[way_below] in b, q, p.
        exact (way_below_to_le q x p).
      + intros I' HI' x p.
        assert (H := is_ideal_rounded (pr2 I) p).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros b.
        induction b as [ b [ q₁ q₂ ]].
        assert (H : principal_ideal b ≪ I).
        {
          apply to_way_below_ideal.
          exact q₂.
        }
        exact (HI' (b ,, H) x q₁).
  Qed.

  Definition rounded_ideal_completion_basis
    : dcpo_basis rounded_ideal_completion.
  Proof.
    use make_dcpo_basis.
    - exact rounded_ideal_completion_basis_data.
    - exact rounded_ideal_completion_basis_laws.
  Defined.

  Definition rounded_ideal_completion_continuous_struct
    : continuous_dcpo_struct rounded_ideal_completion.
  Proof.
    use continuous_struct_from_basis.
    exact rounded_ideal_completion_basis.
  Defined.
End RoundedIdealCompletion.

(**
 5. Rounded ideal completion for reflexive bases
 *)
Section RoundedIdealCompletionAlgebraic.
  Context (B : abstract_basis)
          (HB : is_reflexive_abstract_basis B).

  Proposition rounded_ideal_completion_compact_basis_laws
    : compact_basis_laws
        (rounded_ideal_completion B)
        (rounded_ideal_completion_basis_data B).
  Proof.
    refine (_ ,, _ ,, _).
    - intros b ; cbn -[way_below] in *.
      apply to_way_below_ideal ; cbn.
      apply HB.
    - intro I.
      split.
      + assert (H := is_ideal_el (pr2 I)).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros b.
        induction b as [ b p ].
        refine (hinhpr (b ,, _)).
        intros x q ; cbn in q.
        exact (is_ideal_lower_set (pr2 I) p q).
      + intros b₁ b₂.
        induction b₁ as [ b₁ p₁ ].
        induction b₂ as [ b₂ p₂ ].
        cbn in b₁, p₁, b₂, p₂.
        assert (Hb₁ : in_rounded_ideal B b₁ I).
        {
          apply p₁.
          apply HB.
        }
        assert (Hb₂ : in_rounded_ideal B b₂ I).
        {
          apply p₂.
          apply HB.
        }
        assert (H := is_ideal_top (pr2 I) Hb₁ Hb₂).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intro t.
        induction t as ( t & q₁ & q₂ & q₃ ).
        simple refine (hinhpr ((t ,, _) ,, _ ,, _)) ; cbn.
        * intros x r.
          exact (is_ideal_lower_set (pr2 I) q₁ r).
        * intros x r.
          exact (trans_abstract_basis r q₂).
        * intros x r.
          exact (trans_abstract_basis r q₃).
    - (* `I` is the supremum of all principal ideals way below `I` *)
      intro I.
      split.
      + intros b x p.
        induction b as [ b q ].
        cbn in b, q, p.
        apply q.
        exact p.
      + intros I' HI' x p.
        assert (H := is_ideal_rounded (pr2 I) p).
        revert H.
        use factor_through_squash.
        {
          apply propproperty.
        }
        intros b.
        induction b as [ b [ q₁ q₂ ]].
        refine (HI' (b ,, _) x q₁) ; cbn.
        intros c r.
        exact (is_ideal_lower_set (pr2 I) q₂ r).
  Qed.

  Definition rounded_ideal_completion_compact_basis
    : compact_basis (rounded_ideal_completion B).
  Proof.
    use make_compact_basis.
    - exact (rounded_ideal_completion_basis_data B).
    - exact rounded_ideal_completion_compact_basis_laws.
  Defined.
End RoundedIdealCompletionAlgebraic.
