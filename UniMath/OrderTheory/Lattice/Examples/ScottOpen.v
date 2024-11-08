(**********************************************************************************************

 The complete Heyting algebra of Scott open sets

 Given a DCPO `D` the type of Scott sets in `D` forms a complete Heyting algebra. The lattice
 operations are given by union and intersection of subsets, and type-indexed unions are
 constructed in a similar way. Exponentials are constructed using a suitable union.

 Content
 1. Lattice operations
 2. Top and bottom element
 3. Suprema
 4. Exponentials
 5. The complete Heyting algebra of Scott open sets
 6. A basis for this complete Heyting algebra

 **********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.WayBelow.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottTopology.
Require Import UniMath.OrderTheory.DCPOs.Basis.Basis.
Require Import UniMath.OrderTheory.DCPOs.Basis.Continuous.
Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.OrderTheory.Lattice.Bounded.
Require Import UniMath.OrderTheory.Lattice.Heyting.
Require Import UniMath.OrderTheory.Lattice.CompleteHeyting.

Local Open Scope dcpo.

Section ScottOpenCHA.
  Context (D : dcpo).

  (** * 1. Lattice operations *)
  Proposition islatticeop_scott_open_set
    : @islatticeop
        (set_of_scott_open_set D)
        scott_open_set_intersection
        scott_open_set_bin_union.
  Proof.
    repeat split.
    - intros P₁ P₂ P₃ ; use eq_scott_open_set ; intro x ; cbn.
      + intros p.
        induction p as [ [ p₁ p₂ ] p₃ ].
        exact (p₁ ,, p₂ ,, p₃).
      + intros p.
        induction p as [ p₁ [ p₂ p₃ ]].
        exact ((p₁ ,, p₂) ,, p₃).
    - intros P₁ P₂ ; use eq_scott_open_set ; intro x ; cbn.
      + intros p.
        exact (pr2 p ,, pr1 p).
      + intros p.
        exact (pr2 p ,, pr1 p).
    - intros P₁ P₂ P₃ ; use eq_scott_open_set ; intro x.
      + use factor_through_squash_hProp.
        intro p.
        induction p as [ p | p ].
        * revert p.
          use factor_through_squash_hProp.
          intro p.
          induction p as [ p | p ].
          ** use hdisj_in1.
             exact p.
          ** use hdisj_in2.
             use hdisj_in1.
             exact p.
        * do 2 use hdisj_in2.
          exact p.
      + use factor_through_squash_hProp.
        intro p.
        induction p as [ p | p ].
        * do 2 use hdisj_in1.
          exact p.
        * revert p.
          use factor_through_squash_hProp.
          intro p.
          induction p as [ p | p ].
          ** use hdisj_in1.
             use hdisj_in2.
             exact p.
          ** use hdisj_in2.
             exact p.
    - intros P₁ P₂ ; use eq_scott_open_set ; intro x.
      + use factor_through_squash_hProp.
        intro p.
        induction p as [ p | p ].
        * use hdisj_in2.
          exact p.
        * use hdisj_in1.
          exact p.
      + use factor_through_squash_hProp.
        intro p.
        induction p as [ p | p ].
        * use hdisj_in2.
          exact p.
        * use hdisj_in1.
          exact p.
    - intros P₁ P₂ ; use eq_scott_open_set ; intro x.
      + intro p.
        induction p as [ p q ].
        exact p.
      + intro p.
        refine (p ,, _).
        use hdisj_in1.
        exact p.
    - intros P₁ P₂ ; use eq_scott_open_set ; intro x.
      + use factor_through_squash_hProp.
        intros p.
        induction p as [ p | p ].
        * exact p.
        * exact (pr1 p).
      + intro p.
        use hdisj_in1.
        exact p.
  Qed.

  Definition lattice_scott_open_set
    : lattice (set_of_scott_open_set D).
  Proof.
    use make_lattice.
    - exact scott_open_set_intersection.
    - exact scott_open_set_bin_union.
    - exact islatticeop_scott_open_set.
  Defined.

  (** * 2. Top and bottom element *)
  Proposition bounded_latticeop_scott_open_set
    : bounded_latticeop
        lattice_scott_open_set
        (false_scott_open_set D)
        (true_scott_open_set D).
  Proof.
    repeat split.
    - intros P ; use eq_scott_open_set ; intro x.
      + use factor_through_squash_hProp.
        intros p.
        induction p as [ p | p ].
        * apply fromempty.
          exact p.
        * exact p.
      + intro p.
        use hdisj_in2.
        exact p.
    - intros P ; use eq_scott_open_set ; intro x.
      + intro p.
        exact (pr2 p).
      + intro p.
        exact (tt ,, p).
  Qed.

  Definition bounded_lattice_scott_open_set
    : bounded_lattice (set_of_scott_open_set D).
  Proof.
    use make_bounded_lattice.
    - exact lattice_scott_open_set.
    - exact (false_scott_open_set D).
    - exact (true_scott_open_set D).
    - exact bounded_latticeop_scott_open_set.
  Defined.

  Proposition bounded_lattice_scott_open_set_le
              {P Q : scott_open_set D}
              (H : ∏ (x : D), P x → Q x)
    : Lle bounded_lattice_scott_open_set P Q.
  Proof.
    use eq_scott_open_set.
    - intro x ; cbn.
      exact (λ p, pr1 p).
    - intros x p ; cbn.
      refine (p ,, _).
      apply H.
      exact p.
  Qed.

  Proposition from_bounded_lattice_scott_open_set_le
              {P Q : scott_open_set D}
              (H : Lle bounded_lattice_scott_open_set P Q)
              {x : D}
              (p : P x)
    : Q x.
  Proof.
    exact (pr2 (pr2 (weqlogeq _ _ (maponpaths (λ R, pr1 R x) H)) p)).
  Qed.

  (** * 3. Suprema *)
  Proposition is_upperbound_union_scott_open
              {I : UU}
              (P : I → scott_open_set D)
    : is_upperbound_lattice
        bounded_lattice_scott_open_set
        P
        (scott_open_set_union P).
  Proof.
    intros i.
    use bounded_lattice_scott_open_set_le.
    intros x p.
    exact (hinhpr (i ,, p)).
  Qed.

  Proposition is_least_upperbounded_union_open
              {I : UU}
              (P : I → scott_open_set D)
              (Q : scott_open_set D)
              (HQ : is_upperbound_lattice bounded_lattice_scott_open_set P Q)
    : Lle bounded_lattice_scott_open_set (scott_open_set_union P) Q.
  Proof.
    use bounded_lattice_scott_open_set_le.
    intros x.
    use factor_through_squash_hProp.
    intros i.
    induction i as [ i Hi ].
    exact (from_bounded_lattice_scott_open_set_le (HQ i) Hi).
  Qed.

  Definition is_complete_lattice_scott_open_set
    : is_complete_lattice bounded_lattice_scott_open_set.
  Proof.
    intros I P.
    refine (scott_open_set_union P ,, _).
    split.
    - exact (is_upperbound_union_scott_open P).
    - exact (is_least_upperbounded_union_open P).
  Defined.

  (** * 4. Exponentials *)
  Proposition exponential_scott_open_law
              (P Q R : scott_open_set D)
    : scott_open_set_intersection R (scott_open_set_exp P Q) = R
      <->
      scott_open_set_intersection (scott_open_set_intersection R P) Q
      =
      scott_open_set_intersection R P.
  Proof.
    split ; intro H ; use eq_scott_open_set ; intro x.
    - cbn.
      exact pr1.
    - cbn.
      intros p.
      refine (p ,, _).
      refine (factor_through_squash_hProp
                _ _
                (pr2 (pr2 (weqlogeq _ _ (maponpaths (λ R, pr1 R x) H)) (pr1 p)))).
      intro j.
      induction j as [ [ S HS₁ ] HS₂ ] ; cbn in HS₂.
      apply HS₁.
      exact (pr2 p ,, HS₂).
    - intro p.
      induction p as [ p q ].
      exact p.
    - intro p.
      refine (p ,, _).
      use hinhpr.
      simple refine ((_ ,, _) ,, _).
      + exact R.
      + cbn.
        intros y q.
        apply (pr2 (weqlogeq _ _ (maponpaths (λ R, pr1 R y) H))) ; cbn.
        exact (pr2 q ,, pr1 q).
      + exact p.
  Qed.

  Definition exponential_scott_open
    : exponential bounded_lattice_scott_open_set.
  Proof.
    use make_exponential.
    - exact (λ P Q, scott_open_set_exp P Q).
    - exact exponential_scott_open_law.
  Defined.

  (** * 5. The complete Heyting algebra of Scott open sets *)
  Definition scott_open_cha
    : complete_heyting_algebra.
  Proof.
    use make_complete_heyting_algebra.
    - exact (set_of_scott_open_set D).
    - exact bounded_lattice_scott_open_set.
    - exact is_complete_lattice_scott_open_set.
    - exact exponential_scott_open.
  Defined.

  Proposition scott_open_cha_le
              {X₁ X₂ : scott_open_cha}
              (H : ∏ (x : D), pr1 X₁ x → pr1 X₂ x)
    : (X₁ ≤ X₂)%heyting.
  Proof.
    use bounded_lattice_scott_open_set_le.
    exact H.
  Qed.

  (** * 6. A basis for this complete Heyting algebra *)
  Context (B : dcpo_basis D).

  Definition cha_basis_data_scott_open_cha
    : cha_basis_data scott_open_cha.
  Proof.
    use make_cha_basis_data.
    - exact B.
    - exact (λ b, way_below_upper_scott_open_set (continuous_struct_from_basis B) (B b)).
    - exact (λ b₁ b₂, B b₁ ≪ B b₂).
  Defined.

  Proposition cha_basis_laws_scott_open_cha
    : cha_basis_laws cha_basis_data_scott_open_cha.
  Proof.
    repeat split ; cbn -[way_below].
    - intros b₁ b₂ b₃ p q.
      exact (trans_way_below p q).
    - intros X.
      use eq_scott_open_set.
      + intros x p.
        assert (Hx : X (⨆ directed_set_from_basis B x)).
        {
          rewrite (approximating_basis_lub B x).
          exact p.
        }
        pose proof (is_scott_open_lub_inaccessible
                      X
                      (directed_set_from_basis B x)
                      Hx)
          as q.
        revert q.
        use factor_through_squash_hProp.
        intros b.
        induction b as [ [ b q₁ ] q₂ ].
        cbn in q₂ ; unfold basis_below_map in q₂ ; cbn in q₂.
        use hinhpr.
        simple refine ((_ ,, _) ,, _).
        * exact b.
        * use bounded_lattice_scott_open_set_le ; cbn -[way_below].
          intros y r.
          refine (is_scott_open_upper_set X q₂ _).
          use way_below_to_le.
          exact r.
        * cbn -[way_below].
          exact q₁.
      + intros x.
        use factor_through_squash_hProp.
        cbn -[way_below].
        intro b.
        induction b as [ [ b p ] q ].
        exact (from_bounded_lattice_scott_open_set_le p q).
    - intros b₁ b₂ p.
      use scott_open_cha_le ; cbn -[way_below].
      intros x q.
      exact (trans_way_below p q).
  Qed.

  Definition cha_basis_scott_open_cha
    : cha_basis scott_open_cha.
  Proof.
    use make_cha_basis.
    - exact cha_basis_data_scott_open_cha.
    - exact cha_basis_laws_scott_open_cha.
  Defined.
End ScottOpenCHA.
