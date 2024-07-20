(**********************************************************************************************

 Complete Heyting Algebras of Sieves

 We consider two ways to construct a Heyting algebra from a poset `X`.

 The first way is via sieves. A sieve in a poset is a downwards closed set. The collection of
 all sieves then forms a Heyting algebra. The order is given by subset, the lattice operations
 are given by union and intersection, and the supremum of a collection of sieves is also given
 by the union.

 For the other construction, we assume that we have a coverage of `X`. A coverage on a poset
 specifies for each element a collection of covers ([is_coverage]), and we represent this as
 a function that maps inhabitants of `X` and predicates `X → hProp` to a proposition. There
 are several requirements for coverages that we explain below. If we have a coverage on a poset,
 then we can define the notion of a closed sieve ([closed_sieve]). Note the similarities between
 the definition of coverage and that of a Grothendieck topology and the definition of a closed
 sieve and that of a sheaf.

 To show that closed sieves form a Heyting algebra, we use impredicativity. The union of closed
 sieves and the initial closed sieve are constructed as intersections that quantify over the
 collection of all closed sieves. Hence, to guarantee that they land in the right universe, we
 need to use propositional resizing.

 References:
 - Appendix A in "Intuitionistic Set Theory" by John Bell

 Content
 1. Sieves
 2. Operations on sieve
 3. The Heyting algebra of sieves
 4. Coverages
 5. Closed sieves
 6. Operations on closed sieves
 7. The complete Heyting algebra of closed sieves

 **********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.OrderTheory.Lattice.Bounded.
Require Import UniMath.OrderTheory.Lattice.Distributive.
Require Import UniMath.OrderTheory.Lattice.Heyting.
Require Import UniMath.OrderTheory.Lattice.CompleteHeyting.
Require Import UniMath.OrderTheory.Lattice.Examples.FromPartialOrder.

Local Open Scope poset.
Local Open Scope logic.

Section FixPoset.
  Context (X : Poset).

  (** * 1. Sieves *)
  Definition is_sieve (S : X → hProp) : hProp
    := ∀ (x y : X), x ≤ y ⇒ S y ⇒ S x.

  Definition sieve : UU
    := ∑ (S : X → hProp), is_sieve S.

  Definition sieve_to_pred
             (S : sieve)
             (x : X)
    : hProp.
  Proof.
    exact (pr1 S x).
  Defined.

  Coercion sieve_to_pred : sieve >-> Funclass.

  Proposition sieve_downwards_closed
              (S : sieve)
              {x y : X}
              (p : x ≤ y)
              (q : S y)
    : S x.
  Proof.
    exact (pr2 S x y p q).
  Qed.

  Proposition eq_sieve
              {S₁ S₂ : sieve}
              (H₁ : ∏ (x : X), S₁ x → S₂ x)
              (H₂ : ∏ (x : X), S₂ x → S₁ x)
    : S₁ = S₂.
  Proof.
    use subtypePath ; [ intro ; apply propproperty | ].
    use funextsec ; intro x.
    use hPropUnivalence.
    - apply H₁.
    - apply H₂.
  Qed.

  Proposition eq_sieve_l
              {S₁ S₂ : sieve}
              (p : S₁ = S₂)
              (x : X)
              (q : S₁ x)
    : S₂ x.
  Proof.
    induction p.
    exact q.
  Qed.

  Proposition eq_sieve_r
              {S₁ S₂ : sieve}
              (p : S₁ = S₂)
              (x : X)
              (q : S₂ x)
    : S₁ x.
  Proof.
    induction p.
    exact q.
  Qed.

  Definition make_sieve
             (S : X → hProp)
             (HS : is_sieve S)
    : sieve
    := S ,, HS.

  Definition isaset_sieve
    : isaset sieve.
  Proof.
    use isaset_total2.
    - use funspace_isaset.
      apply isasethProp.
    - intros.
      apply isasetaprop.
      apply propproperty.
  Qed.

  Definition set_of_sieves : hSet
    := make_hSet sieve isaset_sieve.

  (** * 2. Operations on sieve *)

  (** Every subset generates a sieve *)
  Proposition generated_sieve
              (P : X → hProp)
    : sieve.
  Proof.
    use make_sieve.
    - exact (λ x, ∃ (y : X), P y ∧ x ≤ y).
    - abstract
        (intros x y p ;
         use factor_through_squash_hProp ;
         intros l ;
         induction l as [ l [ q₁ q₂ ] ] ;
         refine (hinhpr (l ,, q₁ ,, _)) ;
         exact (istrans_posetRelation _ _ _ _ p q₂)).
  Defined.

  (** Lower sieve *)
  Definition lower_elements_sieve
             (x : X)
    : sieve.
  Proof.
    use make_sieve.
    - exact (λ y, y ≤ x).
    - abstract
        (intros y₁ y₂ p q ;
         exact (istrans_posetRelation _ _ _ _ p q)).
  Defined.

  (** Heyting algebra operations on sieve *)
  Definition empty_sieve
    : sieve.
  Proof.
    use make_sieve.
    - exact (λ x, hfalse).
    - abstract
        (intros x y p q ;
         exact q).
  Defined.

  Definition full_sieve
    : sieve.
  Proof.
    use make_sieve.
    - exact (λ x, htrue).
    - abstract
        (intros x y p q ;
         exact tt).
  Defined.

  Definition sieve_intersection
             (S₁ S₂ : sieve)
    : sieve.
  Proof.
    use make_sieve.
    - exact (λ x, S₁ x ∧ S₂ x).
    - abstract
        (intros x y p q ;
         induction q as [ q₁ q₂ ] ;
         exact (sieve_downwards_closed S₁ p q₁ ,, sieve_downwards_closed S₂ p q₂)).
  Defined.

  Definition sieve_union
             (S₁ S₂ : sieve)
    : sieve.
  Proof.
    use make_sieve.
    - exact (λ x, S₁ x ∨ S₂ x).
    - abstract
        (intros x y p ;
         use factor_through_squash_hProp ;
         intros q ;
         induction q as [ q | q ] ;
         use hinhpr ;
         [ exact (inl (sieve_downwards_closed S₁ p q))
         | exact (inr (sieve_downwards_closed S₂ p q)) ]).
  Defined.

  Definition sieve_type_union
             (I : UU)
             (SI : I → sieve)
    : sieve.
  Proof.
    use make_sieve.
    - exact (λ x, ∃ (i : I), SI i x).
    - abstract
        (intros x y p ;
         use factor_through_squash_hProp ;
         intros iq ;
         induction iq as [ i q ] ;
         refine (hinhpr (i ,, _)) ;
         exact (sieve_downwards_closed (SI i) p q)).
  Defined.

  Definition sieve_type_intersection
             (I : UU)
             (SI : I → sieve)
    : sieve.
  Proof.
    use make_sieve.
    - exact (λ x, ∀ (i : I), SI i x).
    - abstract
        (intros x y p H i ;
         exact (sieve_downwards_closed (SI i) p (H i))).
  Defined.

  Definition subset_sieve
             (S₁ S₂ : sieve)
    : hProp
    := ∀ x, S₁ x ⇒ S₂ x.

  Proposition isrefl_subset_sieve
    : isrefl subset_sieve.
  Proof.
    intros S x p.
    exact p.
  Qed.

  Proposition isantisymm_subset_sieve
    : isantisymm subset_sieve.
  Proof.
    intros S₁ S₂ p q.
    use eq_sieve.
    - apply p.
    - apply q.
  Qed.

  Proposition istrans_subset_sieve
    : istrans subset_sieve.
  Proof.
    intros S₁ S₂ S₃ p q x r.
    exact (q x (p x r)).
  Qed.

  Definition sieve_exponential
             (S₁ S₂ : sieve)
    : sieve.
  Proof.
    use make_sieve.
    - exact (λ x, subset_sieve (sieve_intersection S₁ (lower_elements_sieve x)) S₂).
    - abstract
        (intros x y p q z r ; cbn in * ;
         apply q ;
         refine (pr1 r ,, _) ;
         exact (istrans_posetRelation _ _ _ _ (pr2 r) p)).
  Defined.

  (** * 3. The Heyting algebra of sieves *)
  Proposition lattice_laws_set_of_sieves
    : @islatticeop set_of_sieves sieve_intersection sieve_union.
  Proof.
    repeat split.
    - intros S₁ S₂ S₃.
      use eq_sieve ; intro x ; cbn.
      + intros pqr.
        induction pqr as [ [ p q ] r ].
        exact (p ,, q ,, r).
      + intros pqr.
        induction pqr as [ p [ q r ]].
        exact ((p ,, q) ,, r).
    - intros S₁ S₂.
      use eq_sieve ; intro x ; cbn.
      + intros pq.
        induction pq as [ p q ].
        exact (q ,, p).
      + intros pq.
        induction pq as [ p q ].
        exact (q ,, p).
    - intros S₁ S₂ S₃.
      use eq_sieve ; intro x.
      + use factor_through_squash_hProp.
        intros pqr.
        induction pqr as [ pq | r ].
        * revert pq.
          use factor_through_squash_hProp.
          intros pq.
          induction pq as [ p | q ].
          ** exact (hinhpr (inl p)).
          ** exact (hinhpr (inr (hinhpr (inl q)))).
        * exact (hinhpr (inr (hinhpr (inr r)))).
      + use factor_through_squash_hProp.
        intros pqr.
        induction pqr as [ p | qr ].
        * exact (hinhpr (inl (hinhpr (inl p)))).
        * revert qr.
          use factor_through_squash_hProp.
          intros qr.
          induction qr as [ q | r ].
          ** exact (hinhpr (inl (hinhpr (inr q)))).
          ** exact (hinhpr (inr r)).
    - intros S₁ S₂.
      use eq_sieve ; intro x.
      + use factor_through_squash_hProp.
        intros pq.
        induction pq as [ p | q ].
        * exact (hinhpr (inr p)).
        * exact (hinhpr (inl q)).
      + use factor_through_squash_hProp.
        intros pq.
        induction pq as [ p | q ].
        * exact (hinhpr (inr p)).
        * exact (hinhpr (inl q)).
    - intros S₁ S₂.
      use eq_sieve ; intro x.
      + intros pq.
        induction pq as [ p pq ].
        exact p.
      + intros p.
        exact (p ,, hinhpr (inl p)).
    - intros S₁ S₂.
      use eq_sieve ; intro x.
      + use factor_through_squash_hProp.
        intros pq.
        induction pq as [ p | pq ].
        * exact p.
        * exact (pr1 pq).
      + intros p.
        exact (hinhpr (inl p)).
  Qed.

  Definition lattice_set_of_sieves
    : lattice set_of_sieves.
  Proof.
    use make_lattice.
    - exact sieve_intersection.
    - exact sieve_union.
    - exact lattice_laws_set_of_sieves.
  Defined.

  Proposition bounded_lattice_laws_set_of_sieves
    : bounded_latticeop lattice_set_of_sieves empty_sieve full_sieve.
  Proof.
    repeat split.
    - intros S.
      use eq_sieve ; intro x.
      + use factor_through_squash_hProp.
        intros p.
        induction p as [ p | p ].
        * apply fromempty.
          exact p.
        * exact p.
      + intro p.
        exact (hinhpr (inr p)).
    - intros S.
      use eq_sieve ; intro x ; cbn.
      + intros pq.
        exact (pr2 pq).
      + intros p.
        exact (tt ,, p).
  Qed.

  Definition bounded_lattice_set_of_sieves
    : bounded_lattice set_of_sieves.
  Proof.
    Check poset_to_bounded_lattice.
    use make_bounded_lattice.
    - exact lattice_set_of_sieves.
    - exact empty_sieve.
    - exact full_sieve.
    - exact bounded_lattice_laws_set_of_sieves.
  Defined.

  Proposition is_lub_sieve_type_union
              (I : UU)
              (SI : I → sieve)
    : is_least_upperbound_lattice
        bounded_lattice_set_of_sieves
        SI
        (sieve_type_union I SI).
  Proof.
    split.
    - intro i.
      use eq_sieve ; intro x.
      + intro pq.
        induction pq as [ p q ].
        exact p.
      + intro p.
        exact (p ,, hinhpr (i ,, p)).
    - intros T HT.
      use eq_sieve ; intro x.
      + intros pq.
        induction pq as [ p q ].
        revert p.
        use factor_through_squash_hProp.
        intros ir.
        exact (hinhpr ir).
      + use factor_through_squash_hProp.
        intros ir.
        refine (hinhpr ir ,, _).
        induction ir as [ i r ].
        exact (pr2 (eq_sieve_r (HT i) x r)).
  Qed.

  Definition is_complete_set_of_sieve
    : is_complete_lattice bounded_lattice_set_of_sieves.
  Proof.
    intros I SI.
    refine (sieve_type_union I SI ,, _).
    apply is_lub_sieve_type_union.
  Defined.

  Proposition exponential_laws_set_of_sieves
              (S₁ S₂ S₃ : sieve)
    : Lle bounded_lattice_set_of_sieves S₃ (sieve_exponential S₁ S₂)
      <->
      Lle bounded_lattice_set_of_sieves (Lmin bounded_lattice_set_of_sieves S₃ S₁) S₂.
  Proof.
    split ; cbn.
    - intro H.
      use eq_sieve ; intro x ; cbn.
      + intros rpq.
        exact (pr11 rpq ,, pr21 rpq).
      + intros rp.
        refine (rp ,, _).
        use (pr2 (eq_sieve_r H x (pr1 rp))).
        refine (pr2 rp ,, _).
        apply isrefl_posetRelation.
    - intro H.
      use eq_sieve ; intro x ; cbn.
      + intros rpq.
        exact (pr1 rpq).
      + intros r.
        refine (r ,, _).
        intros y pq.
        induction pq as [ p q ].
        refine (pr2 (eq_sieve_r H y _)) ; cbn.
        exact (sieve_downwards_closed S₃ q r ,, p).
  Qed.

  Definition exponential_set_of_sieves
    : exponential bounded_lattice_set_of_sieves.
  Proof.
    use make_exponential.
    - exact sieve_exponential.
    - exact exponential_laws_set_of_sieves.
  Defined.

  Definition complete_heyting_algebra_sieves
    : complete_heyting_algebra.
  Proof.
    use make_complete_heyting_algebra.
    - exact set_of_sieves.
    - exact bounded_lattice_set_of_sieves.
    - exact is_complete_set_of_sieve.
    - exact exponential_set_of_sieves.
  Defined.

  (** * 4. Coverages *)

  (**
     The data of a coverage is a collection of subsets for every element in the poset.
     We represent this via a function `P : X → (X → hProp) → hProp`.
     Given such a function, we say that cover of `x` is a subset `C` such that `P x C`.
     Coverages are supposed to satisfy two requirements:
     1. Every cover `C` of `x` is a subset of the lower set of `x`.
        Precisely, this means that if `C` is a cover of `x` (i.e. `P x C`)
        and `y` is a member of `C` (i.e. `C y`), then `y ≤ x`.
     2. If `y ≤ x`, then every cover of `x` can be refined to a cover of `y`.
        Precisely, this means that if we have a cover `C` of `x` (i.e. `P x C`)
        and if `y ≤ x`, then there is a cover `C'` of `y` (i.e. `P y C`, such that
        every member of `C'` is below something in `C`. The final requirement says that
        for all `z : X` such that `C' x`, there is an `s : X` such that `C s` and `z ≤ s`.
   *)
  Definition is_coverage
             (P : X → (X → hProp) → hProp)
    : hProp
    := (∀ (x y : X)
          (C : X → hProp),
        P x C ⇒ C y ⇒ y ≤ x)
       ∧
       (∀ (x y : X)
          (C : X → hProp),
         y ≤ x
         ⇒ P x C
         ⇒ ∃ (C' : X → hProp),
           P y C'
           ∧
           ∀ (z : X), C' z ⇒ ∃ (s : X), C s ∧ z ≤ s).

  Definition coverage
    : UU
    := ∑ (P : X → (X → hProp) → hProp), is_coverage P.

  Definition coverage_map
             (P : coverage)
             (x : X)
             (C : X → hProp)
    : hProp
    := pr1 P x C.

  Coercion coverage_map : coverage >-> Funclass.

  Proposition cover_downwards_closed
              {P : coverage}
              {x y : X}
              {C : X → hProp}
              (H : P x C)
              (p : C y)
    : y ≤ x.
  Proof.
    exact (pr12 P x y C H p).
  Qed.

  Proposition cover_sharpen
              {P : coverage}
              {x y : X}
              (C : X → hProp)
              (p : y ≤ x)
              (q : P x C)
    : ∃ (C' : X → hProp),
      P y C'
      ∧
      ∀ (z : X), C' z ⇒ ∃ (s : X), C s ∧ z ≤ s.
  Proof.
    exact (pr22 P x y C p q).
  Qed.

  Context (P : coverage).

  (** * 5. Closed sieves *)

  (**
     We fix a coverage `P`.
     A sieve `S` is closed with regards to `P` if every `x : X` is a member of `S`
     whenever there is a cover of `x` that is a subset of `S`.
   *)
  Definition is_closed_sieve
             (S : sieve)
    : hProp
    := ∀ (x : X)
         (C : X → hProp)
         (p : P x C)
         (H : ∏ (y : X), C y → S y),
       S x.

  Definition closed_sieve
    : UU
    := ∑ (S : sieve), is_closed_sieve S.

  Definition make_closed_sieve
             (S : sieve)
             (H : is_closed_sieve S)
    : closed_sieve
    := S ,, H.

  Coercion closed_sieve_to_sieve
           (S : closed_sieve)
    : sieve.
  Proof.
    exact (pr1 S).
  Defined.

  Proposition is_closed_closed_sieve
              (S : closed_sieve)
              (x : X)
              (C : X → hProp)
              (p : P x C)
              (H : ∏ (y : X), C y → S y)
    : S x.
  Proof.
    exact (pr2 S x C p H).
  Qed.

  Proposition eq_closed_sieve
              {S S' : closed_sieve}
              (p : closed_sieve_to_sieve S = closed_sieve_to_sieve S')
    : S = S'.
  Proof.
    use subtypePath.
    {
      intro.
      apply propproperty.
    }
    exact p.
  Qed.

  Proposition isaset_closed_sieve
    : isaset closed_sieve.
  Proof.
    use isaset_total2.
    - apply isaset_sieve.
    - intro.
      apply isasetaprop.
      apply propproperty.
  Qed.

  Definition set_of_closed_sieves
    : hSet
    := make_hSet closed_sieve isaset_closed_sieve.

  (** * 6. Operations on closed sieves *)

  (** Poset of closed sieves *)
  Definition closed_sieves_partial_order
    : PartialOrder set_of_closed_sieves.
  Proof.
    use make_PartialOrder.
    - exact (λ (S₁ S₂ : closed_sieve), subset_sieve S₁ S₂).
    - repeat split.
      + abstract
          (refine (λ (S₁ S₂ S₃ : closed_sieve), _) ;
           exact (istrans_subset_sieve S₁ S₂ S₃)).
      + abstract
          (refine (λ (S : closed_sieve), _) ;
           exact (isrefl_subset_sieve S)).
      + abstract
          (refine (λ (S₁ S₂ : closed_sieve) p q, _) ;
           use eq_closed_sieve ;
           exact (eq_sieve p q)).
  Defined.

  Definition closed_sieves_poset
    : Poset.
  Proof.
    use make_Poset.
    - exact set_of_closed_sieves.
    - exact closed_sieves_partial_order.
  Defined.

  (** Heyting algebra operations on sieve *)
  Definition closed_sieve_full
    : closed_sieve.
  Proof.
    use make_closed_sieve.
    - exact full_sieve.
    - abstract
        (intros x C p H ;
         exact tt).
  Defined.

  Definition closed_sieve_max_el
    : max_el closed_sieves_poset.
  Proof.
    refine (closed_sieve_full ,, _).
    abstract
      (intros S x p ;
       exact tt).
  Defined.

  Definition closed_sieve_intersection
             (S₁ S₂ : closed_sieve)
    : closed_sieve.
  Proof.
    use make_closed_sieve.
    - exact (sieve_intersection S₁ S₂).
    - abstract
        (intros x C p H ;
         refine (is_closed_closed_sieve S₁ x C p _ ,, is_closed_closed_sieve S₂ x C p _) ;
         apply H).
  Defined.

  Definition closed_sieve_min_operation
    : min_operation closed_sieves_poset.
  Proof.
    intros S₁ S₂.
    refine (closed_sieve_intersection S₁ S₂ ,, _ ,, _ ,, _).
    - abstract
        (intros x p ;
         exact (pr1 p)).
    - abstract
        (intros x p ;
         exact (pr2 p)).
    - abstract
        (intros S p q x r ; cbn in * ;
         exact (p x r ,, q x r)).
  Defined.

  Definition closed_sieve_type_intersection
             (I : UU)
             (PI : I → closed_sieve)
    : closed_sieve.
  Proof.
    use make_closed_sieve.
    - exact (sieve_type_intersection I PI).
    - abstract
        (intros x C p H i ;
         refine (is_closed_closed_sieve (PI i) x C p _) ;
         intros y q ;
         exact (H y q i)).
  Defined.

  Definition closed_sieve_min_el
    : min_el closed_sieves_poset.
  Proof.
    simple refine (_ ,, _).
    - exact (closed_sieve_type_intersection closed_sieve (idfun closed_sieve)).
    - abstract
        (intros S x H ; cbn in * ;
         exact (H S)).
  Defined.

  Definition closed_sieve_union
             (S₁ S₂ : closed_sieve)
    : closed_sieve
    := closed_sieve_type_intersection
         (∑ (T : closed_sieve), subset_sieve (sieve_union S₁ S₂) T)
         (λ T, pr1 T).

  Definition closed_sieve_max_operation
    : max_operation closed_sieves_poset.
  Proof.
    intros S₁ S₂.
    refine (closed_sieve_union S₁ S₂ ,, _ ,, _ ,, _).
    - abstract
        (intros x p ;
         intro H ;
         induction H as [ T H ] ;
         cbn ;
         use H ;
         exact (hinhpr (inl p))).
    - abstract
        (intros x p ;
         intro H ;
         induction H as [ T H ] ;
         cbn ;
         use H ;
         exact (hinhpr (inr p))).
    - abstract
        (intros T p q x ;
         intro H ;
         refine (H (_ ,, _)) ;
         intro y ;
         use factor_through_squash_hProp ;
         intros z ;
         induction z as [ z | z ] ;
         [ exact (p y z) | exact (q y z) ]).
  Defined.

  Proposition is_closed_sieve_exponential
              (S₁ S₂ : closed_sieve)
    : is_closed_sieve (sieve_exponential S₁ S₂).
  Proof.
    intros x C p H y q.
    induction q as [ q₁ q₂ ].
    cbn in *.
    pose (U := λ (z : X), S₁ z ∧ ∃ (a : X), C a ∧ z ≤ a).
    assert (∏ (w : X), U w → S₂ w) as H₁.
    {
      intro w.
      intros r.
      induction r as [ r₁ r₂ ].
      revert r₂.
      use factor_through_squash_hProp.
      intros ( z & r₂ & r₃ ).
      use (H z r₂).
      split ; [ | exact r₃ ].
      refine (sieve_downwards_closed S₁ _ r₁).
      apply isrefl_posetRelation.
    }
    assert (∏ (w : X), S₁ w → w ≤ y → S₂ w) as H₂.
    {
      intros w Hw₁ Hw₂.
      pose proof (cover_sharpen C (istrans_posetRelation _ _ _ _ Hw₂ q₂) p) as s.
      revert s.
      use factor_through_squash_hProp.
      intros ( C' & r & HC' ).
      use (is_closed_closed_sieve S₂ _ C' r).
      intros v Hv.
      use H₁.
      specialize (HC' v Hv).
      split ; [ | exact HC' ].
      revert HC'.
      use factor_through_squash_hProp.
      intros ( s & Hs₁ & Hs₂ ).
      refine (sieve_downwards_closed S₁ _ Hw₁).
      exact (cover_downwards_closed r Hv).
    }
    use H₂.
    - exact q₁.
    - apply isrefl_posetRelation.
  Qed.

  Definition closed_sieve_exponential
             (S₁ S₂ : closed_sieve)
    : closed_sieve.
  Proof.
    use make_closed_sieve.
    - exact (sieve_exponential S₁ S₂).
    - apply is_closed_sieve_exponential.
  Defined.

  Definition bounded_lattice_set_of_closed_sieves
    : bounded_lattice set_of_closed_sieves.
  Proof.
    use (poset_to_bounded_lattice closed_sieves_poset).
    - exact closed_sieve_min_operation.
    - exact closed_sieve_max_operation.
    - exact closed_sieve_min_el.
    - exact closed_sieve_max_el.
  Defined.

  Proposition exponential_laws_set_of_closed_sieves
              (S₁ S₂ S₃ : closed_sieve)
    : Lle bounded_lattice_set_of_closed_sieves S₃ (closed_sieve_exponential S₁ S₂)
      <->
      Lle bounded_lattice_set_of_closed_sieves
          (Lmin bounded_lattice_set_of_closed_sieves S₃ S₁) S₂.
  Proof.
    split ; cbn.
    - intro H.
      use eq_closed_sieve.
      use eq_sieve ; intro x ; cbn.
      + intros rpq.
        exact (pr11 rpq ,, pr21 rpq).
      + intros rp.
        refine (rp ,, _).
        use (pr2 (eq_sieve_r (maponpaths pr1 H) x (pr1 rp))).
        refine (pr2 rp ,, _).
        apply isrefl_posetRelation.
    - intro H.
      use eq_closed_sieve.
      use eq_sieve ; intro x ; cbn.
      + intros rpq.
        exact (pr1 rpq).
      + intros r.
        refine (r ,, _).
        intros y pq.
        induction pq as [ p q ].
        refine (pr2 (eq_sieve_r (maponpaths pr1 H) y _)) ; cbn.
        exact (sieve_downwards_closed S₃ q r ,, p).
  Qed.

  Proposition is_glb_closed_sieve_type_intersection
              (I : UU)
              (f : I → set_of_closed_sieves)
    : is_greatest_lowerbound_lattice
        bounded_lattice_set_of_closed_sieves
        f
        (closed_sieve_type_intersection I f).
  Proof.
    split.
    - intros i.
      use eq_closed_sieve.
      use eq_sieve.
      + intros x H j ; cbn in *.
        exact (pr1 H j).
      + intros x p ; cbn in *.
        refine (p ,, _).
        exact (p i).
    - intros S H ; cbn.
      use eq_closed_sieve.
      use eq_sieve.
      + intros x p ; cbn in *.
        exact (pr1 p).
      + intros x p ; cbn in *.
        refine (p ,, _).
        intro i.
        exact (pr2 (eq_sieve_r (maponpaths pr1 (H i)) x p)).
  Qed.

  Definition is_complete_set_of_closed_sieve
    : is_complete_lattice bounded_lattice_set_of_closed_sieves.
  Proof.
    use complete_lattice_from_glb.
    intros I f.
    refine (closed_sieve_type_intersection I f ,, _).
    apply is_glb_closed_sieve_type_intersection.
  Defined.

  Definition exponential_set_of_closed_sieve
    : exponential bounded_lattice_set_of_closed_sieves.
  Proof.
    use make_exponential.
    - exact closed_sieve_exponential.
    - exact exponential_laws_set_of_closed_sieves.
  Defined.

  (** * 7. The complete Heyting algebra of closed sieves *)
  Definition complete_heyting_algebra_closed_sieves
    : complete_heyting_algebra.
  Proof.
    use make_complete_heyting_algebra.
    - exact set_of_closed_sieves.
    - exact bounded_lattice_set_of_closed_sieves.
    - exact is_complete_set_of_closed_sieve.
    - exact exponential_set_of_closed_sieve.
  Defined.
End FixPoset.
