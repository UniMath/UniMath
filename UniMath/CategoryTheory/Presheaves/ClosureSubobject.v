(**

 Closure of subobjects of sheaves

 There are various ways to construct the sheafification of a presheaf. While the most common
 one is the ++-construction, this construction has some disadvantages in a constructive
 setting. In essence, the reason is that one needs to take a quotient inductive type that
 has a constructor of an infinite arity, and one needs some form of choice (i.e., axiom of
 multiple choice or WISC) to get such higher inductive types. An alternative construction can
 be found in Section V.3 in 'Sheaves in Geometry and Logic' by Mac Lane and Moerdijk where
 the sheafification is constructed for arbitrary toposes with a Lawvere-Tierney topology. They
 use multiple steps to construct the sheafification, and one of the steps involves taking the
 closure of a subobject of a sheaf.

 Let's say that we have some sheaf `B` and a monomorphism `τ` from a presheaf `A` into `B`. To
 construct the closure of `A`, we first note that `τ` gives rise to a morphism, which we call
 `χ`, from `B` to the subobject classifier of presheaves. Recall that the subobject classifier
 of presheaves is given by all sieves, and that the subobject classifier of sheaves is given
 by all closed sieves. Hence, we can take a morphism from `B` to the subobject classifier of
 sheaves by taking the closure of sieves. This morphism, which we call `χ'`, gives rise to a
 monomorphism into `B` in the category of sheaves, and this gives us the closure of the
 subobject `A`. We denote this subobject by `A'`.

 An interesting aspect of this construction is that every morphism from `A` to a sheaf `Z` can
 uniquely be extend to `A'`. In fact, this property uniquely characterises the notion of
 sheaves, and it is how sheaves are defined for Lawvere-Tierney topologies. We prove the
 extension property as well.

 References
 - 'Sheaves in Geometry and Logic' by Mac Lane and Moerdijk

 Content
 1. Closure of subobjects
 2. Extending morphisms to the closure

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifierSheaf.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.Presheaves.ConstructionsSheaves.
Require Import UniMath.CategoryTheory.Presheaves.ClosedSieves.

Local Open Scope cat.

Section Closure.
  Context {C : site}
          {A : C^op ⟶ HSET}
          {B : sheaf C}
          {τ : A ⟹ B}
          (Hτ : isMonic (C := PreShv C) τ).

  (** * 1. Closure of subobjects *)
  Definition subobject_closure_nat_trans
    : sheaf_nat_trans B subobject_classifier_sheaf.
  Proof.
    use make_sheaf_nat_trans.
    exact (nat_trans_comp
             _ _ _
             (psh_characteristic_mor τ Hτ)
             subobject_classifier_psh_closure).
  Defined.

  Definition closure_subobject_pullback
    : Pullback
        subobject_closure_nat_trans
        subobject_classifier_sheaf_truth
    := pullback_cat_of_sheaves
         C
         _ _ _
         subobject_closure_nat_trans
         subobject_classifier_sheaf_truth.

  Definition closure_subobject_pullback_psh
    : Pullback
        (C := PreShv C)
        (pr1 subobject_closure_nat_trans)
        (pr1 subobject_classifier_sheaf_truth)
    := functor_preserves_pullback_on_pullback
         (F := sheaf_incl C)
         (pullback_cat_of_sheaves C)
         (preserves_pb_sheaf_incl C)
         subobject_closure_nat_trans
         subobject_classifier_sheaf_truth.

  Definition closure_subobject
    : sheaf C
    := PullbackObject closure_subobject_pullback.

  Definition closure_subobject_mor
    : A ⟹ closure_subobject.
  Proof.
    use (PullbackArrow closure_subobject_pullback_psh).
    - exact τ.
    - exact (TerminalArrow Terminal_PreShv A).
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ;
         use funextsec ;
         intro a ;
         cbn ;
         apply maponpaths ;
         use closed_sieve_eq ;
         use sieve_eq ; [ intros ; apply tt | ] ;
         intros y g [] ;
         use closure_sieve_contains ;
         cbn ;
         refine (#A g a ,, _) ;
         exact (eqtohomot (nat_trans_ax τ _ _ g) a)).
  Defined.

  Proposition isMonic_closure_subobject_mor
    : isMonic (C := PreShv C) closure_subobject_mor.
  Proof.
    intros Z θ₁ θ₂ p.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intros x.
    use funextsec.
    intros z.
    use (isMonic_presheaf_injective Hτ).
    exact (maponpaths (λ w, pr11 w) (eqtohomot (nat_trans_eq_pointwise p x) z)).
  Qed.

  (** * 2. Extending morphisms to the closure *)
  Context (Z : sheaf C).

  Definition restrict_mor_from_closure
             (θ : closure_subobject ⟹ Z)
    : A ⟹ Z
    := nat_trans_comp
         _ _ _
         closure_subobject_mor
         θ.

  Section Extension.
    Context (θ : A ⟹ Z).

    Definition extend_mor_matching_family
               {x : C}
               (b : (B x : hSet))
      : matching_family
          Z
          (fiber_sieve (psh_characteristic_mor_monic τ Hτ) (xx := tt) b).
    Proof.
      use make_matching_family.
      - exact (λ y f a, θ y (pr1 a)).
      - abstract
          (cbn ; unfold in_fiber ; cbn ;
           intros y₁ y₂ f₁ f₂ g p [ a₁ q₁ ] [ a₂ q₂ ] ;
           induction p ;
           cbn ;
           refine (!(eqtohomot (nat_trans_ax θ _ _ g) a₂) @ _) ;
           cbn ;
           apply maponpaths ;
           use (isMonic_presheaf_injective Hτ) ;
           refine (eqtohomot (nat_trans_ax τ _ _ g) a₂ @ _) ;
           cbn ;
           rewrite q₂ ;
           refine (!(eqtohomot (functor_comp B f₂ g) b) @ _) ;
           cbn ;
           exact (!q₁)).
    Defined.

    Proposition extend_mor_to_closure_covering
                {x : C}
                (b : (closure_subobject x : hSet))
      : C x (fiber_sieve (psh_characteristic_mor_monic τ Hτ) (xx := tt) (pr11 b)).
    Proof.
      pose (fiber_paths (pr2 b)) as p.
      cbn in p.
      rewrite transportf_const in p.
      cbn in p.
      pose (from_sieve_eq_r (sieve_eq_from_closed p) (identity _) tt) as q.
      cbn in q.
      rewrite id_precomp_sieve in q.
      exact q.
    Qed.

    Definition extend_mor_to_closure_data
      : nat_trans_data closure_subobject Z.
    Proof.
      intros x b.
      exact (sheaf_amalgamation
               (is_sheaf_sheaf Z)
               (extend_mor_to_closure_covering b)
               (extend_mor_matching_family (pr11 b))).
    Defined.

    Arguments extend_mor_to_closure_data /.

    Proposition extend_mor_to_closure_laws
      : is_nat_trans _ _ extend_mor_to_closure_data.
    Proof.
      intros x y f.
      use funextsec.
      intro b.
      cbn -[extend_mor_matching_family closure_subobject].
      simple refine (sheaf_amalgamation_unique (is_sheaf_sheaf Z) _ _ _).
      - exact (fiber_sieve
                 (psh_characteristic_mor_monic τ Hτ)
                 (xx := tt)
                 (pr11 (# closure_subobject f b))).
      - exact (extend_mor_to_closure_covering (# closure_subobject f b)).
      - exact (extend_mor_matching_family (pr11 (# closure_subobject f b))).
      - intros z g p.
        exact (amalgamation_restr _ g p).
      - cbn ; unfold in_fiber ; cbn.
        intros z g [ a p ].
        cbn.
        refine (!(eqtohomot (functor_comp Z f g) _) @ _).
        etrans.
        {
          use amalgamation_restr.
          refine (a ,, _).
          unfold in_fiber ; cbn.
          refine (p @ _).
          apply (eqtohomot (!(functor_comp B f g))).
        }
        cbn.
        apply idpath.
    Qed.

    Definition extend_mor_to_closure
      : closure_subobject ⟹ Z.
    Proof.
      use make_nat_trans.
      - exact extend_mor_to_closure_data.
      - exact extend_mor_to_closure_laws.
    Defined.

    Proposition extend_mor_to_closure_restrict_pt
                {x : C}
                (a : (A x : hSet))
      : extend_mor_to_closure x (closure_subobject_mor x a) = θ x a.
    Proof.
      cbn -[closure_subobject_mor].
      use (sheaf_amalgamation_unique
             (is_sheaf_sheaf Z)
             _
             (z := extend_mor_matching_family (τ x a))).
      - refine (transportb (C x) _ (site_truth_sieve _)).
        use sieve_eq.
        + intros.
          apply tt.
        + cbn.
          intros.
          refine (#A g a ,, _).
          unfold in_fiber ; cbn.
          exact (eqtohomot (nat_trans_ax τ _ _ g) a).
      - intros y f p.
        apply amalgamation_restr.
      - cbn ; unfold in_fiber ; cbn.
        intros y f p.
        refine (!(eqtohomot (nat_trans_ax θ _ _ f) a) @ _).
        cbn.
        apply maponpaths.
        use (isMonic_presheaf_injective Hτ).
        refine (_ @ !(pr2 p)).
        exact (eqtohomot (nat_trans_ax τ _ _ f) a).
    Qed.

    Proposition extend_mor_to_closure_restrict
      : restrict_mor_from_closure extend_mor_to_closure = θ.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intros x.
      use funextsec.
      intros a.
      exact (extend_mor_to_closure_restrict_pt a).
    Qed.

    Proposition extend_mor_to_closure_unique
                {ζ₁ ζ₂ : closure_subobject ⟹ Z}
                (p : restrict_mor_from_closure ζ₁ = θ)
                (q : restrict_mor_from_closure ζ₂ = θ)
      : ζ₁ = ζ₂.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use funextsec.
      intro b.
      use (sheaf_amalgamation_unique
             (is_sheaf_sheaf Z)).
      - exact (fiber_sieve (psh_characteristic_mor_monic τ Hτ) (xx := tt) (pr11 b)).
      - apply extend_mor_to_closure_covering.
      - apply extend_mor_matching_family.
      - cbn ; unfold in_fiber ; cbn.
        intros y f [ a r ].
        cbn.
        refine (_ @ eqtohomot (nat_trans_eq_pointwise p y) a).
        refine (!(eqtohomot (nat_trans_ax ζ₁ _ _ f) b) @ _).
        cbn -[closure_subobject_mor closure_subobject].
        apply maponpaths.
        use subtypePath.
        {
          intro.
          apply setproperty.
        }
        use subtypePath.
        {
          intro.
          apply isapropunit.
        }
        cbn.
        exact (!r).
      - cbn ; unfold in_fiber ; cbn.
        intros y f [ a r ].
        cbn.
        refine (_ @ eqtohomot (nat_trans_eq_pointwise q y) a).
        refine (!(eqtohomot (nat_trans_ax ζ₂ _ _ f) b) @ _).
        cbn -[closure_subobject_mor closure_subobject].
        apply maponpaths.
        use subtypePath.
        {
          intro.
          apply setproperty.
        }
        use subtypePath.
        {
          intro.
          apply isapropunit.
        }
        cbn.
        exact (!r).
    Qed.
  End Extension.
End Closure.
