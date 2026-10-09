(**

 Closed sieves

 Our goal is to define the subobject classifier in the category of sheaves. To do so, we
 first recall that the subobject classifier of presheaves is given by the collection of
 all sieves. Recall that a sieve on an object `x : C` is given by ` functor
 `ω : (C/x)^op` ⟶ hProp`. Concretely, this is a collection of morphisms into `y` that
 is downwards closed in the sense that if we have a morphism from `f₁ : y₁ --> x` to
 `f₂ : y₂ --> x`, then `f₁` is included in `ω` if `f₂` is.

 The subobject classifier of sheaves is rather similar, but slightly different. Instead
 of looking at all sieves, we only look at the sieves that satisfy a property known as
 'closed'. The subobject classifier of sheaves is defined as the sheaf of closed sieves.
 A sieve `ω` is closed if all arrows that cover `ω` are also contained in `ω`.

 In this file, we define the basic notions and operations for closed sieves. In particular,
 we define the closure operation.

 Content
 1. Closed sieves
 2. Accessors for closed sieves
 3. Operations on closed sieves
 4. Laws for closed sieves

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.

Local Open Scope cat.

Section ClosedSieves.
  Context {C : site}.

  (** * 1. Closed sieves *)
  Definition is_closed_sieve
             {x : C}
             (ω : sieve x)
    : hProp
    := (∀ (y : C) (f : y --> x), C y (f^* ω) ⇒ ω y f)%logic.

  Definition closed_sieve
             (x : C)
    : UU
    := ∑ (ω : sieve x), is_closed_sieve ω.

  Definition make_closed_sieve
             {x : C}
             (ω : sieve x)
             (Hω : is_closed_sieve ω)
    : closed_sieve x
    := ω ,, Hω.

  Proposition isaset_closed_sieve
              (x : C)
    : isaset (closed_sieve x).
  Proof.
    use isaset_total2.
    - apply isaset_sieve.
    - intro ω.
      apply isasetaprop.
      apply propproperty.
  Qed.

  Definition set_of_closed_sieves
             (x : C)
    : hSet.
  Proof.
    use make_hSet.
    - exact (closed_sieve x).
    - exact (isaset_closed_sieve x).
  Defined.

  (** * 2. Accessors for closed sieves *)
  Coercion closed_sieve_to_sieve
           {x : C}
           (ω : closed_sieve x)
    : sieve x
    := pr1 ω.

  Proposition is_closed_closed_sieve
              {x : C}
              (ω : closed_sieve x)
    : is_closed_sieve ω.
  Proof.
    exact (pr2 ω).
  Defined.

  Proposition closed_sieve_closed
              {x : C}
              (ω : closed_sieve x)
              {y : C}
              (f : y --> x)
              (p : C y (f^* ω))
    : ω y f.
  Proof.
    exact (is_closed_closed_sieve ω y f p).
  Defined.

  Proposition closed_sieve_eq
              {x : C}
              {ω₁ ω₂ : closed_sieve x}
              (p : (ω₁ : sieve x) = ω₂)
    : ω₁ = ω₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply propproperty.
    }
    exact p.
  Qed.

  Proposition sieve_eq_from_closed
              {x : C}
              {ω₁ ω₂ : closed_sieve x}
              (p : ω₁ = ω₂)
    : (ω₁ : sieve x) = ω₂.
  Proof.
    exact (maponpaths pr1 p).
  Qed.

  (** * 3. Operations on closed sieves *)
  Definition truth_closed_sieve
             (x : C)
    : closed_sieve x.
  Proof.
    use make_closed_sieve.
    - exact (truth_sieve x).
    - abstract
        (intros y f p ; cbn ;
         exact tt).
  Defined.

  Proposition is_closed_precomp
              {x y : C}
              (ω : sieve x)
              (f : y --> x)
              (Hω : is_closed_sieve ω)
    : is_closed_sieve (f^* ω).
  Proof.
    intros z g p ; cbn.
    apply (Hω z (g · f)).
    rewrite comp_precomp_sieve.
    exact p.
  Qed.

  Definition precomp_closed_sieve
             {x y : C}
             (ω : closed_sieve x)
             (f : y --> x)
    : closed_sieve y.
  Proof.
    use make_closed_sieve.
    - exact (f^* ω).
    - exact (is_closed_precomp ω f (is_closed_closed_sieve ω)).
  Defined.

  Definition closure_sieve
             {x : C}
             (ω : sieve x)
    : sieve x.
  Proof.
    use make_sieve.
    - exact (λ y f, C _ (f^* ω)).
    - abstract
        (intros y₁ y₂ g₁ g₂ h p q ; cbn in * ;
         rewrite <- p ;
         rewrite comp_precomp_sieve ;
         use site_sieve_stable ;
         exact q).
  Defined.

  Proposition is_closed_closure_sieve
              {x : C}
              (ω : sieve x)
    : is_closed_sieve (closure_sieve ω).
  Proof.
    intros y f p.
    use (site_trans_sieve p).
    intros z g q ; cbn in *.
    rewrite <- comp_precomp_sieve.
    exact q.
  Qed.

  Definition closure_closed_sieve
             {x : C}
             (ω : sieve x)
    : closed_sieve x.
  Proof.
    use make_closed_sieve.
    - exact (closure_sieve ω).
    - apply is_closed_closure_sieve.
  Defined.

  (** * 4. Laws for closed sieves *)
  Proposition sieve_contains_to_eq_precomp
              {x : C}
              (ω : sieve x)
              {y : C}
              {f : y --> x}
              (p : ω y f)
    : f^* ω = truth_sieve y.
  Proof.
    use sieve_eq.
    - intros.
      exact tt.
    - cbn.
      intros z g _.
      exact (#ω ω g (idpath _) p).
  Qed.

  Proposition sieve_contains_closed
              {x : C}
              (ω : sieve x)
              {y : C}
              (f : y --> x)
              (p : ω y f)
    : C y (f^* ω).
  Proof.
    rewrite (sieve_contains_to_eq_precomp ω p).
    apply site_truth_sieve.
  Qed.

  Proposition closure_sieve_contains
              {x : C}
              (ω : sieve x)
              {y : C}
              (f : y --> x)
              (p : ω y f)
    : closure_sieve ω y f.
  Proof.
    cbn.
    apply sieve_contains_closed.
    exact p.
  Qed.

  Proposition contains_closure_sieve
              {x : C}
              (ω₁ : sieve x)
              (ω₂ : closed_sieve x)
              (H : ∏ (y : C) (f : y --> x), ω₁ y f → ω₂ y f)
              {y : C}
              (f : y --> x)
              (p : closure_sieve ω₁ y f)
    : ω₂ y f.
  Proof.
    use closed_sieve_closed.
    use (site_trans_sieve p) ; cbn.
    intros w h q.
    rewrite <- comp_precomp_sieve.
    use sieve_contains_closed.
    apply H.
    exact q.
  Qed.

  Proposition closure_closed_sieve_eq
              {x : C}
              (ω : closed_sieve x)
    : closure_sieve ω = ω.
  Proof.
    use sieve_eq.
    - use contains_closure_sieve.
      intros y g p.
      exact p.
    - intros y g.
      apply closure_sieve_contains.
  Qed.

  Proposition precomp_closure_sieve
              {x : C}
              (ω : sieve x)
              {y : C}
              (f : y --> x)
    : f^* (closure_sieve ω) = closure_sieve (f^* ω).
  Proof.
    use sieve_eq.
    - cbn ; intros z g p.
      rewrite <- comp_precomp_sieve.
      exact p.
    - cbn ; intros z g p.
      rewrite comp_precomp_sieve.
      exact p.
  Qed.

  Proposition closure_closure_sieve
              {x : C}
              (ω : sieve x)
    : closure_sieve (closure_sieve ω) = closure_sieve ω.
  Proof.
    exact (closure_closed_sieve_eq (closure_closed_sieve ω)).
  Qed.

  Proposition closure_monotone
              {x : C}
              {ω₁ ω₂ : sieve x}
              (H : ∏ (y : C) (f : y --> x), ω₁ y f → ω₂ y f)
              {y : C}
              (f : y --> x)
    : closure_sieve ω₁ y f → closure_sieve ω₂ y f.
  Proof.
    revert y f.
    use (contains_closure_sieve ω₁ (closure_closed_sieve ω₂)).
    intros y f p.
    apply closure_sieve_contains.
    apply H.
    exact p.
  Qed.

  Proposition closed_sieve_eq_cover
              {x : C}
              {ψ : sieve x}
              (H : C x ψ)
              {ω₁ ω₂ : closed_sieve x}
              (p₁ : ∏ (y : C) (f : y --> x), ψ y f → ω₁ y f → ω₂ y f)
              (p₂ : ∏ (y : C) (f : y --> x), ψ y f → ω₂ y f → ω₁ y f)
    : ω₁ = ω₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply propproperty.
    }
    use sieve_eq ; cbn.
    - intros y g q.
      use (closed_sieve_closed ω₂).
      apply sieve_contains_closed in q.
      use site_trans_sieve.
      + exact (g^* ψ).
      + use site_sieve_stable.
        exact H.
      + intros z h r.
        apply sieve_contains_closed.
        apply (p₁ z (h · g) r).
        use (closed_sieve_closed ω₁).
        rewrite comp_precomp_sieve.
        use site_sieve_stable.
        exact q.
    - intros y g q.
      use (closed_sieve_closed ω₁).
      apply sieve_contains_closed in q.
      use site_trans_sieve.
      + exact (g^* ψ).
      + use site_sieve_stable.
        exact H.
      + intros z h r.
        apply sieve_contains_closed.
        apply (p₂ z (h · g) r).
        use (closed_sieve_closed ω₂).
        rewrite comp_precomp_sieve.
        use site_sieve_stable.
        exact q.
  Qed.
End ClosedSieves.
