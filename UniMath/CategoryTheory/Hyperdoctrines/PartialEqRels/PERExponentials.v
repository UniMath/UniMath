(******************************************************************************************

 Exponentials of partial setoids

 In this file, we show that the category of partial setoids in a tripos has exponentials.
 The reason why this is so, is because we can construct a type of morphisms using the powerset
 construction in a tripos. More specifically, if we have two partial setoids `X` and `Y`,
 then the partial setoid of morphisms from `X` to `Y` has `ℙ(X ×h Y)` as its underlying
 carrier, and the partial equivalence relation says that two sets `P` and `Q` are equal if
 they have the same elements and if they actually represent partial setoid morphisms. Here
 we use essentially the same requirements as given in `PERMorphisms.v`.

 The constructon is this file is based on the proof of Theorem 2.2.1 in "Realizability: an
 introduction to its categorical side". In that proof, exponentials are constructed explicitly.
 However, the proof in "Tripos Theory in Retrospect" is based on power objects.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts
 - "Realizability: an introduction to its categorical side" by Jaap van Oosten

 Content
 1. The exponential object
 2. The evaluation morphism
 3. Lambda abstraction of partial setoid morphisms
 4. Uniqueness
 5. Exponentials in the category of partial setoids

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.GenericPredicate.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERBinProducts.

Local Open Scope cat.
Local Open Scope hd.

Section Exponentials.
  Context {H : tripos}.

  Section ExpPartialSetoid.
    Context (X Y : partial_setoid H).
    Context (Z : partial_setoid H)
            (φ : partial_setoid_morphism (prod_partial_setoid X Z) Y).

    (*
      the main idea of the definition is okay
      however
      - develop infrastructure
      - some aadditional assumptions might be needed
     *)
    (** * 3. Lambda abstraction of partial setoid morphisms *)
    Definition lam_partial_setoid_form
      : form (Z ×h exp_partial_setoid)
      := let z := π₁ (π₁ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)))) in
         let P := π₂ (π₁ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)))) in
         let x := π₂ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y))) in
         let y := π₂ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)) in
         (∀h ∀h (φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ] ⇔ ⟨ x , y ⟩ ∈ P)).

    Proposition lam_partial_setoid_laws
      : partial_setoid_morphism_laws lam_partial_setoid_form.
    Proof.
      repeat split.
      - unfold partial_setoid_mor_dom_defined_law ; cbn.
        simplify_form.
        use forall_intro.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        pose (z := π₂ (π₁ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y))))).
        pose (f := π₂ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y)))).
        fold z f.
        admit. (* needs to be assumption *)
      - unfold partial_setoid_mor_cod_defined_law ; cbn.
        simplify_form.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        pose (z := π₂ (π₁ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y))))).
        pose (f := π₂ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y)))).
        fold z f.
        use eq_in_exp_partial_setoid.
        + admit. (* needs to be assumption *)
        + admit. (* free *)
      - unfold partial_setoid_mor_eq_defined_law ; cbn.
        admit.
      - unfold  partial_setoid_mor_unique_im_law ; cbn -[lam_partial_setoid_form].
        do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        pose (z := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))))).
        pose (f := π₂ (π₁ (tm_var (((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y))))).
        pose (g := π₂ (tm_var (((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))).
        fold z f g.
        simplify.
        use eq_in_exp_partial_setoid.
        + admit. (* needs to be assumption *)
        + unfold exp_partial_setoid_eq, f, g, z ; clear f g z.
          simplify.
          do 2 use forall_intro.
          simplify.
          pose (x := π₂ (π₁ (tm_var (((((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y)))).
          pose (y := π₂ (tm_var (((((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y))).
          pose (f := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y))))).
          pose (g := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y)))))).
          pose (z := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y))))))).
          fold x y z f g.
          admit. (* looks goed *)
      - unfold partial_setoid_mor_hom_exists_law ; cbn.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        use exists_intro.
        + refine {{ _ }}.
          admit.
        + (* seems ok *)
          admit.
    Admitted.

    Definition lam_partial_setoid
      : partial_setoid_morphism Z exp_partial_setoid.
    Proof.
      use make_partial_setoid_morphism.
      - exact lam_partial_setoid_form.
      - exact lam_partial_setoid_laws.
    Defined.

    Proposition lam_partial_setoid_comm
      : φ
        =
        partial_setoid_comp_morphism
          (pair_partial_setoid_morphism
             (partial_setoid_comp_morphism
                (partial_setoid_pr1 X Z)
                (id_partial_setoid_morphism X))
             (partial_setoid_comp_morphism
                (partial_setoid_pr2 X Z)
                lam_partial_setoid))
          eval_partial_setoid.
    Proof.
      use eq_partial_setoid_morphism.
      - cbn.
    Admitted.

    Context (φ' : partial_setoid_morphism Z exp_partial_setoid)
            (p : φ
                 =
                 partial_setoid_comp_morphism
                   (pair_partial_setoid_morphism
                      (partial_setoid_comp_morphism
                         (partial_setoid_pr1 X Z)
                         (id_partial_setoid_morphism X))
                      (partial_setoid_comp_morphism
                         (partial_setoid_pr2 X Z)
                         φ'))
                   eval_partial_setoid).

    (** * 4. Uniqueness *)
    Proposition lam_partial_setoid_unique
      : φ' = lam_partial_setoid.
    Proof.
    Admitted.
  End ExpPartialSetoid.

  (** * 5. Exponentials in the category of partial setoids *)
  Definition exponentials_partial_setoid
    : Exponentials (binproducts_partial_setoid H).
  Proof.
    intros X.
    use left_adjoint_from_partial.
    - exact (λ Y, exp_partial_setoid X Y).
    - exact (λ Y, eval_partial_setoid X Y).
    - intros Y Z f.
      use make_iscontr.
      + simple refine (_ ,, _).
        * exact (lam_partial_setoid X Y Z f).
        * exact (lam_partial_setoid_comm X Y Z f).
      + abstract
          (intros f' ;
           induction f' as [ f' p ] ;
           use subtypePath ; [ intro ; apply homset_property | ] ; cbn ;
           exact (lam_partial_setoid_unique X Y Z f f' p)).
  Defined.
End Exponentials.

Arguments exp_partial_setoid_per_form {H} X Y /.
Arguments eval_partial_setoid_form {H} X Y /.
Arguments lam_partial_setoid_form {H X Y Z} φ /.


(**

 back up

 **)




Section Exponentials.
  Context {H : tripos}.

  Section ExpPartialSetoid.
    Context (X Y : partial_setoid H).

    (** * 1. The exponential object *)
    Definition exp_partial_setoid_dom_defined_law
      : form (ℙ (X ×h Y))
      := let f := π₁ (π₁ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y))) in
         let x := π₂ (π₁ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y))) in
         let y := π₂ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y)) in
         (∀h ∀h (⟨ x , y ⟩ ∈ f ⇒ x ~ x)).

    Definition exp_partial_setoid_cod_defined_law
      : form (ℙ (X ×h Y))
      := let f := π₁ (π₁ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y))) in
         let x := π₂ (π₁ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y))) in
         let y := π₂ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y)) in
         (∀h ∀h (⟨ x , y ⟩ ∈ f ⇒ y ~ y)).

    Definition exp_partial_setoid_eq_defined_law
      : form (ℙ (X ×h Y))
      := let f := π₁ (π₁ (π₁ (π₁ (tm_var ((((ℙ (X ×h Y) ×h X) ×h X) ×h Y) ×h Y))))) in
         let x := π₂ (π₁ (π₁ (π₁ (tm_var ((((ℙ (X ×h Y) ×h X) ×h X) ×h Y) ×h Y))))) in
         let x' := π₂ (π₁ (π₁ (tm_var ((((ℙ (X ×h Y) ×h X) ×h X) ×h Y) ×h Y)))) in
         let y := π₂ (π₁ (tm_var ((((ℙ (X ×h Y) ×h X) ×h X) ×h Y) ×h Y))) in
         let y' := π₂ (tm_var ((((ℙ (X ×h Y) ×h X) ×h X) ×h Y) ×h Y)) in
         (∀h ∀h ∀h ∀h (x ~ x' ⇒ y ~ y' ⇒ ⟨ x , y ⟩ ∈ f ⇒ ⟨ x' , y' ⟩ ∈ f)).

    Definition exp_partial_setoid_unique_im_law
      : form (ℙ (X ×h Y))
      := let f := π₁ (π₁ (π₁ (tm_var (((ℙ (X ×h Y) ×h X) ×h Y) ×h Y)))) in
         let x := π₂ (π₁ (π₁ (tm_var (((ℙ (X ×h Y) ×h X) ×h Y) ×h Y)))) in
         let y := π₂ (π₁ (tm_var (((ℙ (X ×h Y) ×h X) ×h Y) ×h Y))) in
         let y' := π₂ (tm_var (((ℙ (X ×h Y) ×h X) ×h Y) ×h Y)) in
         (∀h ∀h ∀h (⟨ x , y ⟩ ∈ f ⇒ ⟨ x , y' ⟩ ∈ f ⇒ y ~ y')).

    Definition exp_partial_setoid_im_exists_law
      : form (ℙ (X ×h Y))
      := let f := π₁ (tm_var (ℙ (X ×h Y) ×h X)) in
         let x := π₂ (tm_var (ℙ (X ×h Y) ×h X)) in
         let γ := π₁ (tm_var ((ℙ (X ×h Y) ×h X) ×h Y)) in
         (∀h (x ~ x ⇒ ∃h (⟨ x [ γ ]tm , π₂ (tm_var _) ⟩ ∈ (f [ γ ]tm)))).

    Definition exp_partial_setoid_is_function
      : form (ℙ (X ×h Y))
      := exp_partial_setoid_dom_defined_law
         ∧
         exp_partial_setoid_cod_defined_law
         ∧
         exp_partial_setoid_eq_defined_law
         ∧
         exp_partial_setoid_unique_im_law
         ∧
         exp_partial_setoid_im_exists_law.

    Proposition exp_partial_setoid_dom_defined
                {Γ : ty H}
                {Δ : form Γ}
                {f : tm Γ (ℙ (X ×h Y))}
                {x : tm Γ X}
                {y : tm Γ Y}
                (p : Δ ⊢ exp_partial_setoid_is_function [ f ])
                (q : Δ ⊢ ⟨ x , y ⟩ ∈ f)
      : Δ ⊢ x ~ x.
    Proof.
      unfold exp_partial_setoid_is_function in p.
      rewrite !conj_subst in p.
      pose proof (r := conj_elim_left p).
      clear p.
      unfold exp_partial_setoid_dom_defined_law in r.
      rewrite !forall_subst in r.
      pose proof (r' := forall_elim r x).
      clear r ; rename r' into r.
      rewrite forall_subst in r.
      pose proof (r' := forall_elim r y).
      clear r ; rename r' into r.
      refine (weaken_cut r _).
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      refine (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
      use weaken_left.
      exact q.
    Qed.

    Proposition exp_partial_setoid_cod_defined
                {Γ : ty H}
                {Δ : form Γ}
                {f : tm Γ (ℙ (X ×h Y))}
                {x : tm Γ X}
                {y : tm Γ Y}
                (p : Δ ⊢ exp_partial_setoid_is_function [ f ])
                (q : Δ ⊢ ⟨ x , y ⟩ ∈ f)
      : Δ ⊢ y ~ y.
    Proof.
      unfold exp_partial_setoid_is_function in p.
      rewrite !conj_subst in p.
      pose proof (r := conj_elim_left (conj_elim_right p)).
      clear p.
      unfold exp_partial_setoid_cod_defined_law in r.
      rewrite !forall_subst in r.
      pose proof (r' := forall_elim r x).
      clear r ; rename r' into r.
      rewrite forall_subst in r.
      pose proof (r' := forall_elim r y).
      clear r ; rename r' into r.
      refine (weaken_cut r _).
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      refine (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
      use weaken_left.
      exact q.
    Qed.

    Proposition exp_partial_setoid_eq_defined
                {Γ : ty H}
                {Δ : form Γ}
                {f : tm Γ (ℙ (X ×h Y))}
                (p : Δ ⊢ exp_partial_setoid_is_function [ f ])
                {x x' : tm Γ X}
                (qx : Δ ⊢ x ~ x')
                {y y' : tm Γ Y}
                (qy : Δ ⊢ y ~y')
                (q : Δ ⊢ ⟨ x , y ⟩ ∈ f)
      : Δ ⊢ ⟨ x' , y' ⟩ ∈ f.
    Proof.
      unfold exp_partial_setoid_is_function in p.
      rewrite !conj_subst in p.
      pose proof (r := conj_elim_left (conj_elim_right (conj_elim_right p))).
      clear p.
      unfold exp_partial_setoid_eq_defined_law in r.
      rewrite !forall_subst in r.
      rewrite !impl_subst in r.
      rewrite !partial_setoid_subst in r.
      rewrite !hyperdoctrine_pr2_subst in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !hyperdoctrine_pair_subst in r.
      rewrite !hyperdoctrine_pr2_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pair_pr1 in r.
      rewrite !hyperdoctrine_pair_pr2 in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !var_tm_subst in r.
      pose proof (r' := forall_elim r x).
      clear r ; rename r' into r.
      rewrite !forall_subst in r.
      rewrite !impl_subst in r.
      rewrite !partial_setoid_subst in r.
      rewrite !tripos_in_subst in r.
      rewrite !hyperdoctrine_pr2_subst in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !hyperdoctrine_pair_subst in r.
      rewrite !hyperdoctrine_pr2_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pair_pr1 in r.
      rewrite !hyperdoctrine_pair_pr2 in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !tm_subst_comp in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pair_subst in r.
      rewrite !hyperdoctrine_pair_pr1 in r.
      rewrite !hyperdoctrine_pair_pr2 in r.
      rewrite !hyperdoctrine_pr2_subst in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pair_pr1 in r.
      rewrite !hyperdoctrine_pair_pr2 in r.
      rewrite !tm_subst_comp in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pair_pr1 in r.
      pose proof (r' := forall_elim r x').
      clear r ; rename r' into r.
      rewrite !forall_subst in r.
      rewrite !impl_subst in r.
      rewrite !partial_setoid_subst in r.
      rewrite !tripos_in_subst in r.
      rewrite !hyperdoctrine_pr2_subst in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !hyperdoctrine_pair_subst in r.
      rewrite !hyperdoctrine_pr2_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pair_pr1 in r.
      rewrite !hyperdoctrine_pair_pr2 in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !tm_subst_comp in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pair_pr1 in r.
      rewrite !hyperdoctrine_pair_pr2 in r.
      pose proof (r' := forall_elim r y).
      clear r ; rename r' into r.
      rewrite !forall_subst in r.
      rewrite !impl_subst in r.
      rewrite !partial_setoid_subst in r.
      rewrite !tripos_in_subst in r.
      rewrite !hyperdoctrine_pr2_subst in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !hyperdoctrine_pair_subst in r.
      rewrite !hyperdoctrine_pr2_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pair_pr1 in r.
      rewrite !hyperdoctrine_pair_pr2 in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !tm_subst_comp in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pair_pr1 in r.
      rewrite !hyperdoctrine_pair_pr2 in r.
      pose proof (r' := forall_elim r y').
      clear r ; rename r' into r.
      rewrite !impl_subst in r.
      rewrite !partial_setoid_subst in r.
      rewrite !tripos_in_subst in r.
      rewrite !hyperdoctrine_pr2_subst in r.
      rewrite !hyperdoctrine_pair_subst in r.
      rewrite !hyperdoctrine_pr2_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pair_pr2 in r.
      rewrite !tm_subst_comp in r.
      rewrite !hyperdoctrine_pr1_subst in r.
      rewrite !var_tm_subst in r.
      rewrite !hyperdoctrine_pair_pr1 in r.
      rewrite !tm_subst_var in r.
      use (weaken_cut r _).
      refine (weaken_cut
                (impl_elim
                   _
                   (impl_elim
                      _
                      (impl_elim
                         _
                         (weaken_right (hyperdoctrine_hyp _) _))))
                _).
      - use weaken_left.
        exact q.
      - use weaken_left.
        exact qy.
      - use weaken_left.
        exact qx.
      - use weaken_right.
        apply hyperdoctrine_hyp.
    Qed.

    Proposition exp_partial_setoid_unique_im
                {Γ : ty H}
                {Δ : form Γ}
                {f : tm Γ (ℙ (X ×h Y))}
                (p : Δ ⊢ exp_partial_setoid_is_function [ f ])
                {x : tm Γ X}
                {y y' : tm Γ Y}
                (q₁ : Δ ⊢ ⟨ x , y ⟩ ∈ f)
                (q₂ : Δ ⊢ ⟨ x , y' ⟩ ∈ f)
      : Δ ⊢ y ~ y'.
    Proof.
      unfold exp_partial_setoid_is_function in p.
      rewrite !conj_subst in p.
      pose proof (r := conj_elim_left (conj_elim_right (conj_elim_right (conj_elim_right p)))).
      clear p.
      unfold exp_partial_setoid_unique_im_law in r.
      rewrite !forall_subst in r.
      pose proof (r' := forall_elim r x).
      clear r ; rename r' into r.
      rewrite !forall_subst in r.
      pose proof (r' := forall_elim r y).
      clear r ; rename r' into r.
      rewrite !forall_subst in r.
      pose proof (r' := forall_elim r y').
      clear r ; rename r' into r.
      refine (weaken_cut r _).
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      refine (impl_elim
                _
                (impl_elim
                   _
                   (weaken_right (hyperdoctrine_hyp _) _))).
      - use weaken_left.
        exact q₂.
      - use weaken_left.
        exact q₁.
    Qed.

    Proposition exp_partial_setoid_im_exists
                {Γ : ty H}
                {Δ : form Γ}
                {f : tm Γ (ℙ (X ×h Y))}
                (p : Δ ⊢ exp_partial_setoid_is_function [ f ])
                {x : tm Γ X}
                (q : Δ ⊢ x ~ x)
      : Δ ⊢ (∃h (⟨ x [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ∈ (f [ π₁ (tm_var _) ]tm))).
    Proof.
      unfold exp_partial_setoid_is_function in p.
      rewrite !conj_subst in p.
      pose proof (r := conj_elim_right (conj_elim_right (conj_elim_right (conj_elim_right p)))).
      clear p.
      unfold exp_partial_setoid_im_exists_law in r.
      rewrite !forall_subst in r.
      pose (r' := forall_elim r x).
      refine (weaken_cut r' _).
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      use (impl_elim _ (weaken_right (hyperdoctrine_hyp _) _)).
      use weaken_left.
      exact q.
    Qed.

    Definition exp_partial_setoid_eq
      : form (ℙ (X ×h Y) ×h ℙ (X ×h Y))
      := let f := π₁ (π₁ (π₁ (tm_var (((ℙ (X ×h Y) ×h ℙ (X ×h Y)) ×h X) ×h Y)))) in
         let g := π₂ (π₁ (π₁ (tm_var (((ℙ (X ×h Y) ×h ℙ (X ×h Y)) ×h X) ×h Y)))) in
         let x := π₂ (π₁ (tm_var (((ℙ (X ×h Y) ×h ℙ (X ×h Y)) ×h X) ×h Y))) in
         let y := π₂ (tm_var (((ℙ (X ×h Y) ×h ℙ (X ×h Y)) ×h X) ×h Y)) in
         (∀h ∀h ((⟨ x , y ⟩ ∈ f) ⇔ (⟨ x , y ⟩ ∈ g))).

    Proposition from_exp_partial_setoid_eq
                {Γ : ty H}
                {Δ : form Γ}
                {f g : tm Γ (ℙ (X ×h Y))}
                (p : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , g ⟩ ])
                {x : tm Γ X}
                {y : tm Γ Y}
                (q : Δ ⊢ ⟨ x , y ⟩ ∈ f)
      : Δ ⊢ ⟨ x , y ⟩ ∈ g.
    Proof.
      unfold exp_partial_setoid_eq in p.
      rewrite !forall_subst in p.
      pose proof (forall_elim p x) as p'.
      clear p ; rename p' into p.
      rewrite forall_subst in p.
      pose proof (forall_elim p y) as p'.
      clear p ; rename p' into p.
      refine (weaken_cut p _).
      simplify.
      use (iff_elim_left (weaken_right (hyperdoctrine_hyp _) _)).
      use weaken_left.
      exact q.
    Qed.

    Proposition exp_partial_setoid_eq_sym
                {Γ : ty H}
                {Δ : form Γ}
                {f g : tm Γ (ℙ (X ×h Y))}
                (p : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , g ⟩ ])
      : Δ ⊢ exp_partial_setoid_eq [ ⟨ g , f ⟩ ].
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold exp_partial_setoid_eq.
      simplify.
      do 2 use forall_intro.
      simplify.
      pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
      pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
      pose (y := π₂ (tm_var ((Γ ×h X) ×h Y))).
      fold γ x y.
      simple refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) x) _).
      simplify_form.
      simple refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) y) _).
      simplify.
      fold γ.
      use iff_sym.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition exp_partial_setoid_eq_trans
                {Γ : ty H}
                {Δ : form Γ}
                {f g h : tm Γ (ℙ (X ×h Y))}
                (p : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , g ⟩ ])
                (q : Δ ⊢ exp_partial_setoid_eq [ ⟨ g , h ⟩ ])
      : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , h ⟩ ].
    Proof.
      refine (weaken_cut p _).
      unfold exp_partial_setoid_eq.
      simplify_form.
      do 2 use forall_intro.
      simplify.
      pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
      pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
      pose (y := π₂ (tm_var ((Γ ×h X) ×h Y))).
      fold γ x y.
      use hyp_sym.
      simple refine (weaken_cut (weaken_left (forall_elim (hyperdoctrine_hyp _) x) _) _).
      use hyp_ltrans.
      use weaken_right.
      simplify_form.
      use hyp_sym.
      simple refine (weaken_cut (weaken_left (forall_elim (hyperdoctrine_hyp _) y) _) _).
      use hyp_ltrans.
      use weaken_right.
      simplify.
      use (iff_trans (weaken_right (hyperdoctrine_hyp _) _)).
      use weaken_left.
      refine (hyperdoctrine_cut (hyperdoctrine_proof_subst _ q) _).
      unfold exp_partial_setoid_eq.
      simplify.
      simple refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) x) _).
      simplify_form.
      simple refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) y) _).
      simplify.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition exp_partial_setoid_eq_is_function
                {Γ : ty H}
                {Δ : form Γ}
                {f g : tm Γ (ℙ (X ×h Y))}
                (p : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , g ⟩ ])
                (q : Δ ⊢ exp_partial_setoid_is_function [ f ])
      : Δ ⊢ exp_partial_setoid_is_function [ g ].
    Proof.
      unfold exp_partial_setoid_is_function.
      simplify_form.
      repeat use conj_intro.
      - unfold exp_partial_setoid_dom_defined_law.
        simplify_form.
        do 2 use forall_intro.
        use impl_intro.
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
        pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
        pose (y := π₂ (tm_var ((Γ ×h X) ×h Y))).
        fold γ x y.
        use exp_partial_setoid_dom_defined.
        + exact (f [ γ ]tm).
        + exact y.
        + use weaken_left.
          refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ q) _).
          simplify.
          apply hyperdoctrine_hyp.
        + use (weaken_cut (weaken_left (hyperdoctrine_proof_subst γ p) _) _).
          use hyp_ltrans.
          use weaken_right.
          simplify.
          use from_exp_partial_setoid_eq.
          * exact (g [ γ ]tm).
          * use weaken_right.
            use exp_partial_setoid_eq_sym.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            apply hyperdoctrine_hyp.
      - unfold exp_partial_setoid_cod_defined_law.
        simplify_form.
        do 2 use forall_intro.
        use impl_intro.
        rewrite partial_setoid_subst.
        simplify.
        pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
        pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
        pose (y := π₂ (tm_var ((Γ ×h X) ×h Y))).
        fold γ x y.
        use exp_partial_setoid_cod_defined.
        + exact (f [ γ ]tm).
        + exact x.
        + use weaken_left.
          refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ q) _).
          simplify.
          apply hyperdoctrine_hyp.
        + use (weaken_cut (weaken_left (hyperdoctrine_proof_subst γ p) _) _).
          use hyp_ltrans.
          use weaken_right.
          simplify.
          use from_exp_partial_setoid_eq.
          * exact (g [ γ ]tm).
          * use weaken_right.
            use exp_partial_setoid_eq_sym.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            apply hyperdoctrine_hyp.
      - unfold exp_partial_setoid_eq_defined_law.
        simplify_form.
        do 4 use forall_intro.
        do 3 use impl_intro.
        rewrite !partial_setoid_subst.
        simplify.
        pose (γ := π₁ (π₁ (π₁ (π₁ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y)))))).
        pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y)))))).
        pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y))))).
        pose (y₁ := π₂ (π₁ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y)))).
        pose (y₂ := π₂ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y))).
        fold γ x₁ x₂ y₁ y₂.
        use from_exp_partial_setoid_eq.
        + exact (f [ γ ]tm).
        + do 3 use weaken_left.
          refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ p) _).
          simplify.
          apply hyperdoctrine_hyp.
        + use exp_partial_setoid_eq_defined.
          * do 3 use weaken_left.
            refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ q) _).
            simplify.
            apply hyperdoctrine_hyp.
          * exact x₁.
          * do 2 use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
          * exact y₁.
          * use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
          * use from_exp_partial_setoid_eq.
            ** exact (g [ γ ]tm).
            ** do 3 use weaken_left.
               refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ p) _).
               simplify.
               use exp_partial_setoid_eq_sym.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
      - unfold exp_partial_setoid_unique_im_law.
        simplify_form.
        do 3 use forall_intro.
        do 2 use impl_intro.
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        pose (γ := π₁ (π₁ (π₁ (tm_var (((Γ ×h X) ×h Y) ×h Y))))).
        pose (x := π₂ (π₁ (π₁ (tm_var (((Γ ×h X) ×h Y) ×h Y))))).
        pose (y₁ := π₂ (π₁ (tm_var (((Γ ×h X) ×h Y) ×h Y)))).
        pose (y₂ := π₂ (tm_var (((Γ ×h X) ×h Y) ×h Y))).
        fold γ x y₁ y₂.
        use exp_partial_setoid_unique_im.
        + exact (f [ γ ]tm).
        + do 2 use weaken_left.
          refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ q) _).
          simplify.
          apply hyperdoctrine_hyp.
        + exact x.
        + use from_exp_partial_setoid_eq.
          * exact (g [ γ ]tm).
          * do 2 use weaken_left.
            refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ p) _).
            simplify.
            use exp_partial_setoid_eq_sym.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
        + use from_exp_partial_setoid_eq.
          * exact (g [ γ ]tm).
          * do 2 use weaken_left.
            refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ p) _).
            simplify.
            use exp_partial_setoid_eq_sym.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
      - unfold exp_partial_setoid_im_exists_law.
        simplify_form.
        use forall_intro.
        use impl_intro.
        rewrite partial_setoid_subst.
        simplify.
        pose (γ := π₁ (tm_var (Γ ×h X))).
        pose (x := π₂ (tm_var (Γ ×h X))).
        fold γ x.
        use (exists_elim (exp_partial_setoid_im_exists _ _)).
        + exact (f [ γ ]tm).
        + use weaken_left.
          refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ q) _).
          simplify.
          apply hyperdoctrine_hyp.
        + exact x.
        + use weaken_right.
          apply hyperdoctrine_hyp.
        + unfold γ, x ; clear γ x.
          simplify.
          pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
          pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
          pose (y := π₂ (tm_var ((Γ ×h X) ×h Y))).
          fold γ x y.
          use exists_intro.
          * exact y.
          * simplify.
            fold γ x.
            use from_exp_partial_setoid_eq.
            ** exact (f [ γ ]tm).
            ** do 2 use weaken_left.
               refine (hyperdoctrine_cut (hyperdoctrine_proof_subst γ p) _).
               simplify.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
    Qed.

    (*** Up to here: basics file ***)

    Definition exp_partial_setoid_per_form
      : form (ℙ (X ×h Y) ×h ℙ (X ×h Y))
      := exp_partial_setoid_is_function [ π₁ (tm_var _) ]
         ∧
         exp_partial_setoid_eq.

    Arguments exp_partial_setoid_per_form /.

    Proposition exp_partial_setoid_per_axioms
      : per_axioms exp_partial_setoid_per_form.
    Proof.
      split.
      - unfold per_symm_axiom ; cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        pose (f := π₂ (π₁ (tm_var ((𝟙 ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y))))).
        pose (g := π₂ (tm_var ((𝟙 ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))).
        fold f g.
        use conj_intro.
        + use exp_partial_setoid_eq_is_function.
          * exact f.
          * use weaken_right.
            apply hyperdoctrine_hyp.
          * use weaken_left.
            apply hyperdoctrine_hyp.
        + use weaken_right.
          use exp_partial_setoid_eq_sym.
          apply hyperdoctrine_hyp.
      - unfold per_trans_axiom ; cbn.
        do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify.
        pose (f := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))))).
        pose (g := π₂ (π₁ (tm_var (((𝟙 ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y))))).
        pose (h := π₂ (tm_var (((𝟙 ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))).
        fold f g h.
        use conj_intro.
        + do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        + use exp_partial_setoid_eq_trans.
          * exact g.
          * use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
          * do 2 use weaken_right.
            apply hyperdoctrine_hyp.
    Qed.

    Definition exp_partial_setoid_per
      : per (ℙ (X ×h Y)).
    Proof.
      use make_per.
      - exact exp_partial_setoid_per_form.
      - exact exp_partial_setoid_per_axioms.
    Defined.

    Definition exp_partial_setoid
      : partial_setoid H.
    Proof.
      use make_partial_setoid.
      - exact (ℙ (X ×h Y)).
      -exact exp_partial_setoid_per.
    Defined.

    Proposition eq_in_exp_partial_setoid
                {Γ : ty H}
                {f g : tm Γ exp_partial_setoid}
                {Δ : form Γ}
                (p : Δ ⊢ exp_partial_setoid_is_function [ f ])
                (q : Δ ⊢ exp_partial_setoid_eq [⟨ f , g ⟩])
      : Δ ⊢ f ~ g.
    Proof.
      unfold partial_setoid_formula ; cbn.
      simplify.
      use conj_intro.
      - exact p.
      - exact q.
    Qed.

    Proposition from_eq_in_exp_partial_setoid_function_left
                {Γ : ty H}
                {f g : tm Γ exp_partial_setoid}
                {Δ : form Γ}
                (p : Δ ⊢ f ~ g)
      : Δ ⊢ exp_partial_setoid_is_function [ f ].
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold partial_setoid_formula ; cbn.
      simplify.
      use weaken_left.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition from_eq_in_exp_partial_setoid_function_right
                {Γ : ty H}
                {f g : tm Γ exp_partial_setoid}
                {Δ : form Γ}
                (p : Δ ⊢ f ~ g)
      : Δ ⊢ exp_partial_setoid_is_function [ g ].
    Proof.
      refine (hyperdoctrine_cut (partial_setoid_sym p) _).
      unfold partial_setoid_formula ; cbn.
      simplify.
      use weaken_left.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition from_eq_in_exp_partial_setoid_function_eq
                {Γ : ty H}
                {f g : tm Γ exp_partial_setoid}
                {Δ : form Γ}
                (p : Δ ⊢ f ~ g)
      : Δ ⊢ exp_partial_setoid_eq [⟨ f , g ⟩].
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold partial_setoid_formula ; cbn.
      simplify.
      use weaken_right.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition from_eq_in_exp_partial_setoid
                {Γ : ty H}
                {f g : tm Γ exp_partial_setoid}
                {Δ : form Γ}
                (p : Δ ⊢ f ~ g)
      : Δ ⊢ exp_partial_setoid_is_function [ f ] ∧ exp_partial_setoid_eq [⟨ f , g ⟩].
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold partial_setoid_formula ; cbn.
      simplify.
      apply hyperdoctrine_hyp.
    Qed.

    (** file 1 *)

    (** * 2. The evaluation morphism *)

    (* here we might need to add assumptions that `f` is a function *)
    Definition eval_partial_setoid_form
      : form (prod_partial_setoid X exp_partial_setoid ×h Y)
      := let x := π₁ (π₁ (tm_var ((X ×h ℙ (X ×h Y)) ×h Y))) in
         let f := π₂ (π₁ (tm_var ((X ×h ℙ (X ×h Y)) ×h Y))) in
         let y := π₂ (tm_var ((X ×h ℙ (X ×h Y)) ×h Y)) in
         (exp_partial_setoid_is_function [ f ])
         ∧
         (exp_partial_setoid_eq [ ⟨ f , f ⟩ ])
         ∧
         ⟨ x , y ⟩ ∈ f.

    Arguments eval_partial_setoid_form /.

    (* here we need good projections of the laws of being a function *)
    Proposition eval_partial_setoid_laws
      : partial_setoid_morphism_laws eval_partial_setoid_form.
    Proof.
      repeat split.
      - unfold partial_setoid_mor_dom_defined_law ; cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        pose (x := π₁ (π₂ (π₁ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))))).
        pose (f := π₂ (π₂ (π₁ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))))).
        pose (y := π₂ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))).
        use eq_in_prod_partial_setoid ; cbn ; fold x y f.
        + use exp_partial_setoid_dom_defined.
          * exact f.
          * exact y.
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * do 2 use weaken_right.
            apply hyperdoctrine_hyp.
        + use hyp_rtrans.
          use weaken_left.
          unfold partial_setoid_formula.
          cbn.
          simplify.
          apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_cod_defined_law ; cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        pose (x := π₁ (π₂ (π₁ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))))).
        pose (f := π₂ (π₂ (π₁ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))))).
        pose (y := π₂ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))).
        fold x y f.
        use exp_partial_setoid_cod_defined.
        + exact f.
        + exact x.
        + use weaken_left.
          apply hyperdoctrine_hyp.
        + do 2 use weaken_right.
          apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_eq_defined_law ; cbn.
        do 4 use forall_intro.
        use impl_intro.
        use weaken_right.
        do 2 use impl_intro.
        simplify.
        pose (Γ := (((𝟙 ×h X ×h ℙ (X ×h Y)) ×h X ×h ℙ (X ×h Y)) ×h Y) ×h Y).
        pose (f := π₂ (π₂ (π₁ (π₁ (π₁ (tm_var Γ)))))).
        pose (g := π₂ (π₂ (π₁ (π₁ (tm_var Γ))))).
        pose (x₁ := π₁ (π₂ (π₁ (π₁ (π₁ (tm_var Γ)))))).
        pose (x₂ := π₁ (π₂ (π₁ (π₁ (tm_var Γ))))).
        pose (y₁ := π₂ (π₁ (tm_var Γ))).
        pose (y₂ := π₂ (tm_var Γ)).
        unfold Γ in * ; clear Γ.
        fold f g x₁ x₂ y₁ y₂.
        refine (weaken_cut _ _).
        {
          do 2 use weaken_left.
          exact (from_eq_in_prod_partial_setoid _ _ (hyperdoctrine_hyp _)).
        }
        cbn.
        fold x₁ x₂ f g.
        do 2 use hyp_ltrans.
        use weaken_right.
        repeat use conj_intro.
        + use exp_partial_setoid_eq_is_function.
          * exact f.
          * use from_eq_in_exp_partial_setoid_function_eq.
            do 3 use weaken_right.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            do 2 use weaken_left.
            apply hyperdoctrine_hyp.
        + use from_eq_in_exp_partial_setoid_function_eq.
          use partial_setoid_refl_r.
          {
            exact f.
          }
          do 3 use weaken_right.
          apply hyperdoctrine_hyp.
        + use exp_partial_setoid_eq_defined.
          * use from_eq_in_exp_partial_setoid_function_right.
            {
              exact f.
            }
            do 3 use weaken_right.
            apply hyperdoctrine_hyp.
          * exact x₁.
          * do 2 use weaken_right.
            use weaken_left.
            apply hyperdoctrine_hyp.
          * exact y₁.
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use from_exp_partial_setoid_eq.
            ** exact f.
            ** use from_eq_in_exp_partial_setoid_function_eq.
               do 3 use weaken_right.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               use weaken_left.
               do 2 use weaken_right.
               apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_unique_im_law ; cbn.
        do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify.
        pose (x := π₁ (π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y) ×h Y)))))).
        pose (f := π₂ (π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y) ×h Y)))))).
        pose (y := π₂ (π₁ (tm_var (((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y) ×h Y)))).
        pose (y' := π₂ (tm_var (((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y) ×h Y))).
        fold x f y y'.
        use exp_partial_setoid_unique_im.
        + exact f.
        + do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        + exact x.
        + use weaken_left.
          do 2 use weaken_right.
          apply hyperdoctrine_hyp.
        + do 3 use weaken_right.
          apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_hom_exists_law.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        cbn.
        pose (x := π₁ (π₂ (tm_var (𝟙 ×h X ×h ℙ (X ×h Y))))).
        pose (f := π₂ (π₂ (tm_var (𝟙 ×h X ×h ℙ (X ×h Y))))).
        use (hyperdoctrine_cut
               (from_eq_in_prod_partial_setoid _ _ (hyperdoctrine_hyp _))).
        cbn.
        fold x f.
        refine (hyperdoctrine_cut _ _).
        {
          refine (conj_intro (weaken_left (hyperdoctrine_hyp _) _) _).
          use weaken_right.
          exact (from_eq_in_exp_partial_setoid (hyperdoctrine_hyp _)).
        }
        use (exists_elim (exp_partial_setoid_im_exists _ _)).
        + exact f.
        + use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
        + exact x.
        + use weaken_left.
          apply hyperdoctrine_hyp.
        + unfold x, f ; clear x f.
          simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          pose (x := π₁ (π₂ (π₁ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))))).
          pose (f := π₂ (π₂ (π₁ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))))).
          pose (y := π₂ (tm_var ((𝟙 ×h X ×h ℙ (X ×h Y)) ×h Y))).
          fold x f y.
          use exists_intro.
          * exact y.
          * simplify.
            fold x f.
            repeat use conj_intro.
            ** use weaken_left.
               use weaken_right.
               use weaken_left.
               apply hyperdoctrine_hyp.
            ** use weaken_left.
               do 2 use weaken_right.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
    Qed.

    Definition eval_partial_setoid
      : partial_setoid_morphism
          (prod_partial_setoid X exp_partial_setoid)
          Y.
    Proof.
      use make_partial_setoid_morphism.
      - exact eval_partial_setoid_form.
      - exact eval_partial_setoid_laws.
    Defined.

    Context (Z : partial_setoid H)
            (φ : partial_setoid_morphism (prod_partial_setoid X Z) Y).

    (*
      the main idea of the definition is okay
      however
      - develop infrastructure
      - some aadditional assumptions might be needed
     *)
    (** * 3. Lambda abstraction of partial setoid morphisms *)
    Definition lam_partial_setoid_form
      : form (Z ×h exp_partial_setoid)
      := let z := π₁ (π₁ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)))) in
         let P := π₂ (π₁ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)))) in
         let x := π₂ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y))) in
         let y := π₂ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)) in
         (∀h ∀h (φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ] ⇔ ⟨ x , y ⟩ ∈ P)).

    Proposition lam_partial_setoid_laws
      : partial_setoid_morphism_laws lam_partial_setoid_form.
    Proof.
      repeat split.
      - unfold partial_setoid_mor_dom_defined_law ; cbn.
        simplify_form.
        use forall_intro.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        pose (z := π₂ (π₁ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y))))).
        pose (f := π₂ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y)))).
        fold z f.
        admit. (* needs to be assumption *)
      - unfold partial_setoid_mor_cod_defined_law ; cbn.
        simplify_form.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        pose (z := π₂ (π₁ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y))))).
        pose (f := π₂ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y)))).
        fold z f.
        use eq_in_exp_partial_setoid.
        + admit. (* needs to be assumption *)
        + admit. (* free *)
      - unfold partial_setoid_mor_eq_defined_law ; cbn.
        admit.
      - unfold  partial_setoid_mor_unique_im_law ; cbn -[lam_partial_setoid_form].
        do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        pose (z := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))))).
        pose (f := π₂ (π₁ (tm_var (((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y))))).
        pose (g := π₂ (tm_var (((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))).
        fold z f g.
        simplify.
        use eq_in_exp_partial_setoid.
        + admit. (* needs to be assumption *)
        + unfold exp_partial_setoid_eq, f, g, z ; clear f g z.
          simplify.
          do 2 use forall_intro.
          simplify.
          pose (x := π₂ (π₁ (tm_var (((((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y)))).
          pose (y := π₂ (tm_var (((((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y))).
          pose (f := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y))))).
          pose (g := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y)))))).
          pose (z := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y))))))).
          fold x y z f g.
          admit. (* looks goed *)
      - unfold partial_setoid_mor_hom_exists_law ; cbn.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        use exists_intro.
        + refine {{ _ }}.
          admit.
        + (* seems ok *)
          admit.
    Admitted.

    Definition lam_partial_setoid
      : partial_setoid_morphism Z exp_partial_setoid.
    Proof.
      use make_partial_setoid_morphism.
      - exact lam_partial_setoid_form.
      - exact lam_partial_setoid_laws.
    Defined.

    Proposition lam_partial_setoid_comm
      : φ
        =
        partial_setoid_comp_morphism
          (pair_partial_setoid_morphism
             (partial_setoid_comp_morphism
                (partial_setoid_pr1 X Z)
                (id_partial_setoid_morphism X))
             (partial_setoid_comp_morphism
                (partial_setoid_pr2 X Z)
                lam_partial_setoid))
          eval_partial_setoid.
    Proof.
      use eq_partial_setoid_morphism.
      - cbn.
    Admitted.

    Context (φ' : partial_setoid_morphism Z exp_partial_setoid)
            (p : φ
                 =
                 partial_setoid_comp_morphism
                   (pair_partial_setoid_morphism
                      (partial_setoid_comp_morphism
                         (partial_setoid_pr1 X Z)
                         (id_partial_setoid_morphism X))
                      (partial_setoid_comp_morphism
                         (partial_setoid_pr2 X Z)
                         φ'))
                   eval_partial_setoid).

    (** * 4. Uniqueness *)
    Proposition lam_partial_setoid_unique
      : φ' = lam_partial_setoid.
    Proof.
    Admitted.
  End ExpPartialSetoid.

  (** * 5. Exponentials in the category of partial setoids *)
  Definition exponentials_partial_setoid
    : Exponentials (binproducts_partial_setoid H).
  Proof.
    intros X.
    use left_adjoint_from_partial.
    - exact (λ Y, exp_partial_setoid X Y).
    - exact (λ Y, eval_partial_setoid X Y).
    - intros Y Z f.
      use make_iscontr.
      + simple refine (_ ,, _).
        * exact (lam_partial_setoid X Y Z f).
        * exact (lam_partial_setoid_comm X Y Z f).
      + abstract
          (intros f' ;
           induction f' as [ f' p ] ;
           use subtypePath ; [ intro ; apply homset_property | ] ; cbn ;
           exact (lam_partial_setoid_unique X Y Z f f' p)).
  Defined.
End Exponentials.

Arguments exp_partial_setoid_per_form {H} X Y /.
Arguments eval_partial_setoid_form {H} X Y /.
Arguments lam_partial_setoid_form {H X Y Z} φ /.
