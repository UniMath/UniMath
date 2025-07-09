(******************************************************************************************

 Lambda abstraction for partial setoids

 In this file, we define lambda abstraction for partial setoids, which is yet another piece
 necessary to construct exponentials in the category of partial setoids.

 Fix partial setoids `X`, `Y`, and `Z`, and let `φ` be a morphism from `X ×h Z` to `Y`. The
 lambda abstraction of `φ` is a morphism from `Z` to the exponential from `X` to `Y`. Recall
 that the exponential was defined using the powerset operation, and in essence, the function
 space from `X` to `Y` is defined as the collection of all  functional relations between  `X`
 and `Y`. The underlying formula of the lambda abstraction operator is thus given by a relation
 between `Z` and the exponential from `X` to `Y`. Let's say we have some term `z` of type `X`
 and a term `f` of the exponential, then these are related if both `z` and `f` are defined
 (i.e., `z ~ z` and `f ~ f`), and if for all `x` and `y` we have that `φ` sends the pair
 `⟨ x , z ⟩` to `y` if and only if `f` sends `x` to `y`. The requirements are written down
 formally in [lam_partial_setoid_is_def] and [lam_partial_setoid_eq].

 We are required to check that this is a partial setoid morphism, and thus we must show
 that every `z` such that `z ~ z` has an image, and thus we must verify that every `z` gets
 mapped to an actual function by lambda abstraction.  One of the required checks is that
 images exist and for that we use [lam_image_form].

 Content
 1. The formula defining abstraction
 2. Accessors
 3. The image
 4. Lambda abstraction

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.GenericPredicate.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERBinProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.ExponentialPER.

Local Open Scope cat.
Local Open Scope hd.

Section PERLambda.
  Context {H : tripos}
          {X Y Z : partial_setoid H}
          (φ : partial_setoid_morphism (prod_partial_setoid X Z) Y).

  (** * 1. The formula defining abstraction *)
  Definition lam_partial_setoid_is_def
    : form (Z ×h exp_partial_setoid X Y)
    := let z := π₁ (tm_var (Z ×h exp_partial_setoid X Y)) in
       let f := π₂ (tm_var (Z ×h exp_partial_setoid X Y)) in
       z ~ z
       ∧
       exp_partial_setoid_is_function [ f ].

  Definition lam_partial_setoid_eq
    : form (Z ×h exp_partial_setoid X Y)
    := let z := π₁ (π₁ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)))) in
       let f := π₂ (π₁ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)))) in
       let x := π₂ (π₁ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y))) in
       let y := π₂ (tm_var (((Z ×h ℙ (X ×h Y)) ×h X) ×h Y)) in
       (∀h ∀h (φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ] ⇔ ⟨ x , y ⟩ ∈ f)).

  Definition lam_partial_setoid_form
    : form (Z ×h exp_partial_setoid X Y)
    := lam_partial_setoid_is_def
       ∧
       lam_partial_setoid_eq.

  (** * 2. Accessors *)
  Section Accessors.
    Context {Γ : ty H}
            {Δ : form Γ}
            (z : tm Γ Z)
            (f : tm Γ (exp_partial_setoid X Y))
            (p : Δ ⊢ lam_partial_setoid_form [⟨ z , f ⟩]).

    Proposition lam_partial_setoid_form_def_dom
      : Δ ⊢ z ~ z.
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold lam_partial_setoid_form.
      hypersimplify_form.
      use weaken_left.
      unfold lam_partial_setoid_is_def.
      hypersimplify_form.
      use weaken_left.
      hypersimplify.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition lam_partial_setoid_form_is_function
      : Δ ⊢ exp_partial_setoid_is_function [ f ].
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold lam_partial_setoid_form.
      hypersimplify_form.
      use weaken_left.
      unfold lam_partial_setoid_is_def.
      hypersimplify_form.
      use weaken_right.
      hypersimplify.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition lam_partial_setoid_form_def_fun
      : Δ ⊢ exp_partial_setoid_eq [ ⟨ f , f ⟩ ].
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold lam_partial_setoid_form.
      hypersimplify_form.
      use weaken_left.
      unfold lam_partial_setoid_is_def.
      hypersimplify_form.
      use weaken_right.
      hypersimplify.
      apply exp_partial_setoid_eq_refl.
    Qed.

    Proposition lam_partial_setoid_eq_iff
                (x : tm Γ X)
                (y : tm Γ Y)
      : Δ ⊢ φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ] ⇔ ⟨ x , y ⟩ ∈ f.
    Proof.
      refine (hyperdoctrine_cut p _).
      unfold lam_partial_setoid_form.
      hypersimplify_form.
      use weaken_right.
      unfold lam_partial_setoid_eq.
      hypersimplify_form.
      use (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) x) _).
      hypersimplify_form.
      use (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) y) _).
      cbn.
      hypersimplify.
      apply hyperdoctrine_hyp.
    Qed.

    Proposition lam_partial_setoid_eq_left
                (x : tm Γ X)
                (y : tm Γ Y)
                (q : Δ ⊢ φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ])
      : Δ ⊢ ⟨ x , y ⟩ ∈ f.
    Proof.
      use (iff_elim_left (lam_partial_setoid_eq_iff x y)).
      exact q.
    Qed.

    Proposition lam_partial_setoid_eq_right
                (x : tm Γ X)
                (y : tm Γ Y)
                (q : Δ ⊢ ⟨ x , y ⟩ ∈ f)
      : Δ ⊢ φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ].
    Proof.
      use (iff_elim_right (lam_partial_setoid_eq_iff x y)).
      exact q.
    Qed.
  End Accessors.

  Proposition to_lam_partial_setoid_eq
              {Γ : ty H}
              (z : tm Γ Z)
              (f : tm Γ (exp_partial_setoid X Y))
              {Δ : form Γ}
              (p₁ : Δ ⊢ z ~ z)
              (p₂ : Δ ⊢ exp_partial_setoid_is_function [ f ])
              (p₃ : Δ ⊢ lam_partial_setoid_eq [⟨ z , f ⟩])
    : Δ ⊢ lam_partial_setoid_form [ ⟨ z , f ⟩ ].
  Proof.
    unfold lam_partial_setoid_form, lam_partial_setoid_is_def.
    cbn.
    hypersimplify_form.
    hypersimplify.
    repeat use conj_intro.
    - exact p₁.
    - exact p₂.
    - exact p₃.
  Qed.

  (** The formula is preserved under the partial setoid relation of the first argument *)
  Proposition lam_partial_setoid_eq_arg
              {Γ : ty H}
              (z z' : tm Γ Z)
              (f : tm Γ (exp_partial_setoid X Y))
              {Δ : form Γ}
              (p : Δ ⊢ z ~ z')
              (q : Δ ⊢ f ~ f)
              (r : Δ ⊢ lam_partial_setoid_form [⟨ z , f ⟩])
    : Δ ⊢ lam_partial_setoid_form [⟨ z' , f ⟩].
  Proof.
    use to_lam_partial_setoid_eq.
    - exact (partial_setoid_refl_r p).
    - exact (lam_partial_setoid_form_is_function _ _ r).
    - unfold lam_partial_setoid_eq.
      rewrite !forall_subst.
      do 2 use forall_intro.
      cbn.
      hypersimplify.
      pose (γ := π₁ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
      pose (x := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
      pose (y := π₂ (tm_var ((Γ ×h X) ×h Y))).
      fold γ x y.
      use iff_intro.
      + use lam_partial_setoid_eq_left.
        * exact (z [ γ ]tm).
        * use weaken_left.
          refine (hyperdoctrine_cut
                    (hyperdoctrine_proof_subst γ r)
                    _).
          hypersimplify.
          apply hyperdoctrine_hyp.
        * use (partial_setoid_mor_eq_defined φ).
          ** exact ⟨ x , z' [ γ ]tm ⟩.
          ** exact y.
          ** use eq_in_prod_partial_setoid.
             *** hypersimplify.
                 use weaken_right.
                 refine (hyperdoctrine_cut
                           (partial_setoid_mor_dom_defined
                              φ ⟨ x , z' [ γ ]tm ⟩ y
                              (hyperdoctrine_hyp _))
                           _).
                 use (hyperdoctrine_cut
                        (eq_in_prod_partial_setoid_l _ _ (hyperdoctrine_hyp _))
                        _).
                 hypersimplify.
                 apply hyperdoctrine_hyp.
             *** use weaken_left.
                 hypersimplify.
                 rewrite <- partial_setoid_subst.
                 use hyperdoctrine_proof_subst.
                 use partial_setoid_sym.
                 exact p.
          ** use (partial_setoid_mor_cod_defined φ).
             *** exact ⟨ x , z' [ γ ]tm ⟩.
             *** use weaken_right.
                 apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
      + assert (Δ [γ] ∧ ⟨ x, y ⟩ ∈ f [γ ]tm ⊢ x ~ x) as lem₁.
        {
          refine (hyperdoctrine_cut _ _).
          * use (partial_setoid_mor_dom_defined φ ⟨ x , z [ γ ]tm ⟩ y _).
            use (lam_partial_setoid_eq_right (z [ γ ]tm) (f [ γ ]tm) _ x y).
            ** use weaken_left.
               refine (hyperdoctrine_cut
                         (hyperdoctrine_proof_subst γ r)
                         _).
               hypersimplify.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
          * refine (hyperdoctrine_cut
                      (eq_in_prod_partial_setoid_l _ _ (hyperdoctrine_hyp _))
                      _).
            hypersimplify.
            apply hyperdoctrine_hyp.
        }
        assert (Δ [γ] ∧ ⟨ x, y ⟩ ∈ f [γ ]tm ⊢ y ~ y) as lem₂.
        {
          use (partial_setoid_mor_cod_defined φ ⟨ x , z [ γ ]tm ⟩ y _).
          use (lam_partial_setoid_eq_right (z [ γ ]tm) (f [ γ ]tm) _ x y).
          {
            use weaken_left.
            refine (hyperdoctrine_cut
                      (hyperdoctrine_proof_subst γ r)
                      _).
            hypersimplify.
            apply hyperdoctrine_hyp.
          }
          use weaken_right.
          apply hyperdoctrine_hyp.
        }
        use (partial_setoid_mor_eq_defined φ).
        * exact ⟨ x , z [ γ ]tm ⟩.
        * exact y.
        * use eq_in_prod_partial_setoid.
          ** hypersimplify.
             exact lem₁.
          ** hypersimplify.
             use weaken_left.
             rewrite <- partial_setoid_subst.
             use hyperdoctrine_proof_subst.
             exact p.
        * exact lem₂.
        * use lam_partial_setoid_eq_right.
          ** exact (f [ γ ]tm).
          ** use weaken_left.
             refine (hyperdoctrine_cut
                       (hyperdoctrine_proof_subst γ r)
                       _).
             hypersimplify.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
  Qed.

  (** * 3. The image *)
  Definition lam_image_form
    : form ((X ×h Y) ×h 𝟙 ×h Z)
    := let x := π₁ (π₁ (tm_var ((X ×h Y) ×h 𝟙 ×h Z))) in
       let y := π₂ (π₁ (tm_var ((X ×h Y) ×h 𝟙 ×h Z))) in
       let z := π₂ (π₂ (tm_var ((X ×h Y) ×h 𝟙 ×h Z))) in
       φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ].

  Proposition lam_image_form_eq_help
              (x := π₁ (tm_var ((X ×h Y) ×h 𝟙 ×h Z)))
              (γ := π₂ (tm_var ((X ×h Y) ×h 𝟙 ×h Z)))
    : lam_image_form = (x ∈ {{lam_image_form}} [ γ ]tm).
  Proof.
    exact (mor_to_tripos_power_eq _ _ lam_image_form).
  Qed.

  Proposition lam_image_form_eq
              {Γ : ty H}
              (x : tm Γ X)
              (y : tm Γ Y)
              (z : tm Γ Z)
    : ⟨ x , y ⟩ ∈ {{lam_image_form}} [⟨ !!, z ⟩ ]tm
      =
      φ [ ⟨ ⟨ x , z ⟩ , y ⟩ ].
  Proof.
    refine (!_).
    etrans.
    {
      refine (_ @ maponpaths (λ φ, φ [ ⟨ ⟨ x , y ⟩ , ⟨ !! , z ⟩ ⟩ ]) lam_image_form_eq_help).
      unfold lam_image_form.
      cbn.
      hypersimplify.
      apply idpath.
    }
    cbn.
    hypersimplify.
    apply idpath.
  Qed.

  Proposition is_function_lam_image_form
              (Δ : form (𝟙 ×h Z))
              (p : Δ ⊢ π₂ (tm_var _) ~ π₂ (tm_var _))
    : Δ ⊢ exp_partial_setoid_is_function [{{lam_image_form}}].
  Proof.
    unfold exp_partial_setoid_is_function.
    hypersimplify_form.
    repeat use conj_intro.
    - unfold exp_partial_setoid_dom_defined_law.
      hypersimplify_form.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      hypersimplify_form.
      hypersimplify.
      pose (x := π₂ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))).
      pose (y := π₂ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))).
      pose (z := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
      fold x y z.
      rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
      fold z.
      assert (π₁ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))) = !!) as ->.
      {
        apply hyperdoctrine_unit_eta.
      }
      rewrite lam_image_form_eq.
      refine (hyperdoctrine_cut
                (partial_setoid_mor_dom_defined φ ⟨ x , z ⟩ y (hyperdoctrine_hyp _))
                _).
      refine (hyperdoctrine_cut (eq_in_prod_partial_setoid_l _ _ (hyperdoctrine_hyp _)) _).
      hypersimplify.
      apply hyperdoctrine_hyp.
    - unfold exp_partial_setoid_cod_defined_law.
      hypersimplify_form.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      hypersimplify_form.
      hypersimplify.
      pose (x := π₂ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))).
      pose (y := π₂ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))).
      pose (z := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
      fold x y z.
      rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
      fold z.
      assert (π₁ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))) = !!) as ->.
      {
        apply hyperdoctrine_unit_eta.
      }
      use (partial_setoid_mor_cod_defined φ ⟨ x , z ⟩ y _).
      rewrite lam_image_form_eq.
      apply hyperdoctrine_hyp.
    - unfold exp_partial_setoid_eq_defined_law.
      hypersimplify_form.
      do 4 use forall_intro.
      do 3 use impl_intro.
      hypersimplify_form.
      hypersimplify.
      pose (Γ := ((((𝟙 ×h Z) ×h X) ×h X) ×h Y) ×h Y).
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var Γ)))).
      pose (y₁ := π₂ (π₁ (tm_var Γ))).
      pose (y₂ := π₂ (tm_var Γ)).
      pose (z := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
      unfold Γ in * ; clear Γ.
      fold x₁ x₂ y₁ y₂ z.
      rewrite (hyperdoctrine_pair_eta
                 (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h Z) ×h X) ×h X) ×h Y) ×h Y))))))).
      fold z.
      assert (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h Z) ×h X) ×h X) ×h Y) ×h Y)))))) = !!)
        as ->.
      {
        apply hyperdoctrine_unit_eta.
      }
      rewrite !lam_image_form_eq.
      use (partial_setoid_mor_eq_defined φ).
      + exact ⟨ x₁ , z ⟩.
      + exact y₁.
      + use eq_in_prod_partial_setoid.
        * hypersimplify.
          do 2 use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        * hypersimplify.
          do 3 use weaken_left.
          refine (hyperdoctrine_cut
                    (hyperdoctrine_proof_subst ⟨ !! , z ⟩ p)
                    _).
          hypersimplify.
          apply hyperdoctrine_hyp.
      + use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold exp_partial_setoid_unique_im_law.
      hypersimplify_form.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      hypersimplify_form.
      hypersimplify.
      pose (z := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Z) ×h X) ×h Y) ×h Y)))))).
      pose (x := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h Z) ×h X) ×h Y) ×h Y))))).
      pose (y := π₂ (π₁ (tm_var ((((𝟙 ×h Z) ×h X) ×h Y) ×h Y)))).
      pose (y' := π₂ (tm_var ((((𝟙 ×h Z) ×h X) ×h Y) ×h Y))).
      fold x y y' z.
      rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Z) ×h X) ×h Y) ×h Y)))))).
      fold z.
      assert (π₁ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Z) ×h X) ×h Y) ×h Y))))) = !!) as ->.
      {
        apply hyperdoctrine_unit_eta.
      }
      rewrite !lam_image_form_eq.
      use (partial_setoid_mor_unique_im φ).
      + exact ⟨ x , z ⟩.
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold exp_partial_setoid_im_exists_law.
      hypersimplify_form.
      use forall_intro.
      use impl_intro.
      hypersimplify.
      pose (x := π₂ (tm_var ((𝟙 ×h Z) ×h X))).
      pose (z := π₂ (π₁ (tm_var ((𝟙 ×h Z) ×h X)))).
      fold x.
      refine (weaken_cut _ _).
      {
        use weaken_left.
        exact (hyperdoctrine_proof_subst (π₁ (tm_var ((𝟙 ×h Z) ×h X))) p).
      }
      use hyp_ltrans.
      use weaken_right.
      hypersimplify.
      fold z.
      use (exists_elim (partial_setoid_mor_hom_exists φ (x := ⟨ x , z ⟩) _)).
      + use eq_in_prod_partial_setoid.
        * hypersimplify.
          use weaken_left.
          apply hyperdoctrine_hyp.
        * hypersimplify.
          use weaken_right.
          apply hyperdoctrine_hyp.
      + unfold x, z ; clear x z.
        rewrite exists_subst.
        pose (x := π₂ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))).
        pose (y := π₂ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))).
        pose (z := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
        use exists_intro.
        {
          exact y.
        }
        cbn.
        hypersimplify_form.
        hypersimplify.
        fold x y z.
        rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
        fold z.
        assert (π₁ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))) = !!) as ->.
        {
          apply hyperdoctrine_unit_eta.
        }
        rewrite lam_image_form_eq.
        use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Proposition lam_partial_setoid_eq_image_form
              (Δ : form (𝟙 ×h Z))
    :  Δ ⊢ lam_partial_setoid_eq [⟨ π₂ (tm_var (𝟙 ×h Z)) , {{lam_image_form}} ⟩].
  Proof.
    unfold lam_partial_setoid_eq.
    rewrite !forall_subst.
    do 2 use forall_intro.
    cbn.
    hypersimplify.
    pose (x := π₂ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))).
    pose (y := π₂ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))).
    pose (z := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
    fold x y z.
    rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y))))).
    fold z.
    assert (π₁ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h X) ×h Y)))) = !!) as ->.
    {
      apply hyperdoctrine_unit_eta.
    }
    rewrite lam_image_form_eq.
    apply iff_refl.
  Qed.

  (** * 4. Lambda abstraction *)
  Proposition lam_partial_setoid_laws
    : partial_setoid_morphism_laws lam_partial_setoid_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law ; cbn.
      hypersimplify_form.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      pose (z := π₂ (π₁ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y))))).
      pose (f := π₂ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y)))).
      fold z f.
      use (lam_partial_setoid_form_def_dom z f).
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law ; cbn.
      hypersimplify_form.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      pose (z := π₂ (π₁ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y))))).
      pose (f := π₂ (tm_var ((𝟙 ×h Z) ×h ℙ (X ×h Y)))).
      fold z f.
      use eq_in_exp_partial_setoid.
      + use (lam_partial_setoid_form_is_function z f).
        apply hyperdoctrine_hyp.
      + use (lam_partial_setoid_form_def_fun z f).
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law ; cbn.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      pose (Γ := (((𝟙 ×h Z) ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)).
      pose (f' := π₂ (tm_var Γ)).
      pose (f := π₂ (π₁ (tm_var Γ))).
      pose (z' := π₂ (π₁ (π₁ (tm_var Γ)))).
      pose (z := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
      unfold Γ in * ; clear Γ.
      fold f f' z z'.
      use to_lam_partial_setoid_eq.
      + refine (partial_setoid_refl_r _).
        do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + use exp_partial_setoid_eq_is_function.
        * exact f.
        * use weaken_left.
          use weaken_right.
          use from_eq_in_exp_partial_setoid_function_eq.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          use (lam_partial_setoid_form_is_function z f).
          apply hyperdoctrine_hyp.
      + unfold lam_partial_setoid_eq.
        hypersimplify_form.
        do 2 use forall_intro.
        unfold f', f, z', z ; cbn ; clear f' f z' z.
        hypersimplify_form.
        hypersimplify.
        pose (Γ := (((((𝟙 ×h Z) ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y).
        pose (y := π₂ (tm_var Γ)).
        pose (x := π₂ (π₁ (tm_var Γ))).
        pose (f' := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (f := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
        pose (z' := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
        pose (z := π₂ (π₁ (π₁ (π₁ (π₁ (π₁ (tm_var Γ))))))).
        unfold Γ in * ; clear Γ ; cbn.
        fold x y z z' f f'.
        use iff_intro.
        * use from_exp_partial_setoid_eq.
          ** exact f.
          ** do 2 use weaken_left.
             use weaken_right.
             use from_eq_in_exp_partial_setoid_function_eq.
             apply hyperdoctrine_hyp.
          ** refine (lam_partial_setoid_eq_left z f _ x y _).
             *** use weaken_left.
                 use weaken_right.
                 apply hyperdoctrine_hyp.
             *** use (partial_setoid_mor_eq_defined φ).
                 **** exact ⟨ x , z' ⟩.
                 **** exact y.
                 **** use eq_in_prod_partial_setoid.
                      {
                        hypersimplify.
                        use weaken_right.
                        refine (hyperdoctrine_cut
                                  (partial_setoid_mor_dom_defined
                                     φ
                                     ⟨ x , z' ⟩ y
                                     (hyperdoctrine_hyp _))
                                  _).
                        refine (hyperdoctrine_cut
                                  (eq_in_prod_partial_setoid_l
                                     _ _
                                     (hyperdoctrine_hyp _))
                                  _).
                        hypersimplify.
                        apply hyperdoctrine_hyp.
                      }
                      hypersimplify.
                      do 3 use weaken_left.
                      use partial_setoid_sym.
                      apply hyperdoctrine_hyp.
                 **** use weaken_right.
                      exact (partial_setoid_mor_cod_defined
                               φ
                               ⟨ x , z' ⟩ y
                               (hyperdoctrine_hyp _)).
                 **** use weaken_right.
                      apply hyperdoctrine_hyp.
        * refine (lam_partial_setoid_eq_right z' f _ x y _).
          ** use lam_partial_setoid_eq_arg.
             *** exact z.
             *** do 3 use weaken_left.
                 apply hyperdoctrine_hyp.
             *** do 2 use weaken_left.
                 use weaken_right.
                 exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
             *** use weaken_left.
                 use weaken_right.
                 apply hyperdoctrine_hyp.
          ** use from_exp_partial_setoid_eq.
             *** exact f'.
             *** do 2 use weaken_left.
                 use weaken_right.
                 use from_eq_in_exp_partial_setoid_function_eq.
                 use partial_setoid_sym.
                 apply hyperdoctrine_hyp.
             *** use weaken_right.
                 apply hyperdoctrine_hyp.
    - unfold  partial_setoid_mor_unique_im_law ; cbn -[lam_partial_setoid_form].
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      pose (z := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))))).
      pose (f := π₂ (π₁ (tm_var (((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y))))).
      pose (g := π₂ (tm_var (((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)))).
      fold z f g.
      hypersimplify.
      use eq_in_exp_partial_setoid.
      + use weaken_left.
        use (lam_partial_setoid_form_is_function z f).
        apply hyperdoctrine_hyp.
      + unfold exp_partial_setoid_eq, f, g, z ; clear f g z.
        hypersimplify.
        do 2 use forall_intro.
        hypersimplify.
        pose (Γ := ((((𝟙 ×h Z) ×h ℙ (X ×h Y)) ×h ℙ (X ×h Y)) ×h X) ×h Y).
        pose (x := π₂ (π₁ (tm_var Γ))).
        pose (y := π₂ (tm_var Γ)).
        pose (f := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (g := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
        pose (z := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var Γ)))))).
        unfold Γ in * ; clear Γ.
        fold x y z f g.
        refine (iff_trans _ _).
        {
          use iff_sym.
          use (lam_partial_setoid_eq_iff z g).
          use weaken_left.
          apply hyperdoctrine_hyp.
        }
        use (lam_partial_setoid_eq_iff z f).
        use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law ; cbn.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      hypersimplify.
      use exists_intro.
      + exact {{ lam_image_form }}.
      + pose (z := π₂ (tm_var (𝟙 ×h Z))).
        hypersimplify.
        fold z.
        use to_lam_partial_setoid_eq.
        * apply hyperdoctrine_hyp.
        * apply is_function_lam_image_form.
          fold z.
          apply hyperdoctrine_hyp.
        * apply lam_partial_setoid_eq_image_form.
  Qed.

  Definition lam_partial_setoid
    : partial_setoid_morphism Z (exp_partial_setoid X Y).
  Proof.
    use make_partial_setoid_morphism.
    - exact lam_partial_setoid_form.
    - exact lam_partial_setoid_laws.
  Defined.
End PERLambda.
