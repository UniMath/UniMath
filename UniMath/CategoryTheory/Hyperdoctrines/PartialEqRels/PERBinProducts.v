(******************************************************************************************

 Binary products of partial setoids

 We show that the category of partial setoids has binary products. To construct the binary
 product of two partial setoids, we take the products of their underlying types. This is
 possible, because by definition the category of types in a first-order hyperdoctrine has
 binary products. The partial equivalence relation of the product is defined componentwise.
 The precise definition is given in the file `PERs.v`. In this file, we construct the
 projections and the pairing function, and we conclude that from this we obtain binary
 products in the category of partial setoids.

 Note that we define the projections in a slightly different way compared to Lemma 3.2 in
 "Tripos Theory in Retrospect". To understand way, let us assume we have two partial setoids
 `(X, ~_{X})` and `(Y, ~_{Y})`. To define the partial equivalence relation on `X ×h Y`, we
 need a formula `_{X ×h Y}` in context `(X ×h Y) ×h (X ×h Y)`. In essence, this formula is
 defined as follows `(x₁, y₁) ~_{X ×h Y} (x₂, y₂)` if and only if `x₁ ~_{X} x₂` and
 `y₁ ~_{Y} y₂`. For the first projection, we need to give a formula, call it `φ` in context
 `(X ×h Y) ×h X`. For this formula, Pitts takes `π₁ y ~_{X} x` for `y : X ×h Y` and `x : X`.
 However, we take a stronger one, namely `π₁ y ~_{X} x ∧ π₂ y ~_{Y} π₂ y`. In Pitt's formula,
 we are guaranteed that `x : X` is defined and `π₁ y` is defined. This is because whenever
 we have `a ~ b` for some elements `a` and `b`, then we must also have `a ~ a` and `b ~ b`
 by symmetry and transitivity. However, we are not guaranteed that `π₂ y` is also defined.
 This is what is added in our formula compared to one given by Pitts.

 We need to have this assumption because we want the first projection
 to be a morphism. In the file `PERMorphisms.v`, the full list of requirements are given.
 The relevant requirement is strictness: if `φ` is the formula describing a partial setoid
 morphism and we have `φ x y` for some `x` and `y`, then we must also have `x ~ x` (and
 `y ~ y`(. This requirement is called 'strictness' in "Realizability: an introduction to its
 categorical side" by Jaap van Oosten. Now let us compare the two formulas:
 1. With our formula, we must prove `π₁ x ~ y ∧ π₂ x ~ π₂ x ⊢ π₁ x ~ π₁ x ∧ π₂ x ~ π₂ x`.
    This holds.
 2. However, we would get the goal `π₁ x ~ y ⊢ π₁ x ~ π₁ x ∧ π₂ x ~ π₂ x` if we used the
    formula by Pitts instead. Here we would get stuck on proving `π₂ x ~ π₂ x`.

 Finally, we show that the constant object functor preserves binary products.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts
 - "Realizability: an introduction to its categorical side" by Jaap van Oosten

 Content
 1. The first projection
 2. The second projection
 3. Pairing partial setoid morphisms
 4. The uniqueness
 5. Binary products of partial setoids
 6. Preservation of binary products by the constant object functor

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERConstantObjects.

Local Open Scope cat.
Local Open Scope hd.

Section Projections.
  Context {H : first_order_hyperdoctrine}
          (X Y : partial_setoid H).

  (** * 1. The first projection *)
  Definition partial_setoid_pr1_form
    : form ((prod_partial_setoid X Y) ×h X)
    := let x := π₁ (π₁ (tm_var _)) : tm ((X ×h Y) ×h X) X in
       let y := π₂ (π₁ (tm_var _)) : tm ((X ×h Y) ×h X) Y in
       let x' := π₂ (tm_var _) : tm ((X ×h Y) ×h X) X in
       x ~ x' ∧ y ~ y.

  Arguments partial_setoid_pr1_form /.

  Proposition partial_setoid_pr1_laws
    : partial_setoid_morphism_laws partial_setoid_pr1_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := X).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use eq_in_prod_partial_setoid.
      + use partial_setoid_refl_l.
        * exact y.
        * simplify.
          use weaken_left.
          use hyperdoctrine_hyp.
      + use weaken_right.
        unfold x.
        simplify.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := X).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      simplify_form.
      use weaken_left.
      rewrite !partial_setoid_subst.
      simplify.
      use partial_setoid_refl_r.
      + exact (π₁ x).
      + apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := X).
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
      pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
      pose (y₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x₁ x₂ y₁ y₂.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use impl_intro.
      cbn.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use conj_intro.
      + use (partial_setoid_trans y₁).
        * use (partial_setoid_trans (π₁ x₁)).
          ** do 2 use weaken_left.
             use partial_setoid_sym.
             use eq_in_prod_partial_setoid_l.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
        * use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
      + do 2 use weaken_left.
        use eq_in_prod_partial_setoid_r.
        use partial_setoid_refl_r ; [ | apply hyperdoctrine_hyp ].
    - unfold partial_setoid_mor_unique_im_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := X).
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
      pose (z₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
      pose (z₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x z₁ z₂.
      cbn.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use partial_setoid_trans.
      + exact (π₁ x).
      + use partial_setoid_sym.
        use weaken_left.
        use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := X).
      pose (x := π₂ (tm_var (𝟙 ×h T))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      cbn.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use exists_intro.
      + exact (π₁ (π₂ (tm_var _))).
      + simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        use conj_intro.
        * unfold y.
          simplify.
          use eq_in_prod_partial_setoid_l.
          apply hyperdoctrine_hyp.
        * use eq_in_prod_partial_setoid_r.
          apply hyperdoctrine_hyp.
  Qed.

  Definition partial_setoid_pr1
    : partial_setoid_morphism (prod_partial_setoid X Y) X.
  Proof.
    use make_partial_setoid_morphism.
    - exact partial_setoid_pr1_form.
    - exact partial_setoid_pr1_laws.
  Defined.

  (** * 2. The second projection *)
  Definition partial_setoid_pr2_form
    : form ((prod_partial_setoid X Y) ×h Y)
    := let x := π₁ (π₁ (tm_var _)) : tm ((X ×h Y) ×h Y) X in
       let y := π₂ (π₁ (tm_var _)) : tm ((X ×h Y) ×h Y) Y in
       let y' := π₂ (tm_var _) : tm ((X ×h Y) ×h Y) Y in
       x ~ x ∧ y ~ y'.

  Arguments partial_setoid_pr2_form /.

  Proposition partial_setoid_pr2_laws
    : partial_setoid_morphism_laws partial_setoid_pr2_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := Y).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use eq_in_prod_partial_setoid.
      + use weaken_left.
        unfold x.
        simplify.
        apply hyperdoctrine_hyp.
      + use partial_setoid_refl_l.
        * exact y.
        * simplify.
          use weaken_right.
          use hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := Y).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      simplify_form.
      use weaken_right.
      rewrite !partial_setoid_subst.
      simplify.
      use partial_setoid_refl_r.
      + exact (π₂ x).
      + apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := Y).
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
      pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
      pose (y₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x₁ x₂ y₁ y₂.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use impl_intro.
      cbn.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use conj_intro.
      + do 2 use weaken_left.
        use eq_in_prod_partial_setoid_l.
        use partial_setoid_refl_r ; [ | apply hyperdoctrine_hyp ].
      + use (partial_setoid_trans y₁).
        * use (partial_setoid_trans (π₂ x₁)).
          ** do 2 use weaken_left.
             use partial_setoid_sym.
             use eq_in_prod_partial_setoid_r.
             apply hyperdoctrine_hyp.
          ** do 2 use weaken_right.
             apply hyperdoctrine_hyp.
        * use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := Y).
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
      pose (z₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
      pose (z₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x z₁ z₂.
      cbn.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use partial_setoid_trans.
      + exact (π₂ x).
      + use partial_setoid_sym.
        use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
      + do 2 use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := Y).
      pose (x := π₂ (tm_var (𝟙 ×h T))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      cbn.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use exists_intro.
      + exact (π₂ (π₂ (tm_var _))).
      + simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        use conj_intro.
        * use eq_in_prod_partial_setoid_l.
          apply hyperdoctrine_hyp.
        * unfold y.
          simplify.
          use eq_in_prod_partial_setoid_r.
          apply hyperdoctrine_hyp.
  Qed.

  Definition partial_setoid_pr2
    : partial_setoid_morphism (prod_partial_setoid X Y) Y.
  Proof.
    use make_partial_setoid_morphism.
    - exact partial_setoid_pr2_form.
    - exact partial_setoid_pr2_laws.
  Defined.
End Projections.

Arguments partial_setoid_pr1_form {H} X Y /.
Arguments partial_setoid_pr2_form {H} X Y /.

Section Pairing.
  Context {H : first_order_hyperdoctrine}
          {W X Y : partial_setoid H}
          (φ : partial_setoid_morphism W X)
          (ψ : partial_setoid_morphism W Y).

  (** * 3. Pairing partial setoid morphisms *)
  Definition pair_partial_setoid_morphism_form
    : form (W ×h prod_partial_setoid X Y)
    := let w := π₁ (tm_var (W ×h X ×h Y)) in
       let x := π₁ (π₂ (tm_var (W ×h X ×h Y))) in
       let y := π₂ (π₂ (tm_var (W ×h X ×h Y))) in
       φ [ ⟨ w , x ⟩ ] ∧ ψ [ ⟨ w , y ⟩ ].

  Proposition pair_partial_setoid_morphism_laws
    : partial_setoid_morphism_laws pair_partial_setoid_morphism_form.
  Proof.
    unfold pair_partial_setoid_morphism_form.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      cbn ; simplify.
      pose (w := π₂ (π₁ (tm_var ((𝟙 ×h W) ×h X ×h Y)))).
      pose (x := π₁ (π₂ (tm_var ((𝟙 ×h W) ×h X ×h Y)))).
      pose (y := π₂ (π₂ (tm_var ((𝟙 ×h W) ×h X ×h Y)))).
      fold w x y.
      do 2 use forall_intro.
      use impl_intro.
      do 2 use weaken_right.
      use (partial_setoid_mor_dom_defined ψ w y).
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law.
      cbn ; simplify.
      pose (w := π₂ (π₁ (tm_var ((𝟙 ×h W) ×h X ×h Y)))).
      pose (x := π₁ (π₂ (tm_var ((𝟙 ×h W) ×h X ×h Y)))).
      pose (y := π₂ (π₂ (tm_var ((𝟙 ×h W) ×h X ×h Y)))).
      fold w x y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use eq_in_prod_partial_setoid ; fold x y.
      + use weaken_left.
        use (partial_setoid_mor_cod_defined φ w x).
        apply hyperdoctrine_hyp.
      + use weaken_right.
        use (partial_setoid_mor_cod_defined ψ w y).
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law.
      pose (T := W).
      pose (T' := prod_partial_setoid X Y).
      pose (w₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
      pose (w₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
      pose (xy₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
      pose (xy₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold w₁ w₂ xy₁ xy₂.
      simplify.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      use conj_intro.
      + use hyp_rtrans.
        use weaken_left.
        use (partial_setoid_mor_eq_defined φ).
        * exact w₁.
        * exact (π₁ xy₁).
        * do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          use weaken_right.
          use eq_in_prod_partial_setoid_l.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
      + use hyp_sym.
        use hyp_ltrans.
        use weaken_right.
        use (partial_setoid_mor_eq_defined ψ).
        * exact w₁.
        * exact (π₂ xy₁).
        * use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
        * do 2 use weaken_right.
          use eq_in_prod_partial_setoid_r.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law.
      pose (T := W).
      pose (T' := prod_partial_setoid X Y).
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
      pose (z₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
      pose (z₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x z₁ z₂.
      simplify.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use eq_in_prod_partial_setoid.
      + use hyp_rtrans.
        use weaken_left.
        use hyp_sym.
        use hyp_rtrans.
        use weaken_left.
        use (partial_setoid_mor_unique_im φ).
        * exact x.
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
      + use hyp_ltrans.
        use weaken_right.
        use hyp_sym.
        use hyp_ltrans.
        use weaken_right.
        use (partial_setoid_mor_unique_im ψ).
        * exact x.
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      pose (T := W).
      pose (T' := prod_partial_setoid X Y).
      pose (x := π₂ (tm_var (𝟙 ×h T))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      cbn.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      simplify.
      use (exists_elim
             (partial_setoid_mor_hom_exists φ (hyperdoctrine_hyp _))).
      rewrite partial_setoid_subst.
      use (exists_elim
             (partial_setoid_mor_hom_exists ψ (weaken_left (hyperdoctrine_hyp _) _))).
      unfold x, y.
      simplify_form.
      use hyp_ltrans.
      use weaken_right.
      use exists_intro.
      + exact (⟨ π₂ (π₁ (tm_var _)) , π₂ (tm_var _) ⟩).
      + unfold x, y.
        simplify.
        apply hyperdoctrine_hyp.
  Qed.

  Definition pair_partial_setoid_morphism
    : partial_setoid_morphism W (prod_partial_setoid X Y).
  Proof.
    use make_partial_setoid_morphism.
    - exact pair_partial_setoid_morphism_form.
    - exact pair_partial_setoid_morphism_laws.
  Defined.

  Arguments pair_partial_setoid_morphism_form /.

  Proposition pair_partial_setoid_morphism_pr1
    : partial_setoid_comp_morphism
        pair_partial_setoid_morphism
        (partial_setoid_pr1 _ _)
      =
      φ.
  Proof.
    use eq_partial_setoid_morphism ; cbn.
    - use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      unfold partial_setoid_pr1_form.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      pose (w := π₁ (π₁ (tm_var ((W ×h X) ×h X ×h Y)))).
      pose (x := π₁ (π₂ (tm_var ((W ×h X) ×h X ×h Y)))).
      pose (x' := π₂ (π₁ (tm_var ((W ×h X) ×h X ×h Y)))).
      pose (y := π₂ (π₂ (tm_var ((W ×h X) ×h X ×h Y)))).
      fold w x x' y.
      rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((W ×h X) ×h X ×h Y)))).
      fold w x'.
      use hyp_rtrans.
      use weaken_left.
      use hyp_sym.
      use hyp_rtrans.
      use weaken_left.
      use (partial_setoid_mor_eq_defined φ).
      + exact w.
      + exact x.
      + use weaken_right.
        exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - use (exists_elim (partial_setoid_mor_hom_exists ψ _)).
      + exact (π₁ (tm_var _)).
      + use (partial_setoid_mor_dom_defined φ _ (π₂ (tm_var _))).
        rewrite <- hyperdoctrine_pair_eta.
        rewrite hyperdoctrine_id_subst.
        apply hyperdoctrine_hyp.
      + unfold partial_setoid_pr1_form.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        use exists_intro.
        * exact (⟨ π₂ (π₁ (tm_var _)) , π₂ (tm_var _) ⟩).
        * simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          use conj_intro.
          ** use conj_intro.
             *** use weaken_left.
                 rewrite <- hyperdoctrine_pair_eta.
                 apply hyperdoctrine_hyp.
             *** use weaken_right.
                 apply hyperdoctrine_hyp.
          ** use conj_intro.
             *** use weaken_left.
                 use (partial_setoid_mor_cod_defined φ).
                 {
                   exact (π₁ (π₁ (tm_var _))).
                 }
                 rewrite <- hyperdoctrine_pair_eta.
                 apply hyperdoctrine_hyp.
             *** use weaken_right.
                 exact (partial_setoid_mor_cod_defined ψ _ _ (hyperdoctrine_hyp _)).
  Qed.

  Proposition pair_partial_setoid_morphism_pr2
    : partial_setoid_comp_morphism
        pair_partial_setoid_morphism
        (partial_setoid_pr2 _ _)
      =
      ψ.
  Proof.
    use eq_partial_setoid_morphism ; cbn.
    - use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      unfold partial_setoid_pr2_form.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      pose (w := π₁ (π₁ (tm_var ((W ×h Y) ×h X ×h Y)))).
      pose (x := π₁ (π₂ (tm_var ((W ×h Y) ×h X ×h Y)))).
      pose (y' := π₂ (π₁ (tm_var ((W ×h Y) ×h X ×h Y)))).
      pose (y := π₂ (π₂ (tm_var ((W ×h Y) ×h X ×h Y)))).
      fold w x y y'.
      rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((W ×h Y) ×h X ×h Y)))).
      fold w y'.
      use hyp_ltrans.
      use weaken_right.
      use hyp_sym.
      use hyp_ltrans.
      use weaken_right.
      use (partial_setoid_mor_eq_defined ψ).
      + exact w.
      + exact y.
      + use weaken_right.
        exact (partial_setoid_mor_dom_defined ψ _ _ (hyperdoctrine_hyp _)).
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - use (exists_elim (partial_setoid_mor_hom_exists φ _)).
      + exact (π₁ (tm_var _)).
      + use (partial_setoid_mor_dom_defined ψ _ (π₂ (tm_var _))).
        rewrite <- hyperdoctrine_pair_eta.
        rewrite hyperdoctrine_id_subst.
        apply hyperdoctrine_hyp.
      + unfold partial_setoid_pr2_form.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        use exists_intro.
        * exact (⟨ π₂ (tm_var _) , π₂ (π₁ (tm_var _)) ⟩).
        * simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          use conj_intro.
          ** use conj_intro.
             *** use weaken_right.
                 apply hyperdoctrine_hyp.
             *** use weaken_left.
                 rewrite <- hyperdoctrine_pair_eta.
                 apply hyperdoctrine_hyp.
          ** use conj_intro.
             *** use weaken_right.
                 exact (partial_setoid_mor_cod_defined φ _ _ (hyperdoctrine_hyp _)).
             *** use weaken_left.
                 use (partial_setoid_mor_cod_defined ψ).
                 {
                   exact (π₁ (π₁ (tm_var _))).
                 }
                 rewrite <- hyperdoctrine_pair_eta.
                 apply hyperdoctrine_hyp.
  Qed.

  (** * 4. The uniqueness *)
  Context {χ : partial_setoid_morphism W (prod_partial_setoid X Y)}
          (p₁ : partial_setoid_comp_morphism χ (partial_setoid_pr1 X Y) = φ)
          (p₂ : partial_setoid_comp_morphism χ (partial_setoid_pr2 X Y) = ψ).

  Proposition pair_partial_setoid_morphism_unique
    : χ = pair_partial_setoid_morphism.
  Proof.
    use eq_partial_setoid_morphism ; cbn.
    - use conj_intro.
      + refine (from_eq_partial_setoid_morphism_f p₁ _) ; cbn.
        simplify_form.
        use exists_intro.
        * exact (π₂ (tm_var _)).
        * simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          rewrite <- hyperdoctrine_pair_eta.
          simplify_form.
          repeat (use conj_intro).
          ** apply hyperdoctrine_hyp.
          ** use eq_in_prod_partial_setoid_l.
             use (partial_setoid_mor_cod_defined χ (π₁ (tm_var _))).
             rewrite <- hyperdoctrine_pair_eta.
             simplify_form.
             apply hyperdoctrine_hyp.
          ** use eq_in_prod_partial_setoid_r.
             use (partial_setoid_mor_cod_defined χ (π₁ (tm_var _))).
             rewrite <- hyperdoctrine_pair_eta.
             simplify_form.
             apply hyperdoctrine_hyp.
      + refine (from_eq_partial_setoid_morphism_f p₂ _) ; cbn.
        simplify_form.
        use exists_intro.
        * exact (π₂ (tm_var _)).
        * simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          rewrite <- hyperdoctrine_pair_eta.
          simplify_form.
          repeat (use conj_intro).
          ** apply hyperdoctrine_hyp.
          ** use eq_in_prod_partial_setoid_l.
             use (partial_setoid_mor_cod_defined χ (π₁ (tm_var _))).
             rewrite <- hyperdoctrine_pair_eta.
             simplify_form.
             apply hyperdoctrine_hyp.
          ** use eq_in_prod_partial_setoid_r.
             use (partial_setoid_mor_cod_defined χ (π₁ (tm_var _))).
             rewrite <- hyperdoctrine_pair_eta.
             simplify_form.
             apply hyperdoctrine_hyp.
    - pose (w := π₁ (tm_var (W ×h X ×h Y))).
      pose (x := π₁ (π₂ (tm_var (W ×h X ×h Y)))).
      pose (y := π₂ (π₂ (tm_var (W ×h X ×h Y)))).
      pose (Δ := φ [⟨ w, x ⟩] ∧ ψ [⟨ w, y ⟩]).
      fold w x y Δ.
      assert (Δ ⊢ φ [⟨ w , x ⟩]) as q.
      {
        use weaken_left.
        apply hyperdoctrine_hyp.
      }
      use (weaken_cut (from_eq_partial_setoid_morphism_b p₁ q)).
      cbn.
      simplify_form.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      rewrite conj_subst.
      use hyp_ltrans.
      use weaken_right.
      simplify_form.
      rewrite !partial_setoid_subst.
      unfold Δ, w, x, y.
      simplify.
      clear q w x y Δ.
      use hyp_ltrans.
      use weaken_right.
      refine (weaken_cut
                (weaken_left
                   (from_eq_partial_setoid_morphism_b
                      p₂
                      (hyperdoctrine_hyp _))
                   _)
                _).
      use hyp_ltrans.
      use weaken_right.
      cbn.
      simplify.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      rewrite conj_subst.
      use hyp_ltrans.
      use weaken_right.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      pose (w := π₁ (π₁ (π₁ (tm_var (((W ×h X ×h Y) ×h X ×h Y) ×h X ×h Y))))).
      pose (xy₁:= π₂ (π₁ (tm_var (((W ×h X ×h Y) ×h X ×h Y) ×h X ×h Y)))).
      pose (xy₂ := π₂ (π₁ (π₁ (tm_var (((W ×h X ×h Y) ×h X ×h Y) ×h X ×h Y))))).
      pose (xy₃ := π₂ (tm_var (((W ×h X ×h Y) ×h X ×h Y) ×h X ×h Y))).
      fold w xy₁ xy₂ xy₃.
      rewrite (hyperdoctrine_pair_eta (π₁ (π₁ (tm_var (((W ×h X ×h Y) ×h X ×h Y) ×h X ×h Y))))).
      fold w xy₂.
      use (partial_setoid_mor_eq_defined χ).
      + exact w.
      + exact xy₁.
      + use (partial_setoid_mor_dom_defined χ _ xy₁).
        do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + use eq_in_prod_partial_setoid.
        * use weaken_left.
          use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
        * use partial_setoid_trans.
          ** exact (π₂ xy₃).
          ** use eq_in_prod_partial_setoid_r.
             use (partial_setoid_mor_unique_im χ).
             *** exact w.
             *** do 2 use weaken_left.
                 apply hyperdoctrine_hyp.
             *** use weaken_right.
                 use weaken_left.
                 apply hyperdoctrine_hyp.
          ** do 3 use weaken_right.
             apply hyperdoctrine_hyp.
      + do 2 use weaken_left.
        apply hyperdoctrine_hyp.
  Qed.
End Pairing.

Arguments pair_partial_setoid_morphism_form {H W X Y} φ ψ /.

(** * 5. Binary products of partial setoids *)
Definition binproducts_partial_setoid
           (H : first_order_hyperdoctrine)
  : BinProducts (category_of_partial_setoids H).
Proof.
  intros X Y.
  use make_BinProduct.
  - exact (prod_partial_setoid X Y).
  - exact (partial_setoid_pr1 X Y).
  - exact (partial_setoid_pr2 X Y).
  - intros W φ ψ.
    use make_iscontr.
    + simple refine (_ ,, _ ,, _).
      * exact (pair_partial_setoid_morphism φ ψ).
      * apply pair_partial_setoid_morphism_pr1.
      * apply pair_partial_setoid_morphism_pr2.
    + abstract
        (intros χ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         exact (pair_partial_setoid_morphism_unique _ _ (pr12 χ) (pr22 χ))).
Defined.

(** * 6. Preservation of binary products by the constant object functor *)
Section PreservesBinProductConstant.
  Context {H : first_order_hyperdoctrine}
          (X Y : ty H).

  Definition preserves_binproduct_functor_to_partial_setoids_inv_form
    : form
        (prod_partial_setoid (eq_partial_setoid X) (eq_partial_setoid Y)
         ×h
         eq_partial_setoid (X ×h Y))
    := π₁ (tm_var _) ≡ π₂ (tm_var _).

  Arguments preserves_binproduct_functor_to_partial_setoids_inv_form /.

  Proposition preserves_binproduct_functor_to_partial_setoids_inv_laws
    : partial_setoid_morphism_laws
        preserves_binproduct_functor_to_partial_setoids_inv_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law ; cbn.
      do 2 (use forall_intro).
      use impl_intro.
      use weaken_right.
      use eq_in_prod_partial_setoid.
      + use eq_in_eq_partial_setoid.
        apply hyperdoctrine_refl.
      + use eq_in_eq_partial_setoid.
        apply hyperdoctrine_refl.
    - unfold partial_setoid_mor_cod_defined_law ; cbn.
      do 2 (use forall_intro).
      use impl_intro.
      use weaken_right.
      use eq_in_eq_partial_setoid.
      apply hyperdoctrine_refl.
    - unfold partial_setoid_mor_eq_defined_law ; cbn.
      do 4 (use forall_intro).
      use impl_intro.
      use weaken_right.
      do 2 (use impl_intro).
      simplify.
      pose (xy₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h X ×h Y) ×h X ×h Y) ×h X ×h Y) ×h X ×h Y)))))).
      pose (xy₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h X ×h Y) ×h X ×h Y) ×h X ×h Y) ×h X ×h Y))))).
      pose (xy₃ := π₂ (π₁ (tm_var ((((𝟙 ×h X ×h Y) ×h X ×h Y) ×h X ×h Y) ×h X ×h Y)))).
      pose (xy₄ := π₂ (tm_var ((((𝟙 ×h X ×h Y) ×h X ×h Y) ×h X ×h Y) ×h X ×h Y))).
      fold xy₁ xy₂ xy₃ xy₄.
      use hyperdoctrine_eq_trans.
      + exact xy₁.
      + do 2 use weaken_left.
        use hyperdoctrine_eq_sym.
        use hyperdoctrine_eq_prod_eq.
        * use from_eq_in_eq_partial_setoid.
          exact (eq_in_prod_partial_setoid_l _ _ (hyperdoctrine_hyp _)).
        * use from_eq_in_eq_partial_setoid.
          exact (eq_in_prod_partial_setoid_r _ _ (hyperdoctrine_hyp _)).
      + use hyperdoctrine_eq_trans.
        * exact xy₃.
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          use weaken_right.
          use from_eq_in_eq_partial_setoid.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law ; cbn.
      do 3 (use forall_intro).
      use impl_intro.
      use weaken_right.
      use impl_intro.
      simplify.
      pose (xy₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X ×h Y) ×h X ×h Y) ×h X ×h Y))))).
      pose (xy₂ := π₂ (π₁ (tm_var (((𝟙 ×h X ×h Y) ×h X ×h Y) ×h X ×h Y)))).
      pose (xy₃ := π₂ (tm_var (((𝟙 ×h X ×h Y) ×h X ×h Y) ×h X ×h Y))).
      fold xy₁ xy₂ xy₃.
      use eq_in_eq_partial_setoid.
      use hyperdoctrine_eq_trans.
      + exact xy₁.
      + use hyperdoctrine_eq_sym.
        use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law ; cbn.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use exists_intro.
      + exact (π₂ (tm_var _)).
      + simplify.
        apply hyperdoctrine_refl.
  Qed.

  Definition preserves_binproduct_functor_to_partial_setoids_inv
    : partial_setoid_morphism
        (prod_partial_setoid (eq_partial_setoid X) (eq_partial_setoid Y))
        (eq_partial_setoid (X ×h Y)).
  Proof.
    use make_partial_setoid_morphism.
    - exact preserves_binproduct_functor_to_partial_setoids_inv_form.
    - exact preserves_binproduct_functor_to_partial_setoids_inv_laws.
  Defined.

  Let φ
    : partial_setoid_morphism
        (eq_partial_setoid (X ×h Y))
        (prod_partial_setoid (eq_partial_setoid X) (eq_partial_setoid Y))
    := pair_partial_setoid_morphism
         (term_partial_setoid_morphism
            (BinProductPr1 _ (hyperdoctrine_binproducts _ X Y)))
         (term_partial_setoid_morphism
            (BinProductPr2 _ (hyperdoctrine_binproducts _ X Y))).

  Proposition preserves_binproduct_functor_to_partial_setoids_inv_left
    : partial_setoid_comp_morphism
        preserves_binproduct_functor_to_partial_setoids_inv
        φ
      =
      id_partial_setoid_morphism _.
  Proof.
    unfold φ.
    assert (BinProductPr1 (hyperdoctrine_type_category H) (hyperdoctrine_binproducts H X Y)
            =
            π₁ (tm_var _)) as q.
    {
      unfold hyperdoctrine_pr1, tm_var.
      rewrite id_left.
      apply idpath.
    }
    rewrite q ; clear q.
    assert (BinProductPr2 (hyperdoctrine_type_category H) (hyperdoctrine_binproducts H X Y)
            =
            π₂ (tm_var _)) as q.
    {
      unfold hyperdoctrine_pr2, tm_var.
      rewrite id_left.
      apply idpath.
    }
    rewrite q ; clear q.
    use eq_partial_setoid_morphism.
    - use (exists_elim (hyperdoctrine_hyp _)) ; cbn.
      use weaken_right.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      pose (xy₁ := π₁ (π₁ (tm_var (((X ×h Y) ×h X ×h Y) ×h X ×h Y)))).
      pose (xy₂ := π₂ (π₁ (tm_var (((X ×h Y) ×h X ×h Y) ×h X ×h Y)))).
      pose (xy₃ := π₂ (tm_var (((X ×h Y) ×h X ×h Y) ×h X ×h Y))).
      cbn.
      fold xy₁ xy₂ xy₃.
      use eq_in_prod_partial_setoid.
      + use eq_in_eq_partial_setoid.
        simple refine (hyperdoctrine_eq_trans _ _).
        * exact (π₁ xy₃).
        * use weaken_left.
          use hyperdoctrine_eq_pr1.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
      + use eq_in_eq_partial_setoid.
        simple refine (hyperdoctrine_eq_trans _ _).
        * exact (π₂ xy₃).
        * use weaken_left.
          use hyperdoctrine_eq_pr2.
          apply hyperdoctrine_hyp.
        * do 2 use weaken_right.
          apply hyperdoctrine_hyp.
    - cbn.
      use exists_intro.
      + exact (π₁ (tm_var _)).
      + simplify.
        repeat (use conj_intro).
        * apply hyperdoctrine_refl.
        * use from_eq_in_eq_partial_setoid.
          exact (eq_in_prod_partial_setoid_l _ _ (hyperdoctrine_hyp _)).
        * use from_eq_in_eq_partial_setoid.
          exact (eq_in_prod_partial_setoid_r _ _ (hyperdoctrine_hyp _)).
  Qed.

  Proposition preserves_binproduct_functor_to_partial_setoids_inv_right
    : partial_setoid_comp_morphism
        φ
        preserves_binproduct_functor_to_partial_setoids_inv
      =
      id_partial_setoid_morphism _.
  Proof.
    unfold φ.
    assert (BinProductPr1 (hyperdoctrine_type_category H) (hyperdoctrine_binproducts H X Y)
            =
            π₁ (tm_var _)) as q.
    {
      unfold hyperdoctrine_pr1, tm_var.
      rewrite id_left.
      apply idpath.
    }
    rewrite q ; clear q.
    assert (BinProductPr2 (hyperdoctrine_type_category H) (hyperdoctrine_binproducts H X Y)
            =
            π₂ (tm_var _)) as q.
    {
      unfold hyperdoctrine_pr2, tm_var.
      rewrite id_left.
      apply idpath.
    }
    rewrite q ; clear q.
    use eq_partial_setoid_morphism.
    - use (exists_elim (hyperdoctrine_hyp _)) ; cbn.
      use weaken_right.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      pose (xy₁ := π₁ (π₁ (tm_var (((X ×h Y) ×h X ×h Y) ×h X ×h Y)))).
      pose (xy₂ := π₂ (π₁ (tm_var (((X ×h Y) ×h X ×h Y) ×h X ×h Y)))).
      pose (xy₃ := π₂ (tm_var (((X ×h Y) ×h X ×h Y) ×h X ×h Y))).
      cbn.
      fold xy₁ xy₂ xy₃.
      use eq_in_eq_partial_setoid.
      use hyperdoctrine_eq_prod_eq.
      + simple refine (hyperdoctrine_eq_trans _ _).
        * exact (π₁ xy₃).
        * do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        * use hyperdoctrine_eq_pr1.
          use weaken_right.
          apply hyperdoctrine_hyp.
      + simple refine (hyperdoctrine_eq_trans _ _).
        * exact (π₂ xy₃).
        * use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        * use hyperdoctrine_eq_pr2.
          use weaken_right.
          apply hyperdoctrine_hyp.
    - cbn.
      use exists_intro.
      + exact (π₁ (tm_var _)).
      + simplify.
        repeat (use conj_intro).
        * apply hyperdoctrine_refl.
        * apply hyperdoctrine_refl.
        * use from_eq_in_eq_partial_setoid.
          apply hyperdoctrine_hyp.
  Qed.
End PreservesBinProductConstant.

Definition preserves_binproduct_functor_to_partial_setoids
           (H : first_order_hyperdoctrine)
  : preserves_binproduct (functor_to_partial_setoids H).
Proof.
  use preserves_binproduct_chosen_to_chosen.
  - exact (hyperdoctrine_binproducts H).
  - exact (binproducts_partial_setoid H).
  - intros X Y.
    use make_is_z_isomorphism.
    + apply preserves_binproduct_functor_to_partial_setoids_inv.
    + abstract
        (split ;
         [ apply preserves_binproduct_functor_to_partial_setoids_inv_right
         | apply preserves_binproduct_functor_to_partial_setoids_inv_left ]).
Defined.
