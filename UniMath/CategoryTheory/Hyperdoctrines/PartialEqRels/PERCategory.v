(******************************************************************************************

 The category of partial setoids

 Given a hyperdoctrine `H`, we can define the type of partial setoids in `H`. Concretely,
 a partial setoid is a type `X` in `H` together with a partial equvialence relation (i.e.,
 a formula on `X ×h X` that is symmetric and transitive). We also defined the notion of a
 morphism between partial setoids: morphisms from a partial setoid `X` to a partial setoid
 `Y` are given by relations on `X` and `Y` satisfying some properties (which are described
 in the file `PerMorphisms.v`). In this file, we show how partial setoids together with
 partial setoid morphisms form a category. To do so, we define the identity partial setoid
 morphism and the composition, and we show that the category laws are satisfied.

 Note that the category of partial setoids is the basis for the tripos-to-topos construction.
 If one looks at triposes, then the category of partial setoids actually is a topos.
 However, even if one only looks at first-order hyperdoctrines, then this category still
 has a lot of structure. For instance, it has all finite limits.

 The most interesting aspect of this construction is that in general this does not give
 rise to a univalent category. For instance, on the category of sets we can define the
 trivial hyperdoctrine, whose formulas in context `Γ` are given by inhabitants of the unit
 type. In this case, partial setoids are the same as sets: this is because every set has
 a unique partial equivalence relation in this hyperdoctrine since there is only one
 formula. However, there also always is a unique morphism between any two partial setoids.
 For that reason, the resulting category is not univalent. For this reason, if one wants
 a tripos-to-univalent-topos construction, then one needs to apply the Rezk completion
 to the category of partial setoids. This works well due to the universal property of the
 tripos-to-topos construction (see Theorem 3.6 in "Tripos Theory in Retrospect" by Andrew
 Pitts).

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts

 Content
 1. The identity morphism
 2. The composition of morphisms of partial setoids
 3. The category of partial setoids
 4. Isomorphisms of partial setoids

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.

Local Open Scope cat.
Local Open Scope hd.

(** * 1. The identity morphism *)
Definition id_partial_setoid_morphism_form
           {H : first_order_hyperdoctrine}
           (X : partial_setoid H)
  : form (X ×h X)
  := π₁ (tm_var _) ~ π₂ (tm_var _).

Arguments id_partial_setoid_morphism_form {H} X /.

Proposition id_partial_setoid_morphism_laws
            {H : first_order_hyperdoctrine}
            (X : partial_setoid H)
  : partial_setoid_morphism_laws (id_partial_setoid_morphism_form X).
Proof.
  repeat split.
  - unfold partial_setoid_mor_dom_defined_law.
    pose (T := X).
    pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T)))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T))).
    unfold T in *.
    fold x y.
    cbn.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    hypersimplify.
    exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
  - unfold partial_setoid_mor_cod_defined_law.
    pose (T := X).
    pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T)))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T))).
    unfold T in *.
    fold x y.
    cbn.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    hypersimplify.
    exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
  - unfold partial_setoid_mor_eq_defined_law.
    pose (T := X).
    pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T) ×h T)))))).
    pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T) ×h T))))).
    pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T) ×h T)))).
    pose (y₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T) ×h T))).
    unfold T in *.
    fold x₁ x₂ y₁ y₂.
    cbn.
    use forall_intro.
    use forall_intro.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    use impl_intro.
    hypersimplify.
    use partial_setoid_trans.
    + exact x₁.
    + use partial_setoid_sym.
      do 2 use weaken_left.
      use hyperdoctrine_hyp.
    + use partial_setoid_trans.
      * exact y₁.
      * use weaken_right.
        use hyperdoctrine_hyp.
      * use weaken_left.
        use weaken_right.
        use hyperdoctrine_hyp.
  - unfold partial_setoid_mor_unique_im_law.
    pose (T := X).
    pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T) ×h T))))).
    pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T) ×h T)))).
    pose (y₂ := π₂ (tm_var (((𝟙 ×h T) ×h T) ×h T))).
    unfold T in *.
    fold x y₁ y₂.
    cbn.
    use forall_intro.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    hypersimplify.
    use partial_setoid_trans.
    + exact x.
    + use partial_setoid_sym.
      use weaken_left.
      use hyperdoctrine_hyp.
    + use weaken_right.
      use hyperdoctrine_hyp.
  - unfold partial_setoid_mor_hom_exists_law.
    pose (T := X).
    pose (x := π₂ (tm_var (𝟙 ×h T))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T))).
    unfold T in *.
    fold x y.
    cbn.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    hypersimplify.
    use exists_intro.
    + exact x.
    + unfold y.
      hypersimplify.
      use hyperdoctrine_hyp.
Qed.

Definition id_partial_setoid_morphism
           {H : first_order_hyperdoctrine}
           (X : partial_setoid H)
  : partial_setoid_morphism X X.
Proof.
  use make_partial_setoid_morphism.
  - exact (id_partial_setoid_morphism_form X).
  - exact (id_partial_setoid_morphism_laws X).
Defined.

(** * 2. The composition of morphisms of partial setoids *)
Section CompPartialSetoidMorphism.
  Context {H : first_order_hyperdoctrine}
          {X Y Z : partial_setoid H}
          (φ₁ : partial_setoid_morphism X Y)
          (φ₂ : partial_setoid_morphism Y Z).

  Definition partial_setoid_comp_morphism_form
    : form (X ×h Z)
    := let x := π₁ (π₁ (tm_var _)) : tm ((X ×h Z) ×h Y) X in
       let y := π₂ (tm_var _) : tm ((X ×h Z) ×h Y) Y in
       let z := π₂ (π₁ (tm_var _)) : tm ((X ×h Z) ×h Y) Z in
       (∃h (φ₁ [ ⟨ x , y ⟩ ] ∧ φ₂ [ ⟨ y , z ⟩ ])).

  Arguments partial_setoid_comp_morphism_form /.

  Proposition partial_setoid_comp_morphism_laws
    : partial_setoid_morphism_laws
        partial_setoid_comp_morphism_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      pose (T := X).
      pose (T' := Z).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (z := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x z.
      unfold partial_setoid_comp_morphism_form.
      hypersimplify.
      pose (y := π₂ (tm_var (((𝟙 ×h X) ×h Z) ×h Y))).
      fold y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      rewrite partial_setoid_subst.
      unfold x, y, z.
      hypersimplify.
      use weaken_left.
      apply (partial_setoid_mor_dom_defined φ₁ _ _ (hyperdoctrine_hyp _)).
    - unfold partial_setoid_mor_cod_defined_law.
      pose (T := X).
      pose (T' := Z).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (z := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x z.
      unfold partial_setoid_comp_morphism_form.
      hypersimplify.
      pose (y := π₂ (tm_var (((𝟙 ×h X) ×h Z) ×h Y))).
      fold y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      rewrite partial_setoid_subst.
      unfold x, y, z.
      hypersimplify.
      use weaken_right.
      apply (partial_setoid_mor_cod_defined φ₂ _ _ (hyperdoctrine_hyp _)).
    - unfold partial_setoid_mor_eq_defined_law.
      pose (T := X).
      pose (T' := Z).
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
      pose (z₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
      pose (z₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x₁ x₂ z₁ z₂.
      unfold partial_setoid_comp_morphism_form.
      hypersimplify.
      pose (y := π₂ (tm_var (((((𝟙 ×h X) ×h X) ×h Z) ×h Z) ×h Y))).
      fold y.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      use hyp_sym.
      refine (exists_elim _ _) ; [ use weaken_left ; apply hyperdoctrine_hyp | ].
      rewrite conj_subst.
      use hyp_ltrans.
      use weaken_right.
      hypersimplify.
      use exists_intro.
      + exact (π₂ (tm_var _)).
      + hypersimplify.
        use conj_intro.
        * use hyp_rtrans.
          use weaken_left.
          use hyp_sym.
          use hyp_rtrans.
          use weaken_left.
          unfold x₁, x₂, y.
          hypersimplify.
          use (partial_setoid_mor_eq_defined
                 φ₁
                 _
                 _
                 (weaken_left (hyperdoctrine_hyp _) _)).
          ** use weaken_right.
             use hyperdoctrine_hyp.
          ** use weaken_left.
             exact (partial_setoid_mor_cod_defined φ₁ _ _ (hyperdoctrine_hyp _)).
        * use hyp_ltrans.
          use weaken_right.
          use hyp_sym.
          use hyp_ltrans.
          use weaken_right.
          unfold z₁, z₂, y.
          hypersimplify.
          use (partial_setoid_mor_eq_defined
                 φ₂
                 _
                 _
                 (weaken_left (hyperdoctrine_hyp _) _)).
          ** use weaken_left.
             exact (partial_setoid_mor_dom_defined φ₂ _ _ (hyperdoctrine_hyp _)).
          ** use weaken_right.
             use hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law.
      pose (T := X).
      pose (T' := Z).
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
      pose (z₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
      pose (z₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x z₁ z₂.
      unfold partial_setoid_comp_morphism_form.
      hypersimplify.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      hypersimplify.
      use impl_intro.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      rewrite conj_subst.
      use hyp_ltrans.
      use weaken_right.
      hypersimplify.
      unfold x, z₁, z₂.
      clear x z₁ z₂.
      hypersimplify.
      pose (x := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h Z) ×h Z) ×h Y) ×h Y))))))).
      pose (y := π₂ (π₁ (tm_var (((((𝟙 ×h X) ×h Z) ×h Z) ×h Y) ×h Y)))).
      pose (y' := π₂ (tm_var (((((𝟙 ×h X) ×h Z) ×h Z) ×h Y) ×h Y))).
      pose (z₁ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h Z) ×h Z) ×h Y) ×h Y)))))).
      pose (z₂ := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h Z) ×h Z) ×h Y) ×h Y))))).
      fold x y y' z₁ z₂.
      use (partial_setoid_mor_unique_im φ₂).
      + exact y.
      + use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
      + use (partial_setoid_mor_eq_defined φ₂).
        * exact y'.
        * exact z₂.
        * use hyp_rtrans.
          use weaken_left.
          use hyp_sym.
          use hyp_rtrans.
          use weaken_left.
          use (partial_setoid_mor_unique_im φ₁).
          ** exact x.
          ** use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
        * use (partial_setoid_mor_cod_defined φ₂).
          ** exact y'.
          ** do 2 use weaken_right.
             apply hyperdoctrine_hyp.
        * do 2 use weaken_right.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      pose (x := π₂ (tm_var (𝟙 ×h X))).
      pose (z := π₂ (tm_var ((𝟙 ×h X) ×h Z))).
      fold x z.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use (exists_elim (partial_setoid_mor_hom_exists φ₁ (hyperdoctrine_hyp _))).
      use weaken_right.
      pose (y := π₂ (tm_var ((𝟙 ×h X) ×h Y))).
      fold y.
      use weaken_cut.
      + exact (y ~ y).
      + exact (partial_setoid_mor_cod_defined φ₁ _ _ (hyperdoctrine_hyp _)).
      + use (exists_elim
               (partial_setoid_mor_hom_exists φ₂ (weaken_right (hyperdoctrine_hyp _) _))).
        hypersimplify_form.
        use hyp_sym.
        use hyp_rtrans.
        use weaken_left.
        use hyp_sym.
        use exists_intro.
        * exact (π₂ (tm_var _)).
        * unfold partial_setoid_comp_morphism_form.
          hypersimplify.
          use exists_intro.
          ** exact (π₂ (π₁ (tm_var _))).
          ** unfold x, y, z.
             hypersimplify.
             apply hyperdoctrine_hyp.
  Qed.

  Definition partial_setoid_comp_morphism
    : partial_setoid_morphism X Z.
  Proof.
    use make_partial_setoid_morphism.
    - exact partial_setoid_comp_morphism_form.
    - exact partial_setoid_comp_morphism_laws.
  Defined.
End CompPartialSetoidMorphism.

Arguments partial_setoid_comp_morphism_form {H X Y Z} φ₁ φ₂ /.

(** * 3. The category of partial setoids *)
Section CategoryOfPartialSetoids.
  Context (H : first_order_hyperdoctrine).

  Definition precategory_ob_mor_of_partial_setoids
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (partial_setoid H).
    - exact (λ (X Y : partial_setoid H), partial_setoid_morphism X Y).
  Defined.

  Definition precategory_data_of_partial_setoids
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact precategory_ob_mor_of_partial_setoids.
    - exact id_partial_setoid_morphism.
    - exact (λ _ _ _ f g, partial_setoid_comp_morphism f g).
  Defined.

  Proposition precategory_of_partial_setoids_laws
    : is_precategory precategory_data_of_partial_setoids.
  Proof.
    use make_is_precategory_one_assoc.
    - intros X Y φ.
      use eq_partial_setoid_morphism ; cbn in *.
      + use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        hypersimplify.
        pose (x := π₁ (π₁ (tm_var ((X ×h Y) ×h X)))).
        pose (x' := π₂ (tm_var ((X ×h Y) ×h X))).
        pose (y := π₂ (π₁ (tm_var ((X ×h Y) ×h X)))).
        fold x x' y.
        rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((X ×h Y) ×h X)))).
        fold x y.
        use (partial_setoid_mor_eq_defined φ).
        * exact x'.
        * exact y.
        * use weaken_left.
          use partial_setoid_sym.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          exact (partial_setoid_mor_cod_defined φ _ _ (hyperdoctrine_hyp _)).
        * use weaken_right.
          apply hyperdoctrine_hyp.
      + hypersimplify.
        pose (x := π₁ (π₁ (tm_var ((X ×h Y) ×h X)))).
        pose (x' := π₂ (tm_var ((X ×h Y) ×h X))).
        pose (y := π₂ (π₁ (tm_var ((X ×h Y) ×h X)))).
        fold x x' y.
        use exists_intro.
        * exact (π₁ (tm_var (X ×h Y))).
        * hypersimplify_form.
          rewrite partial_setoid_subst.
          unfold x, x', y ; clear x x' y.
          hypersimplify.
          use conj_intro.
          ** use (partial_setoid_mor_dom_defined φ _ (π₂ (tm_var _))).
             rewrite <- hyperdoctrine_pair_eta.
             rewrite hyperdoctrine_id_subst.
             apply hyperdoctrine_hyp.
          ** rewrite <- hyperdoctrine_pair_eta.
             rewrite hyperdoctrine_id_subst.
             apply hyperdoctrine_hyp.
    - intros X Y φ.
      use eq_partial_setoid_morphism ; cbn in *.
      + use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        hypersimplify.
        pose (x := π₁ (π₁ (tm_var ((X ×h Y) ×h Y)))).
        pose (y := π₂ (π₁ (tm_var ((X ×h Y) ×h Y)))).
        pose (y' := π₂ (tm_var ((X ×h Y) ×h Y))).
        fold x y y'.
        rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((X ×h Y) ×h Y)))).
        fold x y.
        use (partial_setoid_mor_eq_defined φ).
        * exact x.
        * exact y'.
        * use weaken_left.
          exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
      + hypersimplify.
        pose (x := π₁ (π₁ (tm_var ((X ×h Y) ×h Y)))).
        pose (y := π₂ (π₁ (tm_var ((X ×h Y) ×h Y)))).
        pose (y' := π₂ (tm_var ((X ×h Y) ×h Y))).
        fold x y y'.
        use exists_intro.
        * exact (π₂ (tm_var (X ×h Y))).
        * hypersimplify_form.
          rewrite partial_setoid_subst.
          unfold x, y, y' ; clear x y y'.
          hypersimplify.
          use conj_intro.
          ** rewrite <- hyperdoctrine_pair_eta.
             rewrite hyperdoctrine_id_subst.
             apply hyperdoctrine_hyp.
          ** use (partial_setoid_mor_cod_defined φ (π₁ (tm_var _))).
             rewrite <- hyperdoctrine_pair_eta.
             rewrite hyperdoctrine_id_subst.
             apply hyperdoctrine_hyp.
    - intros W X Y Z φ₁ φ₂ φ₃.
      use eq_partial_setoid_morphism ; cbn in *.
      + use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        hypersimplify_form.
        use hyp_sym.
        use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
        hypersimplify_form.
        use hyp_ltrans.
        use weaken_right.
        hypersimplify.
        pose (w := π₁ (π₁ (π₁ (tm_var (((W ×h Z) ×h X) ×h Y))))).
        pose (x := π₂ (π₁ (tm_var (((W ×h Z) ×h X) ×h Y)))).
        pose (y := π₂ (tm_var (((W ×h Z) ×h X) ×h Y))).
        pose (z := π₂ (π₁ (π₁ (tm_var (((W ×h Z) ×h X) ×h Y))))).
        fold w x y z.
        use exists_intro.
        * exact y.
        * hypersimplify.
          fold z.
          use conj_intro.
          ** use exists_intro.
             *** exact x.
             *** hypersimplify.
                 fold w.
                 use conj_intro.
                 **** use weaken_left.
                      apply hyperdoctrine_hyp.
                 **** use weaken_right.
                      use weaken_left.
                      apply hyperdoctrine_hyp.
          ** do 2 use weaken_right.
             apply hyperdoctrine_hyp.
      + use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        hypersimplify_form.
        use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
        hypersimplify_form.
        use hyp_ltrans.
        use weaken_right.
        hypersimplify.
        pose (w := π₁ (π₁ (π₁ (tm_var (((W ×h Z) ×h Y) ×h X))))).
        pose (x := π₂ (tm_var (((W ×h Z) ×h Y) ×h X))).
        pose (y := π₂ (π₁ (tm_var (((W ×h Z) ×h Y) ×h X)))).
        pose (z := π₂ (π₁ (π₁ (tm_var (((W ×h Z) ×h Y) ×h X))))).
        fold w x y z.
        use exists_intro.
        * exact x.
        * hypersimplify.
          fold w.
          use conj_intro.
          ** use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
          ** use exists_intro.
             *** exact y.
             *** hypersimplify.
                 fold z.
                 use conj_intro.
                 **** do 2  use weaken_right.
                      apply hyperdoctrine_hyp.
                 **** use weaken_left.
                      apply hyperdoctrine_hyp.
  Qed.

  Definition precategory_of_partial_setoids
    : precategory.
  Proof.
    use make_precategory.
    - exact precategory_data_of_partial_setoids.
    - exact precategory_of_partial_setoids_laws.
  Defined.

  Definition category_of_partial_setoids
    : category.
  Proof.
    use make_category.
    - exact precategory_of_partial_setoids.
    - abstract
        (intros X Y ;
         exact isaset_partial_setoid_morphism).
  Defined.

  (** * 4. Isomorphisms of partial setoids *)
  Definition per_morphism_surjective_law
             {X Y : partial_setoid H}
             (φ : partial_setoid_morphism X Y)
    : UU
    := let Γ := (𝟙 ×h Y) ×h X in
       let x := π₂ (tm_var Γ) in
       let y := π₂ (π₁ (tm_var Γ)) in
       ⊤ ⊢ (∀h (π₂ (tm_var _) ~ π₂ (tm_var _) ⇒ ∃h (φ [ ⟨ x , y ⟩ ]))).

  Proposition per_morphism_surjective
              {X Y : partial_setoid H}
              {φ : partial_setoid_morphism X Y}
              (Hφ : per_morphism_surjective_law φ)
              {Γ : ty H}
              {Δ : form Γ}
              (y : tm Γ Y)
              (p : Δ ⊢ y ~ y)
    : Δ ⊢ (∃h (φ [ ⟨ π₂ (tm_var _) , y [ π₁ (tm_var _) ]tm ⟩ ])).
  Proof.
    refine (hyperdoctrine_cut _ _).
    {
      refine (conj_intro _ p).
      refine (hyperdoctrine_cut _ (hyperdoctrine_proof_subst !! Hφ)).
      hypersimplify.
      apply truth_intro.
    }
    hypersimplify.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      refine (forall_elim (hyperdoctrine_hyp _) _).
      exact y.
    }
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    refine (impl_elim _ _).
    - use weaken_left.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Definition per_morphism_injective_law
             {X Y : partial_setoid H}
             (φ : partial_setoid_morphism X Y)
    : UU
    := let Γ := ((𝟙 ×h X) ×h X) ×h Y in
       let y := π₂ (tm_var Γ) in
       let x₂ := π₂ (π₁ (tm_var Γ)) in
       let x₁ := π₂ (π₁ (π₁ (tm_var Γ))) in
       ⊤ ⊢ (∀h ∀h ∀h (φ [ ⟨ x₁ , y ⟩ ] ⇒ φ [ ⟨ x₂ , y ⟩ ] ⇒ x₁ ~ x₂)).

  Proposition per_morphism_injective
              {X Y : partial_setoid H}
              {φ : partial_setoid_morphism X Y}
              (Hφ : per_morphism_injective_law φ)
              {Γ : ty H}
              {Δ : form Γ}
              {x₁ x₂ : tm Γ X}
              {y : tm Γ Y}
              (p : Δ ⊢ φ [ ⟨ x₁ , y ⟩ ])
              (q : Δ ⊢ φ [ ⟨ x₂ , y ⟩ ])
    : Δ ⊢ x₁ ~ x₂.
  Proof.
    refine (hyperdoctrine_cut _ _).
    {
      refine (conj_intro _ q).
      refine (conj_intro _ p).
      refine (hyperdoctrine_cut _ (hyperdoctrine_proof_subst !! Hφ)).
      hypersimplify.
      apply truth_intro.
    }
    hypersimplify.
    use hyp_ltrans.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      refine (forall_elim (hyperdoctrine_hyp _) _).
      exact x₁.
    }
    use hyp_ltrans.
    use weaken_right.
    use hyp_sym.
    hypersimplify.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      refine (forall_elim (hyperdoctrine_hyp _) _).
      exact x₂.
    }
    use hyp_ltrans.
    use weaken_right.
    use hyp_sym.
    hypersimplify.
    refine (weaken_cut _ _).
    {
      use weaken_left.
      refine (forall_elim (hyperdoctrine_hyp _) _).
      exact y.
    }
    use hyp_ltrans.
    use weaken_right.
    hypersimplify.
    refine (impl_elim _ _).
    - use weaken_left.
      use weaken_right.
      apply hyperdoctrine_hyp.
    - refine (impl_elim _ _).
      + do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Section Isomorphism.
    Context {X Y : partial_setoid H}
            (φ : partial_setoid_morphism X Y)
            (H₁ : per_morphism_surjective_law φ)
            (H₂ : per_morphism_injective_law φ).

    Let ψ : form (Y ×h X) := φ [ ⟨ π₂ (tm_var _) , π₁ (tm_var _) ⟩ ].

    Proposition partial_setoid_morphism_inverse_laws
      : partial_setoid_morphism_laws ψ.
    Proof.
      unfold ψ.
      repeat split.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        use (partial_setoid_mor_cod_defined φ).
        {
          exact (π₂ (tm_var _)).
        }
        hypersimplify.
        apply hyperdoctrine_hyp.
      - do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        use (partial_setoid_mor_dom_defined φ).
        {
          exact (π₂ (π₁ (tm_var _))).
        }
        hypersimplify.
        apply hyperdoctrine_hyp.
      - do 4 use forall_intro.
        use impl_intro.
        use weaken_right.
        do 2 use impl_intro.
        hypersimplify.
        pose (Γ := (((𝟙 ×h Y) ×h Y) ×h X) ×h X).
        fold Γ.
        pose (y₁ := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
        pose (y₂ := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (x₁ := π₂ (π₁ (tm_var Γ))).
        pose (x₂ := π₂ (tm_var Γ)).
        fold x₁ x₂ y₁ y₂.
         use (partial_setoid_mor_eq_defined φ).
        + exact x₁.
        + exact y₁.
        + use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        + do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
      - do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        hypersimplify.
        use impl_intro.
        pose (Γ := ((𝟙 ×h Y) ×h X) ×h X).
        fold Γ.
        pose (x₂ := π₂ (tm_var Γ)).
        pose (x₁ := π₂ (π₁ (tm_var Γ))).
        pose (y := π₂ (π₁ (π₁ (tm_var Γ)))).
        fold x₁ x₂ y.
        use (per_morphism_injective H₂).
        + exact y.
        + use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_right.
          apply hyperdoctrine_hyp.
      - use forall_intro.
        use impl_intro.
        use weaken_right.
        refine (exists_elim _ _).
        {
          refine (per_morphism_surjective H₁ _ _).
          apply hyperdoctrine_hyp.
        }
        hypersimplify.
        pose (Γ := (𝟙 ×h Y) ×h X).
        pose (x := π₂ (tm_var Γ)).
        pose (y := π₂ (π₁ (tm_var Γ))).
        use exists_intro.
        {
          exact x.
        }
        hypersimplify.
        fold Γ x y.
        use weaken_right.
        apply hyperdoctrine_hyp.
    Qed.

    Definition partial_setoid_morphism_inverse
      : partial_setoid_morphism Y X.
    Proof.
      use make_partial_setoid_morphism.
      - exact ψ.
      - exact partial_setoid_morphism_inverse_laws.
    Defined.

    Proposition make_partial_setoid_z_iso_laws
      : is_inverse_in_precat
          (C := category_of_partial_setoids)
          φ
          partial_setoid_morphism_inverse.
    Proof.
      split.
      - use eq_partial_setoid_morphism.
        + cbn.
          refine (exists_elim (hyperdoctrine_hyp _) _).
          use weaken_right.
          unfold ψ.
          hypersimplify.
          pose (Γ := (X ×h X) ×h Y).
          fold Γ.
          pose (x₁ := π₁ (π₁ (tm_var Γ))).
          pose (x₂ := π₂ (π₁ (tm_var Γ))).
          pose (y := π₂ (tm_var Γ)).
          fold x₁ x₂ y.
          use (per_morphism_injective H₂).
          * exact y.
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
        + cbn.
          unfold ψ.
          refine (exists_elim (partial_setoid_mor_hom_exists φ _) _).
          {
            refine (partial_setoid_refl_r _).
            apply hyperdoctrine_hyp.
          }
          hypersimplify.
          pose (Γ := (X ×h X) ×h Y).
          fold Γ.
          pose (x₁ := π₁ (π₁ (tm_var Γ))).
          pose (x₂ := π₂ (π₁ (tm_var Γ))).
          pose (y := π₂ (tm_var Γ)).
          fold x₁ x₂ y.
          use exists_intro.
          {
            exact y.
          }
          hypersimplify.
          fold x₁ x₂.
          use conj_intro.
          * use (partial_setoid_mor_eq_defined φ).
            ** exact x₂.
            ** exact y.
            ** use weaken_left.
               use partial_setoid_sym.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               refine (partial_setoid_mor_cod_defined φ _ _ _).
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
      - use eq_partial_setoid_morphism.
        + cbn.
          refine (exists_elim (hyperdoctrine_hyp _) _).
          use weaken_right.
          unfold ψ.
          hypersimplify.
          pose (Γ := (Y ×h Y) ×h X).
          fold Γ.
          pose (y₁ := π₁ (π₁ (tm_var Γ))).
          pose (y₂ := π₂ (π₁ (tm_var Γ))).
          pose (x := π₂ (tm_var Γ)).
          fold x y₁ y₂.
          use (partial_setoid_mor_unique_im φ).
          * exact x.
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
        + cbn.
          unfold ψ.
          refine (exists_elim (per_morphism_surjective H₁ _ _) _).
          {
            refine (partial_setoid_refl_r _).
            apply hyperdoctrine_hyp.
          }
          hypersimplify.
          pose (Γ := (Y ×h Y) ×h X).
          fold Γ.
          pose (y₁ := π₁ (π₁ (tm_var Γ))).
          pose (y₂ := π₂ (π₁ (tm_var Γ))).
          pose (x := π₂ (tm_var Γ)).
          fold x y₁ y₂.
          use exists_intro.
          {
            exact x.
          }
          hypersimplify.
          fold y₁ y₂.
          use conj_intro.
          * use (partial_setoid_mor_eq_defined φ).
            ** exact x.
            ** exact y₂.
            ** use weaken_right.
               refine (partial_setoid_mor_dom_defined φ _ _ _).
               apply hyperdoctrine_hyp.
            ** use weaken_left.
               use partial_setoid_sym.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
    Qed.

    Definition make_partial_setoid_z_iso
      : z_iso (C := category_of_partial_setoids) X Y.
    Proof.
      use make_z_iso.
      - exact φ.
      - exact partial_setoid_morphism_inverse.
      - exact make_partial_setoid_z_iso_laws.
    Defined.
  End Isomorphism.
End CategoryOfPartialSetoids.
