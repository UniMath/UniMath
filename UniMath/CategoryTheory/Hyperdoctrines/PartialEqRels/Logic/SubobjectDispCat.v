(******************************************************************************************

 Subobjects in the category of partial setoids

 In this file, we characterize the internal logic of  the category of partial setoids in a
 first-order hyperdoctrine. To do so, we first give an alternative description of subobjects.
 Subobjects of a partial setoid `X` can equivalently be described as a formula `φ` in context
 [X] such that
 - if `φ [ x ]` holds, then also `x ~ x`
 - if both `x ~ y` and `φ [ x ]` hold, then so does `φ [ y ]`
 The first requirement expresses that everything that satisfies `φ`, also is a defined
 element, and the second requirement expresses that `φ` is well-defined with respect to the
 partial equivalence relation of `X`. This statement comes from Lemma 3.3 in "Tripos Theory
 in Retrospect" by Andrew Pitts.

 We also construct the displayed category of subobjects of partial setoids, and we show
 that this displayed category is univalent. In addition, we construct a cleaving on this
 displayed category, which gives us the substitution operation.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts

 Content
 1. Subobjects of partial setoids
 2. Accessors for subobjects of partial setoids
 3. Morphisms between subobjects of partial setoids
 4. The displayed category of subobjects
 5. This displayed category is univalent
 6. The cleaving

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERMorphisms.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERCategory.

Local Open Scope cat.
Local Open Scope hd.

Section PartialEqRelDispCat.
  Context {H : first_order_hyperdoctrine}.

  (** * 1. Subobjects of partial setoids *)
  Definition per_subobject_def_law
             {X : partial_setoid H}
             (φ : form X)
    : UU
    := let x := π₂ (tm_var (𝟙 ×h X)) in
       (⊤ ⊢ ∀h (φ [ x ] ⇒ x ~ x)).

  Definition per_subobject_eq_law
             {X : partial_setoid H}
             (φ : form X)
    : UU
    := let x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h X))) in
       let y := π₂ (tm_var ((𝟙 ×h X) ×h X)) in
       (⊤ ⊢ ∀h ∀h (x ~ y ⇒ φ [ x ] ⇒ φ [ y ])).

  Definition per_subobject_laws
             {X : partial_setoid H}
             (φ : form X)
    : UU
    := per_subobject_def_law φ
       ×
       per_subobject_eq_law φ.

  Proposition isaprop_per_subobject_laws
              {X : partial_setoid H}
              (φ : form X)
    : isaprop (per_subobject_laws φ).
  Proof.
    use isapropdirprod ;
      use invproofirrelevance ;
      intros p q ;
      apply hyperdoctrine_proof_eq.
  Qed.

  Definition per_subobject
             (X : partial_setoid H)
    : UU
    := ∑ (φ : form X), per_subobject_laws φ.

  Definition make_per_subobject
             {X : partial_setoid H}
             (φ : form X)
             (Hφ : per_subobject_laws φ)
    : per_subobject X
    := φ ,, Hφ.

  Proposition isaset_per_subobject
              (X : partial_setoid H)
    : isaset (per_subobject X).
  Proof.
    use isaset_total2.
    - apply isaset_hyperdoctrine_formula.
    - intro ψ.
      apply isasetaprop.
      apply isaprop_per_subobject_laws.
  Qed.

  (** * 2. Accessors for subobjects of partial setoids *)
  Coercion per_subobject_to_form
           {X : partial_setoid H}
           (φ : per_subobject X)
    : form X
    := pr1 φ.

  Proposition path_per_subobject
              (X : partial_setoid H)
              {φ ψ : per_subobject X}
              (p : (φ : form X) = ψ)
    : φ = ψ.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_per_subobject_laws.
    }
    exact p.
  Qed.

  Proposition per_subobject_def
              {X : partial_setoid H}
              (φ : per_subobject X)
              {Γ : ty H}
              {Δ : form Γ}
              (x : tm Γ X)
              (p : Δ ⊢ φ [ x ])
    : Δ ⊢ x ~ x.
  Proof.
    use (impl_elim p).
    pose proof (hyperdoctrine_proof_subst (!! : tm Γ 𝟙) (pr12 φ)) as q.
    cbn in q.
    rewrite forall_subst in q.
    pose proof (q' := forall_elim q x) ; clear q.
    rewrite hyperdoctrine_comp_subst in q'.
    rewrite impl_subst in q'.
    rewrite partial_setoid_subst in q'.
    rewrite hyperdoctrine_pr2_subst in q'.
    rewrite var_tm_subst in q'.
    rewrite hyperdoctrine_pair_subst in q'.
    rewrite hyperdoctrine_pair_pr2 in q'.
    rewrite hyperdoctrine_pr2_subst in q'.
    rewrite var_tm_subst in q'.
    rewrite hyperdoctrine_pair_pr2 in q'.
    rewrite hyperdoctrine_comp_subst in q'.
    rewrite hyperdoctrine_pr2_subst in q'.
    rewrite var_tm_subst in q'.
    rewrite hyperdoctrine_pair_pr2 in q'.
    rewrite truth_subst in q'.
    refine (hyperdoctrine_cut _ q').
    apply truth_intro.
  Qed.

  Proposition per_subobject_eq
              {X : partial_setoid H}
              (φ : per_subobject X)
              {Γ : ty H}
              {Δ : form Γ}
              {x y : tm Γ X}
              (p₁ : Δ ⊢ x ~ y)
              (p₂ : Δ ⊢ φ [ x ])
    : Δ ⊢ φ [ y ].
  Proof.
    use (impl_elim p₂).
    use (impl_elim p₁).
    pose proof (hyperdoctrine_proof_subst (!! : tm Γ 𝟙) (pr22 φ)) as q.
    cbn in q.
    rewrite truth_subst in q.
    rewrite !forall_subst in q.
    rewrite !impl_subst in q.
    rewrite !partial_setoid_subst in q.
    rewrite !hyperdoctrine_comp_subst in q.
    rewrite !hyperdoctrine_pr2_subst in q.
    rewrite !hyperdoctrine_pr1_subst in q.
    rewrite !var_tm_subst in q.
    rewrite hyperdoctrine_pair_pr1 in q.
    rewrite hyperdoctrine_pair_pr2 in q.
    rewrite hyperdoctrine_pair_subst in q.
    rewrite hyperdoctrine_pair_pr2 in q.
    rewrite hyperdoctrine_pr2_subst in q.
    rewrite !var_tm_subst in q.
    pose proof (q' := forall_elim q x) ; clear q.
    rewrite forall_subst in q'.
    rewrite !impl_subst in q'.
    rewrite !partial_setoid_subst in q'.
    rewrite !hyperdoctrine_comp_subst in q'.
    rewrite !hyperdoctrine_pr2_subst in q'.
    rewrite !hyperdoctrine_pr1_subst in q'.
    rewrite !var_tm_subst in q'.
    rewrite hyperdoctrine_pair_pr1 in q'.
    rewrite hyperdoctrine_pair_pr2 in q'.
    rewrite hyperdoctrine_pair_subst in q'.
    rewrite hyperdoctrine_pair_pr2 in q'.
    pose proof (q'' := forall_elim q' y) ; clear q'.
    rewrite !impl_subst in q''.
    rewrite !partial_setoid_subst in q''.
    rewrite !hyperdoctrine_comp_subst in q''.
    rewrite !tm_subst_comp in q''.
    rewrite !hyperdoctrine_pr1_subst in q''.
    rewrite !hyperdoctrine_pr2_subst in q''.
    rewrite !var_tm_subst in q''.
    rewrite hyperdoctrine_pair_pr1 in q''.
    rewrite hyperdoctrine_pair_pr2 in q''.
    rewrite !tm_subst_var in q''.
    refine (hyperdoctrine_cut _ q'').
    apply truth_intro.
  Qed.

  (** * 3. Morphisms between subobjects of partial setoids *)
  Definition per_subobject_mor_law
             {X Y : partial_setoid H}
             (φ : partial_setoid_morphism X Y)
             (ψ₁ : per_subobject X)
             (ψ₂ : per_subobject Y)
    : UU
    := let x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h Y))) in
       let y := π₂ (tm_var ((𝟙 ×h X) ×h Y)) in
       (⊤ ⊢ ∀h ∀h (φ [ ⟨ x , y ⟩ ] ⇒ ψ₁ [ x ] ⇒ ψ₂ [ y ])).

  Arguments per_subobject_mor_law {X Y} φ ψ₁ ψ₂ /.

  Proposition per_subobject_mor_law_over_id
              {X : partial_setoid H}
              (ψ₁ ψ₂ : per_subobject X)
              (p : ψ₁ ⊢ ψ₂)
    : per_subobject_mor_law (id_partial_setoid_morphism _) ψ₁ ψ₂.
  Proof.
    unfold per_subobject_mor_law.
    do 2 use forall_intro.
    use impl_intro.
    cbn.
    use weaken_right.
    hypersimplify.
    use impl_intro.
    refine (hyperdoctrine_cut
              _
              (hyperdoctrine_proof_subst _ p)).
    refine (per_subobject_eq ψ₁ _ _).
    - use weaken_left.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Proposition isaprop_per_subobject_mor_law
              {X Y : partial_setoid H}
              (φ : partial_setoid_morphism X Y)
              (ψ₁ : per_subobject X)
              (ψ₂ : per_subobject Y)
    : isaprop (per_subobject_mor_law φ ψ₁ ψ₂).
  Proof.
    use invproofirrelevance.
    intros p q.
    apply hyperdoctrine_proof_eq.
  Qed.

  Proposition per_subobject_mor
              {X Y : partial_setoid H}
              {φ : partial_setoid_morphism X Y}
              {ψ₁ : per_subobject X}
              {ψ₂ : per_subobject Y}
              (p : per_subobject_mor_law φ ψ₁ ψ₂)
              {Γ : ty H}
              {Δ : form Γ}
              {x : tm Γ X}
              {y : tm Γ Y}
              (q₁ : Δ ⊢ φ [ ⟨ x , y ⟩ ])
              (q₂ : Δ ⊢ ψ₁ [ x ])
    : Δ ⊢ ψ₂ [ y ].
  Proof.
    use (impl_elim q₂).
    use (impl_elim q₁).
    pose proof (hyperdoctrine_proof_subst (!! : tm Γ 𝟙) p) as r.
    cbn in r.
    rewrite truth_subst in r.
    rewrite !forall_subst in r.
    rewrite !impl_subst in r.
    rewrite !hyperdoctrine_comp_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite hyperdoctrine_pair_pr1 in r.
    rewrite hyperdoctrine_pair_pr2 in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite hyperdoctrine_pair_pr2 in r.
    rewrite hyperdoctrine_pr2_subst in r.
    rewrite hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite hyperdoctrine_pair_pr1 in r.
    rewrite hyperdoctrine_pair_pr2 in r.
    rewrite hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite hyperdoctrine_pair_pr2 in r.
    pose proof (r' := forall_elim r x) ; clear r.
    rewrite forall_subst in r'.
    rewrite !impl_subst in r'.
    rewrite !hyperdoctrine_comp_subst in r'.
    rewrite !hyperdoctrine_pr2_subst in r'.
    rewrite !hyperdoctrine_pr1_subst in r'.
    rewrite !var_tm_subst in r'.
    rewrite hyperdoctrine_pair_pr1 in r'.
    rewrite hyperdoctrine_pair_pr2 in r'.
    rewrite !hyperdoctrine_pair_subst in r'.
    rewrite hyperdoctrine_pair_pr2 in r'.
    rewrite hyperdoctrine_pr2_subst in r'.
    rewrite hyperdoctrine_pr1_subst in r'.
    rewrite !var_tm_subst in r'.
    rewrite hyperdoctrine_pair_pr1 in r'.
    rewrite hyperdoctrine_pair_pr2 in r'.
    rewrite hyperdoctrine_pr2_subst in r'.
    rewrite !var_tm_subst in r'.
    rewrite hyperdoctrine_pair_pr2 in r'.
    pose proof (r'' := forall_elim r' y) ; clear r'.
    rewrite !impl_subst in r''.
    rewrite !hyperdoctrine_comp_subst in r''.
    rewrite !hyperdoctrine_pr2_subst in r''.
    rewrite !var_tm_subst in r''.
    rewrite hyperdoctrine_pair_pr2 in r''.
    rewrite !hyperdoctrine_pair_subst in r''.
    rewrite hyperdoctrine_pr2_subst in r''.
    rewrite !var_tm_subst in r''.
    rewrite hyperdoctrine_pair_pr2 in r''.
    rewrite !tm_subst_comp in r''.
    rewrite !hyperdoctrine_pr1_subst in r''.
    rewrite !var_tm_subst in r''.
    rewrite hyperdoctrine_pair_pr1 in r''.
    rewrite !tm_subst_var in r''.
    refine (hyperdoctrine_cut _ r'').
    apply truth_intro.
  Qed.

  Proposition per_subobject_mor_over_id
              {X : partial_setoid H}
              {ψ₁ ψ₂ : per_subobject X}
              (p : per_subobject_mor_law (id_partial_setoid_morphism _) ψ₁ ψ₂)
              {Γ : ty H}
              {Δ : form Γ}
              {x : tm Γ X}
              (q : Δ ⊢ ψ₁ [ x ])
    : Δ ⊢ ψ₂ [ x ].
  Proof.
    use (per_subobject_mor p).
    - exact x.
    - cbn.
      hypersimplify.
      refine (per_subobject_def _ _ _).
      exact q.
    - exact q.
  Qed.

  (** * 4. The displayed category of subobjects *)
  Definition disp_cat_ob_mor_per_subobject
    : disp_cat_ob_mor (category_of_partial_setoids H).
  Proof.
    simple refine (_ ,, _).
    - exact (λ (X : partial_setoid H), per_subobject X).
    - exact (λ (X Y : partial_setoid H)
               (ψ₁ : per_subobject X)
               (ψ₂ : per_subobject Y)
               (φ : partial_setoid_morphism X Y),
             per_subobject_mor_law φ ψ₁ ψ₂).
  Defined.

  Proposition disp_cat_id_comp_per_subobject
    : disp_cat_id_comp
        (category_of_partial_setoids H)
        disp_cat_ob_mor_per_subobject.
  Proof.
    split.
    - cbn.
      intros X ψ.
      use per_subobject_mor_law_over_id.
      apply hyperdoctrine_hyp.
    - intros X Y Z φ₁ φ₂ ψ₁ ψ₂ ψ₃ p q.
      cbn -[per_subobject_mor_law] in * ; cbn.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      rewrite exists_subst.
      use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      rewrite impl_subst.
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X) ×h Z) ×h Y))))).
      pose (z := π₂ (π₁ (tm_var (((𝟙 ×h X) ×h Z) ×h Y)))).
      pose (y := π₂ (tm_var (((𝟙 ×h X) ×h Z) ×h Y))).
      hypersimplify.
      fold x y z.
      use impl_intro.
      use (per_subobject_mor q).
      + exact y.
      + use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
      + use (per_subobject_mor p).
        * exact x.
        * do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
  Qed.

  Definition disp_cat_data_per_subobject
    : disp_cat_data (category_of_partial_setoids H).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_ob_mor_per_subobject.
    - exact disp_cat_id_comp_per_subobject.
  Defined.

  Proposition disp_cat_axioms_per_subobject
    : disp_cat_axioms
        (category_of_partial_setoids H)
        disp_cat_data_per_subobject.
  Proof.
    repeat split.
    - intros.
      apply isaprop_per_subobject_mor_law.
    - intros.
      apply isaprop_per_subobject_mor_law.
    - intros.
      apply isaprop_per_subobject_mor_law.
    - intros.
      apply isasetaprop.
      apply isaprop_per_subobject_mor_law.
  Qed.

  Definition disp_cat_per_subobject
    : disp_cat (category_of_partial_setoids H).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_data_per_subobject.
    - exact disp_cat_axioms_per_subobject.
  Defined.

  Proposition locally_prop_disp_cat_per_subobject
    : locally_propositional disp_cat_per_subobject.
  Proof.
    intros X Y φ ψ₁ ψ₂.
    apply isaprop_per_subobject_mor_law.
  Qed.

  (** * 5. This displayed category is univalent *)
  Proposition is_univalent_disp_cat_per_subobject
    : is_univalent_disp disp_cat_per_subobject.
  Proof.
    use is_univalent_disp_from_fibers.
    intros X ψ₁ ψ₂ ; cbn in X, ψ₁, ψ₂.
    use isweqimplimpl.
    - intros pq.
      pose (p := pr1 pq).
      pose (q := pr12 pq).
      cbn -[per_subobject_mor_law] in p, q.
      use path_per_subobject.
      use hyperdoctrine_formula_eq.
      + pose (x := tm_var X).
        rewrite <- (hyperdoctrine_id_subst ψ₁).
        rewrite <- (hyperdoctrine_id_subst ψ₂).
        use (per_subobject_mor p).
        * apply tm_var.
        * fold x.
          cbn.
          hypersimplify.
          use (per_subobject_def ψ₁).
          apply hyperdoctrine_hyp.
        * apply hyperdoctrine_hyp.
      + pose (x := tm_var X).
        rewrite <- (hyperdoctrine_id_subst ψ₁).
        rewrite <- (hyperdoctrine_id_subst ψ₂).
        use (per_subobject_mor q).
        * apply tm_var.
        * fold x.
          cbn.
          hypersimplify.
          use (per_subobject_def ψ₂).
          apply hyperdoctrine_hyp.
        * apply hyperdoctrine_hyp.
    - apply isaset_per_subobject.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply isaprop_per_subobject_mor_law.
  Qed.

  (** * 6. The cleaving *)
  Section Substitution.
    Context {X Y : partial_setoid H}
            (φ : partial_setoid_morphism Y X)
            (ψ : per_subobject X).

    Let ζ : form Y
      := let y := π₁ (tm_var (Y ×h X)) in
         let x := π₂ (tm_var (Y ×h X)) in
         (∃h (φ [ ⟨ y , x ⟩ ] ∧ ψ [ x ])).

    Proposition per_subobject_subst_laws
      : per_subobject_laws ζ.
    Proof.
      split.
      - unfold ζ.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        rewrite exists_subst.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        hypersimplify.
        pose (x := π₂ (tm_var ((𝟙 ×h Y) ×h X))).
        pose (y := π₂ (π₁ (tm_var ((𝟙 ×h Y) ×h X)))).
        fold x y.
        use weaken_left.
        use (partial_setoid_mor_dom_defined φ).
        + exact x.
        + apply hyperdoctrine_hyp.
      - unfold ζ.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        use hyp_sym.
        rewrite !exists_subst.
        use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
        rewrite !conj_subst.
        use hyp_ltrans.
        use weaken_right.
        hypersimplify.
        pose (y₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Y) ×h Y) ×h X))))).
        pose (y₂ := π₂ (π₁ (tm_var (((𝟙 ×h Y) ×h Y) ×h X)))).
        pose (x := π₂ (tm_var (((𝟙 ×h Y) ×h Y) ×h X))).
        fold y₁ y₂ x.
        use exists_intro.
        + exact x.
        + hypersimplify.
          fold y₂.
          use conj_intro.
          * use (partial_setoid_mor_eq_defined φ).
            ** exact y₁.
            ** exact x.
            ** use weaken_left.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               use weaken_left.
               use (partial_setoid_mor_cod_defined φ).
               *** exact y₁.
               *** apply hyperdoctrine_hyp.
            ** use weaken_right.
               use weaken_left.
               apply hyperdoctrine_hyp.
          * do 2 use weaken_right.
            apply hyperdoctrine_hyp.
    Qed.

    Definition per_subobject_subst
      : per_subobject Y.
    Proof.
      use make_per_subobject.
      - exact ζ.
      - exact per_subobject_subst_laws.
    Defined.

    Arguments per_subobject_subst /.

    Proposition per_subobject_subst_mor
      : per_subobject_mor_law
          φ
          per_subobject_subst
          ψ.
    Proof.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      cbn.
      unfold ζ.
      use hyp_sym.
      rewrite !exists_subst.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      rewrite !conj_subst.
      use hyp_ltrans.
      use weaken_right.
      hypersimplify.
      pose (x₁ := π₂ (π₁ (tm_var (((𝟙 ×h Y) ×h X) ×h X)))).
      pose (x₂ := π₂ (tm_var (((𝟙 ×h Y) ×h X) ×h X))).
      pose (y := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Y) ×h X) ×h X))))).
      fold x₁ x₂ y.
      use (per_subobject_eq ψ).
      - exact x₂.
      - use (partial_setoid_mor_unique_im φ).
        + exact y.
        + use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_left.
          apply hyperdoctrine_hyp.
      - do 2 use weaken_right.
        apply hyperdoctrine_hyp.
    Qed.

    Proposition is_cartesian_per_subobject_subst_mor
      : is_cartesian
          (D := disp_cat_per_subobject)
          per_subobject_subst_mor.
    Proof.
      intros W φ' ψ' p ; cbn -[per_subobject_mor_law] in *.
      use iscontraprop1.
      - use isaproptotal2.
        {
          intro.
          apply homsets_disp.
        }
        intros.
        apply locally_prop_disp_cat_per_subobject.
      - simple refine (_ ,, _) ; [ | apply locally_prop_disp_cat_per_subobject ].
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        cbn ; unfold ζ.
        pose (w := π₂ (π₁ (tm_var ((𝟙 ×h W) ×h Y)))).
        pose (y := π₂ (tm_var ((𝟙 ×h W) ×h Y))).
        fold w y.
        simple refine (exists_elim (partial_setoid_mor_hom_exists φ _) _).
        + exact y.
        + use weaken_left.
          use (partial_setoid_mor_cod_defined φ').
          * exact w.
          * apply hyperdoctrine_hyp.
        + unfold w, y ; clear w y.
          hypersimplify.
          pose (w := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h W) ×h Y) ×h X))))).
          pose (y := π₂ (π₁ (tm_var (((𝟙 ×h W) ×h Y) ×h X)))).
          pose (x := π₂ (tm_var (((𝟙 ×h W) ×h Y) ×h X))).
          fold w x y.
          use exists_intro.
          {
            exact x.
          }
          hypersimplify.
          fold y.
          use conj_intro.
          * use weaken_right.
            apply hyperdoctrine_hyp.
          * use (per_subobject_mor p).
            ** exact w.
            ** cbn.
               simplify_form.
               use exists_intro.
               {
                 exact y.
               }
               hypersimplify.
               use conj_intro.
               *** do 2 use weaken_left.
                   apply hyperdoctrine_hyp.
               *** use weaken_right.
                   apply hyperdoctrine_hyp.
            ** use weaken_left.
               use weaken_right.
               apply hyperdoctrine_hyp.
    Qed.
  End Substitution.

  Arguments per_subobject_subst {X Y} φ ψ /.

  Definition disp_cat_per_subobject_cleaving
    : cleaving disp_cat_per_subobject.
  Proof.
    intros X Y φ ψ ; cbn in *.
    simple refine (_ ,, _ ,, _).
    - exact (per_subobject_subst φ ψ).
    - exact (per_subobject_subst_mor φ ψ).
    - exact (is_cartesian_per_subobject_subst_mor φ ψ).
  Defined.
End PartialEqRelDispCat.

Arguments disp_cat_per_subobject : clear implicits.
Arguments disp_cat_per_subobject_cleaving : clear implicits.
Arguments per_subobject_mor_law {H X Y} φ ψ₁ ψ₂ /.
Arguments per_subobject_subst {H X Y} φ ψ /.
