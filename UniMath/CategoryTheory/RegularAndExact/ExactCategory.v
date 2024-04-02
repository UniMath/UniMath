(********************************************************************************************

 Exact categories

 Contents
 1. Internal relations
 2. The relation on morphisms from an internal relation
 3. Properties of internal relations
 3.1. Internal reflexivity
 3.2. Internal symmetry
 3.3. Internal transitivity
 3.4. Internal equivalence relations
 4. Effective internal equivalence relations
 5. Exact categories

 ********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.

Local Open Scope cat.

(** * 1. Internal relations *)
Definition internal_relation
           {C : category}
           (x : C)
  : UU
  := ∑ (r : C)
       (s t : r --> x),
     ∏ (w : C)
       (f g : w --> r),
     f · s = g · s
     →
     f · t = g · t
     →
     f = g.

Definition make_internal_relation
           {C : category}
           (x : C)
           (r : C)
           (s t : r --> x)
           (p : ∏ (w : C)
                  (f g : w --> r),
                f · s = g · s
                →
                f · t = g · t
                →
                f = g)
  : internal_relation x
  := r ,, s ,, t ,, p.

Coercion internal_relation_ob
         {C : category}
         {x : C}
         (R : internal_relation x)
  : C
  := pr1 R.

Definition internal_relation_src
           {C : category}
           {x : C}
           (R : internal_relation x)
  : R --> x
  := pr12 R.

Definition internal_relation_tar
           {C : category}
           {x : C}
           (R : internal_relation x)
  : R --> x
  := pr122 R.

Proposition internal_relation_monic
            {C : category}
            {x : C}
            (R : internal_relation x)
            {w : C}
            {f g : w --> R}
            (p : f · internal_relation_src R = g · internal_relation_src R)
            (q : f · internal_relation_tar R = g · internal_relation_tar R)
  : f = g.
Proof.
  exact (pr222 R w f g p q).
Qed.

(** * 2. The relation on morphisms from an internal relation *)
Definition internal_relation_to_arr_relation
           {C : category}
           {x : C}
           (R : internal_relation x)
           {w : C}
           (f g : w --> x)
  : UU
  := ∑ (r : w --> R),
     (r · internal_relation_src R = f)
     ×
     (r · internal_relation_tar R = g).

Coercion internal_relation_to_arr_relation_to_mor
         {C : category}
         {x : C}
         {R : internal_relation x}
         {w : C}
         {f g : w --> x}
         (r : internal_relation_to_arr_relation R f g)
  : w --> R
  := pr1 r.

Proposition internal_relation_to_arr_relation_src
            {C : category}
            {x : C}
            {R : internal_relation x}
            {w : C}
            {f g : w --> x}
            (r : internal_relation_to_arr_relation R f g)
  : r · internal_relation_src R = f.
Proof.
  exact (pr12 r).
Defined.

Proposition internal_relation_to_arr_relation_tar
            {C : category}
            {x : C}
            {R : internal_relation x}
            {w : C}
            {f g : w --> x}
            (r : internal_relation_to_arr_relation R f g)
  : r · internal_relation_tar R = g.
Proof.
  exact (pr22 r).
Defined.

Definition make_internal_relation_to_arr_relation
           {C : category}
           {x : C}
           (R : internal_relation x)
           {w : C}
           (f g : w --> x)
           (h : w --> R)
           (p : h · internal_relation_src R = f)
           (q : h · internal_relation_tar R = g)
  : internal_relation_to_arr_relation R f g
  := h ,, p ,, q.

Proposition isaprop_internal_relation_to_arr_relation
            {C : category}
            {x : C}
            (R : internal_relation x)
            {w : C}
            (f g : w --> x)
  : isaprop (internal_relation_to_arr_relation R f g).
Proof.
  use invproofirrelevance.
  intros h₁ h₂.
  use subtypePath.
  {
    intro.
    apply isapropdirprod ; apply homset_property.
  }
  use internal_relation_monic.
  - exact (pr12 h₁ @ !(pr12 h₂)).
  - exact (pr22 h₁ @ !(pr22 h₂)).
Qed.

Definition internal_relation_to_arr_hrel
           {C : category}
           {x : C}
           (R : internal_relation x)
           (w : C)
  : hrel (w --> x)
  := λ (f g : w --> x),
     make_hProp
       (internal_relation_to_arr_relation R f g)
       (isaprop_internal_relation_to_arr_relation R f g).

(** * 3. Properties of internal relations *)

(** ** 3.1. Internal reflexivity *)
Definition internal_isrefl
           {C : category}
           {x : C}
           (R : internal_relation x)
  : UU
  := ∏ (w : C), isrefl (internal_relation_to_arr_hrel R w).

Proposition isaprop_internal_isrefl
            {C : category}
            {x : C}
            (R : internal_relation x)
  : isaprop (internal_isrefl R).
Proof.
  use impred ; intro w.
  use impred ; intro f.
  apply propproperty.
Qed.

Definition internal_isrefl_mor
           {C : category}
           {x : C}
           (R : internal_relation x)
  : UU
  := ∑ (r : x --> R),
     (r · internal_relation_src R = identity _)
     ×
     (r · internal_relation_tar R = identity _).

Coercion mor_of_internal_isrefl_mor
         {C : category}
         {x : C}
         {R : internal_relation x}
         (r : internal_isrefl_mor R)
  : x --> R
  := pr1 r.

Definition internal_isrefl_mor_src
           {C : category}
           {x : C}
           {R : internal_relation x}
           (r : internal_isrefl_mor R)
  : r · internal_relation_src R = identity _
  := pr12 r.

Definition internal_isrefl_mor_tar
           {C : category}
           {x : C}
           {R : internal_relation x}
           (r : internal_isrefl_mor R)
  : r · internal_relation_tar R = identity _
  := pr22 r.

Proposition isaprop_internal_isrefl_mor
            {C : category}
            {x : C}
            (R : internal_relation x)
  : isaprop (internal_isrefl_mor R).
Proof.
  use invproofirrelevance.
  intros r₁ r₂.
  use subtypePath.
  {
    intro.
    apply isapropdirprod ; apply homset_property.
  }
  use internal_relation_monic.
  - exact (pr12 r₁ @ !(pr12 r₂)).
  - exact (pr22 r₁ @ !(pr22 r₂)).
Qed.

Definition make_internal_isrefl_mor
           {C : category}
           {x : C}
           (R : internal_relation x)
           (r : x --> R)
           (p : r · internal_relation_src R = identity _)
           (q : r · internal_relation_tar R = identity _)
  : internal_isrefl_mor R
  := r ,, p ,, q.

Definition internal_isrefl_to_internal_isrefl_mor
           {C : category}
           {x : C}
           {R : internal_relation x}
           (HR : internal_isrefl R)
  : internal_isrefl_mor R.
Proof.
  exact (HR x (identity x)).
Qed.

Definition internal_isrefl_mor_to_internal_isrefl
           {C : category}
           {x : C}
           {R : internal_relation x}
           (HR : internal_isrefl_mor R)
  : internal_isrefl R.
Proof.
  intros w f.
  use make_internal_relation_to_arr_relation.
  - exact (f · HR).
  - rewrite !assoc'.
    rewrite internal_isrefl_mor_src.
    apply id_right.
  - rewrite !assoc'.
    rewrite internal_isrefl_mor_tar.
    apply id_right.
Qed.

Definition internal_isrefl_weq_internal_isrefl_mor
           {C : category}
           {x : C}
           (R : internal_relation x)
  : internal_isrefl R ≃ internal_isrefl_mor R.
Proof.
  use weqimplimpl.
  - exact internal_isrefl_to_internal_isrefl_mor.
  - exact internal_isrefl_mor_to_internal_isrefl.
  - apply isaprop_internal_isrefl.
  - apply isaprop_internal_isrefl_mor.
Defined.

(** ** 3.2. Internal symmetry *)
Definition internal_issymm
           {C : category}
           {x : C}
           (R : internal_relation x)
  : UU
  := ∏ (w : C), issymm (internal_relation_to_arr_hrel R w).

Proposition isaprop_internal_issymm
            {C : category}
            {x : C}
            (R : internal_relation x)
  : isaprop (internal_issymm R).
Proof.
  use impred ; intro w.
  apply isaprop_issymm.
Qed.

Definition internal_issymm_mor
           {C : category}
           {x : C}
           (R : internal_relation x)
  : UU
  := ∑ (s : R --> R),
     (s · internal_relation_src R = internal_relation_tar R)
     ×
     (s · internal_relation_tar R = internal_relation_src R).

Coercion mor_of_internal_issymm_mor
         {C : category}
         {x : C}
         {R : internal_relation x}
         (s : internal_issymm_mor R)
  : R --> R
  := pr1 s.

Definition internal_issymm_mor_src
           {C : category}
           {x : C}
           {R : internal_relation x}
           (s : internal_issymm_mor R)
  : s · internal_relation_src R = internal_relation_tar R
  := pr12 s.

Definition internal_issymm_mor_tar
           {C : category}
           {x : C}
           {R : internal_relation x}
           (s : internal_issymm_mor R)
  : s · internal_relation_tar R = internal_relation_src R
  := pr22 s.

Proposition isaprop_internal_issymm_mor
            {C : category}
            {x : C}
            (R : internal_relation x)
  : isaprop (internal_issymm_mor R).
Proof.
  use invproofirrelevance.
  intros s₁ s₂.
  use subtypePath.
  {
    intro.
    apply isapropdirprod ; apply homset_property.
  }
  use internal_relation_monic.
  - exact (pr12 s₁ @ !(pr12 s₂)).
  - exact (pr22 s₁ @ !(pr22 s₂)).
Qed.

Definition make_internal_issymm_mor
           {C : category}
           {x : C}
           (R : internal_relation x)
           (s : R --> R)
           (p : s · internal_relation_src R = internal_relation_tar R)
           (q : s · internal_relation_tar R = internal_relation_src R)
  : internal_issymm_mor R
  := s ,, p ,, q.

Definition internal_issymm_to_internal_issymm_mor
           {C : category}
           {x : C}
           {R : internal_relation x}
           (HR : internal_issymm R)
  : internal_issymm_mor R.
Proof.
  use (HR R (internal_relation_src R) (internal_relation_tar R)).
  use make_internal_relation_to_arr_relation.
  - apply identity.
  - apply id_left.
  - apply id_left.
Qed.

Definition internal_issymm_mor_to_internal_issymm
           {C : category}
           {x : C}
           {R : internal_relation x}
           (HR : internal_issymm_mor R)
  : internal_issymm R.
Proof.
  intros w f g H.
  induction H as [ h [ p q ] ].
  use make_internal_relation_to_arr_relation.
  - exact (h · HR).
  - rewrite !assoc'.
    rewrite internal_issymm_mor_src.
    exact q.
  - rewrite !assoc'.
    rewrite internal_issymm_mor_tar.
    exact p.
Qed.

Definition internal_issymm_weq_internal_issymm_mor
           {C : category}
           {x : C}
           (R : internal_relation x)
  : internal_issymm R ≃ internal_issymm_mor R.
Proof.
  use weqimplimpl.
  - exact internal_issymm_to_internal_issymm_mor.
  - exact internal_issymm_mor_to_internal_issymm.
  - apply isaprop_internal_issymm.
  - apply isaprop_internal_issymm_mor.
Defined.

(** ** 3.3. Internal transitivity *)
Definition internal_istrans
           {C : category}
           {x : C}
           (R : internal_relation x)
  : UU
  := ∏ (w : C), istrans (internal_relation_to_arr_hrel R w).

Proposition isaprop_internal_istrans
            {C : category}
            {x : C}
            (R : internal_relation x)
  : isaprop (internal_istrans R).
Proof.
  do 6 (use impred ; intro).
  apply propproperty.
Qed.

Definition composable_pairs_rel
           {C : category}
           (PB : Pullbacks C)
           {x : C}
           (R : internal_relation x)
  : C
  := PB _ _ _ (internal_relation_src R) (internal_relation_tar R).

Definition composable_pairs_rel_src
           {C : category}
           (PB : Pullbacks C)
           {x : C}
           (R : internal_relation x)
  : composable_pairs_rel PB R --> R
  := PullbackPr2 _.

Definition composable_pairs_rel_tar
           {C : category}
           (PB : Pullbacks C)
           {x : C}
           (R : internal_relation x)
  : composable_pairs_rel PB R --> R
  := PullbackPr1 _.

Proposition composable_pairs_rel_comm
            {C : category}
            (PB : Pullbacks C)
            {x : C}
            (R : internal_relation x)
  : composable_pairs_rel_src PB R · internal_relation_tar R
    =
    composable_pairs_rel_tar PB R · internal_relation_src R.
Proof.
  exact (!(PullbackSqrCommutes _)).
Qed.

Definition internal_istrans_mor
           {C : category}
           (PB : Pullbacks C)
           {x : C}
           (R : internal_relation x)
  : UU
  := ∑ (t : composable_pairs_rel PB R --> R),
     (t · internal_relation_src R
      =
      composable_pairs_rel_src PB R · internal_relation_src R)
     ×
     (t · internal_relation_tar R
      =
      composable_pairs_rel_tar PB R · internal_relation_tar R).

Coercion mor_of_internal_istrans_mor
         {C : category}
         {PB : Pullbacks C}
         {x : C}
         {R : internal_relation x}
         (t : internal_istrans_mor PB R)
  : composable_pairs_rel PB R --> R
  := pr1 t.

Definition internal_istrans_mor_src
           {C : category}
           {PB : Pullbacks C}
           {x : C}
           {R : internal_relation x}
           (t : internal_istrans_mor PB R)
  : t · internal_relation_src R
    =
    composable_pairs_rel_src PB R · internal_relation_src R
  := pr12 t.

Definition internal_istrans_mor_tar
           {C : category}
           {PB : Pullbacks C}
           {x : C}
           {R : internal_relation x}
           (t : internal_istrans_mor PB R)
  : t · internal_relation_tar R
    =
    composable_pairs_rel_tar PB R · internal_relation_tar R
  := pr22 t.

Proposition isaprop_internal_istrans_mor
            {C : category}
            (PB : Pullbacks C)
            {x : C}
            (R : internal_relation x)
  : isaprop (internal_istrans_mor PB R).
Proof.
  use invproofirrelevance.
  intros t₁ t₂.
  use subtypePath.
  {
    intro.
    apply isapropdirprod ; apply homset_property.
  }
  use internal_relation_monic.
  - exact (pr12 t₁ @ !(pr12 t₂)).
  - exact (pr22 t₁ @ !(pr22 t₂)).
Qed.

Definition make_internal_istrans_mor
           {C : category}
           {PB : Pullbacks C}
           {x : C}
           (R : internal_relation x)
           (t : composable_pairs_rel PB R --> R)
           (p : t · internal_relation_src R
                =
                composable_pairs_rel_src PB R · internal_relation_src R)
           (q : t · internal_relation_tar R
                =
                composable_pairs_rel_tar PB R · internal_relation_tar R)
  : internal_istrans_mor PB R
  := t ,, p ,, q.

Definition internal_istrans_to_internal_istrans_mor
           {C : category}
           (PB : Pullbacks C)
           {x : C}
           {R : internal_relation x}
           (HR : internal_istrans R)
  : internal_istrans_mor PB R.
Proof.
  pose (w := composable_pairs_rel PB R).
  pose (f₁ := composable_pairs_rel_src PB R · internal_relation_src R).
  pose (f₂ := composable_pairs_rel_src PB R · internal_relation_tar R).
  pose (f₃ := composable_pairs_rel_tar PB R · internal_relation_tar R).
  assert (internal_relation_to_arr_relation R f₁ f₂) as H₁.
  {
    use make_internal_relation_to_arr_relation.
    - exact (composable_pairs_rel_src PB R).
    - apply idpath.
    - apply idpath.
  }
  assert (internal_relation_to_arr_relation R f₂ f₃) as H₂.
  {
    use make_internal_relation_to_arr_relation.
    - exact (composable_pairs_rel_tar PB R).
    - rewrite <- composable_pairs_rel_comm.
      apply idpath.
    - apply idpath.
  }
  exact (HR w f₁ f₂ f₃ H₁ H₂).
Qed.

Definition internal_istrans_mor_to_internal_istrans
           {C : category}
           (PB : Pullbacks C)
           {x : C}
           {R : internal_relation x}
           (t : internal_istrans_mor PB R)
  : internal_istrans R.
Proof.
  intros w f₁ f₂ f₃ p₁ p₂ ; cbn in *.
  induction p₁ as [ h₁ [ p₁ q₁ ] ].
  induction p₂ as [ h₂ [ p₂ q₂ ] ].
  use make_internal_relation_to_arr_relation.
  - refine (_ · t).
    use PullbackArrow.
    + exact h₂.
    + exact h₁.
    + abstract
        (rewrite q₁, p₂ ;
         apply idpath).
  - rewrite assoc'.
    rewrite internal_istrans_mor_src.
    rewrite !assoc.
    unfold composable_pairs_rel_src.
    etrans.
    {
      apply maponpaths_2.
      apply PullbackArrow_PullbackPr2.
    }
    apply p₁.
  - rewrite assoc'.
    rewrite internal_istrans_mor_tar.
    rewrite !assoc.
    unfold composable_pairs_rel_tar.
    etrans.
    {
      apply maponpaths_2.
      apply PullbackArrow_PullbackPr1.
    }
    apply q₂.
Qed.

Definition internal_istrans_weq_internal_istrans_mor
           {C : category}
           (PB : Pullbacks C)
           {x : C}
           (R : internal_relation x)
  : internal_istrans R ≃ internal_istrans_mor PB R.
Proof.
  use weqimplimpl.
  - exact (internal_istrans_to_internal_istrans_mor PB).
  - exact (internal_istrans_mor_to_internal_istrans PB).
  - apply isaprop_internal_istrans.
  - apply isaprop_internal_istrans_mor.
Defined.

(** * 3.4. Internal equivalence relations *)
Definition internal_iseqrel
           {C : category}
           {x : C}
           (R : internal_relation x)
  : UU
  := internal_isrefl R × internal_issymm R × internal_istrans R.

Definition internal_eqrel
           {C : category}
           (x : C)
  : UU
  := ∑ (R : internal_relation x), internal_iseqrel R.

Definition make_internal_eqrel
           {C : category}
           (x : C)
           (R : internal_relation x)
           (H : internal_iseqrel R)
  : internal_eqrel x
  := R ,, H.

Coercion internal_eqrel_to_relation
         {C : category}
         {x : C}
         (R : internal_eqrel x)
  : internal_relation x
  := pr1 R.

Definition internal_iseqrel_internal_eqrel
           {C : category}
           {x : C}
           (R : internal_eqrel x)
  : internal_iseqrel R
  := pr2 R.

Definition isrefl_internal_eqrel
           {C : category}
           {x : C}
           (R : internal_eqrel x)
  : internal_isrefl R.
Proof.
  exact (pr12 R).
Defined.

Definition issymm_internal_eqrel
           {C : category}
           {x : C}
           (R : internal_eqrel x)
  : internal_issymm R.
Proof.
  exact (pr122 R).
Defined.

Definition istrans_internal_eqrel
           {C : category}
           {x : C}
           (R : internal_eqrel x)
  : internal_istrans R.
Proof.
  exact (pr222 R).
Defined.

Definition internal_iseqrel_mor_eqrel
           {C : category}
           {x : C}
           (R : internal_eqrel x)
           (w : C)
  : eqrel (w --> x).
Proof.
  use make_eqrel.
  - exact (internal_relation_to_arr_hrel R w).
  - repeat split.
    + apply (internal_iseqrel_internal_eqrel R).
    + apply (internal_iseqrel_internal_eqrel R).
    + apply (internal_iseqrel_internal_eqrel R).
Defined.

(** * 4. Effective internal equivalence relations *)
Definition is_effective
           {C : category}
           {x : C}
           (R : internal_eqrel x)
  : UU
  := ∑ (Coeq : Coequalizer (internal_relation_src R) (internal_relation_tar R)),
     isPullback (CoequalizerEqAr Coeq).

Proposition isaprop_is_effective
            {C : univalent_category}
            {x : C}
            (R : internal_eqrel x)
  : isaprop (is_effective R).
Proof.
  use isaproptotal2.
  - intro.
    apply isaprop_isPullback.
  - intros.
    apply isaprop_Coequalizer.
    apply univalent_category_is_univalent.
Qed.

(** * 5. Exact categories *)
Definition all_internal_eqrel_effective
           (C : category)
  : UU
  := ∏ (x : C) (R : internal_eqrel x), is_effective R.

Proposition isaprop_all_internal_eqrel_effective
            (C : univalent_category)
  : isaprop (all_internal_eqrel_effective C).
Proof.
  do 2 (use impred ; intro).
  apply isaprop_is_effective.
Qed.

Definition is_exact
           (C : category)
  : UU
  := is_regular_category C
     ×
     all_internal_eqrel_effective C.

Definition is_exact_to_is_regular
           {C : category}
           (H : is_exact C)
  : is_regular_category C
  := pr1 H.

Definition is_exact_to_all_internal_eqrel_effective
           {C : category}
           (H : is_exact C)
  : all_internal_eqrel_effective C
  := pr2 H.

Definition isaprop_is_exact
           (C : univalent_category)
  : isaprop (is_exact C).
Proof.
  use isapropdirprod.
  - apply isaprop_is_regular_category.
  - apply isaprop_all_internal_eqrel_effective.
Qed.
