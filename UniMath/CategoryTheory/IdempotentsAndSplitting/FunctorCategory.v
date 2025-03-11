Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.

Local Open Scope cat.

Section IdempotentsSplitInFunctorCats.

  Context {C D : category} (Du : is_univalent D) (Ds : idempotents_split D).

  Definition type_of_choice
    {F : [C, D]} (α : _⟦F, F⟧)
    {c : C} (p : pr1 α c · pr1 α c = pr1 α c)
      : UU
    := ∑ (d : D) (H : retraction d (pr1 F c)),
      pr1 α c = H · retraction_section H.

  Lemma isaprop_type_of_choice
    {F : [C, D]} (α : _⟦F, F⟧)
    {c : C} (p : pr1 α c · pr1 α c = pr1 α c)
    : isaprop (type_of_choice α p).
  Proof.
    apply isaprop_is_split_idempotent.
    apply Du.
  Qed.

  Context {F : [C, D]}
    {α : [C, D]⟦F, F⟧}
    (s : is_idempotent α).

  Lemma create_split_idempotent_functor_ob
    : ∏ c : C, type_of_choice α (toforallpaths _ _ _ (base_paths _ _ s) c).
  Proof.
    intro c.
    set (t := toforallpaths _ _ _ (base_paths _ _ s) c).
    set (q := Ds (pr1 F c) (pr1 α c ,, t)).
    exact (factor_through_squash (isaprop_type_of_choice α t) (idfun _) q).
  Defined.

  Definition create_split_idempotent_functor_data
    : functor_data C D.
  Proof.
    use make_functor_data.
    - exact (λ c, pr1 (create_split_idempotent_functor_ob c)).
    - intros c1 c2 f.
      set (d1 := create_split_idempotent_functor_ob c1).
      set (d2 := create_split_idempotent_functor_ob c2).
      exact (retraction_section (pr12 d1) · #(pr1 F) f · retraction_retraction (pr12 d2)).
  Defined.

  Lemma create_split_idempotent_functor_laws
    : is_functor create_split_idempotent_functor_data.
  Proof.
    split.
    - intro.
      cbn.
      rewrite (functor_id F).
      rewrite id_right.
      set (d := create_split_idempotent_functor_ob a).
      apply retraction_is_retraction.
    - intro ; intros.
      cbn.
      rewrite (functor_comp F).
      rewrite ! assoc.
      do 2 apply maponpaths_2.
      rewrite assoc'.
      set (d := create_split_idempotent_functor_ob b).
      rewrite <- (pr22 d).
      apply pathsinv0.
      etrans. {
        rewrite assoc'.
        apply maponpaths.
        exact (nat_trans_ax α _ _ f).
      }
      rewrite assoc.
      apply maponpaths_2.
      etrans. {
        apply maponpaths.
        exact (pr22 (create_split_idempotent_functor_ob a)).
      }
      cbn.
      rewrite assoc.
      rewrite retraction_is_retraction.
      apply id_left.
  Qed.

  Lemma create_split_idempotent
    : [C, D].
  Proof.
    use make_functor.
    - exact create_split_idempotent_functor_data.
    - apply create_split_idempotent_functor_laws.
  Defined.

  Lemma create_split_idempotent_retraction_nat
    {c1 c2 : C} (f : C⟦c1, c2⟧)
    : # create_split_idempotent_functor_data f
        · retraction_section (pr12 (create_split_idempotent_functor_ob c2)) =
        retraction_section (pr12 (create_split_idempotent_functor_ob c1)) · # (pr1 F) f.
  Proof.
    cbn.
    rewrite assoc'.
    set (d := create_split_idempotent_functor_ob c2).
    rewrite (! pr22 d).
    rewrite assoc'.
    etrans. {
      apply maponpaths.
      apply nat_trans_ax.
    }
    rewrite assoc.
    apply maponpaths_2.
    set (d' := create_split_idempotent_functor_ob c1).
    etrans. {
      apply maponpaths.
      exact (pr22 d').
    }
    rewrite assoc.
    rewrite retraction_is_retraction.
    apply id_left.
  Qed.

  Definition create_split_idempotent_retraction
    : create_split_idempotent_functor_data ⟹ pr1 F.
  Proof.
    use make_nat_trans.
    - exact (λ c, retraction_section (pr12 (create_split_idempotent_functor_ob c))).
    - do 3 intro.
      apply create_split_idempotent_retraction_nat.
  Defined.

  Lemma create_split_idempotent_section_nat
    {c1 c2 : C} (f : C⟦c1, c2⟧)
    :  # (pr1 F) f · pr121 (pr2 (create_split_idempotent_functor_ob c2))
       = pr121 (pr2 (create_split_idempotent_functor_ob c1)) · # create_split_idempotent_functor_data f.
  Proof.
    cbn.
    set (d₁ := create_split_idempotent_functor_ob c1).
    set (d₂ := create_split_idempotent_functor_ob c2).
    rewrite ! assoc.
    etrans.
    2: {
      do 2 apply maponpaths_2.
      exact (pr22 d₁).
    }
    etrans.
    2: {
      apply maponpaths_2.
      apply nat_trans_ax.
    }
    rewrite assoc'.
    apply maponpaths.
    apply pathsinv0.
    etrans. {
      apply maponpaths_2.
      exact (pr22 d₂).
    }
    rewrite assoc'.
    etrans.
    {
      apply maponpaths.
      apply retraction_is_retraction.
    }
    apply id_right.
  Qed.

  Definition create_split_idempotent_section
    : pr1 F ⟹ create_split_idempotent_functor_data.
  Proof.
    use make_nat_trans.
    - exact (λ c, pr1 (pr212 (create_split_idempotent_functor_ob c))).
    - intros c1 c2 f.
      apply create_split_idempotent_section_nat.
  Defined.

  Definition create_split_idempotent_retract
    : retraction create_split_idempotent F.
  Proof.
    simple refine (_ ,, _ ,, _) ; simpl.
    - exact create_split_idempotent_retraction.
    - exact create_split_idempotent_section.
    - use nat_trans_eq.
      { apply homset_property. }
      exact (λ c, pr2 (pr212 (create_split_idempotent_functor_ob c))).
  Defined.

  Lemma create_split_idempotent_naturality
    : α = create_split_idempotent_retract · retraction_section create_split_idempotent_retract.
  Proof.
    use nat_trans_eq.
    { intro ; apply homset_property. }
    intro c.
    exact (pr22 (create_split_idempotent_functor_ob c)).
  Qed.

End IdempotentsSplitInFunctorCats.

Definition idempotents_split_in_functor_cat
  {C D : category} (Du : is_univalent D) (Ds : idempotents_split D)
  : idempotents_split [C, D].
Proof.
  intros F α.
  apply hinhpr.
  exists (create_split_idempotent Du Ds (pr2 α)).
  exists (create_split_idempotent_retract Du Ds (pr2 α)).
  apply create_split_idempotent_naturality.
Defined.
