(* The category REL of (homotopy) relations:
   1. The objects are sets
   2. The morphisms are relations of sets

   Furthermore, we show that REL is univalent.
   Because any invertible relation is a function,
   this reduces to using that SET is univalent.
   Therefore, we show that
   1: The isomorphisms in REL are equivalent to the isomorphisms in SET
   2: Idtoiso_REL factors through Idtoiso_HSET
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.categories.HSET.All.

Local Open Scope cat.

Section Relations.

  Definition bin_hrel (X Y : hSet) : UU := X -> Y -> hProp.
  Identity Coercion idbin_hrel : bin_hrel >-> Funclass.

  Definition REL_precategory_ob_mor
    : precategory_ob_mor
    := make_precategory_ob_mor hSet bin_hrel.

  Definition REL_precategory_id_comp
    : precategory_id_comp REL_precategory_ob_mor.
  Proof.
    exists (λ _ x1 x2, eqset x1 x2).
    exact (λ X Y Z r1 r2 x z, ∃ y : pr1 Y, r1 x y × r2 y z).
  Defined.

  Definition REL_precategory_data : precategory_data.
  Proof.
    exists REL_precategory_ob_mor.
    exact REL_precategory_id_comp.
  Defined.

  Lemma REL_is_precategory : is_precategory REL_precategory_data.
  Proof.
    repeat split ; intro ; intros ;
      repeat (apply funextsec ; intro) ;
      use hPropUnivalence.
    - intro p.
      use (factor_through_squash_hProp (f _ _) _ p).
      clear p ; intro p.
      induction (! pr12 p).
      exact (pr22 p).
    - intro p.
      apply hinhpr.
      exact (x ,, idpath _ ,, p).
    - intro p.
      use (factor_through_squash_hProp (f _ _) _ p).
      clear p ; intro p.
      induction (pr22 p).
      exact (pr12 p).
    - intro p.
      apply hinhpr.
      exact (x0 ,, p ,, idpath _).
    - intro p.
      use (factor_through_squash_hProp ((f · g · h) x x0) _ p).
      clear p ; intro p.
      use (factor_through_squash_hProp ((f · g · h) x x0) _ (pr22 p)).
      intro q.
      apply hinhpr.
      exists (pr1 q).
      split.
      + apply hinhpr.
        exact (pr1 p ,, pr12 p ,, pr12 q).
      + exact (pr22 q).
    - intro p.
      use (factor_through_squash_hProp ((f · (g · h)) x x0) _ p).
      + clear p ; intro p.
        use (factor_through_squash_hProp ((f · (g · h)) x x0) _ (pr12 p)).
        intro q.
        apply hinhpr.
        exists (pr1 q).
        split.
        * exact (pr12 q).
        * apply hinhpr.
          exact (pr1 p,,  pr22 q ,, pr22 p).
    - intro p.
      use (factor_through_squash_hProp ((f · (g · h)) x x0) _ p).
      + clear p ; intro p.
        use (factor_through_squash_hProp ((f · (g · h)) x x0) _ (pr12 p)).
        intro q.
        apply hinhpr.
        exists (pr1 q).
        split.
        * exact (pr12 q).
        * apply hinhpr.
          exact (pr1 p,,  pr22 q ,, pr22 p).
    - intro p.
      use (factor_through_squash_hProp ((f · g · h) x x0) _ p).
      + clear p ; intro p.
        use (factor_through_squash_hProp _ _ (pr22 p)).
        intro q.
        apply hinhpr.
        exists (pr1 q).
        split.
        * apply hinhpr.
          exact (pr1 p ,, pr12 p ,, pr12 q).
        * exact (pr22 q).
  Qed.

  Definition REL_precategory : precategory
    := _ ,, REL_is_precategory.

  Lemma REL_precategory_has_homsets
    : has_homsets REL_precategory.
  Proof.
    exact (λ _ _, isaset_set_fun_space (pr1 _) (_ ,, isaset_set_fun_space _ (_ ,, isasethProp))).
  Qed.

  Definition REL : category
    := REL_precategory ,, REL_precategory_has_homsets.

End Relations.

Section SET_as_full_sub_of_REL.

  Definition function_to_bin_hrel
             {X Y : hSet} (f : X -> Y)
    : bin_hrel X Y
    := λ x y, eqset (f x) y.

  Lemma invertiblefunction_to_invertiblerelation_laws
        {X Y : hSet}
        {f : X → Y}
        (i : is_z_isomorphism (C := HSET) f)
    : (function_to_bin_hrel f : REL⟦_,_⟧) · function_to_bin_hrel (pr1 i) = identity (C := REL) X.
  Proof.
    apply funextsec ; intro x1.
      apply funextsec ; intro x2.
      use hPropUnivalence.
      + intro q.
        use (factor_through_squash_hProp (eqset x1 x2) _ q).
        clear q ; intro q.
        refine (! eqtohomot (pr12 i) x1 @ _ @ pr22 q).
        apply (maponpaths (pr1 i)).
        exact (pr12 q).
      + intro p ; induction p.
        apply hinhpr.
        exact (f x1 ,, idpath _ ,, eqtohomot (pr12 i) x1).
  Qed.

  Definition invertiblefunction_to_invertiblerelation
             {X Y : hSet} {f : X -> Y}
             (i : is_z_isomorphism (C := HSET) f)
    : is_z_isomorphism (C := REL) (function_to_bin_hrel f).
  Proof.
    apply (make_is_z_isomorphism (C := REL) _ (function_to_bin_hrel (pr1 i))).
    split.
    - exact (invertiblefunction_to_invertiblerelation_laws i).
    - exact (invertiblefunction_to_invertiblerelation_laws (is_z_iso_inv_from_z_iso ((_ ,, i) : z_iso (C := HSET) _ _))).
  Defined.

  Definition z_iso_in_SET_to_z_iso_in_REL
             {X Y : HSET} (i : z_iso (C := HSET) X Y)
    : z_iso (C := REL) X Y
    := _ ,, invertiblefunction_to_invertiblerelation (pr2 i).

End SET_as_full_sub_of_REL.

Section Isos.

  Lemma inverse_swap_relation
             {X Y : hSet} {r : bin_hrel X Y}
             (i : is_z_isomorphism (C := REL) r)
    : ∏ (x : X) (y : Y), r x y -> pr1 i y x.
  Proof.
    intros x y p.

    set (t := eqtohomot (eqtohomot (pr12 i) x) x).
    set (q := path_to_fun (X := eqset x x) (! (base_paths _ _ t)) (idpath x)).
    use (factor_through_squash_hProp _ _ q).
    clear q ; intro q.

    assert (q0 : pr1 q = y).
    {
      set (ty := eqtohomot (eqtohomot (pr22 i) (pr1 q)) y).
      use (path_to_fun (base_paths _ _ ty)).
      apply hinhpr.
      exists x.
      split.
      - exact (pr22 q).
      - exact p.
    }

    induction q0.
    exact (pr22 q).
  Qed.

  Lemma inverse_swap_relation_iff
             {X Y : hSet} {r : bin_hrel X Y}
             (i : is_z_isomorphism (C := REL) r)
    : ∏ (x : X) (y : Y), r x y <-> pr1 i y x.
  Proof.
    intros x y.
    split.
    - exact (inverse_swap_relation i x y).
    - exact (inverse_swap_relation (pr2 (z_iso_inv ((r,,i) : z_iso (C := REL) _ _))) y x).
  Qed.

  Definition invertible_relation_is_functional
             {X Y : hSet} {r : bin_hrel X Y}
             (p : is_z_isomorphism (C := REL) r)
    : ∏ (x : X) (y1 y2 : Y),
      r x y1 -> r x y2 -> y1 = y2.
  Proof.
    intros x y1 y2 r1 r2.
    set (q' := base_paths _ _ (eqtohomot (eqtohomot (pr22 p) y1) y2)).
    apply (path_to_fun q').
    apply hinhpr.
    exists x.
    split.
    2: exact r2.
    exact (inverse_swap_relation p _ _ r1).
  Qed.

  Definition bin_hrel_is_z_iso_to_image_isaprop
             {X Y : hSet} {r : bin_hrel X Y}
             (p : is_z_isomorphism (C := REL) r)
    : ∏ x : X, isaprop (∑ y : Y, r x y).
  Proof.
    intros x.
    apply isaproptotal2.
    - intro ; apply r.
    - intros y1 y2.
      apply invertible_relation_is_functional.
      exact p.
  Qed.

  Definition bin_hrel_is_z_iso_to_image
             {X Y : hSet} {r : bin_hrel X Y}
             (p : is_z_isomorphism (C := REL) r)
    : ∏ x : X, ∑ y : Y, r x y.
  Proof.
    intro x.
    set (q := pr12 p).
    set (q' := base_paths _ _ (!(eqtohomot ((eqtohomot q) x) x))).
    set (y := path_to_fun q' (idpath _)).
    use (factor_through_squash_hProp (_ ,, bin_hrel_is_z_iso_to_image_isaprop p x) _ y).
    intro v.
    exact (pr1 v ,, pr12 v).
  Defined.

  Definition bin_hrel_is_z_iso_to_function
             {X Y : hSet} {r : bin_hrel X Y}
             (p : is_z_isomorphism (C := REL) r)
    : X -> Y
    := λ x, pr1 (bin_hrel_is_z_iso_to_image p x).

  Definition is_z_iso_in_REL_to_unique_image
             {X Y : hSet} (r : bin_hrel X Y)
    : is_z_isomorphism (C := REL) r
      -> (∏ x: X, ∃! y : Y, r x y).
  Proof.
    intro i.
    intro x.
    exists (bin_hrel_is_z_iso_to_image i x).
    intro.
    apply (bin_hrel_is_z_iso_to_image_isaprop i x).
  Defined.

  Definition unique_image_to_inverse_law_in_REL
             {X Y : hSet} {r : bin_hrel X Y}
             (py : (∏ y : Y, ∃! x : X, r x y))
             (px : ∏ x: X, ∃! y : Y, r x y)
             (x1 x2 : X)
    : (∃ y : pr1 Y, r x1 y × r x2 y) = eqset x1 x2.
  Proof.
    apply hPropUnivalence.
      + intro q.
        use (factor_through_squash_hProp _ _ q).
        clear q ; intros [y q].
        refine (base_paths _ _ (pr2 (py y) (x1 ,, pr1 q)) @ _).
        exact (! base_paths _ _ (pr2 (py y) (x2 ,, pr2 q))).
      + intro q.
        induction q.
        apply hinhpr.
        exists (pr11 (px x1)).
        split ; apply (pr21 (px x1)).
  Qed.

  Definition unique_image_to_is_z_iso_in_REL
             {X Y : hSet} (r : bin_hrel X Y)
    : (∏ x: X, ∃! y : Y, r x y) × (∏ y : Y, ∃! x : X, r x y)
      -> is_z_isomorphism (C := REL) r.
  Proof.
    intros [px py].
    exists (λ y x, r x y).
    split ; repeat (apply funextsec ; intro).
    - apply (unique_image_to_inverse_law_in_REL py px).
    - apply (unique_image_to_inverse_law_in_REL px py).
  Defined.

  Local Lemma exists_unique_function
        {X : UU} (P Q : X -> hProp)
    : (∏ x : X, P x <-> Q x) -> (∃! x : X, P x) -> (∃! x : X, Q x).
  Proof.
    intros a [x p].
    exists (pr1 x ,, pr1 (a (pr1 x)) (pr2 x)).
    intro t.
    use total2_paths_f.
    - use (base_paths _ _ (p (pr1 t ,, _))).
      exact (pr2 (a (pr1 t)) (pr2 t)).
    - apply (pr2 (Q _)).
  Qed.

  Definition is_z_iso_in_REL_simplified
             {X Y : hSet} (r : bin_hrel X Y)
    : is_z_isomorphism (C := REL) r
      <-> (∏ x: X, ∃! y : Y, r x y) × (∏ y : Y, ∃! x : X, r x y).
  Proof.
    split.
    - intro i.
      split.
      + exact (is_z_iso_in_REL_to_unique_image _ i).
      + intro y.

        set (j := pr2 (z_iso_inv ((r ,, i) : z_iso (C := REL) _ _))).
        set (P := λ x : X, inv_from_z_iso ((r,, i) : z_iso (C := REL) _ _) y x).
        set (Q := λ x : X, r x y).
        set (p := is_z_iso_in_REL_to_unique_image _ j y).

        use (exists_unique_function P Q _ p).
        intro x.
        exact (inverse_swap_relation_iff j y x).
    - apply unique_image_to_is_z_iso_in_REL.
  Qed.

  Definition bin_hrel_is_z_iso_to_equality_inverse_law
             {X Y : hSet} {r : bin_hrel X Y}
             (p : is_z_isomorphism (C := REL) r)
    : ∏ x : X, pr1 (bin_hrel_is_z_iso_to_image (is_z_iso_inv_from_z_iso (r,, p : z_iso (C := REL) X Y)) (pr1 (bin_hrel_is_z_iso_to_image p x))) = x.
  Proof.
    intro x.

    use (invertible_relation_is_functional (pr2 (z_iso_inv ((r,,p) : z_iso (C := REL) X Y)))).
    - exact (bin_hrel_is_z_iso_to_function p x).
    - exact (pr2 (bin_hrel_is_z_iso_to_image (is_z_iso_inv_from_z_iso ((r,, p) : z_iso (C := REL) _ _))  (pr1 (bin_hrel_is_z_iso_to_image p x)))).
    - apply inverse_swap_relation_iff.
      exact (pr2 (bin_hrel_is_z_iso_to_image p x)).
  Qed.

  Definition bin_hrel_is_z_iso_to_equality
             {X Y : hSet} {r : bin_hrel X Y}
             (p : is_z_isomorphism (C := REL) r)
    : z_iso (C := HSET) X Y.
  Proof.
    set (j := (r ,, p : z_iso (C := REL) X Y)).
    set (i := is_z_iso_inv_from_z_iso j).
    use make_z_iso.
    - exact (bin_hrel_is_z_iso_to_function p).
    - exact (bin_hrel_is_z_iso_to_function i).
    - abstract (split ; (apply funextsec ; intro) ;
        [ apply bin_hrel_is_z_iso_to_equality_inverse_law | apply (bin_hrel_is_z_iso_to_equality_inverse_law i)]).
  Defined.

  Lemma bin_hrel_z_iso_equiv_hset_z_iso_law
        {X Y : hSet}
        (i : z_iso (C := HSET) X Y)
    : bin_hrel_is_z_iso_to_function (invertiblefunction_to_invertiblerelation (pr2 i)) = pr1 i.
  Proof.
    apply funextsec ; intro x.
    exact (base_paths _ _ (pr1 (bin_hrel_is_z_iso_to_image_isaprop (invertiblefunction_to_invertiblerelation (pr2 i)) x  (bin_hrel_is_z_iso_to_image (invertiblefunction_to_invertiblerelation (pr2 i)) x) (pr1 i x ,, idpath _)))).
  Qed.

  Lemma bin_hrel_z_iso_equiv_hset_z_iso_law'
        {X Y : hSet} (i : z_iso (C := REL) X Y)
    : function_to_bin_hrel (bin_hrel_is_z_iso_to_function (pr2 i)) = pr1 i.
  Proof.
    apply funextsec ; intro x.
    apply funextsec ; intro y.

    set (q := bin_hrel_is_z_iso_to_image_isaprop (pr2 i) x (bin_hrel_is_z_iso_to_image (pr2 i) x)).
    apply hPropUnivalence.
    - intro p.
      induction p.
      exact (pr2 (bin_hrel_is_z_iso_to_image (pr2 i) x)).
    - intro p.
      set (c := bin_hrel_is_z_iso_to_image_isaprop (pr2 i) x (bin_hrel_is_z_iso_to_image (pr2 i) x) (y,,p)).
      exact (base_paths _ _ (pr1 c)).
  Qed.

  Definition bin_hrel_z_iso_equiv_hset_z_iso
             (X Y : hSet)
    : z_iso (C := HSET) X Y ≃ z_iso (C := REL) X Y.
  Proof.
    use weq_iso.
    - exact (λ i, z_iso_in_SET_to_z_iso_in_REL i).
    - exact (λ i, bin_hrel_is_z_iso_to_equality (pr2 i)).
    - intro ;
        apply z_iso_eq, bin_hrel_z_iso_equiv_hset_z_iso_law.
    - intro ;
        apply z_iso_eq, bin_hrel_z_iso_equiv_hset_z_iso_law'.
  Defined.

End Isos.

Section Univalence.

  Lemma is_univalent_REL : is_univalent REL.
  Proof.
    intros X Y.
    use weqhomot.
    - exact (bin_hrel_z_iso_equiv_hset_z_iso X Y ∘ make_weq _ (is_univalent_HSET X Y))%weq.
    - intro p ; induction p.
      use (z_iso_eq (C := REL)).
      do 2 (apply funextsec ; intro).
      apply idpath.
  Qed.

End Univalence.
