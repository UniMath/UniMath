(**************************************************************************************************

  The cartesian product as a displayed category

  One can view any category C' as a displayed category over the unit category. One can then reindex
  this over another category C, to obtain a displayed category over C, that represents the cartesian
  product. This product category creates limits of a certain shape if C and C' have these limits.
  The arrow category of C is a displayed category over the product category of C with itself
  consisting of all the morphisms in C.

  Contents
  1. One can consider any category as a displayed category over the unit category [disp_over_unit]
  1.1. Univalence of the category over the unit category [is_univalent_disp_disp_over_unit]
  2. The cartesian product as a displayed category over the first component [disp_cartesian]
  2.1 The cartesian product creates limits [creates_limits_disp_cartesian]
  3. The arrow category [arrow]
  4. A direct definition of the product category as a displayed category [disp_cartesian']

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Limits.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.

Local Open Scope cat.
Local Open Scope mor_disp.

(** * 1. One can consider any category as a displayed category over the unit category *)
Section over_terminal_category.

  Variable C : category.

  Definition disp_over_unit_data : disp_cat_data unit_category.
  Proof.
    use tpair.
    - use tpair.
      + intro. apply (ob C).
      + simpl. intros x y c c' e. apply (C ⟦c, c'⟧).
    - use tpair.
      + simpl. intros. apply identity.
      + intros ? ? ? ? ? a b c f g.
        apply (compose (C:=C) f g ).
  Defined.

  Definition disp_over_unit_axioms : disp_cat_axioms _ disp_over_unit_data.
  Proof.
    repeat split; cbn; intros.
    - apply id_left.
    - etrans. apply id_right.
      apply pathsinv0. unfold mor_disp. cbn.
      apply (eqtohomot (transportf_const _ _)).
    - etrans. apply assoc.
      apply pathsinv0. unfold mor_disp. cbn.
      apply (eqtohomot (transportf_const _ _)).
    - apply homset_property.
  Qed.

  Definition disp_over_unit : disp_cat _ := _ ,, disp_over_unit_axioms.

(** ** 1.1. Univalence of the category over the unit category *)

  Lemma isweq_z_iso_to_z_iso_disp
    (a : disp_over_unit tt)
    (b : disp_over_unit tt)
    : isweq (X := z_iso a b) (Y := z_iso_disp (identity_z_iso (tt : unit_category)) a b)
      (λ f, (_ ,, _ ,, z_iso_after_z_iso_inv f ,, z_iso_inv_after_z_iso f)).
  Proof.
    use isweq_iso.
    - intro f.
      exact (make_z_iso _ _ (inv_mor_after_z_iso_disp f ,, z_iso_disp_after_inv_mor f)).
    - intro.
      now apply z_iso_eq.
    - intro.
      now apply eq_z_iso_disp.
  Qed.

  Proposition is_univalent_disp_disp_over_unit
    (HC : is_univalent C)
    : is_univalent_disp disp_over_unit.
  Proof.
    intros a b e aa bb.
    induction e, a.
    use weqhomot.
    - exact (weqcomp (make_weq _ (HC _ _)) (make_weq _ (isweq_z_iso_to_z_iso_disp aa bb))).
    - intro ee.
      induction ee.
      apply eq_z_iso_disp.
      apply idpath.
  Qed.

End over_terminal_category.

Lemma disp_over_unit_fiber_equals_cat
  (C : category)
  (u : unit)
  : (disp_over_unit C)[{u}] = C.
Proof.
  apply (subtypePath (λ _, isaprop_has_homsets _)).
  refine (subtypePairEquality' _ (isaprop_is_precategory _ (homset_property C))).
  induction C as [C Hhomsets].
  induction C as [Cdata Hisprecategory].
  exact (maponpaths (λ x, (pr1 Cdata) ,, x) (pathsdirprod (idpath _) (idpath _))).
Qed.

(** * 2. The cartesian product as a displayed category over the first component *)
Section cartesian_product_pb.
  Variable C C' : category.

  (* TODO: use a better name here (this one is baffling out of context) *)
  Definition disp_cartesian : disp_cat C
    := reindex_disp_cat (functor_to_unit C) (disp_over_unit C').

  Lemma comp_disp_cartesian
    (D := disp_cartesian)
    {c c' c'' : C}
    {F : C⟦c, c'⟧} {F' : C⟦c', c''⟧}
    {A : D c} {A' : D c'} {A'' : D c''}
    (G : A -->[F] A') (G' : A' -->[F'] A'')
    : (G ;; G') = G · G'.
  Proof.
    unfold comp_disp.
    simpl.
    unfold transportb.
    rewrite transportf_set.
    - apply idpath.
    - apply isasetaprop,
        isasetunit.
  Qed.

  Definition cartesian : category := total_category disp_cartesian.

  Lemma cartesian_is_binproduct
    : cartesian = category_binproduct C C'.
  Proof.
    apply subtypePairEquality';
      [ | apply isaprop_has_homsets].
    apply subtypePairEquality';
      [ | apply isaprop_is_precategory, has_homsets_precategory_binproduct; apply homset_property].
    apply (maponpaths (tpair _ _)).
    use pathsdirprod.
    - apply funextsec.
      intro.
      apply (maponpaths (tpair _ _)).
      exact (transportf_set _ _ _ (isasetaprop (isasetunit _ _))).
    - do 5 (apply funextsec; intro).
      apply (maponpaths (tpair _ _)).
      exact (transportf_set _ _ _ (isasetaprop (isasetunit _ _))).
  Qed.

  Definition pr2_functor
    : cartesian ⟶ C'.
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact pr2.
      + exact (λ _ _, pr2).
    - abstract (
        use tpair;
        repeat intro;
        cbn;
        exact (maponpaths (λ x, x _) (transportf_const _ _))
      ).
  Defined.

(** ** 2.1 The cartesian product creates limits *)

  Section Limits.

    Context {J : graph}.
    Context {d : diagram J cartesian}.
    Context (L : LimCone (mapdiagram (pr1_category _) d)).
    Context (L' : LimCone (mapdiagram pr2_functor d)).

    Definition cartesian_limit_tip
      : disp_cartesian (lim L)
      := lim L'.

    Definition cartesian_limit_cone
      (j : vertex J)
      : cartesian_limit_tip -->[ limOut L j] pr2 (dob d j)
      := limOut L' j.

    Definition cartesian_limit_forms_cone
      : forms_cone d (λ j, (limOut L j,, cartesian_limit_cone j) : cartesian ⟦_ ,, _, _ ,, _⟧).
    Proof.
      intros u v e.
      use total2_paths_f.
      + apply (limOutCommutes L).
      + refine (maponpaths (λ x, x _ ) (transportf_const _ _) @ _).
        refine (comp_disp_cartesian _ _ @ _).
        apply (limOutCommutes L').
    Qed.

    Section Arrow.
      Context (tip': total_category disp_cartesian).
      Context (cone': cone d tip').

      Definition cartesian_limit_arrow
        : total_category disp_cartesian ⟦ tip', pr11 L,, cartesian_limit_tip ⟧.
      Proof.
        use tpair.
        - apply (limArrow L _ (mapcone (pr1_category _) d cone')).
        - apply (limArrow L' _ (mapcone (pr2_functor) d cone')).
      Defined.

      Lemma cartesian_limit_arrow_commutes
        : is_cone_mor cone' (make_cone _ cartesian_limit_forms_cone) cartesian_limit_arrow.
      Proof.
        intro u.
        use total2_paths2.
        - apply (limArrowCommutes L).
        - exact (maponpaths (λ x, x _ ) (transportf_const _ _) @ limArrowCommutes L' _ _ _ ).
      Qed.

      Lemma cartesian_limit_arrow_unique
        (arrow' : cartesian ⟦ tip', lim L,, cartesian_limit_tip ⟧)
        (arrow'_commutes : is_cone_mor cone' (make_cone _ cartesian_limit_forms_cone) arrow')
        : (arrow' ,, arrow'_commutes) = (cartesian_limit_arrow ,, cartesian_limit_arrow_commutes).
      Proof.
        use total2_paths_f.
        - use total2_paths2.
          + apply (limArrowUnique L).
            intro u.
            exact (maponpaths pr1 (arrow'_commutes u)).
          + apply (limArrowUnique L').
            intro u.
            refine (maponpaths (λ x, x _) (!transportf_const _ _) @ _).
            refine (_ @ fiber_paths (arrow'_commutes u)).
            exact (maponpaths (λ x, x _) (!transportf_const _ _)).
        - apply impred_isaprop;
          intro;
          apply (homset_property (total_category _)).
      Qed.

    End Arrow.

    Definition creates_limits_disp_cartesian
      : creates_limit d L.
    Proof.
      use make_creates_limit.
      - exact cartesian_limit_tip.
      - exact cartesian_limit_cone.
      - exact cartesian_limit_forms_cone.
      - intros tip' cone'.
        use ((
          cartesian_limit_arrow _ cone' ,,
          cartesian_limit_arrow_commutes _ _) ,,
          λ _, cartesian_limit_arrow_unique _ cone' _ _).
    Defined.

    Definition limits_cartesian
      : LimCone d
      := total_limit _ creates_limits_disp_cartesian.

  End Limits.

End cartesian_product_pb.

(** * 3. The arrow category *)

Section arrow.

  Variable C : category.

  Definition disp_arrow_data : disp_cat_data (cartesian C C).
  Proof.
    use tpair.
    - use tpair.
      + intro H.
        exact (pr1 H --> pr2 H).
      + cbn. intros xy ab f g h.
        exact (compose f (pr2 h) = compose (pr1 h) g ).
    - split.
      + abstract (
          intros;
          apply pathsinv0;
          refine (id_left xx @ _);
          refine (!id_right xx @ _);
          apply maponpaths, pathsinv0;
          apply (eqtohomot (transportf_const _ (C⟦_, _⟧)))
        ).
      + abstract (
          intros;
          refine (maponpaths (λ x, _ (x _)) (transportf_const _ (C⟦_, _⟧)) @ _);
          refine (assoc _ _ _ @ _);
          refine (maponpaths_2 _ X _ @ _);
          refine (!assoc _ _ _ @ _);
          refine (maponpaths _ X0 @ _);
          apply assoc
        ).
  Defined.

  Definition disp_arrow_axioms : disp_cat_axioms _ disp_arrow_data.
  Proof.
    repeat split; intros;
      try apply homset_property.
    apply isasetaprop.
    apply homset_property.
  Qed.

  Definition disp_arrow : disp_cat (cartesian C C) := _ ,, disp_arrow_axioms.

  Definition arrow : category := total_category disp_arrow.

  Definition disp_domain : disp_cat C := sigma_disp_cat disp_arrow.

  Definition total_domain := total_category disp_domain.

End arrow.

(** * 4. A direct definition of the product category as a displayed category *)

Section cartesian_product.

  Variables C C' : category.

  Definition disp_cartesian_ob_mor : disp_cat_ob_mor C.
  Proof.
    use tpair.
    - exact (λ c, C').
    - cbn. intros x y x' y' f. exact (C'⟦x', y'⟧).
  Defined.

  Definition disp_cartesian_data : disp_cat_data C.
  Proof.
    exists disp_cartesian_ob_mor.
    use tpair; cbn.
    - intros; apply identity.
    - intros ? ? ? ? ? ? ? ? f g. apply (f · g).
  Defined.

  Definition disp_cartesian_axioms : disp_cat_axioms _ disp_cartesian_data.
  Proof.
    repeat split; intros; cbn.
    - etrans. apply id_left.
      apply pathsinv0.
      etrans. unfold mor_disp. cbn. apply (eqtohomot (transportf_const _ _)).
      apply idpath.
    - etrans. apply id_right.
      apply pathsinv0.
      etrans. unfold mor_disp. cbn. apply (eqtohomot (transportf_const _ _)).
      apply idpath.
    - etrans. apply assoc.
      apply pathsinv0.
      etrans. unfold mor_disp. cbn. apply (eqtohomot (transportf_const _ _)).
      apply idpath.
    - apply homset_property.
  Qed.

  Definition disp_cartesian' : disp_cat C := _ ,, disp_cartesian_axioms.

End cartesian_product.
