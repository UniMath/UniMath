(** **********************************************************

Benedikt Ahrens March 2016, Anthony Bordg May 2017
Niels van der Weide February 2022: rebasing of general comma categories on displayed categories


************************************************************)


(** **********************************************************

Contents :

        - special comma categories (c ↓ K),
          called [cComma] (constant Comma)
        - forgetful functor [cComma_pr1]
        - morphism [f : C ⟦c, c'⟧] induces
          [functor_cComma_mor : functor (c' ↓ K) (c ↓ K)]
        - general comma categories [comma_category]
          - projection functors ([comma_pr1], [comma_pr2])

        - inserter categories

************************************************************)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Section const_comma_category_definition.

Context (M C : category) (K : functor M C) (c : C).

Definition ccomma_object : UU := ∑ m, C⟦c, K m⟧.
Definition ccomma_morphism (a b : ccomma_object) : UU
  := ∑ f : _ ⟦pr1 a, pr1 b⟧, pr2 a · #K f = pr2 b.

Definition isaset_ccomma_morphism a b : isaset (ccomma_morphism a b).
Proof.
  apply (isofhleveltotal2 2).
  - apply homset_property.
  - intro.
    apply hlevelntosn.
    apply homset_property.
Qed.

Definition cComma_mor_eq a b (f f' : ccomma_morphism a b)
  : pr1 f = pr1 f' -> f = f'.
Proof.
  intro H.
  apply subtypePath.
  intro. apply homset_property.
  exact H.
Qed.

Definition ccomma_id a : ccomma_morphism a a.
Proof.
  exists (identity _ ).
  abstract (
  intermediate_path (pr2 a · identity _ );
   [ apply maponpaths; apply functor_id |];
  apply id_right
  ).
Defined.

Definition ccomma_comp a b d :
  ccomma_morphism a b -> ccomma_morphism b d -> ccomma_morphism a d.
Proof.
  intros f g.
  exists (pr1 f · pr1 g).
  abstract (
  rewrite functor_comp;
  rewrite assoc;
  rewrite (pr2 f);
  apply (pr2 g)
   ).
Defined.

Definition ccomma_precategory_ob_mor : precategory_ob_mor.
Proof.
  exists ccomma_object.
  exact ccomma_morphism.
Defined.

Definition ccomma_precategory_data : precategory_data.
Proof.
  exists ccomma_precategory_ob_mor.
  split.
  - exact ccomma_id.
  - exact ccomma_comp.
Defined.

Definition is_precategory_ccomma_precategory_data
  : is_precategory ccomma_precategory_data.
Proof.
  repeat split.
  - intros. apply cComma_mor_eq.
    simpl. apply id_left.
  - intros. apply cComma_mor_eq.
    simpl. apply id_right.
  - intros. apply cComma_mor_eq.
    simpl. apply assoc.
  - intros. apply cComma_mor_eq.
    simpl. apply assoc'.
Qed.

Definition cComma_precat : precategory.
Proof.
  exists ccomma_precategory_data.
  exact is_precategory_ccomma_precategory_data.
Defined.

Lemma has_homsets_cComma_precat: has_homsets cComma_precat.
Proof.
  red.
  intros a b.
  apply isaset_total2.
  - apply homset_property.
  - intro.
    apply hlevelntosn.
    apply homset_property.
Qed.

Definition cComma : category := cComma_precat ,, has_homsets_cComma_precat.


Definition ccomma_pr1_functor_data : functor_data cComma M.
Proof.
  exists pr1.
  intros a b f. exact (pr1 f).
Defined.

Lemma is_functor_ccomma_pr1 : is_functor ccomma_pr1_functor_data.
Proof.
  split.
  - intro a. apply idpath.
  - intros ? ? ? ? ?. apply idpath.
Qed.

Definition cComma_pr1 : cComma ⟶ M := tpair _ _ is_functor_ccomma_pr1.


End const_comma_category_definition.

Section lemmas_on_const_comma_cats.


Context (M C : category).

Local Notation "c ↓ K" := (cComma _ _ K c) (at level 3).

Context (K : functor M C).
Context {c c' : C}.
Context (h : C ⟦c, c'⟧).


Definition cComma_mor_ob : c' ↓ K → c ↓ K.
Proof.
  intro af.
  exists (pr1 af).
  exact (h · pr2 af).
Defined.

Definition cComma_mor_mor (af af' : c' ↓ K) (g : c' ↓ K ⟦af, af'⟧)
  : c ↓ K ⟦cComma_mor_ob af, cComma_mor_ob af'⟧.
Proof.
  exists (pr1 g).
  abstract (
    simpl;
    rewrite <- assoc;
    rewrite (pr2 g);
    apply idpath
    ).
Defined.

Definition cComma_mor_functor_data : functor_data (c' ↓ K) (c ↓ K).
Proof.
  exists cComma_mor_ob.
  exact cComma_mor_mor.
Defined.

Lemma is_functor_cComma_mor_functor_data : is_functor cComma_mor_functor_data.
Proof.
  split.
  - intro. apply cComma_mor_eq.
    apply idpath.
  - intros ? ? ? ? ?. apply cComma_mor_eq.
    apply idpath.
Qed.

Definition functor_cComma_mor : c' ↓ K ⟶ c ↓ K := tpair _ _ is_functor_cComma_mor_functor_data.

End lemmas_on_const_comma_cats.

(** General comma categories *)
Section CommaCategory.

  Context {C₁ C₂ C₃ : category}
          (F : C₁ ⟶ C₃)
          (G : C₂ ⟶ C₃).

  (** Definition of comma categories via displayed categories *)
  Definition comma_disp_cat_ob_mor
    : disp_cat_ob_mor (category_binproduct C₁ C₂).
  Proof.
    use tpair.
    - exact (λ x, F (pr1 x) --> G (pr2 x)).
    - exact (λ x y i₁ i₂ f, #F (pr1 f) · i₂ = i₁ · #G (pr2 f)).
  Defined.

  Definition comma_disp_cat_id_comp
    : disp_cat_id_comp _ comma_disp_cat_ob_mor.
  Proof.
    use tpair.
    - intros x i; cbn.
      rewrite !functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - cbn; intros x y z f g i₁ i₂ i₃ p q.
      rewrite !functor_comp.
      rewrite !assoc'.
      rewrite q.
      rewrite !assoc.
      rewrite p.
      apply idpath.
  Qed.

  Definition comma_disp_cat_data
    : disp_cat_data (category_binproduct C₁ C₂)
    := comma_disp_cat_ob_mor,, comma_disp_cat_id_comp.

  Definition comma_disp_cat_axioms
    : disp_cat_axioms _ comma_disp_cat_data.
  Proof.
    repeat split ; intros ; try (apply homset_property).
    apply isasetaprop.
    apply homset_property.
  Qed.

  Definition comma_disp_cat
    : disp_cat (category_binproduct C₁ C₂).
  Proof.
    use tpair.
    - exact comma_disp_cat_data.
    - exact comma_disp_cat_axioms.
  Defined.

  Definition comma
    : category
    := total_category comma_disp_cat.

  (** Univalence of the comma category *)
  Definition is_univalent_disp_comma_disp_cat
             (HC₃ : is_univalent C₃)
    : is_univalent_disp comma_disp_cat.
  Proof.
    intros x y p i₁ i₂.
    induction p.
    use isweqimplimpl.
    - intros p.
      pose (pr1 p) as m.
      cbn in m.
      rewrite !functor_id in m.
      rewrite id_left, id_right in m.
      exact (!m).
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition is_univalent_comma
             (HC₁ : is_univalent C₁)
             (HC₂ : is_univalent C₂)
             (HC₃ : is_univalent C₃)
    : is_univalent comma.
  Proof.
    use is_univalent_total_category.
    - apply is_unvialent_category_binproduct.
      + exact HC₁.
      + exact HC₂.
    - exact (is_univalent_disp_comma_disp_cat HC₃).
  Defined.

  (** Isos in comma *)
  Section IsIsoComma.
    Context {x y : comma}
            (f : x --> y)
            (Hf1 : is_z_isomorphism (pr11 f))
            (Hf2 : is_z_isomorphism (pr21 f)).

    Definition inv_comma
      : y --> x.
    Proof.
      refine ((inv_from_z_iso (make_z_iso' _ Hf1) ,, inv_from_z_iso (make_z_iso' _ Hf2)) ,, _).
      abstract
        (cbn;
         rewrite !functor_on_inv_from_z_iso;
         use z_iso_inv_on_left;
         rewrite assoc';
         refine (!_) ;
         use z_iso_inv_on_right;
         cbn;
         exact (!(pr2 f))).
    Defined.

    Lemma is_iso_comma_left_inv
      : f · inv_comma = identity x.
    Proof.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use pathsdirprod; cbn.
      - exact (z_iso_inv_after_z_iso (make_z_iso' _ Hf1)).
      - exact (z_iso_inv_after_z_iso (make_z_iso' _ Hf2)).
    Qed.

    Lemma is_iso_comma_right_inv
      : inv_comma · f = identity y.
    Proof.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use pathsdirprod; cbn.
      - exact (z_iso_after_z_iso_inv (make_z_iso' _ Hf1)).
      - exact (z_iso_after_z_iso_inv (make_z_iso' _ Hf2)).
    Qed.

    Definition is_z_iso_comma
      : is_z_isomorphism f.
    Proof.
      exists inv_comma.
      split.
      - exact is_iso_comma_left_inv.
      - exact is_iso_comma_right_inv.
    Defined.

  End IsIsoComma.

  (** Projection functors *)
  Definition comma_pr1
    : comma ⟶ C₁
    := pr1_category comma_disp_cat ∙ pr1_functor C₁ C₂.

  Definition comma_pr2
    : comma ⟶ C₂
    := pr1_category comma_disp_cat ∙ pr2_functor C₁ C₂.

  (** Natural isomorphism witnessing the commutation *)
  Definition comma_commute_nat_trans_data
    : nat_trans_data (comma_pr1 ∙ F) (comma_pr2 ∙ G).
  Proof.
    intros x; cbn in x.
    exact (pr2 x).
  Defined.

  Definition comma_commute_is_nat_trans
    : is_nat_trans _ _ comma_commute_nat_trans_data.
  Proof.
    intros x y f; unfold comma_commute_nat_trans_data; cbn; cbn in f.
    exact (pr2 f).
  Qed.

  Definition comma_commute
    : comma_pr1 ∙ F ⟹ comma_pr2 ∙ G.
  Proof.
    use make_nat_trans.
    - exact comma_commute_nat_trans_data.
    - exact comma_commute_is_nat_trans.
  Defined.

  (**
     Mapping property of comma category

     We need to check three mapping properties:
     - The first one gives the existence of a functor
     - The second one gives the existence of a natural transformation
     - The third one can be used to show that two natural transformations
       are equal
   *)
  Section UniversalMappingProperty.
    Context {D : category}
            (P : D ⟶ C₁)
            (Q : D ⟶ C₂)
            (η : P ∙ F ⟹ Q ∙ G).

    (** The functor witnessing the universal property *)
    Definition comma_ump1_data
      : functor_data D comma.
    Proof.
      use make_functor_data.
      - exact (λ d, (P d ,, Q d) ,, η d).
      - exact (λ d₁ d₂ f, (#P f ,, #Q f) ,, nat_trans_ax η _ _ f).
    Defined.

    Definition comma_ump1_is_functor
      : is_functor comma_ump1_data.
    Proof.
      split.
      - intro x; cbn.
        use subtypePath.
        {
          intro; apply homset_property.
        }
        cbn.
        rewrite !functor_id.
        apply idpath.
      - intros x y z f g; cbn.
        use subtypePath.
        {
          intro; apply homset_property.
        }
        cbn.
        rewrite !functor_comp.
        apply idpath.
    Qed.

    Definition comma_ump1
      : D ⟶ comma.
    Proof.
      use make_functor.
      - exact comma_ump1_data.
      - exact comma_ump1_is_functor.
    Defined.

    (** The computation rules *)
    Definition comma_ump1_pr1_nat_trans_data
      : nat_trans_data (comma_ump1 ∙ comma_pr1) P
      := λ x, identity _.

    Definition comma_ump1_pr1_is_nat_trans
      : is_nat_trans _ _ comma_ump1_pr1_nat_trans_data.
    Proof.
      intros x y f; cbn; unfold comma_ump1_pr1_nat_trans_data.
      rewrite id_left, id_right.
      apply idpath.
    Qed.

    Definition comma_ump1_pr1_nat_trans
      : comma_ump1 ∙ comma_pr1 ⟹ P.
    Proof.
      use make_nat_trans.
      - exact comma_ump1_pr1_nat_trans_data.
      - exact comma_ump1_pr1_is_nat_trans.
    Defined.

    (** Computation rule for first projection *)
    Definition comma_ump1_pr1
      : nat_z_iso (comma_ump1 ∙ comma_pr1) P.
    Proof.
      use make_nat_z_iso.
      - exact comma_ump1_pr1_nat_trans.
      - intro.
        apply identity_is_z_iso.
    Defined.

    Definition comma_ump1_pr2_nat_trans_data
      : nat_trans_data (comma_ump1 ∙ comma_pr2) Q
      := λ x, identity _.

    Definition comma_ump1_pr2_is_nat_trans
      : is_nat_trans _ _ comma_ump1_pr2_nat_trans_data.
    Proof.
      intros x y f; cbn; unfold comma_ump1_pr2_nat_trans_data.
      rewrite id_left, id_right.
      apply idpath.
    Qed.

    Definition comma_ump1_pr2_nat_trans
      : comma_ump1 ∙ comma_pr2 ⟹ Q.
    Proof.
      use make_nat_trans.
      - exact comma_ump1_pr2_nat_trans_data.
      - exact comma_ump1_pr2_is_nat_trans.
    Defined.

    (** Computation rule for second projection *)
    Definition comma_ump1_pr2
      : nat_z_iso (comma_ump1 ∙ comma_pr2) Q.
    Proof.
      use make_nat_z_iso.
      - exact comma_ump1_pr2_nat_trans.
      - intro.
        apply identity_is_z_iso.
    Defined.

    (** Computation rule for natural iso *)
    Definition comma_ump1_commute
      : pre_whisker comma_ump1 comma_commute
        =
        nat_trans_comp
          _ _ _
          (nat_trans_functor_assoc_inv _ _ _)
          (nat_trans_comp
             _ _ _
             (post_whisker comma_ump1_pr1 F)
             (nat_trans_comp
                _ _ _
                η
                (nat_trans_comp
                   _ _ _
                   (post_whisker (nat_z_iso_inv comma_ump1_pr2) G)
                   (nat_trans_functor_assoc _ _ _)))).
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro; cbn; unfold comma_ump1_pr1_nat_trans_data.
      rewrite (functor_id F), (functor_id G).
      rewrite !id_left.
      rewrite id_right.
      apply idpath.
    Qed.

    (** Now we look at the second universal mapping property *)
    Context (Φ₁ Φ₂ : D ⟶ comma)
            (τ₁ : Φ₁ ∙ comma_pr1 ⟹ Φ₂ ∙ comma_pr1)
            (τ₂ : Φ₁ ∙ comma_pr2 ⟹ Φ₂ ∙ comma_pr2)
            (p : ∏ (x : D),
                 pr2 (Φ₁ x) · #G (τ₂ x)
                 =
                 #F (τ₁ x) · pr2 (Φ₂ x)).

    Definition comma_ump2_nat_trans_data
      : nat_trans_data Φ₁ Φ₂.
    Proof.
      intro x.
      simple refine ((_ ,, _) ,, _) ; cbn.
      - exact (τ₁ x).
      - exact (τ₂ x).
      - abstract
          (exact (!(p x))).
    Defined.

    Definition comma_ump2_is_nat_trans
      : is_nat_trans _ _ comma_ump2_nat_trans_data.
    Proof.
      intros x y f.
      use subtypePath.
      {
        intro ; apply homset_property.
      }
      use pathsdirprod.
      - exact (nat_trans_ax τ₁ _ _ f).
      - exact (nat_trans_ax τ₂ _ _ f).
    Qed.

    Definition comma_ump2
      : Φ₁ ⟹ Φ₂.
    Proof.
      use make_nat_trans.
      - exact comma_ump2_nat_trans_data.
      - exact comma_ump2_is_nat_trans.
    Defined.

    (** The computation rules *)
    Definition comma_ump2_pr1
      : post_whisker comma_ump2 comma_pr1 = τ₁.
    Proof.
      use nat_trans_eq.
      {
        intro; apply homset_property.
      }
      intro x; cbn.
      apply idpath.
    Qed.

    Definition comma_ump2_pr2
      : post_whisker comma_ump2 comma_pr2 = τ₂.
    Proof.
      use nat_trans_eq.
      {
        intro; apply homset_property.
      }
      intro x; cbn.
      apply idpath.
    Qed.

    (** The uniqueness *)
    Context {n₁ n₂ : Φ₁ ⟹ Φ₂}
            (n₁_pr1 : post_whisker n₁ comma_pr1 = τ₁)
            (n₁_pr2 : post_whisker n₁ comma_pr2 = τ₂)
            (n₂_pr1 : post_whisker n₂ comma_pr1 = τ₁)
            (n₂_pr2 : post_whisker n₂ comma_pr2 = τ₂).

    Definition comma_ump_eq_nat_trans
      : n₁ = n₂.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use subtypePath.
      {
        intro; apply homset_property.
      }
      use pathsdirprod.
      - pose (nat_trans_eq_pointwise n₁_pr1 x) as q₁.
        pose (nat_trans_eq_pointwise n₂_pr1 x) as q₂.
        cbn in q₁, q₂.
        exact (q₁ @ !q₂).
      - pose (nat_trans_eq_pointwise n₁_pr2 x) as q₁.
        pose (nat_trans_eq_pointwise n₂_pr2 x) as q₂.
        cbn in q₁, q₂.
        exact (q₁ @ !q₂).
    Qed.

  End UniversalMappingProperty.

End CommaCategory.

Definition univalent_comma
           {C₁ C₂ C₃ : univalent_category}
           (F : C₁ ⟶ C₃)
           (G : C₂ ⟶ C₃)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (comma F G).
  - apply is_univalent_comma.
    + exact (pr2 C₁).
    + exact (pr2 C₂).
    + exact (pr2 C₃).
Defined.
