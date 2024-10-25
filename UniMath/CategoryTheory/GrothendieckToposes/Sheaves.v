(**************************************************************************************************

  Sheaves for a Grothendieck Topology

  Given a site C (a category with, for every X : C, a chosen collection of sieves), there are
  multiple equivalent ways to say when a presheaf F on C is a sheaf. Two of these occur on page 122
  of Mac Lane and Moerdijk. In the list below, g will range over the selected morphisms of S, and h
  will range over the morphisms to the domain of g.
  This file defines F to be a sheaf if, for any object X and any X-sieve S, any of these equivalent
  properties holds:

  - Every natural transformation S ⟹ F factorizes uniquely via the transformation S ⟹ よ(X) of S.
  - For E the equalizer of the product morphisms
      f1, f2 : (∏ g, F (dom g)) → (∏ g h, F (dom h))
      α1(x)_{g, h} = x_{h ⋅ g}
      α2(x)_{g, h} = #F(h)(x_g)
    the morphism β: F(X) → E, given by β(x)_g = #F(g)(x), is an isomorphism.
  - (locality) Given x, y : F(X), if #F(g)(x) = #F(g)(y) for all g, then x = y.
    (glueing)  Given, for all g, x_g : F(dom g) for all g, if for all h, x_{h ⋅ g} = #F(h)(x_g),
                we have x : F(X) such that #F(g)(x) = x_g for all g.

  This file defines these three properties, shows the equivalences. It also defines the category of
  sheaves on a site C as a full subcategory of the presheaf category on C. Lastly, it defines object
  and morphism types for this category.

  Contents
  1. The sheaf properties
  1.1. The natural transformation property [is_sheaf]
  1.2. The equalizer property [is_sheaf']
  1.3. The elementary property [is_sheaf'']
  2. The equivalences
  2.1. The first implies the second [is_sheaf_to_is_sheaf']
  2.2. The second implies the third [is_sheaf'_to_is_sheaf'']
  2.3. The third implies the first [is_sheaf''_to_is_sheaf]
  2.4. The implications the other way around
    [is_sheaf''_to_is_sheaf'] [is_sheaf'_to_is_sheaf] [is_sheaf_to_is_sheaf'']
  3. Sheaves
  3.1. The category of sheaves [sheaf_cat]
  3.2. Sheaves [sheaf]
  3.3. Sheaf morphisms [sheaf_morphism]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.GrothendieckToposes.Sieves.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sites.

Local Open Scope cat.

Section Sheaves.

  Context (C : site).

(** * 1. The sheaf properties *)

  Section SheafProperties.

    Context (P : C^op ⟶ HSET).

(** ** 1.1. The natural transformation property *)

    Definition is_sheaf : UU :=
      ∏ (c : C)
        (S : covering_sieve c)
        (τ : sieve_functor S ⟹ P),
      ∃! (η : yoneda_objects _ c ⟹ P),
        nat_trans_comp _ _ _ (sieve_nat_trans S) η = τ.

    Lemma isaprop_is_sheaf : isaprop is_sheaf.
    Proof.
      apply impred_isaprop; intros t.
      apply impred_isaprop; intros S.
      apply impred_isaprop; intros τ.
      apply isapropiscontr.
    Qed.

(** ** 1.2. The equalizer property *)

    Section EqualizerSheafProperty.

      Context {c : C}.
      Context (S : covering_sieve c).

      (* Domain *)

      Definition sheaf_property_equalizer_domain_factor
        (f : sieve_selected_morphism S)
        : hSet
        := P (sieve_selected_morphism_domain f).

      Definition sheaf_property_equalizer_domain
        : hSet
        := ProductObject _ _ (ProductsHSET _ sheaf_property_equalizer_domain_factor).

      (* Codomain *)

      Definition sheaf_property_equalizer_codomain_index
        : UU
        := ∑ (f : sieve_selected_morphism S) (W : C), C⟦W, sieve_selected_morphism_domain f⟧.

      Definition make_sheaf_property_equalizer_codomain_index
        (f : sieve_selected_morphism S)
        (W : C)
        (g : C⟦W, sieve_selected_morphism_domain f⟧)
        : sheaf_property_equalizer_codomain_index
        := f ,, W ,, g.

      Definition sheaf_property_equalizer_codomain_index_selected_morphism
        (fWg : sheaf_property_equalizer_codomain_index)
        : sieve_selected_morphism S
        := pr1 fWg.

      Definition sheaf_property_equalizer_codomain_index_object
        (fWg : sheaf_property_equalizer_codomain_index)
        : C
        := pr12 fWg.

      Definition sheaf_property_equalizer_codomain_index_morphism
        (fWg : sheaf_property_equalizer_codomain_index)
        : sheaf_property_equalizer_codomain_index_object fWg
            -->
          sieve_selected_morphism_domain (sheaf_property_equalizer_codomain_index_selected_morphism fWg)
        := pr22 fWg.

      Definition sheaf_property_equalizer_codomain_factor
        (fWg : sheaf_property_equalizer_codomain_index)
        : hSet
        := P (sheaf_property_equalizer_codomain_index_object fWg).

      Definition sheaf_property_equalizer_codomain
        : hSet
        := ProductObject _ _ (ProductsHSET _ sheaf_property_equalizer_codomain_factor).

      (* Arrows *)

      Definition sheaf_property_equalizer_arrow1
        : sheaf_property_equalizer_domain → sheaf_property_equalizer_codomain.
      Proof.
        apply (ProductArrow _ SET).
        intro fWg.
        use (ProductPr _ _ _ (sieve_selected_morphism_compose _ _)).
        - apply (sheaf_property_equalizer_codomain_index_selected_morphism fWg).
        - exact (sheaf_property_equalizer_codomain_index_morphism fWg).
      Defined.

      Definition sheaf_property_equalizer_arrow2
        : sheaf_property_equalizer_domain → sheaf_property_equalizer_codomain.
      Proof.
        apply (ProductArrow _ SET).
        intro fWg.
        refine (ProductPr _ _ _ (sheaf_property_equalizer_codomain_index_selected_morphism fWg) · _).
        apply (# P).
        exact (sheaf_property_equalizer_codomain_index_morphism fWg).
      Defined.

      Definition sheaf_property_equalizer_inducer_arrow
        : (P c : hSet) → sheaf_property_equalizer_domain.
      Proof.
        apply (ProductArrow _ SET).
        intro f.
        apply (# P f).
      Defined.

      Lemma sheaf_property_equalizer_inducer_arrow_commutes
        : (sheaf_property_equalizer_arrow1 ∘ sheaf_property_equalizer_inducer_arrow =
          sheaf_property_equalizer_arrow2 ∘ sheaf_property_equalizer_inducer_arrow)%functions.
      Proof.
        apply (ProductArrow_eq _ SET).
        intro VWfg.
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (ProductPrCommutes _ _ _ _ _ _ _) @ _).
        refine (ProductPrCommutes _ _ _ _ _ _ (pr12 VWfg ,, _) @ !_).
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (ProductPrCommutes _ _ _ _ _ _ _) @ _).
        refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (ProductPrCommutes _ _ _ _ _ _ _) @ !_).
        refine (_ @ functor_comp _ _ _).
        apply maponpaths.
        exact (eqtohomot (nat_trans_ax (sieve_nat_trans S) _ _ _) _).
      Qed.

      Definition sheaf_property_equalizer_induced_arrow
        : SET⟦P c, Equalizers_in_HSET _ _ sheaf_property_equalizer_arrow1 sheaf_property_equalizer_arrow2⟧
        := EqualizerIn (C := SET) _ _ _ sheaf_property_equalizer_inducer_arrow_commutes.

    End EqualizerSheafProperty.

    Definition is_sheaf' : UU
      := ∏ c (S : covering_sieve c),
        is_z_isomorphism (sheaf_property_equalizer_induced_arrow S).

    Lemma isaprop_is_sheaf'
      : isaprop is_sheaf'.
    Proof.
      do 2 (apply impred_isaprop; intro).
      apply isaprop_is_z_isomorphism.
    Qed.

(** ** 1.3. The elementary property *)

    Definition sheaf_locality_ax
      : UU
      := ∏ (c : C)
          (S : covering_sieve c)
          (f g : (P c : hSet)),
          (∏
            (h : sieve_selected_morphism S),
              # P h f
            = # P h g)
          → f = g.

    Lemma isaprop_locality_ax
      : isaprop sheaf_locality_ax.
    Proof.
      repeat (apply impred_isaprop; intro).
      apply setproperty.
    Qed.

    Definition sheaf_glueing_ax
      : UU
      := ∏
        (c : C)
        (S : covering_sieve c)
        (x : ∏
          (f : sieve_selected_morphism S),
          (P (sieve_selected_morphism_domain f) : hSet)),
        (∏ (f : sieve_selected_morphism S)
          (W : C)
          (g : C⟦W, sieve_selected_morphism_domain f⟧),
          x (sieve_selected_morphism_compose f g)
          = # P g (x f))
        → ∑ (z : P c : hSet),
            ∏ (f : sieve_selected_morphism S),
              # P f z
              = x f.

    Lemma isaprop_glueing_ax
      (H : sheaf_locality_ax)
      : isaprop sheaf_glueing_ax.
    Proof.
      apply impred_isaprop.
      intro c.
      apply impred_isaprop.
      intro S.
      apply impred_isaprop.
      intro x.
      apply impred_isaprop.
      intro Hx.
      apply invproofirrelevance.
      intros z z'.
      apply subtypePath.
      {
        intro.
        repeat (apply impred_isaprop; intro).
        apply setproperty.
      }
      apply (H c S).
      intro f.
      exact (pr2 z _ @ !pr2 z' _).
    Qed.

    Definition is_sheaf''
      : UU
      := sheaf_locality_ax × sheaf_glueing_ax.

    Lemma isaprop_is_sheaf''
      : isaprop is_sheaf''.
    Proof.
      use (isaprop_total2 (make_hProp _ _) (λ H, make_hProp _ _)).
      - exact isaprop_locality_ax.
      - exact (isaprop_glueing_ax H).
    Qed.

(** * 2. The equivalences *)
(** ** 2.1. The first implies the second *)

    Lemma is_sheaf_to_is_sheaf'
      : is_sheaf → is_sheaf'.
    Proof.
      intros H c S.
      specialize (H c S).
      use (make_is_z_isomorphism _ _ (make_dirprod _ _)).
      - intro fH.
        refine (pr11 (H _) _ (identity c)).
        use make_nat_trans.
        * intros d f.
          refine (pr1 fH (d ,, f)).
        * abstract (
            intros d d' f;
            apply funextfun;
            intro g;
            exact (eqtohomot (pr2 fH) (make_sheaf_property_equalizer_codomain_index _ (make_sieve_selected_morphism _ _) _ _))
          ).
      - apply funextfun.
        intro x.
        use (!eqtohomot (nat_trans_eq_pointwise (path_to_ctr _ _ (H _) (make_nat_trans _ _ _ _) _) _) _ @ _).
        + intros d g.
          refine (# P g x).
        + intros d d' g.
          apply funextfun.
          intro g'.
          exact (eqtohomot (functor_comp P g' g) x).
        + apply nat_trans_eq_alt.
          reflexivity.
        + exact (eqtohomot (functor_id P c) x).
      - apply funextfun.
        intro w.
        apply subtypePath.
        {
          intro.
          apply impred_isaset.
          intro.
          apply setproperty.
        }
        apply funextsec.
        intro f.
        refine (!eqtohomot (nat_trans_ax (pr11 (H _)) _ _ _) _ @ _).
        refine (maponpaths (pr11 (H _) _) (id_right _) @ _).
        exact (eqtohomot (nat_trans_eq_pointwise (pr21 (H _)) _) _).
    Qed.

(** ** 2.2. The second implies the third *)

    Lemma is_sheaf'_to_is_sheaf''
      : is_sheaf' → is_sheaf''.
    Proof.
      intro H.
      split;
        intros c S;
        specialize (H c S);
        pose (i := make_z_iso' _ H).
      - intros f g Hfg.
        refine (!_ @ eqtohomot (z_iso_inv_after_z_iso i) g).
        refine (!_ @ eqtohomot (z_iso_inv_after_z_iso i) f).
        apply (maponpaths (inv_from_z_iso i)).
        apply subtypePath.
        {
          intro.
          apply propproperty.
        }
        apply funextsec.
        intro Vf.
        apply Hfg.
      - intros f Hf.
        use tpair.
        + refine (inv_from_z_iso i _).
          exists (λ Vf, f Vf).
          apply funextsec.
          intro VWfg.
          apply (Hf (make_sieve_selected_morphism _ _)).
        + intros g.
          refine (maponpaths (λ x, pr1 (x _) _) (z_iso_after_z_iso_inv i)).
    Qed.

(** ** 2.3. The third implies the first *)

    Lemma is_sheaf''_to_is_sheaf
      : is_sheaf'' → is_sheaf.
    Proof.
      intros H X S t.
      induction H as [HL HG].
      specialize (HG
        X
        S
        (λ f, t _ (sieve_selected_morphism_preimage f))
        (λ f Z g, eqtohomot (nat_trans_ax t _ _ g) _)).
      use unique_exists.
      - apply (invmap (yoneda_weq C X P)).
        exact (pr1 HG).
      - apply nat_trans_eq_alt.
        intro Y.
        apply funextfun.
        intro x.
        exact (pr2 HG (make_sieve_selected_morphism (S := S) Y x)).
      - intro y.
        apply (homset_property (PreShv C)).
      - intros f Hf.
        apply pathsweq1.
        apply (HL X S).
        intro g.
        refine (_ @ !pr2 HG g).
        refine (!eqtohomot (nat_trans_ax f _ _ _) _ @ _).
        refine (_ @ eqtohomot (nat_trans_eq_weq (homset_property _) _ t Hf _) _).
        apply (maponpaths (f _)).
        apply id_right.
    Qed.

(** ** 2.4. The implications the other way around *)

    Definition is_sheaf''_to_is_sheaf'
      : is_sheaf'' → is_sheaf'
      := (is_sheaf_to_is_sheaf' ∘ is_sheaf''_to_is_sheaf)%functions.

    Definition is_sheaf'_to_is_sheaf
      : is_sheaf' → is_sheaf
      := (is_sheaf''_to_is_sheaf ∘ is_sheaf'_to_is_sheaf'')%functions.

    Definition is_sheaf_to_is_sheaf''
      : is_sheaf → is_sheaf''
      := (is_sheaf'_to_is_sheaf'' ∘ is_sheaf_to_is_sheaf')%functions.

  End SheafProperties.

(** * 3. Sheaves *)
(** ** 3.1. The category of sheaves *)

  (** The category of sheaves is the full subcategory of presheaves consisting of the presheaves
      which satisfy the is_sheaf proposition. *)
  Definition hsubtype_obs_is_sheaf
    (P : PreShv C)
    : hProp
    := make_hProp _ (isaprop_is_sheaf P).

  Definition sheaf_cat :
    category :=
    full_subcat (PreShv C) hsubtype_obs_is_sheaf.

  Lemma sheaf_cat_univalent
    : is_univalent sheaf_cat.
  Proof.
    apply is_univalent_full_subcat.
    - apply is_univalent_functor_category.
      apply is_univalent_HSET.
    - intro.
      apply propproperty.
  Defined.

End Sheaves.

(** ** 3.2. Sheaves *)

Definition sheaf
  (C : site)
  : UU
  := sheaf_cat C.

Definition make_sheaf
  {C : site}
  (F : PreShv C)
  (H : is_sheaf C F)
  : sheaf C
  := F ,, H.

Coercion sheaf_functor
  {C : site}
  (F : sheaf C)
  : C^op ⟶ HSET
  := pr1 F.

Definition sheaf_is_sheaf
  {C : site}
  (F : sheaf C)
  : is_sheaf C F
  := pr2 F.

(** ** 3.3. Sheaf morphisms *)

Section Morphisms.

  Context {C : site}.

  Definition sheaf_morphism
    (F G : sheaf C)
    : UU
    := sheaf_cat C⟦F, G⟧.

  Definition make_sheaf_morphism
    {F G : sheaf C}
    (f : F ⟹ G)
    : sheaf_morphism F G
    := f ,, tt.

  Coercion sheaf_morphism_nat_trans
    {F G : sheaf C}
    (f : sheaf_morphism F G)
    : F ⟹ G
    := pr1 f.

  Lemma sheaf_morphism_eq
    {F G : sheaf C}
    (f g : sheaf_morphism F G)
    (H : (f : _ ⟹ _) = g)
    : f = g.
  Proof.
    use subtypePath.
    {
      intro.
      apply isapropunit.
    }
    exact H.
  Qed.

End Morphisms.
