Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Topology.Topology.
Require Import UniMath.Topology.CategoryTop.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope subtype.
Local Open Scope cat.

Definition topological_space_category
  (T : TopologicalSpace)
  : category.
Proof.
  use make_category.
  - use make_precategory.
    + use make_precategory_data.
      * use make_precategory_ob_mor.
        -- exact (Open (T := T)).
        -- intros U V.
          exact (U ⊆ V).
      * exact (λ U x H, H).
      * exact (λ U V W HUV HVW x Hx, HVW _ (HUV _ Hx)).
    + abstract (
        use make_is_precategory_one_assoc;
        trivial
      ).
  - abstract (
      intros U V;
      apply isasetaprop;
      apply impred;
      intro;
      apply impredfun;
      apply propproperty
    ).
Defined.

Lemma is_univalent_topological_space_category
  (T : TopologicalSpace)
  : is_univalent (topological_space_category T).
Proof.
  intros U V.
  apply isweqimplimpl.
  - intro H.
    apply subtypePath.
    {
      intro.
      apply propproperty.
    }
    apply (invmap (hsubtype_univalence _ _)).
    split.
    + apply (pr1 H _).
    + apply (pr12 H _).
  - apply isaset_total2.
    + apply isasethsubtype.
    + intro.
      apply isasetaprop.
      apply propproperty.
  - apply isofhleveltotal2.
    + apply isaprop_subtype_containedIn.
    + intro f.
      apply isaprop_is_z_isomorphism.
Qed.

Definition continuous_to_functor
  {T T' : TopologicalSpace}
  (F : continuous_function T T')
  : topological_space_category T' ⟶ topological_space_category T.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (continuous_open_preimage F).
    + intros U V HUV t.
      apply (HUV _).
  - abstract easy.
Defined.

Definition continuous_identity
  (T : TopologicalSpace)
  : continuous_function T T
  := identity (T : total_category disp_top).

Definition identity_to_functor_is_identity
  (T : TopologicalSpace)
  : z_iso (C := [_, _]) (functor_identity _) (continuous_to_functor (continuous_identity T)).
Proof.
  use make_z_iso.
  - exact (nat_trans_id (functor_identity _)).
  - exact (nat_trans_id (functor_identity _)).
  - abstract (
      now split;
      apply (nat_trans_eq (homset_property _))
    ).
Defined.

Definition composite_to_functor_is_comp
  {T T' T'' : TopologicalSpace}
  (F : (total_category disp_top)⟦T, T'⟧)
  (F' : (total_category disp_top)⟦T', T''⟧)
  : z_iso (C := [_, _]) (continuous_to_functor (F · F')) ((continuous_to_functor F') ∙ (continuous_to_functor F)).
Proof.
  use make_z_iso.
  - exact (nat_trans_id (continuous_to_functor (F · F'))).
  - exact (nat_trans_id (continuous_to_functor (F · F'))).
  - abstract (
      now split;
      apply (nat_trans_eq (homset_property _))
    ).
Defined.

Section Sheaves.

  Context (D : category).
  Context (HD : is_univalent D).

  Definition D_presheaf
    (T : TopologicalSpace)
    : UU
    := ∑ (P : Open (T := T) → D)
      (res : ∏ (U V : Open), U ⊆ V → D⟦P V, P U⟧),
      (∏ U, res U U (λ x, idfun _) = identity (P U)) ×
      (∏ U V W HUV HVW, res V W HVW · res U V HUV = res U W (λ x t, HVW x (HUV x t))).

  Definition space_with_local_data_disp_cat
    : disp_cat (total_category disp_top).
  Proof.
    use tpair.
    - use tpair.
      + exists D_presheaf.
        intros T T' P P' F.
        exact (
          ∑ (Fh : ∏ (U : Open), D⟦pr1 P' U, pr1 P (continuous_open_preimage F U)⟧),
          ∏ (U V : Open) (HUV : U ⊆ V),
            Fh V · pr12 P (continuous_open_preimage F U) (continuous_open_preimage F V) (λ x t, HUV _ t) = pr12 P' U V HUV · Fh U
        ).
      + split.
        * intros T P.
          use tpair.
          -- intros U.
            apply (pr12 P).
            exact (λ x, idfun _).
          -- abstract (
              intros U V HUV;
              now do 2 refine (pr222 P _ _ _ _ _ @ !_)
            ).
        * intros T T' T'' F F' P P' P'' H H'.
          use tpair.
          -- intro U.
            refine (pr1 H' U · _).
            refine (pr1 H _ · _).
            apply (pr12 P).
            exact (λ x, idfun _).
          -- abstract (
              intros U V HUV;
              refine (_ @ !assoc _ _ _);
              refine (_ @ maponpaths (λ x, x · _) (pr2 H' _ _ _));
              do 2 refine (!_ @ assoc _ _ _);
              refine (maponpaths _ _);
              refine (_ @ !assoc _ _ _);
              refine (_ @ maponpaths (λ x, x · _) (pr2 H _ _ _));
              do 2 refine (!_ @ assoc _ _ _);
              refine (maponpaths _ _);
              now do 2 refine (pr222 P _ _ _ _ _ @ !_)
            ).
    - repeat split; cbn.
      + intros T T' F P P' H.
        apply subtypePath.
        {
          intro.
          do 3 (apply impred; intro).
          apply homset_property.
        }
        apply funextsec.
        intro.
        unfold mor_disp.
        unfold transportb.
        cbn.
        rewrite pr1_transportf.
        rewrite (pr222 P).
        cbn.
        rewrite transportf_sec_constant.
        rewrite (functtransportf (λ x0, pr1 P (continuous_open_preimage x0 x))).
        rewrite <- idtoiso_postcompose.
        apply maponpaths.
        clear H.
        clear P'.
        match goal with
        | [ |- ?a = _ ] => pose a
        end.
        assert (is_z_isomorphism p).
        {
          use make_is_z_isomorphism.
          - apply (pr12 P).
            exact (λ x t, t).
          - split;
              refine (pr222 P _ _ _ _ _ @ _);
              apply (pr122 P).
        }
        refine (maponpaths (λ x, z_iso_mor x) (!pathsweq1' (make_weq _ (HD _ _)) _ (p ,, X) _)).
        match goal with
        | [ |- ?a = _ ] => pose a
        end.
        Search (maponpaths _ _ = _).
        cbn.
        cbn in p0.
        Search (_ = invmap _ _).
        Locate invmap_eq.
        epose (invmap_eq ).
        Search (_ = idtoiso _).
  Defined.

End Sheaves.
