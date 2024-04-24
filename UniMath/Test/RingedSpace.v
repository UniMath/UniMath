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

Require Import UniMath.Test.Opens.
Require Import UniMath.Test.Presheaves.

Local Open Scope subtype.
Local Open Scope cat.

Section Sheaves.

  Context (C : category).
  Context (HC : is_univalent C).

  Definition presheafed_space
    : UU
    := ∑ (T : TopologicalSpace), presheaf_cat C T.

  Definition presheafed_space_hom
    (X X' : presheafed_space)
    : UU
    := ∑ (f: continuous_function (pr1 X) (pr1 X')), presheaf_cat C (pr1 X') ⟦pr2 X', pushforward f (pr2 X)⟧.

  Lemma presheafed_space_hom_eq
    (X X' : presheafed_space)
    (F F' : presheafed_space_hom X X')
    (H1 : pr1 F = pr1 F')
    (H2 : nat_trans_comp _ _ _ (pr2 F) (idtomor (C := [_, _]) _ _ (maponpaths (λ x, pushforward x (pr2 X)) H1)) = pr2 F')
    : F = F'.
  Proof.
    induction F as [base c].
    induction F' as [base' c'].
    cbn in H1.
    induction H1.
    cbn in H2.
    now induction (!nat_trans_comp_id_right (homset_property _) _ _ c @ H2).
  Qed.

  Definition presheafed_space_id
    (X : presheafed_space)
    : presheafed_space_hom X X.
  Proof.
    exists (identity (pr1 X : top_cat)).
    apply inv_from_z_iso.
    apply pushforward_id.
  Defined.

  Definition presheafed_space_comp
    {X X' X'' : presheafed_space}
    (F : presheafed_space_hom X X')
    (F' : presheafed_space_hom X' X'')
    : presheafed_space_hom X X''.
  Proof.
    exists ((pr1 F : top_cat⟦_, _⟧) · pr1 F').
    refine (nat_trans_comp _ _ _ (pr2 F') _).
    refine (nat_trans_comp _ _ _ (pre_whisker _ (pr2 F)) _).
    exact (inv_from_z_iso (pushforward_comp (pr1 F) (pr1 F') _)).
  Defined.

  Local Notation "α >> β" := (nat_trans_comp _ _ _ α β) (at level 50, left associativity).

  Definition presheafed_space_id_right
    (X X' : presheafed_space)
    (F : presheafed_space_hom X X')
    : presheafed_space_comp F (presheafed_space_id X') = F.
  Proof.
    unfold presheafed_space_comp.
    simpl.
    use presheafed_space_hom_eq.
    - apply (id_right (C := top_cat)).
    - apply nat_trans_eq_alt.
      intro U.
      simpl.
      repeat rewrite assoc.
      refine (maponpaths (λ x, x · _ · _) (id_right _) @ _).
      repeat rewrite assoc'.
      refine (_ @ id_left _).
      rewrite assoc.
      refine (maponpaths (λ x, _ · x) _ @ _).
      Search (idtomor _ _).
      + refine (maponpaths (λ x, _ · x U) (!eq_idtoiso_idtomor _ _ _) @ _).
      rewrite assoc.
      rewrite assoc.
      refine (maponpaths (λ x, x · _) (_ : # (pr2 X' :  _ ⟶ _) (identity U) = identity ((pr2 X' : _ ⟶ _) U)) @ _).
      refine (maponpaths (λ x, x · _ · _) _ @ _).

      unfold continuous_open_preimage.

      cbn.
      refine (maponpaths (λ x, (_ · x) · _) _ @ _).
      {
        cbn.
        unfold functor_on_morphisms.
        match goal with
        | [ |- _ ?a ?b _ = _ ] => pose (U0 := a); pose (U1 := b)
        end.
        pose (
          H0 := subtypePath (λ _, propproperty _) (idpath _ : pr1 (continuous_open_preimage (pr1 F) U) = pr1 U0)
        ).
        pose (
          H1 := subtypePath (λ _, propproperty _) (idpath _ : pr1 (continuous_open_preimage (pr1 F) U) = pr1 U1)
        ).
        unfold U0, U1 in H0, H1.
        refine (transportf (λ x, _ x _ _) H0 (transportf (λ x, _ x _ _) H1 _)).
        rewrite X0.
        refine (maponpaths (λ (x : topological_space_category _), pr21 (pr2 X : _ ⟶ _) x _ _) _ @ _).
        rewrite (_ : )
        assert ((continuous_open_preimage (pr1 F)
     (continuous_open_preimage
        ((λ x : pr11 X', x),,
         (λ (x0 : pr11 X') (x1 : hsubtype (pr11 X'))
          (X0 : ishinh_UU (∑ O : Open, O x0 × (∏ x : pr11 X', O x → x1 x))), X0)) U)) = (continuous_open_preimage (pr1 F) U)).
        cbn.
        unfold continuous_open_preimage.
        cbn.
        unfold continuous_function_is_continuous.
        exact (functor_id (pr2 X) _).
        now cbn.
      }
      apply id_right.
      refine (maponpaths (λ x, (x · _) · _) _ @ _).
      + exact (functor_id _ _ U).
      rewrite (functor_id (pr2 X') U).
      match goal with
      | [ |- nat_trans_comp _ _ _ ?a _ = _ ] => pose a
      end.
      simpl.
      simpl in p.

      simpl.
      assert (continuous_to_functor (identity (pr1 X' : top_cat)) = functor_identity _).
      {
        refine (isotoid [_, _] _ _).
        - apply is_univalent_functor_category.
          apply is_univalent_topological_space_category.
        - apply z_iso_from_nat_z_iso.
          apply identity_to_functor_is_identity.
      }
      simpl in X0.
      symmetry in X0.
      induction X0.
      rewrite X0.
      epose (isotoid _ _ (z_iso_from_nat_z_iso _ _)).
  Qed.

  Definition space_with_local_data_disp_cat
    : disp_cat (total_category disp_top).
  Proof.
    use tpair.
    - use tpair.
      + exists D_presheaf.
        intros T T' P P' F.
        exact ((P' : _ ⟶ _) ⟹ (D_presheaf_pushforward F P : _ ⟶ _)).
      + split.
        * intros T P.
          exact (z_iso_mor (idtoiso (C := [_, _]) (!D_presheaf_pushforward_id T P))).
        * intros X Y Z F F' P P' P'' H H'.
          apply (nat_trans_comp _ _ _ H').
          apply (nat_trans_comp _ _ _ (pre_whisker _ H)).
          refine (post_whisker (G := functor_opp (continuous_to_functor F') ∙ functor_opp (continuous_to_functor F)) (nat_trans_id (functor_opp (continuous_to_functor (F · F')))) P).
    - repeat split.
      + intros T T' F P P' H.
        apply nat_trans_eq_alt.
        intro t.
        unfold transportb.
        unfold nat_trans_data_from_nat_trans_funclass.
        unfold mor_disp.
        simpl.
        rewrite (functtransportf (λ f, )).
        rewrite functtransportf
        rewrite pr1_transportf.
        cbn in *.
        Search (pr1 (transportf _ _ _)).
        refine (_ @ !maponpaths (λ x, x t) (pr1_transportf (A := (pr1 T : hSet) → (pr1 T' : hSet)) (B := continuous) (P := λ f H, (P' : _ ⟶ _) ⟹ functor_composite_data (functor_opp_data (continuous_to_functor (f ,, H))) (P : _ ⟶ _)) (!id_left _) H)).
        unfold mor_disp.
        cbn in *.
        epose (transportf_fun).
        epose (functtransportf).
        unfold transportb.

        Search (transportb ()).
  Defined.

End Sheaves.
