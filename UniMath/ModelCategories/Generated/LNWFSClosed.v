Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monads.ComonadCoalgebras.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Coequalizers.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Three.
Require Import UniMath.ModelCategories.NWFS.
Require Import UniMath.ModelCategories.Helpers.
Require Import UniMath.ModelCategories.Generated.MonoidalHelpers.
Require Import UniMath.ModelCategories.Generated.FFMonoidalStructure.
Require Import UniMath.ModelCategories.Generated.LNWFSHelpers.
Require Import UniMath.ModelCategories.Generated.LNWFSMonoidalStructure.
Require Import UniMath.ModelCategories.Generated.LNWFSCocomplete.

Local Open Scope cat.

Section Ff_closed.

Import BifunctorNotations.
Import MonoidalNotations.

Lemma monoidal_right_tensor_cocone
    {C : category}
    (V : monoidal C)
    (A : C)
    {g : graph}
    (d : diagram g _)
    (CC : ColimCocone d)
    (CMon := (C,, V) : monoidal_cat) :
  cocone
      (mapdiagram (monoidal_right_tensor (A : CMon)) d)
      (monoidal_right_tensor (A : CMon) (colim CC)).
Proof.
  use tpair.
  - intro v.
    exact (colimIn _ v ⊗^{V}_{r} A).
  - abstract (
      intros u v e;
      etrans; [apply maponpaths_2|];
      [
        etrans; [apply cancel_precomposition;
                apply (bifunctor_leftid V)|];
        apply (id_right (dmor d e ⊗^{V}_{r} A))
      |];
      etrans; [apply (pathsinv0 (bifunctor_rightcomp V _ _ _ _ _ _))|];
      apply maponpaths;
      apply (colimInCommutes _ _ _ e)
    ).
Defined.

Context {C : category}.
Context (CC : Colims C).
Local Definition Ff_mon : monoidal_cat :=
    (_,, @Ff_monoidal C).

Context {g : graph}.
Context (H : is_connected g).
Context (v0 : vertex g).
Context (FfCC := λ d, ColimFfCocone CC d H v0).
Context (A : Ff_mon).

Opaque LNWFS_tot_lcomp.
Opaque Ff_lcomp.
Opaque Ff_precategory_data.
Opaque LNWFS.

Section Helpers.

Context (d : diagram g Ff_mon).

(* define morphism into colimit pointwise on the middle objects *)
Lemma Ff_right_tensor_preserves_colimit_mor11
    (f : arrow C) :
  three_ob1 (fact_functor (monoidal_right_tensor A (colim (FfCC d))) f) -->
    three_ob1 (fact_functor (colim (FfCC (mapdiagram (monoidal_right_tensor A) d))) f).
Proof.
  use colimArrow.
  use tpair.
  - intro v.
    exact (colimIn (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f) v).
  - abstract (
      intros u v e;
      (* cbn. *)
      etrans; [|
        exact (colimInCommutes ((CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f)) _ _ e)
      ];
      apply cancel_postcomposition;
      apply pathsinv0;
      etrans; [use pr1_transportf_const|];
      etrans; [apply cancel_precomposition|];
      [
        etrans; [use (section_disp_on_eq_morphisms (dob d v) (γ' := identity _)); reflexivity|];
        apply maponpaths;
        apply (section_disp_id (dob d v))
      |];
      apply id_right
    ).
Defined.

Lemma Ff_right_tensor_preserves_colimit_mor :
  (monoidal_right_tensor A) (colim (FfCC d)) -->
      colim (FfCC (mapdiagram (monoidal_right_tensor A) d)).
Proof.
  use tpair.
  - intro f.
    exists (Ff_right_tensor_preserves_colimit_mor11 f).
    abstract (
      split; [
        etrans; [apply assoc'|];
        apply pathsinv0;
        etrans; [apply id_left|];
        etrans; [apply assoc'|];
        apply cancel_precomposition;
        apply pathsinv0;
        etrans; [apply assoc'|];
        apply cancel_precomposition;
        apply (colimArrowCommutes (CCFf_pt_ob1 CC d (fact_R A f)))
      |
      etrans; [apply id_right|];
      apply pathsinv0;
      use colimArrowUnique;
      intro v;
      etrans; [apply assoc|];
      etrans; [apply cancel_postcomposition;
               apply (colimArrowCommutes (CCFf_pt_ob1 CC d (fact_R A f)))|];
      apply (colimArrowCommutes (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f))
      ]
    ).
  - abstract (
      intros f f' γ;
      apply subtypePath; [intro; apply isapropdirprod; apply homset_property|];
      etrans; [use pr1_transportf_const|];
      (* cbn. *)
      etrans; [apply precompWithColimOfArrows|];
      apply pathsinv0;
      etrans; [apply postcompWithColimArrow|];
      apply maponpaths;
      use cocone_paths;
      intro v;
      etrans; [use (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f) _ _ _ v)|];
      reflexivity
    ).
Defined.

Lemma Ff_right_tensor_preserves_colimit_mor_inv :
  colim (FfCC (mapdiagram (monoidal_right_tensor A) d)) -->
    (monoidal_right_tensor A) (colim (FfCC d)).
Proof.
  use colimArrow.
  use monoidal_right_tensor_cocone.
Defined.

Lemma Ff_right_tensor_preserves_colimit_mor_are_inverses :
  is_inverse_in_precat
    (Ff_right_tensor_preserves_colimit_mor)
    (Ff_right_tensor_preserves_colimit_mor_inv).
Proof.
  split.
  - functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    apply (colim_endo_is_identity).
    intro v.
    (* cbn. *)
    (* unfold Ff_right_tensor_preserves_colimit_mor11. *)
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use (colimArrowCommutes (CCFf_pt_ob1 CC d (fact_R A f))).
    (* cbn. *)
    etrans. use (colimArrowCommutes (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f)).
    reflexivity.
  - functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    apply (colim_endo_is_identity).
    intro v.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use (colimArrowCommutes (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f)).
    etrans. use (colimArrowCommutes (CCFf_pt_ob1 CC d (fact_R A f))).
    reflexivity.
Qed.

Opaque ColimFfCocone.

(* Ff_right_closed: *)
Lemma Ff_right_tensor_preserves_colimit_mor_iso :
  z_iso
    ((monoidal_right_tensor A) (colim (FfCC d)))
    (colim (FfCC (mapdiagram (monoidal_right_tensor A) d))).
Proof.
  exists (Ff_right_tensor_preserves_colimit_mor).
  exists (Ff_right_tensor_preserves_colimit_mor_inv).
  exact (Ff_right_tensor_preserves_colimit_mor_are_inverses).
Defined.

(* the following lemma can be used to get a ColimCocone of
   mapdiagram (monoidal_right_tensor A) d
   to monoidal_right_tensor A (colim (FfCC d)),
   so that we can lift the isomorphism to one in LNWFS,
   given that we know the colimit in LNWFS lies over
   that in Ff C  *)
Lemma Ff_right_tensor_cocone_isColimCocone :
  isColimCocone _ _ (monoidal_right_tensor_cocone Ff_mon A d (FfCC d)).
Proof.
  intros cl cc.

  set (mor := colimUnivProp (FfCC (mapdiagram (monoidal_right_tensor A) d)) _ cc).
  destruct mor as [mor uniqueness].

  use unique_exists.
  - apply (compose (Ff_right_tensor_preserves_colimit_mor)).
    exact (pr1 mor).
  - abstract (
      intro v;
      etrans; [|exact (pr2 mor v)];
      etrans; [apply assoc|];
      apply cancel_postcomposition;
      functorial_factorization_mor_eq f;
      etrans; [apply pr1_transportf_const|];
      (* cbn. *)
      (* unfold Ff_right_tensor_preserves_colimit_mor11. *)
      apply (colimArrowCommutes (CCFf_pt_ob1 CC d (fact_R A f)))
    ).
  - abstract (intro; apply impred; intro; apply homset_property).
  - abstract (
      intros y Hy;

      (* unfold is_cocone_mor in Hy. *)
      apply (pre_comp_with_z_iso_is_inj
        (z_iso_inv (Ff_right_tensor_preserves_colimit_mor_iso)));
      apply pathsinv0;
      etrans; [apply assoc|];
      etrans; [apply cancel_postcomposition;
              apply (is_inverse_in_precat2 (Ff_right_tensor_preserves_colimit_mor_are_inverses))|];
      etrans; [apply id_left|];
      apply pathsinv0;
      etrans; [|
        use (base_paths _ _ (uniqueness (z_iso_inv (Ff_right_tensor_preserves_colimit_mor_iso) · y,, _)))
      ]; [reflexivity|];

      intro v;
      etrans; [apply assoc|];
      etrans; [|exact (Hy v)];
      apply cancel_postcomposition;
      apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|];
      apply funextsec;
      intro f;
      apply subtypePath; [intro; apply isapropdirprod; apply homset_property|];
      etrans; [use pr1_transportf_const|];
      apply (colimArrowCommutes (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f))
    ).
Defined.

End Helpers.

Lemma Ff_rt_all_colimits :
  preserves_colimits_of_shape (monoidal_right_tensor (A : Ff_mon)) g.
Proof.
  intros d cl cc.
  intros isCC.
  set (isCCAcl := Ff_right_tensor_cocone_isColimCocone d).
  set (CCAcl := ((_,, (monoidal_right_tensor_cocone Ff_mon A d (FfCC d))),, isCCAcl) : ColimCocone _).
  set (base_iso := isColim_is_z_iso _ (FfCC d) _ _ isCC).
  (* destruct base_iso as [base_iso base_is_iso]. *)


  use (is_z_iso_isColim _ CCAcl).
  exists ((pr1 base_iso) ⊗^{_}_{r} A).
  abstract (
    split; [
      apply pathsinv0;
      use colim_endo_is_identity;
      intro u;
      etrans; [apply assoc|];
      etrans; [apply cancel_postcomposition;
              apply colimArrowCommutes|];
      etrans; [apply cancel_postcomposition, cancel_precomposition;
              apply (bifunctor_leftid Ff_mon)|];
      etrans; [apply cancel_postcomposition, id_right|];
      etrans; [exact (pathsinv0 (bifunctor_rightcomp Ff_mon _ _ _ _ _ _))|];
      etrans; [apply maponpaths;
              apply (colimArrowCommutes (make_ColimCocone _ _ _ isCC))|];
      reflexivity
    |
      apply pathsinv0;
      etrans; [exact (pathsinv0 (bifunctor_rightid Ff_mon _ _))|];
      etrans; [apply maponpaths;
              exact (pathsinv0 (pr22 base_iso))|];
      etrans; [apply (bifunctor_rightcomp Ff_mon)|];
      apply cancel_precomposition;
      use colimArrowUnique;
      intro u;
      apply pathsinv0;
      etrans; [apply cancel_precomposition;
              apply (bifunctor_leftid Ff_mon)|];
      etrans; [apply id_right|];
      apply pathsinv0;
      etrans; [exact (pathsinv0 (bifunctor_rightcomp Ff_mon _ _ _ _ _ _))|];
      apply maponpaths;
      apply colimArrowCommutes
    ]
  ).
Defined.

End Ff_closed.

Lemma Ff_rt_chain {C : category} (CC : Colims C):
    rt_preserves_chains (@Ff_monoidal C).
Proof.
  exact (Ff_rt_all_colimits CC is_connected_nat_graph 0).
Defined.

Lemma Ff_rt_coeq {C : category} (CC : Colims C):
    rt_preserves_coequalizers (@Ff_monoidal C).
Proof.
  exact (Ff_rt_all_colimits CC is_connected_coequalizer_graph (● 0)%stn).
Defined.

Section LNWFS_closed.

Import BifunctorNotations.
Import MonoidalNotations.

Context {C : category}.
Context (CC : Colims C).
Local Definition LNWFS_mon : monoidal_cat :=
    (_,, @LNWFS_tot_monoidal C).

Context {g : graph}.
Context (H : is_connected g).
Context (v0 : vertex g).
Context (LNWFSCC := λ d, ColimLNWFSCocone CC d H v0).

Context (A : LNWFS_mon).

Opaque LNWFS_tot_lcomp.
Opaque Ff_lcomp.
Opaque Ff_precategory_data.
Opaque LNWFS.

Section Helpers.

Context (d : diagram g LNWFS_mon)
        (dbase := mapdiagram (pr1_category _) d).

Opaque ColimFfCocone.

Local Lemma Ff_right_tensor_preserves_colimit_mor_inv_is_LNWFS_colim_mor
    (Ff_rt_cc_inv := Ff_right_tensor_preserves_colimit_mor_inv CC H v0 (pr1 A) dbase)
    (LNWFSmor := colimArrow (LNWFSCC (mapdiagram (monoidal_right_tensor A) d)) _ (mapcocone (monoidal_right_tensor A) _ (colimCocone (LNWFSCC d)))) :
    pr1 LNWFSmor = Ff_rt_cc_inv.
Proof.
  apply pathsinv0.
  functorial_factorization_mor_eq f.

  set (CCFf1 := (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor (pr1 A : Ff_mon)) dbase) f)).
  use (colimArrowUnique' CCFf1).
  intro v.
  etrans. apply (colimArrowCommutes CCFf1).
  apply pathsinv0.
  etrans. apply (colimArrowCommutes CCFf1 _ _ v).
  etrans. apply pr1_transportf_const.
  etrans. apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC (mapdiagram (pr1_category (LNWFS C)) d) (fact_R (pr1 A) f))).
  etrans. apply cancel_postcomposition.
  {
    etrans. use (section_disp_on_eq_morphisms (pr1 (dob d v)) (γ' := identity _)); reflexivity.
    apply maponpaths.
    exact (section_disp_id (pr1 (dob d v)) _).
  }
  apply id_left.
Qed.

Lemma LNWFS_right_tensor_preserves_colimit_mor_inv_disp
    (Ff_rt_cc_inv := Ff_right_tensor_preserves_colimit_mor_inv CC H v0 (pr1 A) dbase) :
  pr2 (colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d)) )
  -->[Ff_rt_cc_inv]
    pr2 ((monoidal_right_tensor A) (colim (LNWFSCC d))).
Proof.
  set (colimAL := colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d))).
  set (AcolimL := monoidal_right_tensor A (colim (LNWFSCC d))).
  set (LNWFSmor := colimArrow (LNWFSCC (mapdiagram (monoidal_right_tensor A) d)) _ (mapcocone (monoidal_right_tensor A) _ (colimCocone (LNWFSCC d)))).

  apply (@Ff_mor_eq_LNWFS_mor C colimAL AcolimL Ff_rt_cc_inv LNWFSmor).
  exact (Ff_right_tensor_preserves_colimit_mor_inv_is_LNWFS_colim_mor).
Qed.

Local Lemma LNWFS_right_tensor_preserves_colimit_mor_disp :
  pr2 ((monoidal_right_tensor A) (colim (LNWFSCC d)))
  -->[Ff_right_tensor_preserves_colimit_mor CC H v0 (pr1 A) dbase]
    pr2 (colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d))).
Proof.
  set (colimAL := colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d))).
  set (AcolimL := monoidal_right_tensor A (colim (LNWFSCC d))).
  set (Ffiso := z_iso_inv (Ff_right_tensor_preserves_colimit_mor_iso CC H v0 (pr1 A) dbase)).
  set (inv_disp := LNWFS_right_tensor_preserves_colimit_mor_inv_disp);
  exact (Ff_iso_inv_LNWFS_mor colimAL AcolimL Ffiso inv_disp).
Qed.

Lemma LNWFS_right_tensor_cocone_isColimCocone :
  isColimCocone _ _ (monoidal_right_tensor_cocone LNWFS_mon A d (LNWFSCC d)).
Proof.
  set (colimAL := colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d))).
  set (AcolimL := monoidal_right_tensor A (colim (LNWFSCC d))).
  set (Ffiso := z_iso_inv (Ff_right_tensor_preserves_colimit_mor_iso CC H v0 (pr1 A) dbase)).

  use (is_z_iso_isColim _ (LNWFSCC (mapdiagram (monoidal_right_tensor A) d))).
  use tpair.
  - exists (z_iso_inv Ffiso).
    exact (LNWFS_right_tensor_preserves_colimit_mor_disp).
  - abstract (
      set (adbase := (mapdiagram (pr1_category (LNWFS C)) (mapdiagram (monoidal_right_tensor A) d)));
      split; (apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|]); [
        etrans; [|exact (pr122 Ffiso)];
        apply cancel_postcomposition
      |
        etrans; [|exact (pr222 Ffiso)];
        apply cancel_precomposition
      ]; (use colimArrowUnique';
        intro v;
        etrans; [apply (colimArrowCommutes (ColimFfCocone CC adbase H v0))|];
        apply pathsinv0;
        etrans; [apply (colimArrowCommutes)|];
        reflexivity)
    ).
Defined.

End Helpers.

Opaque ColimFfCocone.

Lemma LNWFS_rt_all_colimits :
  preserves_colimits_of_shape (monoidal_right_tensor (A : LNWFS_mon)) g.
Proof.
  intros d cl cc.
  intros isCC.
  set (isCCAcl := LNWFS_right_tensor_cocone_isColimCocone d).
  set (CCAcl := ((_,, (monoidal_right_tensor_cocone LNWFS_mon A d (LNWFSCC d))),, isCCAcl) : ColimCocone _).
  set (base_iso := isColim_is_z_iso _ (LNWFSCC d) _ _ isCC).

  use (is_z_iso_isColim _ CCAcl).
  exists ((pr1 base_iso) ⊗^{ LNWFS_mon}_{r} A).
  abstract (
    split; [
      apply pathsinv0;
      use colim_endo_is_identity;
      intro u;
      etrans; [apply assoc|];
      etrans; [apply cancel_postcomposition;
              apply colimArrowCommutes|];
      etrans; [apply cancel_postcomposition, cancel_precomposition;
              apply (bifunctor_leftid LNWFS_mon)|];
      etrans; [apply cancel_postcomposition, id_right|];
      etrans; [exact (pathsinv0 (bifunctor_rightcomp LNWFS_mon _ _ _ _ _ _))|];
      etrans; [apply maponpaths;
              apply (colimArrowCommutes (make_ColimCocone _ _ _ isCC))|];
      reflexivity
    |
      apply pathsinv0;
      etrans; [exact (pathsinv0 (bifunctor_rightid LNWFS_mon _ _))|];
      etrans; [apply maponpaths;
              exact (pathsinv0 (pr22 base_iso))|];
      etrans; [apply (bifunctor_rightcomp LNWFS_mon)|];
      apply cancel_precomposition;
      use colimArrowUnique;
      intro u;
      apply pathsinv0;
      etrans; [apply cancel_precomposition;
              apply (bifunctor_leftid LNWFS_mon)|];
      etrans; [apply id_right|];
      apply pathsinv0;
      etrans; [exact (pathsinv0 (bifunctor_rightcomp LNWFS_mon _ _ _ _ _ _))|];
      apply maponpaths;
      apply colimArrowCommutes
    ]
  ).
Defined.

End LNWFS_closed.

Lemma LNWFS_rt_chain {C : category} (CC : Colims C):
    rt_preserves_chains (@LNWFS_tot_monoidal C).
Proof.
  exact (LNWFS_rt_all_colimits CC is_connected_nat_graph 0).
Defined.

Lemma LNWFS_rt_coeq {C : category} (CC : Colims C):
    rt_preserves_coequalizers (@LNWFS_tot_monoidal C).
Proof.
  exact (LNWFS_rt_all_colimits CC is_connected_coequalizer_graph (● 0)%stn).
Defined.
