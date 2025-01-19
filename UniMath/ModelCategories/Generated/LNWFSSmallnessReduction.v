(* Reducing the smallness requirement on LNWFS to a simpler one
to be applied to the one step comonad *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pushouts.
Require Import UniMath.CategoryTheory.Limits.Graphs.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.EqDiag.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.slicecat.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Three.

Require Import UniMath.ModelCategories.NWFS.
Require Import UniMath.ModelCategories.Generated.MonoidalHelpers.
Require Import UniMath.ModelCategories.Helpers.
Require Import UniMath.ModelCategories.Generated.LNWFSHelpers.
Require Import UniMath.ModelCategories.Generated.MonoidalHelpers.
Require Import UniMath.ModelCategories.Generated.FFMonoidalStructure.
Require Import UniMath.ModelCategories.Generated.LNWFSMonoidalStructure.
Require Import UniMath.ModelCategories.Generated.LNWFSCocomplete.

Local Open Scope cat.

Section SmallnessReduction.

Context {C : category}.
Context (CC : Colims C).

Local Definition Ff_mon : monoidal_cat :=
  (_,, @Ff_monoidal C).
Local Definition LNWFS_mon : monoidal_cat :=
  (_,, @LNWFS_tot_monoidal C).

Import BifunctorNotations.
Import MonoidalNotations.

(* lift edge of diagram to morphism between coconeIns *)
Definition cocone_coconeIn_edge_lifted
    {d : chain C} {y : C}
    (ccy : cocone d y)
    {u v : vertex nat_graph}
    (e : edge u v) :
  coconeIn ccy u --> coconeIn ccy v.
Proof.
  use mors_to_arrow_mor.
  - exact (dmor d e).
  - exact (identity _).
  - abstract (
      etrans; [exact (coconeInCommutes ccy _ _ e)|];
      apply pathsinv0;
      apply id_right
    ).
Defined.

(* define a chain of middle objects from a cocone, i.e.
  X0 --> X1 --> X2 --> X3 ...
    \    |f1  f2|     /
   f0 \  |      |   / f3
            Y
  gives a cocone
  K0 --> K1 --> K2 --> K3 ...
    \    |Rf1   |     /
  Rf0 \  |   Rf2|   / Rf3
            Y

*)
Definition fact_cocone_chain
    (F : Ff C)
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  chain C.
Proof.
  use tpair.
  - intro v.
    exact (arrow_dom (fact_R F (coconeIn ccy v))).
  - intros u v e.
    set (elifted := cocone_coconeIn_edge_lifted ccy e).
    exact (arrow_mor00 (#(fact_R F) elifted)).
Defined.

(* define the factorization of a cocone *)
Definition fact_cocone
    (F : Ff C)
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  cocone (fact_cocone_chain F ccy) y.
Proof.
  use make_cocone.
  - intro v.
    exact (fact_R F (coconeIn ccy v)).
  - abstract (
      intros u v e;
      set (elifted := cocone_coconeIn_edge_lifted ccy e);
      etrans; [exact (arrow_mor_comm (#(fact_R F) elifted))|];
      apply id_right
    ).
Defined.

(* define coconeIn to colimArrow morphism for cocone, i.e.
    Xv ----> X∞
    |        |
    |        |
    v        v
    Y ====== Y
*)
Definition coconeIn_colimArrow_mor
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  ∏ v, coconeIn ccy v --> colimArrow (CC _ d) _ ccy.
Proof.
  intro v.
  use mors_to_arrow_mor.
  - exact (colimIn (CC _ d) v).
  - exact (identity _).
  - abstract (
      etrans; [apply colimArrowCommutes|];
      apply pathsinv0;
      apply id_right
    ).
Defined.

(* define the cocone of right objects with vertex R(colimArrow)
   we will require that this is a colimCocone for the sliced
   R functors to be small *)
Definition dom_fact_R_colimArrow_cocone
    (F : Ff C)
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  cocone
    (fact_cocone_chain F ccy)
    (arrow_dom (fact_R F (colimArrow (CC _ d) _ ccy))).
Proof.
  use make_cocone.
  - intro v.
    exact (arrow_mor00 (#(fact_R F) (coconeIn_colimArrow_mor ccy v))).
  - abstract (
      intros u v e;
      etrans; [use (pr1_section_disp_on_morphisms_comp F)|];
      use (section_disp_on_eq_morphisms F); [
        exact (colimInCommutes (CC _ d) _ _ e)|apply id_left
      ]
    ).
Defined.

(* define smallness of (sliced) R functor *)
Definition FR_slice_omega_small (F : Ff C) : UU :=
    ∏ (d : chain C) (y : C) (ccy : cocone d y),
      isColimCocone _ _ (dom_fact_R_colimArrow_cocone F ccy).

(* a chain in arrow C from a cocone in C *)
Definition cocone_arrow_chain
    {d : chain C} {y : C}
    (ccy : cocone d y) : chain (arrow C).
Proof.
  use tpair.
  - intro v.
    exact (coconeIn ccy v).
  - intros u v e.
    exact (cocone_coconeIn_edge_lifted ccy e).
Defined.

(* we need that the colimArrow into the codomain y
   is a colimit for the chain in arrow C *)
Definition colimArrow_arrow_cocone
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  cocone (cocone_arrow_chain ccy) (colimArrow (CC _ d) _ ccy).
Proof.
  use make_cocone.
  - intro v.
    exact (coconeIn_colimArrow_mor ccy v).
  - abstract (
      intros u v e;
      use arrow_mor_eq; [|apply id_left];
      exact (colimInCommutes (CC _ d) _ _ e)
    ).
Defined.

Definition project_arrow_cocone00
    {cl : arrow C} {d : chain (arrow C)}
    (cc : cocone d cl) :
  cocone (project_diagram00 d) (arrow_dom cl).
Proof.
  use make_cocone.
  - intro v. exact (arrow_mor00 (coconeIn cc v)).
  - abstract (
      intros u v e;
      exact (arrow_mor00_eq (coconeInCommutes cc _ _ e))
    ).
Defined.

Definition project_arrow_cocone11
    {cl : arrow C} {d : chain (arrow C)}
    (cc : cocone d cl) :
  cocone (project_diagram11 d) (arrow_cod cl).
Proof.
  use make_cocone.
  - intro v. exact (arrow_mor11 (coconeIn cc v)).
  - abstract (
      intros u v e;
      exact (arrow_mor11_eq (coconeInCommutes cc _ _ e))
    ).
Defined.

Definition cocone_arrow_chain_y_cocone
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  cocone (project_diagram11 (cocone_arrow_chain ccy)) y.
Proof.
  use make_cocone.
  - intro v. exact (identity y).
  - abstract (intros u v e; apply id_left).
Defined.

(* We also need that y is a colimit for the chain on
   the codomains *)
Definition cocone_arrow_chain_y_cocone_isColimCocone
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  isColimCocone _ _ (cocone_arrow_chain_y_cocone ccy).
Proof.
  intros cl cc.
  use unique_exists.
  - exact (coconeIn cc 0).
  - abstract (
      intro v;
      induction v as [|v Hv]; [apply id_left|];
      etrans; [exact Hv|];
      etrans; [exact (pathsinv0 (coconeInCommutes cc _ _ (idpath (S v))))|];
      apply id_left
    ).
  - abstract (intro; apply impred; intro; apply homset_property).
  - abstract (
      intros x ccx;
      etrans; [|exact (ccx 0)];
      apply pathsinv0;
      apply id_left
    ).
Defined.

Definition cocone_arrow_chain_y_ColimCocone
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  ColimCocone (project_diagram11 (cocone_arrow_chain ccy)) :=
    make_ColimCocone _ _ _ (cocone_arrow_chain_y_cocone_isColimCocone ccy).

Lemma colimArrow_arrow_cocone_isColimCocone
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  isColimCocone _ _ (colimArrow_arrow_cocone ccy).
Proof.
  intros cl cc.

  assert (Hcin : ∏ v, identity y · arrow_mor11 (coconeIn cc 0) = arrow_mor11 (coconeIn cc v)).
  {
    abstract (
      intro v;
      induction v as [|v Hv]; [apply id_left|];
      etrans; [exact Hv|];
      etrans; [exact (pathsinv0 (arrow_mor11_eq (coconeInCommutes cc _ _ (idpath (S v)))))|];
      apply id_left
    ).
  }

  use unique_exists.
  - use mors_to_arrow_mor.
    * exact (colimArrow (CC _ _) _ (project_arrow_cocone00 cc)).
    * exact (colimArrow (cocone_arrow_chain_y_ColimCocone ccy) _ (project_arrow_cocone11 cc)).
    * abstract (
        use colimArrowUnique';
        intro v;
        etrans; [apply assoc|];
        etrans; [apply cancel_postcomposition; apply colimArrowCommutes|];
        apply pathsinv0;
        etrans; [apply assoc|];
        etrans; [apply cancel_postcomposition; apply colimArrowCommutes|];
        etrans; [|exact (pathsinv0 (arrow_mor_comm (coconeIn cc v)))];
        apply cancel_precomposition;
        induction v as [|v Hv]; [reflexivity|];
        etrans; [exact Hv|];
        etrans; [exact (pathsinv0 (arrow_mor11_eq (coconeInCommutes cc _ _ (idpath (S v)))))|];
        apply id_left
      ).
  - abstract (
      intro v;
      use arrow_mor_eq; [apply colimArrowCommutes|];
      exact (Hcin v)
    ).
  - abstract (intro x; apply impred; intro; apply homset_property).
  - abstract (
      intros x ccx;
      use arrow_mor_eq; [
        use colimArrowUnique;
        intro v;
        exact (arrow_mor00_eq (ccx v))|
      ];
      use (colimArrowUnique' (cocone_arrow_chain_y_ColimCocone ccy));
      intro v;
      etrans; [exact (arrow_mor11_eq (ccx v))|];
      apply pathsinv0;
      exact (Hcin v)
    ).
Defined.

Definition colimArrow_arrow_ColimCocone
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  ColimCocone (cocone_arrow_chain ccy) :=
    make_ColimCocone _ _ _ (colimArrow_arrow_cocone_isColimCocone ccy).

(* now we can show that the sliced R functor is omega small
   whenever the L functor preserves chains in arrow C *)
Lemma FR_slice_omega_small_if_L_omega_small (F : Ff C) :
    preserves_colimits_of_shape (fact_L F) nat_graph
    -> FR_slice_omega_small F.
Proof.
  intro HL.
  intros d y ccy.
  (* intros cl cc. *)

  set (isHLCC := HL _ _ _ (colimArrow_arrow_cocone_isColimCocone ccy)).
  set (HLCC := make_ColimCocone _ _ _ isHLCC).
  set (baseCC := arrow_colims CC _ (mapdiagram (fact_L F) (cocone_arrow_chain ccy))).
  set (base_mor := isColim_is_z_iso _ baseCC _ _ isHLCC).

  use (is_z_iso_isColim _ (CC _ (fact_cocone_chain F ccy))).
  exists (arrow_mor11 (pr1 base_mor)).
  split.
  - abstract (
      apply pathsinv0;
      use colim_endo_is_identity;
      intro v;
      etrans; [apply assoc|];
      etrans; [apply cancel_postcomposition; apply colimArrowCommutes|];
      exact (arrow_mor11_eq (colimArrowCommutes HLCC _ (colimCocone baseCC) v))
    ).
  - abstract (
      etrans; [|exact (arrow_mor11_eq (pr22 base_mor))];
      apply cancel_precomposition;
      use colimArrowUnique;
      intro v;
      etrans; [apply colimArrowCommutes|];
      reflexivity
    ).
Qed.

(* we get some issues with equality of diagrams, but
   given a chain d of functorial factorizations,
   the chain of middle objects of F ⊗ d is
   in fact the same as the cocone we just constructed
   for the right maps of all the factorizations
   (Ff_cocone_pointwise_R)
*)
Lemma fact_cocone_chain_eq_chain_pointwise_tensored
    (F : Ff C)
    (d : chain Ff_mon)
    (f : arrow C)
    (ccpointwise := Ff_cocone_pointwise_R d f) :
  eq_diag
      (fact_cocone_chain F ccpointwise)
      (Ff_diagram_pointwise_ob1 (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d) f).
Proof.
  use tpair.
  - intro v.
    reflexivity.
  - abstract (
      intros u v e;
      apply pathsinv0;
      etrans;[ use pr1_transportf_const|];
      etrans;[ apply id_left|];
      apply (section_disp_on_eq_morphisms F); reflexivity
    ).
Defined.

(* The ColimCocone we get from the R map of F being omega small,
   corrected for the equality of diagrams *)
Definition FR_slice_colimcocone_over_pointwise_tensored
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (f : arrow C) :
  ColimCocone (Ff_diagram_pointwise_ob1
    (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d) f).
Proof.
  set (ccpointwise := Ff_cocone_pointwise_R d f).
  set (isHRCC' := HR _ _ ccpointwise).

  (* correct codomain with equality of diagrams *)
  set (eqdiag := fact_cocone_chain_eq_chain_pointwise_tensored F d f).
  set (isHRCC := eq_diag_iscolimcocone _ eqdiag isHRCC').
  exact (make_ColimCocone _ _ _ isHRCC).
Defined.

(* The z-iso on middle objects we obtain from this ColimCocone
   to the colimit we obtain from CC itself on this diagram.
   This isomorphism is the one we need for the isomorphism of
   functorial factorizations. *)
Definition FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (f : arrow C)
    (CL := ChainsFf CC d)
    (FfCC := ChainsFf CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d))
    (ccpointwise := Ff_cocone_pointwise_R d f)
    (baseCC := (CCFf_pt_ob1 CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d) f)) :
  z_iso
    (colim baseCC)
    (arrow_dom (fact_R F (colimArrow (CC _ (Ff_diagram_pointwise_ob1 d f)) _ ccpointwise))).
Proof.
  set (HRCC := FR_slice_colimcocone_over_pointwise_tensored F d HR f).
  set (base_mor := isColim_is_z_iso _ baseCC _ _ (isColimCocone_from_ColimCocone HRCC)).

  exact (_,, base_mor).
Defined.

(* colimIn _ v to the ColimCocone with R(colimArrow) as vertex
   is the same as the right functor of F applied to
   colimIn (ChainsFf CC d) v, since this is how we defined
   ChainsFf CC d
   We have to rewrite this sometimes *)
Local Lemma FcolimArrow_coconeInBase_is_colimInHR
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (f : arrow C)
    (v : vertex nat_graph)
    (CL := ChainsFf CC d)
    (HRCC := FR_slice_colimcocone_over_pointwise_tensored F d HR f) :
  arrow_mor00 (#(fact_R F) (three_mor_mor12 (section_nat_trans (colimIn CL v) f)))
  = colimIn HRCC v.
Proof.
  use (section_disp_on_eq_morphisms F); reflexivity.
Qed.

(* Show that the base_iso we just defined in fact gives a
   morphism of three C, pointwise *)
Lemma FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise_three_comm
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (f : arrow C)
    (CL := ChainsFf CC d)
    (FfCC := ChainsFf CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d))
    (base_mor := FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise F d HR f) :
  (fact_L (F ⊗_{ Ff_mon} colim CL) f) · z_iso_inv base_mor
  = (identity _) · (fact_L (colim FfCC) f)
  × (fact_R (F ⊗_{ Ff_mon} colim CL) f) · (identity _) =
    z_iso_inv base_mor · (fact_R (colim FfCC) f).
Proof.
  set (HRCC := FR_slice_colimcocone_over_pointwise_tensored F d HR f).
  set (baseCC := (CCFf_pt_ob1 CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d) f)).

  split.
  - apply pathsinv0.
    etrans. apply id_left.
    (* cbn. *)
    etrans. apply assoc'.
    apply pathsinv0.
    etrans. apply assoc'.
    etrans. apply assoc'.
    apply cancel_precomposition.
    etrans. apply assoc.

    etrans. apply cancel_postcomposition.
            set (cin0 := colimIn CL 0).
            set (cin012 := three_mor_mor12 (section_nat_trans cin0 f)).
            exact (arrow_mor_comm (#(fact_L F) cin012)).

    etrans. apply assoc'.
    apply cancel_precomposition.
    etrans. etrans. apply cancel_postcomposition.
                    exact (FcolimArrow_coconeInBase_is_colimInHR F d HR f 0).
            apply (colimArrowCommutes HRCC).
    reflexivity.
  - etrans. apply id_right.
    show_id_type.
    apply (colimArrowUnique' HRCC).
    intro v.

    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (colimArrowCommutes HRCC).
    etrans. apply (colimArrowCommutes baseCC).
    apply pathsinv0.

    set (ccpointwise := Ff_cocone_pointwise_R d f).
    set (RcoconeInBase := #(fact_R F) (coconeIn_colimArrow_mor ccpointwise v)).
    etrans. exact (arrow_mor_comm RcoconeInBase).
    apply id_right.
Qed.

(* define the natural transformation we want from
   (F ⊗_{Ff_mon} (colim CL)) (colim FfCC)
   using the z_iso we got from the smallness. *)
Definition FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_data
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (CL := ChainsFf CC d)
    (FfCC := ChainsFf CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d)) :
  section_nat_trans_disp_data (F ⊗_{Ff_mon} (colim CL)) (colim FfCC).
Proof.
  intro f.
  set (base_mor := FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise F d HR f).

  exists (z_iso_inv base_mor).
  exact (FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise_three_comm F d HR f).
Defined.

(* this proof is a mess, but I had to rewrite γ within a
   #F γ... *)
Lemma FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_axioms
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (CL := ChainsFf CC d)
    (FfCC := ChainsFf CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d)) :
  section_nat_trans_disp_axioms (FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_data F d HR).
Proof.
  intros f g γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  etrans. apply pr1_transportf_const.

  set (HRCC := FR_slice_colimcocone_over_pointwise_tensored F d HR f).
  use (colimArrowUnique' HRCC).

  intro v.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          use (pr1_section_disp_on_morphisms_comp F).


  etrans. apply cancel_postcomposition.
          set (mor := three_mor_mor12 (section_nat_trans (colimIn CL v) g)).
          use (section_disp_on_eq_morphisms F (γ' := (#(fact_R (dob d v)) γ · mor))).

          1: etrans. apply (colimOfArrowsIn _ _ (CC nat_graph (Ff_diagram_pointwise_ob1 d f))).
             reflexivity.

          1: etrans. apply id_left.
             apply pathsinv0.
             apply id_right.

  etrans. apply cancel_postcomposition.
          exact (pathsinv0 (pr1_section_disp_on_morphisms_comp F _ _)).
  etrans. apply assoc'.

  etrans. apply cancel_precomposition.
  {
    etrans. apply cancel_postcomposition.
            exact (FcolimArrow_coconeInBase_is_colimInHR F d HR g v).
    set (HRCCg := FR_slice_colimcocone_over_pointwise_tensored F d HR g).
    apply (colimArrowCommutes HRCCg).
  }

  apply pathsinv0.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply (colimArrowCommutes HRCC).
  etrans. apply colimOfArrowsIn.
  reflexivity.
Qed.

Definition FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (CL := ChainsFf CC d)
    (FfCC := ChainsFf CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d)) :
  (F ⊗_{Ff_mon} (colim CL)) --> (colim FfCC) :=
    (_,, FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_axioms F d HR).

(* Use the morphism to show that indeed, F in Ff C
  has the smallness property if fact_R F does*)
Lemma FR_lt_preserves_colim_impl_Ff_lt_preserves_colim
    (F : Ff C)
    (d : chain Ff_mon)
    (CL := ChainsFf CC d) :
  FR_slice_omega_small F ->
    isColimCocone _ _
      (mapcocone (monoidal_left_tensor (F : Ff_mon)) _ (colimCocone CL)).
Proof.
  intro HR.

  set (FfCC := ChainsFf CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d)).
  use (is_z_iso_isColim _ FfCC).
  exists (FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor F d HR).
  split.
  - functorial_factorization_mor_eq f.
    set (HRCC := FR_slice_colimcocone_over_pointwise_tensored F d HR f).
    set (base_iso := FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise F d HR f).

    etrans. apply pr1_transportf_const.
    apply pathsinv0.
    etrans. exact (pathsinv0 (pr122 base_iso)).

    apply compeq; [|reflexivity].
    use colimArrowUnique.
    intro v.
    etrans. apply colimArrowCommutes.
    apply pathsinv0.
    etrans. apply pr1_transportf_const.
    etrans. apply id_left.
    apply (section_disp_on_eq_morphisms F); reflexivity.
  - functorial_factorization_mor_eq f.

    set (HRCC := FR_slice_colimcocone_over_pointwise_tensored F d HR f).
    set (base_iso := FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise F d HR f).

    etrans. apply pr1_transportf_const.
    apply pathsinv0.
    etrans. exact (pathsinv0 (pr222 base_iso)).
    apply compeq; [reflexivity|].
    apply colimArrowUnique.
    intro v.
    etrans. apply colimArrowCommutes.
    apply pathsinv0.
    etrans. apply pr1_transportf_const.
    etrans. apply id_left.
    apply (section_disp_on_eq_morphisms F); reflexivity.
Qed.

Context (L : total_category (LNWFS C))
        (d : chain LNWFS_mon)
        (CL := ChainsLNWFS CC d)
        (dbase := mapdiagram (pr1_category _) d)
        (Ldbase := mapdiagram (monoidal_left_tensor (pr1 L : Ff_mon)) dbase)
        (FfCCbase := ChainsFf CC Ldbase)
        (LNWFSCC := ChainsLNWFS CC (mapdiagram (monoidal_left_tensor (L : LNWFS_mon)) d)).

Opaque LNWFS_tot_lcomp.
Opaque Ff_lcomp.
Opaque Ff_precategory_data.
Opaque LNWFS.

Section Helpers.

Context (HF : isColimCocone _ _
          (mapcocone (monoidal_left_tensor (pr1 L : Ff_mon)) _ (project_cocone _ _ (colimCocone CL))))
        (LNWFSarr := colimArrow LNWFSCC _ (mapcocone (monoidal_left_tensor (L : LNWFS_mon)) _ (colimCocone CL)))
        (base_mor := isColim_is_z_iso _ FfCCbase _ _ HF)
        (Ffiso := (_,, base_mor) : z_iso _ _).

(* commutativity of project_cocone for
    pr1_category and monoidal_left_tensor *)
Section ProjectCoconeComm.

Opaque base_mor.
Opaque ColimFfCocone.
Opaque ColimLNWFSCocone.
Opaque CL.

Local Lemma Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_mor_disp_subproof (v : vertex nat_graph) :
  coconeIn (mapcocone (monoidal_left_tensor (pr1 L : Ff_mon))
    _ (project_cocone d (colim CL) (colimCocone CL))) v =
  colimIn FfCCbase v · pr1 LNWFSarr.
Proof.
  apply pathsinv0.
  functorial_factorization_mor_eq f.
  etrans. use pr1_transportf_const.
  exact (colimArrowCommutes (CCFf_pt_ob1 CC Ldbase f) _ _ v).
Qed.

Local Lemma Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_mor_disp_pr1_category_tensor_commutes :
  z_iso_mor Ffiso = pr1 LNWFSarr.
Proof.
  apply (colimArrowUnique' FfCCbase Ffiso (pr1 LNWFSarr)).
  intro v.
  etrans. apply (colimArrowCommutes FfCCbase).
  exact (Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_mor_disp_subproof v).
Qed.

End ProjectCoconeComm.

(* showing that the morphism induced the the universal
property of the colimit in Ff C is indeed an LNWFS morphism.
we do this by reducing it to the pointwise case. *)
Section DispMor.

Opaque base_mor.
Opaque ColimFfCocone.
Opaque ColimLNWFSCocone.
Opaque CL.
Opaque LNWFSCC.
Opaque Ffiso LNWFSarr.

Lemma Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_mor_disp :
  pr2 (monoidal_left_tensor (L : LNWFS_mon) (colim CL))
  -->[pr1 base_mor] pr2 (colim LNWFSCC).
Proof.
  apply (Ff_iso_inv_LNWFS_mor (colim LNWFSCC) (monoidal_left_tensor (L : LNWFS_mon) (colim CL)) Ffiso).
  apply (@Ff_mor_eq_LNWFS_mor C (colim LNWFSCC) (monoidal_left_tensor (L : LNWFS_mon) (colim CL)) (z_iso_mor Ffiso) LNWFSarr).
  apply pathsinv0.
  exact (Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_mor_disp_pr1_category_tensor_commutes).
Qed.

End DispMor.

Section InvInPrecat.

Opaque base_mor.
Opaque ColimFfCocone.
Opaque CL.
Opaque FfCCbase.

Local Lemma Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_inv_in_precat_subproof :
  colimArrow FfCCbase _
    (mapcocone (monoidal_left_tensor (pr1 L : Ff_mon))
      _ (project_cocone d (colim CL) (colimCocone CL)))
  = (pr1 (colimArrow LNWFSCC _ (mapcocone (monoidal_left_tensor (L : LNWFS_mon)) d (colimCocone CL)))).
Proof.
  use (colimArrowUnique' FfCCbase).
  intro v.
  etrans. exact (colimArrowCommutes FfCCbase _ _ v).
  apply pathsinv0.
  exact (colimArrowCommutes FfCCbase _ _ v).
Qed.

Opaque ColimLNWFSCocone.
Opaque LNWFSCC.
Opaque Ffiso LNWFSarr.

Local Lemma Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_inv_in_precat :
  is_inverse_in_precat
    (pr1 (colimArrow LNWFSCC _ (mapcocone (monoidal_left_tensor (L : LNWFS_mon)) d (colimCocone CL))))
    (pr1 base_mor).
Proof.
  split.
  - use (pathscomp1 (pr12 base_mor) _); [|reflexivity];
    apply (cancel_postcomposition _ _ (pr1 base_mor));
    exact Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_inv_in_precat_subproof.
  - use (pathscomp1 (pr22 base_mor)); [|reflexivity];
    apply (cancel_precomposition _ _ _ _ _ _ (pr1 base_mor));
    exact Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_inv_in_precat_subproof.
Qed.

End InvInPrecat.

End Helpers.

Lemma Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim :
  isColimCocone _ _
    (mapcocone (monoidal_left_tensor (pr1 L : Ff_mon)) _ (project_cocone _ _ (colimCocone CL)))
    ->
    isColimCocone _ _
      (mapcocone (monoidal_left_tensor (L : LNWFS_mon)) _ (colimCocone CL)).
Proof.
  intro HF.

  set (HFCC := make_ColimCocone _ _ _ HF).
  set (base_mor := isColim_is_z_iso _ FfCCbase _ _ HF).
  set (base_inv := colimArrow FfCCbase _ (colimCocone HFCC)).

  use (is_z_iso_isColim _ LNWFSCC).
  use tpair.
  - exists (pr1 base_mor).
    abstract (
      exact (Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_mor_disp HF)
    ).
  - (* showing isomorphism is easy, since we know that the base morphism is an isomorphism *)
    abstract (
      apply LNWFS_inv_in_precat_if_Ff_inv_in_precat;
      exact (Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_inv_in_precat HF)
    ).
Qed.

End SmallnessReduction.
