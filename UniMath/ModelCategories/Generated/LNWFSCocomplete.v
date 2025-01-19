Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monads.ComonadCoalgebras.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Coequalizers.
Require Import UniMath.CategoryTheory.Chains.Chains.

Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Three.
Require Import UniMath.ModelCategories.NWFS.
Require Import UniMath.ModelCategories.Helpers.
Require Import UniMath.ModelCategories.Generated.LNWFSHelpers.
Require Import UniMath.ModelCategories.Generated.FFMonoidalStructure.

Local Open Scope cat.

Section Ff_cocomplete.

Context {C : category}.
Context (CC : Colims C).

Section Ff_cocomplete_diagram.

Context {g : graph} (d : diagram g (Ff C)).
Context (H : is_connected g).

(* diagram of middle objects *)
Definition Ff_diagram_pointwise_ob1 (a : arrow C) : diagram g C.
Proof.
  use tpair.
  - intro v.
    exact (pr1 (pr1 (dob d v) a)).
  - intros u v e.
    exact (pr1 (pr1 (dmor d e) a)).
Defined.

Definition CCFf_pt_ob1 : ∏ (a : arrow C), ColimCocone (Ff_diagram_pointwise_ob1 a) :=
    λ a, CC _ _.


Definition Ff_cocone_pointwise_R
      (f : arrow C) :
    cocone (Ff_diagram_pointwise_ob1 f) (arrow_cod f).
Proof.
  use make_cocone.
  - intro v.
    exact (fact_R (dob d v) f).
  - abstract (
      intros u v e;
      set (ecommf := pr2 (three_mor_comm (section_nat_trans (dmor d e) f)));
      etrans; [exact (pathsinv0 ecommf)|];
      apply id_right
    ).
Defined.

(* this construction only works for non-empty graphs, since
   we need an arrow arrow_dom a --> colim (CCFf_pt_ob1 a),
   but we can only find this for a non-empty graph *)
Definition ColimFf_ob (v0 : vertex g) (a : arrow C) : three_disp C a.
Proof.
  exists (colim (CCFf_pt_ob1 a)).

  exists (pr12 (pr1 (dob d v0) a) · (colimIn (CCFf_pt_ob1 a) v0)).
  use tpair.
  - use colimArrow.
    exact (Ff_cocone_pointwise_R a).
  - (* cbn. *)
    abstract (
      etrans; [apply assoc'|];
      etrans; [apply cancel_precomposition;
              use (colimArrowCommutes (CCFf_pt_ob1 a))|];
      (* cbn. *)
      exact (three_comp (fact_functor (dob d v0) a))
    ).
Defined.

Definition ColimFf_mor (v0 : vertex g)
    {a b : arrow C} (f : a --> b) :
  ColimFf_ob v0 a -->[f] ColimFf_ob v0 b.
Proof.
  use tpair.
  - use colimOfArrows.
    * intro v.
      (* cbn. *)
      set (Dv := (dob d v)).
      exact (pr1 ((section_disp_on_morphisms (section_disp_data_from_section_disp Dv)) f)).
    * intros u v e.
      (* cbn. *)
      abstract (
        set (De := (dmor d e));
        set (Deax := section_nt_disp_axioms_from_section_nt_disp De _ _ f);
        etrans; [exact (pathsinv0 (base_paths _ _ Deax))|];
        etrans; [apply pr1_transportf_const|];
        reflexivity
      ).
  - (* functorality of dob d v *)
    split.
    * (* cbn. *)
      abstract (
        set (Dv0f := ((section_disp_on_morphisms (section_disp_data_from_section_disp (dob d v0))) f));
        set (Dv0fax := pr2 Dv0f);
        etrans; [apply assoc'|];
        etrans; [apply cancel_precomposition;
                 use (colimArrowCommutes (CCFf_pt_ob1 a))|];

        etrans; [apply assoc|];
        apply pathsinv0;
        etrans; [apply assoc|];
        apply cancel_postcomposition;
        exact (pathsinv0 (pr1 Dv0fax))
      ).
    * (* cbn. *)

      abstract (
        etrans; [use postcompWithColimArrow|];
        apply pathsinv0;
        etrans; [use precompWithColimOfArrows|];
        apply maponpaths;
        use cocone_paths;
        intro v;
        (* cbn. *)
        set (Dvf := ((section_disp_on_morphisms (section_disp_data_from_section_disp (dob d v))) f));
        set (Dvfax := pr2 Dvf);

        exact (pathsinv0 (pr2 Dvfax))
      ).
Defined.

Definition ColimFf_data (v0 : vertex g) : section_disp_data (three_disp C) :=
    (_,, @ColimFf_mor v0).

Lemma ColimFf_axioms (v0 : vertex g) : section_disp_axioms (ColimFf_data v0).
Proof.
  split.
  - intro a.
    use subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    apply pathsinv0, colim_endo_is_identity; intro u.
    (* cbn. *)
    etrans. use (colimOfArrowsIn _ _ (CCFf_pt_ob1 a)).
    (* cbn. *)
    etrans. apply cancel_postcomposition.
            apply maponpaths.
            exact (section_disp_id (dob d u) _).
    apply id_left.
  - intros a b c fab fbc.
    use subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    (* cbn. *)
    apply pathsinv0.
    etrans. apply precompWithColimOfArrows.
    apply pathsinv0, colimArrowUnique.
    intro u.
    etrans. apply colimOfArrowsIn.

    apply pathsinv0.
    etrans. apply assoc.
    apply cancel_postcomposition.

    etrans. apply pr1_section_disp_on_morphisms_comp.
    reflexivity.
Qed.

Definition ColimFf (v0 : vertex g) : Ff C :=
    (_,, ColimFf_axioms v0).


(* we need an edge from v0 to v for this to work,
   regarding equality of (arrow_dom v/v0 · colimIn v/v0) *)
Local Definition colim_nat_trans_in_data
      {v0 : vertex g} {v : vertex g} :
    dob d v --> ColimFf v0.
Proof.
  use tpair.
  - intro a.
    exists (colimIn (CCFf_pt_ob1 a) v).
    split.
    * (* unfold ColimFf. *)
      (* cbn. *)
      abstract (
        apply pathsinv0;
        etrans; [apply id_left|];
        set (predicate := λ v, pr12 (pr1 (ColimFf v0) a) = pr12 (pr1 (dob d v) a) · colimIn (CCFf_pt_ob1 a) v);
        use (connected_graph_zig_zag_strong_induction v0 H predicate); [reflexivity|];
        intros u u' Hu uu';
        induction uu' as [e|e]; (etrans; [exact Hu|]);
          [|apply pathsinv0];
          (etrans; [apply cancel_precomposition;
                 exact (pathsinv0 (colimInCommutes (CCFf_pt_ob1 a) _ _ e))|];
           etrans; [apply assoc|];
           apply cancel_postcomposition;
           etrans; [exact (pr12 (pr1 (dmor d e) a))|];
           apply id_left)
      ).
    * abstract (
        etrans; [apply id_right|];
        apply pathsinv0;
        etrans; [apply (colimArrowCommutes (CCFf_pt_ob1 a))|];
        reflexivity
      ).
  - abstract (
      intros a b f;
      apply subtypePath; [intro; apply isapropdirprod; apply homset_property|];
      etrans; [use pr1_transportf_const|];
      apply pathsinv0;
      (* cbn. *)
      etrans; [apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 a))|];
      reflexivity
    ).
Defined.

Local Definition cocone_pointwise (F : Ff C) (cc : cocone d F) a :
  cocone (Ff_diagram_pointwise_ob1 a) (pr1 (pr1 F a)).
Proof.
  use make_cocone.
  - intro v.
    exact (pr1 (pr1 (coconeIn cc v) a)).
  - abstract (
      intros u v e;
      (* cbn. *)
      set (cccomm_pointwise := eq_section_nat_trans_disp_on_morphism (coconeInCommutes cc _ _ e) a);
      apply pathsinv0;
      etrans; [exact (pathsinv0 (base_paths _ _ cccomm_pointwise))|];
      etrans; [use pr1_transportf_const|];
      reflexivity
    ).
Defined.

Definition ColimFf_unique_mor
    (v0: vertex g)
    (F : Ff C) (cc : cocone d F) :
  ColimFf v0 --> F.
Proof.
  use tpair.
  * intro a.
    exists (colimArrow (CCFf_pt_ob1 a) _ (cocone_pointwise F cc a)).
    split.
    + abstract (
        (* cbn. *)
        etrans; [apply assoc'|];
        etrans; [apply cancel_precomposition;
                 apply (colimArrowCommutes (CCFf_pt_ob1 a))|];
        apply pathsinv0;
        etrans; [apply id_left|];
        apply pathsinv0;
        (* cbn. *)
        etrans; [exact (pr12 (pr1 (coconeIn cc v0) a))|];
        apply id_left
      ).
    + abstract (
        etrans; [apply id_right|];
        apply pathsinv0;
        etrans; [apply postcompWithColimArrow|];
        use colimArrowUnique;
        intro u;
        etrans; [apply colimArrowCommutes|];
        (* naturality of coconeIn cc at u *)
        etrans; [exact (pathsinv0 (pr22 (pr1 (coconeIn cc u) a)))|];
        apply id_right
      ).
  * abstract (
      intros a b f;
      apply subtypePath; [intro; apply isapropdirprod; apply homset_property|];
      etrans; [use pr1_transportf_const|];
      etrans; [apply precompWithColimOfArrows|];
      apply pathsinv0;
      etrans; [apply postcompWithColimArrow|];

      use colimArrowUnique;
      intro u;
      etrans; [apply (colimArrowCommutes (CCFf_pt_ob1 a))|];
      (* cbn. *)

      set (ccuf := (section_nt_disp_axioms_from_section_nt_disp (coconeIn cc u)) _ _ f);
      etrans; [exact (pathsinv0 (base_paths _ _ ccuf))|];
      etrans; [use pr1_transportf_const|];
      reflexivity
    ).
Defined.

Lemma ColimFf_unique
    {v0 : vertex g}
    (F : Ff C) (cc : cocone d F) :
  ∃! x : ColimFf v0 --> F,
            ∏ v, colim_nat_trans_in_data · x = coconeIn cc v.
Proof.
  use unique_exists.
  - exact (ColimFf_unique_mor v0 F cc).
  - abstract (
      intro v;
      functorial_factorization_mor_eq a;
      etrans; [use pr1_transportf_const|];
      etrans; [apply (colimArrowCommutes (CCFf_pt_ob1 a))|];
      reflexivity
    ).
  - abstract (
      intro; apply impred; intro; apply homset_property
    ).
  - abstract (
      intros f t;
      functorial_factorization_mor_eq a;
      apply colimArrowUnique;
      intro u;
      (* cbn. *)
      set (tax := eq_section_nat_trans_disp_on_morphism (t u) a);
      apply pathsinv0;
      etrans; [exact (pathsinv0 (base_paths _ _ tax))|];
      etrans; [use pr1_transportf_const|];
      reflexivity
    ).
Defined.

Lemma ColimFfCocone
    (v0 : vertex g) :
  ColimCocone d.
Proof.
  use make_ColimCocone.
  - exact (ColimFf v0).
  - use make_cocone.
    * intro v. exact (colim_nat_trans_in_data).
    * abstract (
        intros u v e;
        functorial_factorization_mor_eq a;
        etrans; [use pr1_transportf_const|];
        (* cbn. *)
        apply (colimInCommutes (CCFf_pt_ob1 a))
      ).
  - intros F cc; exact (ColimFf_unique _ cc).
Defined.

End Ff_cocomplete_diagram.

End Ff_cocomplete.

Lemma ChainsFf {C : category} (HC : Colims C) :
    Chains (Ff C).
Proof.
  intros d.
  use (ColimFfCocone HC d).
  - exact is_connected_nat_graph.
  - exact 0.
Defined.

Lemma CoequalizersFf {C : category} (HC : Colims C) :
    Coequalizers (Ff C).
Proof.
  intros F G f g.
  use (ColimFfCocone HC).
  - exact is_connected_coequalizer_graph.
  - exact (● 0)%stn.
Defined.


Section LNWFS_cocomplete.

Context {C : category}.
Context (CC : Colims C).

Context {g : graph} (d : diagram g (total_category (LNWFS C))).
Context (H : is_connected g).
Context (v0 : vertex g).
Context (FfCC := λ d, ColimFfCocone CC d H v0).


Local Definition lnwfs_Σ {F : Ff C} (L : lnwfs_over F) := pr1 L.

Local Definition LNWFS_diagram_pointwise_comul_mor (a : arrow C) : diagram g (arrow C).
Proof.
  use tpair.
  - intro v.
    set (Σa := lnwfs_Σ (pr2 (dob d v)) a).
    exact (arrow_mor11 Σa).
  - intros u v e.
    set (Lu := dob d u).
    set (Lv := dob d v).
    set (mor := dmor d e : Lu --> Lv).

    set (α := lnwfs_mor (pr2 Lu) (pr2 Lv) (pr1 mor)).
    set (Mu := fact_L (pr1 Lu)).
    set (Mv := fact_L (pr1 Lv)).
    set (mulmor := #Mu (α a) · α (Mv a)).

    use mors_to_arrow_mor.
    * exact (arrow_mor11 (α a)).
    * exact (arrow_mor11 mulmor).
    * abstract (
        set (morax := pr2 mor);
        set (moraxμa := pr1 morax a);
        etrans; [exact (pr2 (pathsdirprodweq (base_paths _ _ moraxμa)))|];
        apply assoc'
      ).
Defined.

Definition ccμ : ∏ (a : arrow C), ColimCocone (LNWFS_diagram_pointwise_comul_mor a) :=
    λ a, (arrow_colims CC) _ _.

Context (dbase := mapdiagram (pr1_category _) d).
Context (Finf := FfCC dbase).

Lemma ccμ_cod_preservation_mor (a : arrow C) :
    arrow_cod (colim (ccμ a)) --> three_ob1 (fact_functor (colim Finf) (fact_L (colim Finf) a)).
Proof.
  use colimOfArrows.
  - intro v.
    (* cbn. *)
    (* three_ob1 ((dob d v) (fact_L (dob d v) a))
                  -->
       three_ob1 ((dob d v) (fact_L Finf a))
    *)
    set (vinFinf := colimIn Finf v).
    set (LvinFinf := three_mor_mor01 (section_nat_trans vinFinf a)).
    set (dobvLvinFinf := #(fact_functor (pr1 (dob d v))) LvinFinf).
    exact (three_mor11 dobvLvinFinf).
  - abstract (
      intros u v e;
      etrans; [apply assoc'|];
      set (morcolim := three_mor_mor01 (section_nat_trans (colim_nat_trans_in_data CC dbase H (v0 := v0) (v := v)) a));
      set (dmorenat := (section_nt_disp_axioms_from_section_nt_disp (dmor dbase e)) _ _ morcolim);
      etrans; [apply cancel_precomposition; exact (pathsinv0 (base_paths _ _ dmorenat))|];
      etrans; [apply cancel_precomposition; apply pr1_transportf_const|];
      (* cbn. *)
      etrans; [apply assoc|];
      apply cancel_postcomposition;
      etrans; [apply pr1_section_disp_on_morphisms_comp|];
      use section_disp_on_eq_morphisms; [apply id_left|];
      apply (colimInCommutes (CCFf_pt_ob1 CC dbase a))
    ).
Defined.

Local Definition ccμ_cod_arrow (a : arrow C) :
    arrow_dom a --> arrow_cod (colim (ccμ a)).
Proof.
  set (ccμinv0 := colimIn (ccμ a) v0).
  set (ccμinv011 := arrow_mor11 ccμinv0).
  set (λλav0 := fact_L (pr1 (dob d v0)) (fact_L (pr1 (dob d v0)) a)).
  exact (λλav0 · ccμinv011).
Defined.

Local Lemma LNWFS_colim_comul_data_subproof
    (v : vertex g)
    (f : arrow C)
  :
    fact_L (pr1 (dob d v)) f ·
    arrow_mor11 (lnwfs_Σ (pr2 (dob d v)) f) ·
    three_mor11 (#(fact_functor (pr1 (dob d v))) (three_mor_mor01 (section_nat_trans (colimIn Finf v) f)))
    =
    fact_L (pr1 (dob d v)) (fact_L (colim Finf) f).
Proof.
  set (Lv := (dob d v)).
  (* λf · σf · m11 = λ_{λ∞f}
    where λf · σf = λλf (component of comul)
    and λλf · m11 = λ_{λ∞f} (commutativity of fact_L (pr1 Lv) (fact_L (colim Finf)) f)
  *)
  etrans. apply cancel_postcomposition.
  {
    set (Σf := lnwfs_Σ (pr2 (dob d v)) f).
    set (Σfcomm := arrow_mor_comm Σf).
    etrans. exact (pathsinv0 Σfcomm).
    etrans. apply cancel_postcomposition.
            exact (lnwfs_Σ_top_map_id _ f).
    apply id_left.
  }
  etrans.
  {
    set (LcolimIn := (# (fact_functor (pr1 Lv)) (three_mor_mor01 (section_nat_trans (colimIn Finf v) f)))).
    set (LcolimIncomm01 := pr1 (three_mor_comm LcolimIn)).
    exact LcolimIncomm01.
  }
  apply id_left.
Qed.

Definition LNWFS_colim_comul_data_first_mor (a : arrow C) :
  fact_L (colim Finf) a --> ccμ_cod_arrow a.
Proof.
  use mors_to_arrow_mor.
  - exact (identity _).
  - exact (colim (ccμ a)).
  - abstract (
      etrans; [apply id_left|];
      apply pathsinv0;
      etrans; [apply assoc'|];
      etrans; [apply cancel_precomposition;
              apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC dbase a))|];
      etrans; [apply assoc|];
      apply cancel_postcomposition;
      set (Σf := lnwfs_Σ (pr2 (dob d v0)) a);
      set (Σfcomm := arrow_mor_comm Σf);
      etrans; [exact (pathsinv0 Σfcomm)|];
      etrans; [apply cancel_postcomposition;
              exact (lnwfs_Σ_top_map_id _ a)|];
      apply id_left
    ).
Defined.

Definition LNWFS_colim_comul_data_second_mor (a : arrow C) :
    ccμ_cod_arrow a --> (fact_L (colim Finf) ∙ fact_L (colim Finf)) a.
Proof.
  use mors_to_arrow_mor.
  - exact (identity _).
  - exact (ccμ_cod_preservation_mor a).
  - abstract (
      etrans; [apply id_left|];
      apply pathsinv0;
      etrans; [apply assoc'|];
      etrans; [apply cancel_precomposition;
              apply (colimOfArrowsIn _ _ (CC g
                  (mapdiagram (PrecategoryBinProduct.pr2_functor C C)
                    (mapdiagram (pr1_category (arrow_disp C))
                        (LNWFS_diagram_pointwise_comul_mor a)))))|];
      etrans; [apply assoc|];
      apply cancel_postcomposition;
      set (LcolimIn := (# (fact_functor (pr1 (dob d v0))) (three_mor_mor01 (section_nat_trans (colimIn Finf v0) a))));
      set (LcolimIncomm01 := pr1 (three_mor_comm LcolimIn));
      etrans; [exact LcolimIncomm01|];
      apply id_left
    ).
Defined.


Definition LNWFS_colim_comul_data :
  nat_trans_data (fact_L (colim Finf)) ((fact_L (colim Finf)) ∙ (fact_L (colim Finf))).
Proof.
  intro a.
  exact (
    LNWFS_colim_comul_data_first_mor a
    · LNWFS_colim_comul_data_second_mor a
  ).
Defined.

Definition LNWFS_colim_comul_ax :
  is_nat_trans _ _ LNWFS_colim_comul_data.
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod.
  - etrans; [apply assoc|].
    etrans; [apply id_right|].
    etrans; [apply id_right|].
    apply pathsinv0.
    etrans. apply assoc'.
    etrans. apply id_left.
    apply id_left.
  -  use colimArrowUnique'.
    intro v.
    (* cbn. *)
    etrans; [apply assoc|].
    etrans; [apply cancel_postcomposition;
            apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC dbase f))|].
    (* cbn. *)
    etrans; [apply assoc|].
    etrans; [apply assoc4|].
    etrans; [apply cancel_postcomposition, cancel_precomposition;
            apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC dbase f'))|].
    etrans; [apply cancel_postcomposition, assoc|].
    etrans; [apply assoc'|].
    etrans; [apply cancel_precomposition, colimOfArrowsIn|].
    etrans; [apply assoc|].
    apply pathsinv0.
    etrans; [apply assoc|].
    (* cbn. *)
    etrans; [apply cancel_postcomposition, assoc|].
    etrans; [do 2 apply cancel_postcomposition;
            apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC dbase f))|].
    (* cbn. *)
    etrans; [apply assoc4|].
    (* unfold ccμ_cod_preservation_mor. *)
    set (ccbase := (CC g
          (mapdiagram (PrecategoryBinProduct.pr2_functor C C)
            (mapdiagram (pr1_category (arrow_disp C))
                (LNWFS_diagram_pointwise_comul_mor f))))).
    etrans; [apply cancel_postcomposition, cancel_precomposition;
            apply (colimOfArrowsIn _ _ ccbase)|].
    clear ccbase.
    (* cbn. *)
    etrans; [apply assoc'|].
    etrans; [apply cancel_precomposition, assoc'|].
    etrans; [do 2 apply cancel_precomposition;
            apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC dbase _))|].
    (* cbn. *)
    etrans; [apply assoc|].
    etrans; [apply assoc|].
    apply cancel_postcomposition.
    apply pathsinv0.
    set (Σnat := nat_trans_ax (lnwfs_Σ (pr2 (dob d v))) _ _ γ).
    set (Σnat11 := pr2 (pathsdirprodweq (base_paths _ _ Σnat))).
    etrans; [apply cancel_postcomposition; exact (Σnat11)|].
    etrans; [apply assoc'|].
    apply pathsinv0.
    etrans; [apply assoc'|].
    apply cancel_precomposition.
    (* cbn. *)
    etrans; [apply pr1_section_disp_on_morphisms_comp|].
    apply pathsinv0.
    etrans; [apply pr1_section_disp_on_morphisms_comp|].
    use (section_disp_on_eq_morphisms (pr1 (dob d v))).
    * etrans; [apply id_right|].
      apply pathsinv0.
      apply id_left.
    * apply pathsinv0.
      etrans; [apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC dbase f))|].
      reflexivity.
Qed.

Definition LNWFS_colim_comul :
    (fact_L (colim Finf)) ⟹ ((fact_L (colim Finf)) ∙ (fact_L (colim Finf))) :=
  (_,, LNWFS_colim_comul_ax).

Local Lemma LNWFS_colim_comul_monad_ax_subproof1
    (f : arrow C)
    (v : vertex g) :
  fact_L (pr1 (dob d v0)) (fact_L (pr1 (dob d v0)) f)
  · arrow_mor11 (colimIn (ccμ f) v0) =
  fact_L (pr1 (dob d v)) (fact_L (pr1 (dob d v)) f)
  · arrow_mor11 (colimIn (ccμ f) v).
Proof.
  set (predicate := λ v,
      fact_L (pr1 (dob d v0)) (fact_L (pr1 (dob d v0)) f)
      · arrow_mor11 (colimIn (ccμ f) v0) =
      fact_L (pr1 (dob d v)) (fact_L (pr1 (dob d v)) f)
      · arrow_mor11 (colimIn (ccμ f) v)).

  enough (He : ∏ (u u' : vertex g) (e : edge u u'),
            fact_L (pr1 (dob d u)) (fact_L (pr1 (dob d u)) f)
            · arrow_mor11 (colimIn (ccμ f) u) =
            fact_L (pr1 (dob d u')) (fact_L (pr1 (dob d u')) f)
            · arrow_mor11 (colimIn (ccμ f) u')).
  {
    use (connected_graph_zig_zag_strong_induction v0 H predicate); [reflexivity|].

    intros u u' Hu e.
    destruct e.
    - etrans. exact Hu.
      exact (He _ _ e).
    - etrans. exact Hu.
      apply pathsinv0.
      exact (He _ _ e).
  }
  intros u u' e.
  set (cinc := colimInCommutes (ccμ f) _ _ e).
  etrans. apply cancel_precomposition.
          exact (pathsinv0 (pr2 (pathsdirprodweq (base_paths _ _ cinc)))).
  etrans. apply assoc.
  apply cancel_postcomposition.

  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
  {
    set (e01 := three_mor_mor01 (section_nat_trans (pr1 (dmor d e)) f)).
    set (Lue01 := #(fact_L (pr1 (dob d u))) e01).
    etrans. apply cancel_precomposition.
            use (section_disp_on_eq_morphisms (pr1 (dob d u)) (γ' := e01)); reflexivity.
    etrans. exact (pathsinv0 (arrow_mor_comm Lue01)).
    apply id_left.
  }
  set (e01 := three_mor_mor01 (section_nat_trans (pr1 (dmor d e)) (fact_L (pr1 (dob d u')) f))).
  etrans. exact (pathsinv0 (arrow_mor_comm e01)).
  apply id_left.
Qed.

Local Lemma LNWFS_colim_comul_monad_ax_subproof
    (f : arrow C)
    (v : vertex g) :
  arrow_mor11 (lnwfs_Σ (pr2 (dob d v)) f)
  · three_mor11 (
      #(fact_functor (pr1 (dob d v)))
      (three_mor_mor01 ((section_nat_trans_data (colim_nat_trans_in_data CC dbase H) f)))
    )
  · three_mor11 (#(fact_functor (pr1 (dob d v))) (LNWFS_colim_comul_data f))
  =
  arrow_mor11 (lnwfs_Σ (pr2 (dob d v)) f)
  · three_mor11 (
      #(fact_functor (pr1 (dob d v)))
      (three_mor_mor01 ((section_nat_trans_data (colim_nat_trans_in_data CC dbase H) f)))
    )
  · arrow_mor11 (lnwfs_Σ (pr2 (dob d v)) (fact_L (colim Finf) f))
  · three_mor11 (
      #(fact_functor (pr1 (dob d v)))
      (three_mor_mor01 ((section_nat_trans_data (colim_nat_trans_in_data CC dbase H) (fact_L (colim Finf) f))))
    ).
Proof.
  set (Lv := dob d v).
  set (law3 := @Comonad_law3 _ (L_monad _ _ (pr22 Lv))).

  etrans. apply cancel_precomposition.
  {
    apply maponpaths.
    apply (functor_comp (fact_functor (pr1 Lv))).
  }
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
  {
    etrans. apply assoc.
    apply cancel_postcomposition.
    etrans. apply pr1_section_disp_on_morphisms_comp.
    use (section_disp_on_eq_morphisms (pr1 Lv)).
    - use (compose (lnwfs_Σ (pr2 (dob d v)) f)).
      use mors_to_arrow_mor.
      * exact (identity _).
      * exact (arrow_mor11 (colimIn (ccμ f) v)).
      * abstract (
          etrans; [apply id_left|];
          exact (LNWFS_colim_comul_monad_ax_subproof1 f v)
        ).
    - apply pathsinv0.
      etrans. apply cancel_postcomposition.
              exact (lnwfs_Σ_top_map_id (pr2 Lv) f).
      reflexivity.
    - etrans. apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC dbase f)).
      reflexivity.
  }
  etrans. apply cancel_precomposition.
          apply cancel_postcomposition.
          exact (pathsinv0 (pr1_section_disp_on_morphisms_comp (pr1 Lv) _ _)).
  etrans. apply assoc.
  etrans. apply cancel_postcomposition, assoc.
  etrans. apply assoc'.
  etrans. apply cancel_postcomposition.
          exact (pr2 (pathsdirprodweq (base_paths _ _ (law3 f)))).

  etrans. apply assoc'.
  apply pathsinv0.
  etrans. apply assoc'.
  etrans. apply assoc'.
  apply cancel_precomposition.

  set (mor := (three_mor_mor01
                (section_nat_trans_data (colim_nat_trans_in_data CC dbase H) f))).
  set (LΣnatFinff := nat_trans_ax (pr12 Lv) _ _ mor).
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          exact (pr2 (pathsdirprodweq (base_paths _ _ LΣnatFinff))).
  etrans. apply assoc'.
  apply cancel_precomposition.
  etrans. apply (pr1_section_disp_on_morphisms_comp (pr1 Lv)).
  apply pathsinv0.
  etrans. apply (pr1_section_disp_on_morphisms_comp (pr1 Lv)).
  apply (section_disp_on_eq_morphisms (pr1 Lv)); [reflexivity|].
  (* cbn. *)
  etrans. apply (colimOfArrowsIn _ _ (CC g
                  (mapdiagram (PrecategoryBinProduct.pr2_functor C C)
                    (mapdiagram (pr1_category (arrow_disp C))
                        (LNWFS_diagram_pointwise_comul_mor f))))).
  reflexivity.
Qed.

Local Lemma LNWFS_colim_comul_data_subproof1
    (f : arrow C)
    (v : vertex g) :
  three_mor11
      (# (fact_functor (pr1 (dob d v))) (three_mor_mor01 (section_nat_trans (colimIn Finf v) f)))
    · fact_R (pr1 (dob d v)) (fact_L (colim Finf) f) =
    fact_R (pr1 (dob d v)) (fact_L (pr1 (dob d v)) f)
    · colimIn (CCFf_pt_ob1 CC dbase f) v.
Proof.
  set (Lv := dob d v).
  set (Lcin := # (fact_functor (pr1 Lv)) (three_mor_mor01 (section_nat_trans (colimIn Finf v) f))).
  set (comm12 := pr2 (three_mor_comm Lcin)).
  apply pathsinv0.
  exact comm12.
Qed.

Lemma LNWFS_colim_comul_monad_ax :
    disp_Comonad_laws (L_monad_data (colim Finf) LNWFS_colim_comul).
Proof.
  repeat split; intro f.
  - apply arrow_mor_eq; [etrans; [apply assoc'|]; etrans; [apply id_left|]; apply id_left|].
    apply pathsinv0.
    apply colim_endo_is_identity.
    intro v.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply assoc.
    etrans. do 2 apply cancel_postcomposition.
            apply (colimOfArrowsIn).
    etrans. apply assoc4.
    etrans. apply cancel_postcomposition, cancel_precomposition.
            apply (colimOfArrowsIn).
    etrans. apply cancel_postcomposition, assoc.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply (colimArrowCommutes).

    set (law1v := @Comonad_law1 _ (L_monad _ _ (pr22 (dob d v))) f).

    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            exact (LNWFS_colim_comul_data_subproof1 f v).

    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            exact (pr2 (pathsdirprodweq (base_paths _ _ law1v))).
    apply id_left.
  - apply arrow_mor_eq; [etrans; [apply assoc'|]; etrans; [apply id_left|]; apply id_left|].
    apply pathsinv0.
    apply colim_endo_is_identity.
    intro v.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply assoc.
    etrans. do 2 apply cancel_postcomposition.
            apply (colimOfArrowsIn).
    (* cbn. *)
    etrans. apply assoc4.
    etrans. apply cancel_postcomposition, cancel_precomposition.
    {
      set (ccmor := (CC g
            (mapdiagram (PrecategoryBinProduct.pr2_functor C C)
              (mapdiagram (pr1_category (arrow_disp C))
                  (LNWFS_diagram_pointwise_comul_mor f))))).
      apply (colimOfArrowsIn _ _ ccmor).
    }
    (* cbn.  *)
    etrans. apply cancel_postcomposition, assoc.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
    {
      set (ccmor := (CCFf_pt_ob1 CC dbase
            (make_dirprod (three_ob0 (f,, ColimFf_ob CC dbase v0 f))
              (colim (CCFf_pt_ob1 CC dbase f)),,
            pr12 ((pr11 (dob d v0)) f) · colimIn (CCFf_pt_ob1 CC dbase f) v0))).
      apply (colimOfArrowsIn _ _ ccmor).
    }
    etrans. apply assoc.
    apply pathsinv0.
    etrans. apply (pathsinv0 (id_left _)).
    apply cancel_postcomposition.
    set (law2v := @Comonad_law2 _ (L_monad _ _ (pr22 (dob d v))) f).
    etrans. exact (pathsinv0 (pr2 (pathsdirprodweq (base_paths _ _ law2v)))).
    apply pathsinv0.
    etrans. apply assoc'.
    apply cancel_precomposition.
    etrans. apply pr1_section_disp_on_morphisms_comp.
    apply section_disp_on_eq_morphisms; [apply id_left|].
    apply (colimArrowCommutes (CCFf_pt_ob1 CC dbase f)).
  - apply arrow_mor_eq; [reflexivity|].
    use colimArrowUnique'.
    intro v.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply assoc.
    etrans. do 2 apply cancel_postcomposition.
            apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC dbase f)).
    etrans. apply assoc'.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
    {
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply (colimOfArrowsIn).
      etrans. apply assoc'.
      apply cancel_precomposition.
      set (ccinf := CCFf_pt_ob1 CC dbase (fact_L (colim Finf) f)).
      apply (colimArrowCommutes ccinf).
    }
    apply pathsinv0.
    (* cbn. *)
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply assoc.
    etrans. do 2 apply cancel_postcomposition.
            apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC dbase f)).
    etrans. apply assoc'.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
    {
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply (colimOfArrowsIn).
      etrans. apply assoc'.
      apply cancel_precomposition.
      set (ccinf := CCFf_pt_ob1 CC dbase (fact_L (colim Finf) f)).
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply (colimArrowCommutes ccinf).
      etrans. apply assoc'.
      apply cancel_precomposition.
      apply (colimOfArrowsIn).
    }
    etrans. apply assoc.
    etrans. apply assoc.
    etrans. apply assoc.
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply assoc.
    apply cancel_postcomposition.
    exact (LNWFS_colim_comul_monad_ax_subproof f v).
Qed.

Definition ColimLNWFS_disp : LNWFS C (colim Finf) :=
    (LNWFS_colim_comul,, LNWFS_colim_comul_monad_ax).

Definition ColimLNWFS : total_category (LNWFS C) :=
    (_,, ColimLNWFS_disp).

Definition ColimLNWFS_disp_in (v : vertex g) :
    pr2 (dob d v) -->[colimIn Finf v] ColimLNWFS_disp.
Proof.
  split; intro f; (apply subtypePath; [intro; apply homset_property|]); apply pathsdirprod.
  - etrans. apply id_left.
    etrans. apply id_left.
    apply pathsinv0.
    etrans. apply id_right.
    etrans. apply id_right.
    apply (lnwfs_Σ_top_map_id (pr2 (dob d v))).
  - etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC dbase f)).
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply colimOfArrowsIn.
    etrans. apply assoc.
    apply pathsinv0.
    apply cancel_postcomposition.
    apply cancel_precomposition.
    apply section_disp_on_eq_morphisms; reflexivity.
  - apply id_left.
  - apply (colimArrowCommutes (CCFf_pt_ob1 CC dbase f)).
Qed.

Definition ColimLNWFS_in (v : vertex g) :
    dob d v --> ColimLNWFS :=
  (colimIn Finf v,, ColimLNWFS_disp_in v).

Local Open Scope mor_disp.

Lemma project_cocone
    (L : total_category (LNWFS C))
    (cc : cocone d L) :
  cocone dbase (pr1 L).
Proof.
  use make_cocone.
  - intro v.
    exact (pr1 (coconeIn cc v)).
  - abstract (
      intros u v e;
      exact (base_paths _ _ (coconeInCommutes cc _ _ e))
    ).
Defined.

Lemma ColimLNWFS_disp_cc_mor
    {L: total_category (LNWFS C)} (cc : cocone d L) :
  ColimLNWFS_disp
    -->[ColimFf_unique_mor CC dbase v0 (pr1 L) (project_cocone _ cc)]
    (pr2 L).
Proof.
  split; intro f.
  - apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod.
    * etrans. apply id_left.
      apply pathsinv0.
      etrans. apply assoc'.
      etrans. apply assoc'.
      etrans. apply id_left.
      etrans. apply id_left.
      etrans. apply id_left.
      (* cbn. *)
      apply pathsinv0.
      apply (lnwfs_Σ_top_map_id (pr2 L)).
    * use colimArrowUnique'.
      intro v.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply (colimArrowCommutes).
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply assoc.
      etrans. do 2 apply cancel_postcomposition.
              etrans. apply assoc.
              apply cancel_postcomposition.
              apply colimOfArrowsIn.
      etrans. apply assoc'.
      etrans. apply assoc4.
      etrans. apply cancel_postcomposition, cancel_precomposition.
              apply colimArrowCommutes.
      etrans. apply cancel_postcomposition, assoc.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
      {
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply colimOfArrowsIn.
        etrans. apply assoc'.
        apply cancel_precomposition.
        apply colimArrowCommutes.
      }

      apply pathsinv0.
      etrans. exact (pr2 (pathsdirprodweq (base_paths _ _ (pr12 (coconeIn cc v) f)))).
      etrans. apply assoc'.
      apply pathsinv0.
      etrans. apply assoc'.
      apply cancel_precomposition.

      etrans. apply assoc.
      apply cancel_postcomposition.

      etrans. apply (pr1_section_disp_on_morphisms_comp).
      apply section_disp_on_eq_morphisms.
      + apply id_left.
      + apply (colimArrowCommutes (CCFf_pt_ob1 CC dbase f)).
  - apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; [apply id_left|].
    use colimArrowUnique.
    intro v.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply colimArrowCommutes.

    exact (pr2 (pathsdirprodweq (base_paths _ _ (pr22 (coconeIn cc v) f)))).
Qed.

Lemma ColimLNWFS_unique
    {L: total_category (LNWFS C)} (cc : cocone d L) :
  ∃! x : ColimLNWFS --> L,
    ∏ v, ColimLNWFS_in v · x = coconeIn cc v.
Proof.
  set (Ff_unique := ColimFf_unique (v0 := v0) CC _ H _ (project_cocone _ cc)).

  use unique_exists.
  - exists (pr1 (iscontrpr1 Ff_unique)).
    exact (ColimLNWFS_disp_cc_mor cc).
  - abstract (
      intro v;
      apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|];
      apply (pr2 (iscontrpr1 Ff_unique))
    ).
  - abstract (
      intro y; apply impred; intro; apply homset_property
    ).
  - abstract (
      intros y ccy;
      destruct y as [Fy Ly];
      use total2_paths2_f; [|apply isaprop_lnwfs_mor_axioms];
      set (Ff_uniqueness := λ t, base_paths _ _ (iscontr_uniqueness Ff_unique t));
      use (Ff_uniqueness (Fy,, _));
      intro v;
      exact (base_paths _ _ (ccy v))
    ).
Defined.

Lemma ColimLNWFSCocone :
  ColimCocone d.
Proof.
  use make_ColimCocone.
  - exists (colim Finf).
    exact (ColimLNWFS_disp).
  - use make_cocone.
    * intro v.
      exists (colimIn Finf v).
      exact (ColimLNWFS_disp_in v).
    * abstract (
        intros u v e;
        apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|];
        exact (colimInCommutes Finf _ _ e)
      ).
  - intros L cc; exact (ColimLNWFS_unique cc).
Defined.

End LNWFS_cocomplete.

Lemma ChainsLNWFS {C : category} (HC : Colims C) :
    Chains (total_category (LNWFS C)).
Proof.
  intros d.
  use (ColimLNWFSCocone HC).
  - exact is_connected_nat_graph.
  - exact 0.
Defined.

Lemma CoequalizersLNWFS {C : category} (HC : Colims C) :
    Coequalizers (total_category (LNWFS C)).
Proof.
  intros F G f g.
  use (ColimLNWFSCocone HC).
  - exact is_connected_coequalizer_graph.
  - exact (● 0)%stn.
Defined.
