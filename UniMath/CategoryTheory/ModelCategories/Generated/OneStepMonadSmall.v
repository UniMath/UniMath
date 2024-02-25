Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pushouts.
Require Import UniMath.CategoryTheory.Limits.Graphs.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.Comonads.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Three.

Require Import UniMath.CategoryTheory.ModelCategories.MorphismClass.
Require Import UniMath.CategoryTheory.ModelCategories.NWFS.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.LiftingWithClass.
Require Import UniMath.CategoryTheory.ModelCategories.Generated.OneStepMonad.
Require Import UniMath.CategoryTheory.ModelCategories.Helpers.

Local Open Scope cat.

Definition presentable {C : category} (x : C) :=
    preserves_colimits_of_shape
      (cov_homSet_functor x)
      nat_graph.

Definition class_presentable {C : category} (J : morphism_class C) :=
    ∏ (g : arrow C), J _ _ g -> (presentable g).

Section OSCSmall.

Context {C : category}.
Context (J : morphism_class C).
Context (CC : Colims C).

Local Definition F1 := one_step_factorization J CC.
Local Definition K := morcls_coprod_functor J CC.

(* lifting problem to base colimit from other colimCocone by
   composing colimArrow *)
Definition morcls_lp_colim_lp_to_morcls_base_colim_lp
    {d : chain (arrow C)}
    {cl : arrow C}
    {cc : cocone d cl}
    (isclCC : isColimCocone d cl cc)
    (S : morcls_lp J cl) :
  morcls_lp J (colim (arrow_colims CC _ d)).
Proof.
  exists (morcls_lp_map S).
  apply (compose S).
  set (clCC := make_ColimCocone _ _ _ isclCC).
  exact (colimArrow clCC _ (colimCocone (arrow_colims CC _ d))).
Defined.

(* diagram of homsets *)
Definition homSet_diagram
    (f : arrow C)
    (d : chain (arrow C)) :=
  mapdiagram (cov_homSet_functor f) d.

Definition homSet_diagram_colim
    (f : arrow C)
    (d : chain (arrow C)) :=
  ColimsHSET _ (homSet_diagram f d).

Definition homSet (f cl : arrow C) : HSET.
Proof.
  use make_hSet.
  - exact (f --> cl).
  - apply homset_property.
Defined.

(* set of lifting problems f --> colim (K d) *)
Definition arrow_colimK_lp_hSet
    (f : arrow C)
    (d : chain (arrow C)) : hSet :=
  homSet f (colim (arrow_colims CC _ (mapdiagram K d))).


(* induced isomorphism on
    lifting problems f --> cl
       ===>
    colim (homSet_diagram_colim)
*)
Definition presentable_lp_homSet_colim_z_iso
    {d : chain (arrow C)}
    {cl : arrow C}
    {cc : cocone d cl}
    (isclCC : isColimCocone d cl cc)
    (f : arrow C)
    (Hf : presentable f) :
  z_iso
    (homSet f cl)
    (colim (homSet_diagram_colim f d)).
Proof.
  set (homset_ccbase_isCC := Hf _ _ _ isclCC).
  set (homset_ccbase_CC := make_ColimCocone _ _ _ homset_ccbase_isCC).
  set (homset_iso := isColim_is_z_iso _ (ColimsHSET _ (homSet_diagram f d)) _ _ homset_ccbase_isCC).
  exact ((_,, is_z_isomorphism_inv homset_iso) : z_iso _ _).
Defined.

(* lifting problem J --> cl as element in colim (homSet_diagram (pr1 S) d) *)
Definition presentable_lp_homSet_colim_arrow
    {d : chain (arrow C)}
    {cl : arrow C}
    {cc : cocone d cl}
    (isclCC : isColimCocone d cl cc)
    (S : morcls_lp J cl)
    (HS : presentable (pr1 (morcls_lp_map S))) :
  pr1hSet (colim (homSet_diagram_colim (pr1 (morcls_lp_map S)) d)).
Proof.
  set (homset_ccbase_isCC := HS _ _ _ (pr2 (arrow_colims CC _ d))).
  set (homset_ccbase_CC := make_ColimCocone _ _ _ homset_ccbase_isCC).
  set (homset_iso := isColim_is_z_iso _ (ColimsHSET _ (homSet_diagram (pr1 (morcls_lp_map S)) d)) _ _ homset_ccbase_isCC).
  exact (pr1 homset_iso (pr2 (morcls_lp_colim_lp_to_morcls_base_colim_lp isclCC S))).
Defined.

(* inclusion of arrow into CoproductArrow in the arrow category *)
Definition morcls_lp_coprod_in
    {f : arrow C}
    (S : morcls_lp J f) :
  pr1 (morcls_lp_map S) --> morcls_lp_coprod CC J f.
Proof.
  use mors_to_arrow_mor.
  - exact (CoproductIn (morcls_lp_dom_coprod CC J f) S).
  - exact (CoproductIn (morcls_lp_cod_coprod CC J f) S).
  - abstract (
      exact (CoproductOfArrows'In _ _ (morcls_lp_dom_coprod CC J f) _ _ S)
    ).
Defined.

(* HSET colimit base, i.e. pairs of (v : vertex nat_graph, S : f --> dob d v) *)
Local Definition HSETcobase (f : arrow C) (d : chain (arrow C)) :=
    Colimits.cobase _ (homSet_diagram f d).

(* given a lp (f, S) : morcls_lp J cl,
   a map from HSET colimit base (i.e. pairs of (v, f --> dob d v))
   to lifting problems f --> (colim (K d)) *)
(* we will use this to define a map from the colimit *)
Definition presentable_lp_homSet_colim_colimK_fun
    (d : chain (arrow C))
    {cl : arrow C}
    (S : morcls_lp J cl) :
  HSETcobase (pr1 (morcls_lp_map S)) d
  -> pr1hSet (arrow_colimK_lp_hSet (pr1 (morcls_lp_map S)) d).
Proof.
  intro vS'.
  destruct vS' as [v S'].
  set (S'lp := (morcls_lp_map S,, S') : morcls_lp J (dob d v)).
  apply (compose (morcls_lp_coprod_in S'lp)).
  exact (colimIn (arrow_colims CC _ (mapdiagram K d)) v).
Defined.

(* helper relation on the function to show that it preserves
   the colimit equivalence relation on HSETcobase *)
Local Definition presentable_lp_homSet_colim_colimK_fun_rel
    (d : chain (arrow C))
    {cl : arrow C}
    (S : morcls_lp J cl) :
  hrel (HSETcobase (pr1 (morcls_lp_map S)) d).
Proof.
  intros uS vT.
  exists (
    presentable_lp_homSet_colim_colimK_fun d S uS
    = presentable_lp_homSet_colim_colimK_fun d S vT
  ).
  apply homset_property.
Defined.

(* we show it is an equivalence relation *)
Local Definition presentable_lp_homSet_colim_colimK_fun_eqrel
    (d : chain (arrow C))
    {cl : arrow C}
    (S : morcls_lp J cl) :
  eqrel (HSETcobase (pr1 (morcls_lp_map S)) d).
Proof.
  exists (presentable_lp_homSet_colim_colimK_fun_rel d S).
  abstract (
    repeat split;
      [ intros x y z H1 H2 ;
        exact (pathscomp0 H1 H2)
      |
        intros x y H;
        exact (pathsinv0 H)
      ]
  ).
Defined.

(* we show that our equivalence relation holds, whenever two
   pairs (u,, f --> dob d u) and (v,, f --> dob d v)
   are related through the relation on HSETcobase,
   i.e. there is a morphism dob d u --> dob d v
   such that the composite with dob d u is equal to dob d v.
   This is the exact relation that we want to find back in
   our proofs later "if it holds for all (u,, f --> dob d u),
   then our proof holds"
*)
Lemma presentable_lp_homSet_colim_colimK_fun_rel0_impl
    (d : chain (arrow C))
    {cl : arrow C}
    (S' : morcls_lp J cl)
    (uS vT : (HSETcobase (pr1 (morcls_lp_map S')) d))
    (HuSvT : Colimits.rel0 _ _ uS vT) :
  presentable_lp_homSet_colim_colimK_fun_eqrel d S' uS vT.
Proof.
  use HuSvT. clear HuSvT.
  intro H; simpl.
  destruct H as [f Hf].
  destruct uS as [u Su].
  destruct vT as [v Tv].

  unfold presentable_lp_homSet_colim_colimK_fun.
  cbn in f.
  induction f.
  etrans. apply maponpaths.
          set (ccincomm := colimInCommutes (arrow_colims CC nat_graph (mapdiagram K d)) _ _ (idpath (S u))).
          exact (pathsinv0 ccincomm).
  rewrite assoc.
  apply (cancel_postcomposition _ _ (colimIn (arrow_colims CC nat_graph (mapdiagram K d)) (S u))).
  use arrow_mor_eq.
  - etrans. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_dom_coprod CC J (dob d u)) _ _ (morcls_lp_map S',, Su)).
    etrans. apply id_left.
    cbn.
    morcls_lp_coproduct_in_eq.
    use arrow_mor_eq.
    * use (pathscomp1 (arrow_mor00_eq Hf)); [|reflexivity].
      etrans. apply assoc'.
      apply id_left.
    * use (pathscomp1 (arrow_mor11_eq Hf)); [|reflexivity].
      etrans. apply assoc'.
      apply id_left.
  - etrans. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (dob d u)) _ _ (morcls_lp_map S',, Su)).
    etrans. apply id_left.
    cbn.
    morcls_lp_coproduct_in_eq.
    use arrow_mor_eq.
    * use (pathscomp1 (arrow_mor00_eq Hf)); [|reflexivity].
      etrans. apply assoc'.
      apply id_left.
    * use (pathscomp1 (arrow_mor11_eq Hf)); [|reflexivity].
      etrans. apply assoc'.
      apply id_left.
Qed.

(* This implies that our equivalence relation
   holds whenever two pairs are related by the closure
   of the relations on HSETcobase *)
Lemma presentable_lp_homSet_colim_colimK_fun_rel_impl
    (d : chain (arrow C))
    {cl : arrow C}
    (S : morcls_lp J cl)
    (uS vT : (HSETcobase (pr1 (morcls_lp_map S)) d))
    (HuSvT : Colimits.rel _ _ uS vT) :
  presentable_lp_homSet_colim_colimK_fun_eqrel d S uS vT.
Proof.
  set (meqrel := @minimal_eqrel_from_hrel _ (Colimits.rel0 _ (homSet_diagram (pr1 (morcls_lp_map S)) d))).
  set (presfun := presentable_lp_homSet_colim_colimK_fun_eqrel d S).

  apply (meqrel presfun).
  - apply (presentable_lp_homSet_colim_colimK_fun_rel0_impl d S).
  - trivial.
Qed.

(* This in turn implies that our function is compatible
   with the equivalence relation on ColimHSET of HSETcobase *)
Definition presentable_lp_homSet_colim_colimK_fun_iscomprel
    (d : chain (arrow C))
    {cl : arrow C}
    (S : morcls_lp J cl)
    (HS : presentable (pr1 (morcls_lp_map S))) :
  iscomprelfun
      (Colimits.rel _ (homSet_diagram (pr1 (morcls_lp_map S)) _))
      (presentable_lp_homSet_colim_colimK_fun d S).
Proof.
  intros uS' vT'.
  apply presentable_lp_homSet_colim_colimK_fun_rel_impl.
Qed.

(* This allows us to use the function to define an arrow
   f --> colim (K d)
  given any lifting problem f --> cl for cl a colimit on d *)
Definition presentable_lp_colimK_mor
    {d : chain (arrow C)}
    {cl : arrow C}
    {cc : cocone d cl}
    (isclCC : isColimCocone d cl cc)
    (S : morcls_lp J cl)
    (HS : presentable (pr1 (morcls_lp_map S))) :
  pr1 (morcls_lp_map S) --> colim (arrow_colims CC _ (mapdiagram K d)).
Proof.
  set (f := presentable_lp_homSet_colim_colimK_fun d S).
  set (fcomprel := presentable_lp_homSet_colim_colimK_fun_iscomprel d S HS).
  set (homset_colim_arrow := presentable_lp_homSet_colim_arrow isclCC S HS).
  exact (setquotuniv _ _ f fcomprel homset_colim_arrow).
Defined.

(* ABSOLUTELY disgusting *)
(* we want to show that the arrow f --> colim (K d) we get
   for any lifting problem of the form Sv · coconeIn cc v
   is the same as the canonical projection of (v,, Sv)
   down to the set quotient. *)
Lemma presentable_lp_homSet_colim_arrow_of_factored_arrow
    {d : chain (arrow C)}
    {cl : arrow C}
    {cc : cocone d cl}
    (isclCC : isColimCocone d cl cc)
    {v : vertex nat_graph}
    (S : morcls_lp J (dob d v))
    (HS : presentable (pr1 (morcls_lp_map S))) :
  let Sin := (pr1 S,, pr2 S · coconeIn cc v) : morcls_lp J cl in
  presentable_lp_homSet_colim_arrow isclCC Sin HS
  = setquotpr (Colimits.eqr _ (homSet_diagram (pr1 (morcls_lp_map Sin)) d)) (v,, pr2 S).
Proof.
  intro Sin.
  set (homset_ccbase_isCC := HS _ _ _ (pr2 (arrow_colims CC _ d))).
  set (homset_ccbase_CC := make_ColimCocone _ _ _ homset_ccbase_isCC).
  set (homset_iso := isColim_is_z_iso _ (ColimsHSET _ (homSet_diagram (pr1 (morcls_lp_map S)) d)) _ _ homset_ccbase_isCC).
  set (carrcomm := colimArrowCommutes (homset_ccbase_CC) _ (colimCocone (ColimsHSET _ (homSet_diagram (pr1 (morcls_lp_map S)) d))) v).
  use (pathscomp1 (funeq carrcomm (pr2 S))); [|reflexivity].
  etrans. use (funeq _ (pr2 S)).
          2: {
            use (colimArrowCommutes (homset_ccbase_CC)).
          }
  (* unfold Sinarr. *)
  unfold presentable_lp_homSet_colim_arrow.
  set (iso := isColim_is_z_iso
          _
          (ColimsHSET nat_graph
            (homSet_diagram (pr1 (morcls_lp_map Sin)) d))
          _ _
          (HS d (pr11 (arrow_colims CC nat_graph d))
            (pr21 (arrow_colims CC nat_graph d))
            (pr2 (arrow_colims CC nat_graph d)))).
  set (ziso := (_,, iso) : z_iso _ _).
  set (iso_rel := pr122 ziso).
  assert (X : pr2 (morcls_lp_colim_lp_to_morcls_base_colim_lp isclCC Sin) = pr1 ziso (coconeIn
                  (colimCocone
                    (ColimsHSET nat_graph
                        (homSet_diagram (pr1 (morcls_lp_map S)) d))) v
                  (pr2 S))).
  {
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply (colimArrowCommutes (make_ColimCocone _ _ _ isclCC)).
    apply pathsinv0.
    etrans. apply assoc'.
    use arrow_mor_eq; apply id_left.
  }
  rewrite X.
  apply pathsinv0.
  etrans. use (funeq iso_rel).
  reflexivity.
Qed.

(* we can use this to show that the following relation holds
   for any such arrow *)
Lemma presentable_lp_colimK_mor_coconeInCommutes
    {d : chain (arrow C)}
    {cl : arrow C}
    {cc : cocone d cl}
    (isclCC : isColimCocone d cl cc)
    {v : vertex nat_graph}
    (S : morcls_lp J (dob d v))
    (HS : presentable (pr1 (morcls_lp_map S))) :
  presentable_lp_colimK_mor isclCC (pr1 S,, pr2 S · coconeIn cc v) HS
  = morcls_lp_coprod_in S · colimIn (arrow_colims CC _ (mapdiagram K d)) v.
Proof.
  set (Sin := (pr1 S,, pr2 S · coconeIn cc v) : morcls_lp J cl).
  unfold presentable_lp_colimK_mor.
  set (Sinarr := presentable_lp_homSet_colim_arrow isclCC Sin HS).
  set (rel := (Colimits.eqr _ (homSet_diagram (pr1 (morcls_lp_map Sin)) d))).
  set (X := presentable_lp_homSet_colim_arrow_of_factored_arrow isclCC S HS : Sinarr = setquotpr rel (v,, pr2 S)).
  rewrite X.
  etrans. exact (
    setquotunivcomm
      rel
      _
      (presentable_lp_homSet_colim_colimK_fun d Sin)
      (presentable_lp_homSet_colim_colimK_fun_iscomprel d Sin HS)
      (v,, pr2 S)
  ).
  unfold presentable_lp_homSet_colim_colimK_fun.
  use arrow_mor_eq; reflexivity.
Qed.

(* predicate type to show relations on f --> cl given
   that it holds for any (v,, Sv · colimIn cc v) *)
Local Definition predicate_type
    (d : chain (arrow C))
    (cl : arrow C)
    (f : arrow C) :=
  (f --> cl) -> hProp.

(* disgusting, but very useful *)
(* we show that a predicate on a lifting problem f --> cl
   holds whenever it holds for any (Sv · colimIn cc v) for
   a pair (v,, Sv : f --> dob d v) *)
Definition presentable_lp_colimK_mor_univ
    {d : chain (arrow C)}
    {cl : arrow C}
    {cc : cocone d cl}
    (isclCC : isColimCocone d cl cc)
    (S : morcls_lp J cl)
    (HS : presentable (pr1 (morcls_lp_map S)))
    (P : predicate_type d cl (pr1 (morcls_lp_map S)))
    (PS : ∏ (v : vertex nat_graph)
      (Sv : pr1hSet (dob (homSet_diagram (pr1 (morcls_lp_map S)) d) v)),
        P (Sv · (colimIn (make_ColimCocone _ _ _ isclCC) v))) :
  P (pr2 S).
Proof.
  set (homset_z_iso := presentable_lp_homSet_colim_z_iso isclCC (pr1 (morcls_lp_map S)) HS).
  set (Srew := funeq (pr122 homset_z_iso) (pr2 S)).
  change (P (identity (homSet (pr1 (morcls_lp_map S)) cl) (pr2 S))).
  rewrite <- Srew.
  set (Spr := (pr1 homset_z_iso) (pr2 S)).
  change (P ((pr12 homset_z_iso) Spr)).

  simpl.
  unfold colimArrow.
  simpl.
  unfold from_colimHSET.
  simpl.
  set (rel := (Colimits.eqr _ (homSet_diagram (pr1 (morcls_lp_map S)) d))).
  transparent assert (pred : (pr1hSet (colim (homSet_diagram_colim (pr1 (morcls_lp_map S)) d)) -> hProp)).
  {
    intro S'.
    exact (P
      (setquotuniv
        rel
        _
        (Colimits.from_cobase _ _ _
            (mapcocone (cov_homSet_functor (pr1 (morcls_lp_map S))) d cc))
        (iscomprel_from_base _ _ _
            (mapcocone (cov_homSet_functor (pr1 (morcls_lp_map S))) d cc))
        S'
      )
    ).
  }
  use (setquotunivprop rel pred).
  intro uSu.
  change (pred (setquotpr rel uSu)).
  unfold pred.
  set (predcomm := setquotunivcomm
    rel
    _
    (Colimits.from_cobase _ _ _
        (mapcocone (cov_homSet_functor (pr1 (morcls_lp_map S))) d cc))
    (iscomprel_from_base _ _ _
        (mapcocone (cov_homSet_functor (pr1 (morcls_lp_map S))) d cc))
    uSu
  ).
  rewrite predcomm.
  destruct uSu as [u Su].
  change (P (identity _ · Su · (colimIn (make_ColimCocone _ _ _ isclCC) u))).
  rewrite id_left.
  exact (PS u Su).
Qed.

(* we use thsi to show the following relation *)
Lemma presentable_lp_colimK_mor_colimArrowCommutes
    {d : chain (arrow C)}
    {cl : arrow C}
    {cc : cocone d cl}
    (isclCC : isColimCocone d cl cc)
    (S : morcls_lp J cl)
    (HS : presentable (pr1 (morcls_lp_map S))) :
  presentable_lp_colimK_mor isclCC S HS
  · colimArrow (arrow_colims CC _ (mapdiagram K d)) _ (mapcocone K d cc)
  = morcls_lp_coprod_in S.
Proof.
  unfold presentable_lp_colimK_mor.

  set (g := (morcls_lp_map S)).
  transparent assert (pred : (predicate_type d cl (pr1 g))).
  {
    intro S'.
    use make_hProp.
    - exact (
        presentable_lp_colimK_mor isclCC (g,, S') HS
        · colimArrow (arrow_colims CC _ (mapdiagram K d)) _ (mapcocone K d cc)
        = morcls_lp_coprod_in (g,, S')
      ).
    - apply homset_property.
  }

  use (presentable_lp_colimK_mor_univ isclCC S HS pred).
  intros u Su.
  set (Su' := (pr1 S,, Su) : morcls_lp J (dob d u)).
  unfold pred.
  simpl.
  etrans. apply maponpaths_2.
          exact (presentable_lp_colimK_mor_coconeInCommutes isclCC Su' HS).
  use subtypePath; [intro; apply homset_property|].
  apply pathsdirprod.
  - etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply (colimArrowCommutes (CC _ (project_diagram00 (mapdiagram K d)))).
    etrans. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_dom_coprod CC J (dob d u)) _ _ Su').
    apply id_left.
  - etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply (colimArrowCommutes (CC _ (project_diagram11 (mapdiagram K d)))).
    etrans. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (dob d u)) _ _ Su').
    apply id_left.
Qed.

(* The main proof of interest! *)
Lemma K_small_if_J_small :
  class_presentable J
  -> preserves_colimits_of_shape K nat_graph.
Proof.
  intros HJ.
  intros d cl cc isclCC.

  set (clCC := make_ColimCocone _ _ _ isclCC).
  set (Kd00 := project_diagram00 (mapdiagram K d)).
  set (Kd11 := project_diagram11 (mapdiagram K d)).

  use (is_z_iso_isColim _ (arrow_colims CC _ (mapdiagram K d))).
  use tpair.
  - use mors_to_arrow_mor.
    * use CoproductArrow.
      intro S.
      exact (arrow_mor00 (presentable_lp_colimK_mor isclCC S (HJ _ (pr2 (morcls_lp_map S))))).
    * use CoproductArrow.
      intro S.
      exact (arrow_mor11 (presentable_lp_colimK_mor isclCC S (HJ _ (pr2 (morcls_lp_map S))))).
    * abstract (
        use CoproductArrow_eq;
        intro S;
        etrans; [apply assoc|];
        etrans; [apply cancel_postcomposition;
                apply (CoproductInCommutes (morcls_lp_dom_coprod CC J cl))|];
        apply pathsinv0;
        etrans; [apply assoc|];
        etrans; [apply cancel_postcomposition;
                apply (CoproductOfArrows'In _ _ (morcls_lp_dom_coprod CC J cl) _ _ S)|];
        etrans; [apply assoc'|];
        etrans; [apply cancel_precomposition;
                apply (CoproductInCommutes (morcls_lp_cod_coprod CC J cl))|];
        set (mor := (presentable_lp_colimK_mor isclCC S (HJ _ (pr2 (morcls_lp_map S)))));
        exact (pathsinv0 (arrow_mor_comm mor))
      ).
  - split.
    * apply pathsinv0.
      use (colim_endo_is_identity).
      intro v.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply (colimArrowCommutes).
      use arrow_mor_eq.
      + use CoproductArrow_eq.
        intro S.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply (CoproductOfArrowsInclusionIn _ (morcls_lp_dom_coprod CC J (dob d v))).
        etrans. apply assoc'.
        etrans. apply id_left.
        etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J cl) _ (pr1 S,, _)).
        exact (arrow_mor00_eq (presentable_lp_colimK_mor_coconeInCommutes isclCC S (HJ _ (pr2 (morcls_lp_map S))))).
      + use CoproductArrow_eq.
        intro S.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (dob d v))).
        etrans. apply assoc'.
        etrans. apply id_left.
        etrans. apply (CoproductInCommutes (morcls_lp_cod_coprod CC J cl) _ (pr1 S,, _)).
        exact (arrow_mor11_eq (presentable_lp_colimK_mor_coconeInCommutes isclCC S (HJ _ (pr2 (morcls_lp_map S))))).
    * use arrow_mor_eq.
      + use CoproductArrow_eq.
        intro S.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply (CoproductInCommutes (morcls_lp_dom_coprod CC J cl) _ S).
        apply pathsinv0.
        etrans. apply id_right.
        apply pathsinv0.
        exact (arrow_mor00_eq (presentable_lp_colimK_mor_colimArrowCommutes isclCC S (HJ _ (pr2 (morcls_lp_map S))))).
      + use CoproductArrow_eq.
        intro S.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply (CoproductInCommutes (morcls_lp_cod_coprod CC J cl) _ S).
        apply pathsinv0.
        etrans. apply id_right.
        apply pathsinv0.
        exact (arrow_mor11_eq (presentable_lp_colimK_mor_colimArrowCommutes isclCC S (HJ _ (pr2 (morcls_lp_map S))))).
Qed.

(* no need for information about f here,
   this morphism is just the pushout square *)
Definition K_L1_colim_mor (f : arrow C) :
   K f --> fact_L F1 f.
Proof.
 use mors_to_arrow_mor.
 * exact (arrow_mor00 (morcls_lp_coprod_diagram CC J f)).
 * exact (PushoutIn1 (morcls_lp_coprod_diagram_pushout CC J f)).
 * abstract (
     set (pocomm := PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout CC J f));
     exact (pathsinv0 pocomm)
   ).
Defined.

(* this is just the pushout square again *)
Definition colim_K_L1_mor_pointwise
  {g : graph}
  (d : diagram g (arrow C))
  (v : vertex g) :
    dob (mapdiagram K d) v
    --> dob (mapdiagram (fact_L F1) d) v :=
  K_L1_colim_mor (dob d v).

(* pushouts and coproducts commute *)
Lemma colim_K_L1_mor_commutes
    {g : graph} (d : diagram g (arrow C))
    {u v : vertex g} (e : edge u v) :
  dmor (mapdiagram K d) e · colim_K_L1_mor_pointwise d v
  = colim_K_L1_mor_pointwise d u · dmor (mapdiagram (fact_L F1) d) e.
Proof.
  use arrow_mor_eq.
  - etrans. apply (precompWithCoproductArrowInclusion).
    use CoproductArrow_eq.
    intro S.
    etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J (dob d u))).
    etrans. apply id_left.
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (CoproductInCommutes (morcls_lp_dom_coprod CC J (dob d u))).
    reflexivity.
  - use CoproductArrow_eq.
    intro S.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (dob d u))).
    apply pathsinv0.
    etrans. apply cancel_precomposition.
            apply (PushoutArrow_PushoutIn1).
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (dob d u))).
    reflexivity.
Qed.

(* colim (K fi) --> colim (L1 fi) *)
Definition colim_K_L1_mor
    {g : graph} (d : diagram g (arrow C)) :
  colim (arrow_colims CC g (mapdiagram K d))
  --> colim (arrow_colims CC g (mapdiagram (fact_L F1) d)).
Proof.
  use colimOfArrows.
  - intro v.
    exact (colim_K_L1_mor_pointwise d v).
  - abstract (
      exact (@colim_K_L1_mor_commutes g d)
    ).
Defined.

(* colim (K fi) --> K (colim fi) *)
Definition can_K_mor
    {g : graph} (d : diagram g (arrow C))
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  z_iso
    (colim (arrow_colims CC g (mapdiagram K d)))
    (K f).
Proof.
  set (HKCC := HK isclCC).
  set (K_mor := isColim_is_z_iso _ (arrow_colims CC _ (mapdiagram K d)) _ _ HKCC).
  exact (_,, K_mor).
Defined.

(* L1 (colim fi) --> colim fi *)
Definition L_colim_id_mor (f : arrow C) :
    fact_L F1 f --> f.
Proof.
  exact (ε (lnwfs_L_monad (one_step_comonad J CC)) f).
Defined.

(* colim (L1 fi) --> colim fi *)
Definition colim_L_id_mor
    {g : graph} (d : diagram g (arrow C))
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf)  :
  colim (arrow_colims CC g (mapdiagram (fact_L F1) d))
  --> f.
Proof.
  use colimArrow.
  set (ccL1f := mapcocone (fact_L F1) _ ccf).
  use make_cocone.
  - intro v.
    use mors_to_arrow_mor.
    * exact (arrow_mor00 (coconeIn ccL1f v)).
    * exact ((arrow_mor11 (coconeIn ccL1f v)) · fact_R F1 f).
    * abstract (
        apply pathsinv0;
        etrans; [apply assoc|];
        etrans; [apply cancel_postcomposition;
                exact (pathsinv0 (arrow_mor_comm (coconeIn ccL1f v)))|];
        etrans; [apply assoc'|];
        apply cancel_precomposition;
        exact (three_comp (fact_functor F1 f))
      ).
  - abstract (
      intros u v e;
      set (ccL1fcomm := coconeInCommutes ccL1f _ _ e);
      use arrow_mor_eq; [
        exact (arrow_mor00_eq ccL1fcomm)
      | etrans; [apply assoc|];
        etrans; [apply cancel_postcomposition;
                 exact (arrow_mor11_eq ccL1fcomm)|];
        reflexivity
      ]
    ).
Defined.

(* we need to know that arrow_dom f is
   a colimit for (L1 d)00, after all, all morphisms
   are identity. We need an isomorphism *)
Definition dom_colim_dom_L1_cocone
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} (ccf : cocone d f):
  cocone (project_diagram00 (mapdiagram (fact_L F1) d)) (arrow_dom f).
Proof.
  use make_cocone.
  - intro v. exact (arrow_mor00 (coconeIn ccf v)).
  - abstract (intros u v e; exact (arrow_mor00_eq (coconeInCommutes ccf _ _ e))).
Defined.

Definition dom_colim_dom_L1_isColimCocone
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf) :
  isColimCocone _ _ (dom_colim_dom_L1_cocone ccf).
Proof.
  set (base_mor := isColim_is_z_iso _ (arrow_colims CC _ d) _ _ isclCC).
  use (is_z_iso_isColim _ (CC _ (project_diagram00 (mapdiagram (fact_L F1) d)))).
  exists (arrow_mor00 (pr1 base_mor)).
  abstract (
    split; [
      etrans; [|exact (arrow_mor00_eq (pr12 base_mor))];
      apply cancel_postcomposition
      | etrans; [|exact (arrow_mor00_eq (pr22 base_mor))];
        apply cancel_precomposition
    ]; (
      use colimArrowUnique;
      intro v;
      etrans; [apply colimArrowCommutes|];
      reflexivity
    )
  ).
Defined.

(* the isomorphism dom f --> colim (L1 d)00 *)
Definition colim_dom_L1_dom_iso
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf) :
  z_iso
    (arrow_dom f)
    (colim (CC _ (project_diagram00 (mapdiagram (fact_L F1) d)))).
Proof.
  set (fCC := dom_colim_dom_L1_isColimCocone isclCC).
  set (baseCC := CC _ (project_diagram00 (mapdiagram (fact_L F1) d))).
  set (mor := isColim_is_z_iso _ baseCC _ _ fCC).
  exact (z_iso_inv (_,, mor)).
Defined.

(* arrow_dom (L1 colim fi) --> arrow_dom (colim (L1 fi)) *)
Definition L1_colim_L1_map00
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf) :
  arrow_dom (fact_L F1 f)
  --> arrow_dom (colim (arrow_colims CC g (mapdiagram (fact_L F1) d))).
Proof.
  apply (compose (arrow_mor00 (L_colim_id_mor f))).
  exact (colim_dom_L1_dom_iso isclCC).
Defined.

(* K (colim fi) --> colim (L1 fi) *)
(* arrow_mor11 is the bottom pushout map *)
Definition Kcolim_colimL1_mor
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  K f
  --> colim (arrow_colims CC g (mapdiagram (fact_L F1) d)).
Proof.
  apply (compose (z_iso_inv (can_K_mor d HK isclCC))).
  exact (colim_K_L1_mor d).
Defined.

(* top pushout map *)
Definition L1_colim_L1_map_pushoutOut2
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf) :
  arrow_dom (fact_L F1 f)
  --> arrow_cod (colim (arrow_colims CC g (mapdiagram (fact_L F1) d))).
Proof.
  apply (compose (L1_colim_L1_map00 isclCC)).
  exact (colim (arrow_colims CC g (mapdiagram (fact_L F1) d))).
Defined.

(* we show that arrow_dom (K f) is a colimCocone,
   given that (K f) is a colim for the mapped diagram,
   i.e. we project the ColimCocone to the 0 ob/arr *)
Definition L1_colim_L1_map_dom_Kf_is_colimCocone
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf)
    (isHKCC := HK isclCC)
    (HKCC := make_ColimCocone _ _ _ isHKCC)
    (HKCC00 := project_cocone00 (colimCocone HKCC)) :
  isColimCocone _ _ HKCC00 :=
    project_colimcocone00 CC isHKCC.

(* we show that arrow_cod (K f) is a colimCocone,
   given that (K f) is a colim for the mapped diagram,
   i.e. we project the ColimCocone to the 1 ob/arr *)
Definition L1_colim_L1_map_cod_Kf_is_colimCocone
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf)
    (isHKCC := HK isclCC)
    (HKCC := make_ColimCocone _ _ _ isHKCC)
    (HKCC11 := project_cocone11 (colimCocone HKCC)) :
  isColimCocone _ _ HKCC11 :=
    project_colimcocone11 CC isHKCC.

(* we show that the canonical iso from
   K (colim fi) --> colim (K fi)
   projects to the one on the domains *)
Local Lemma colim_iso_inv_projects
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf)
    (dbase := project_diagram00 (mapdiagram K d))
    (isKfCC := L1_colim_L1_map_dom_Kf_is_colimCocone HK isclCC)
    (KfCC := make_ColimCocone _ _ _ isKfCC)
    (Kf_mor := isColim_is_z_iso _ (CC _ dbase) _ _ isKfCC) :
  arrow_mor00 (z_iso_inv (can_K_mor d HK isclCC))
  = pr1 Kf_mor.
Proof.
  set (iso := (_,, Kf_mor) : z_iso _ _).
  apply (post_comp_with_z_iso_is_inj iso).
  apply pathsinv0.
  etrans. exact (pr22 Kf_mor).

  set (can_K_is_iso := pr222 (can_K_mor d HK isclCC)).
  etrans. exact (pathsinv0 (arrow_mor00_eq can_K_is_iso)).
  apply cancel_precomposition.
  use colimArrowUnique.
  intro v.
  etrans. apply (colimArrowCommutes (CC g dbase)).
  reflexivity.
Qed.

Local Lemma L1_colim_L1_map_ispushoutOut_subproof0
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  arrow_mor00 (Kcolim_colimL1_mor HK isclCC)
  · z_iso_inv (colim_dom_L1_dom_iso isclCC)
  = arrow_mor00 (morcls_lp_coprod_diagram CC J f).
Proof.
  set (isKfCC := L1_colim_L1_map_dom_Kf_is_colimCocone HK isclCC).
  set (KfCC := make_ColimCocone _ _ _ isKfCC).

  use (colimArrowUnique' KfCC).
  intro v.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply assoc.
  etrans. do 2 apply cancel_postcomposition.
          etrans. apply cancel_precomposition.
                  exact (colim_iso_inv_projects HK isclCC).
          apply (colimArrowCommutes KfCC).
  etrans. apply cancel_postcomposition.
          apply (colimArrowCommutes (CC _ (project_diagram00 (mapdiagram K d)))).
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          apply (colimArrowCommutes (CC _ (project_diagram00 (mapdiagram (fact_L F1) d)))).

  apply pathsinv0.
  etrans. apply (precompWithCoproductArrowInclusion _ _ (morcls_lp_dom_coprod CC J f)).
  use CoproductArrow_eq.
  intro S.
  etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J (dob d v))).
  etrans. apply id_left.
  apply pathsinv0.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply (CoproductInCommutes (morcls_lp_dom_coprod CC J (dob d v))).
  reflexivity.
Qed.

Lemma L1_colim_L1_map_ispushoutOut_subproof
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  arrow_mor00 (K_L1_colim_mor f)
  · (L1_colim_L1_map00 isclCC)
  = arrow_mor00 (Kcolim_colimL1_mor HK isclCC).
Proof.
  use CoproductArrow_eq.
  intro S.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply (CoproductInCommutes (morcls_lp_dom_coprod CC J f)).
  etrans. apply cancel_precomposition.
          apply id_left.

  apply (post_comp_with_z_iso_is_inj (z_iso_inv (colim_dom_L1_dom_iso isclCC))).
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          exact (pr122 (colim_dom_L1_dom_iso isclCC)).
  etrans. apply id_right.

  apply pathsinv0.
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          exact (L1_colim_L1_map_ispushoutOut_subproof0 HK isclCC).
  etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J f)).
  reflexivity.
Qed.

Lemma L1_colim_L1_map_ispushoutOut
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  K f · arrow_mor11 (Kcolim_colimL1_mor HK isclCC)
  = arrow_mor00 (K_L1_colim_mor f)
  · L1_colim_L1_map_pushoutOut2 isclCC.
Proof.
  apply pathsinv0.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          exact (L1_colim_L1_map_ispushoutOut_subproof HK isclCC).

  exact (arrow_mor_comm (Kcolim_colimL1_mor HK isclCC)).
Qed.

(* the map L1 (colim fi) --> colim (L1 fi)
   that we need, defined with the pushout *)
Definition L1_colim_L1_map
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  fact_L F1 f
  --> colim (arrow_colims CC g (mapdiagram (fact_L F1) d)).
Proof.
  set (KLcolimPO := morcls_lp_coprod_diagram_pushout CC J f).
  use mors_to_arrow_mor.
  * exact (L1_colim_L1_map00 isclCC).
  * use (PushoutArrow KLcolimPO).
    + exact (arrow_mor11 (Kcolim_colimL1_mor HK isclCC)).
    + exact (L1_colim_L1_map_pushoutOut2 isclCC).
    + exact (L1_colim_L1_map_ispushoutOut HK isclCC).
  * abstract (
      set (poin2 := PushoutArrow_PushoutIn2 KLcolimPO _ _ _ (L1_colim_L1_map_ispushoutOut HK isclCC));
      exact (pathsinv0 poin2)
    ).
Defined.

(* the canonical arrow from f --> (colim CC d)
   (where the colimit is not necessarily f)
   projects down to the colimArrow on the domains  *)
Local Lemma colimArrow_projects
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf)
    (fcc := make_ColimCocone d f ccf isclCC)
    (domfcc := make_ColimCocone _ _ _ (dom_colim_dom_L1_isColimCocone isclCC)) :
  arrow_mor00 (colimArrow fcc _ (colimCocone (arrow_colims CC _ d)))
  = colimArrow domfcc _ (colimCocone (CC _ (project_diagram00 d))).
Proof.
  use (colimArrowUnique' domfcc).
  intro v.
  etrans. exact (arrow_mor00_eq (colimArrowCommutes fcc _ (colimCocone (arrow_colims CC _ d)) v)).
  apply pathsinv0.
  etrans. apply colimArrowCommutes.
  reflexivity.
Qed.

Local Lemma colimIn00_L1_colim_L1_commutes
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf)
    (v : vertex g) :
    arrow_mor00 (coconeIn (mapcocone (fact_L F1) d ccf) v · L1_colim_L1_map HK isclCC) =
    arrow_mor00 (colimIn (arrow_colims CC g (mapdiagram (fact_L F1) d)) v).
Proof.
  set (domfiscc := dom_colim_dom_L1_isColimCocone isclCC).
  set (domfcc := make_ColimCocone _ _ _ domfiscc).
  etrans. apply cancel_precomposition.
          apply id_left.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          etrans. apply cancel_precomposition.
                  exact (colimArrow_projects isclCC).
          apply (colimArrowCommutes domfcc).
  etrans. apply (colimArrowCommutes (CC _ (project_diagram00 d))).
  reflexivity.
Qed.
(*
Local Lemma arrow_mor11_comp
    {f g h : arrow C}
    (γ : f --> g)
    (γ' : g --> h) :
  arrow_mor11 γ · arrow_mor11 γ' = arrow_mor11 (γ · γ').
Proof.
  reflexivity.
Qed. *)

Local Lemma colimIn11_Kcolim_colimL1_commutes
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf)
    (v : vertex g)
    (iscodKfCC := L1_colim_L1_map_cod_Kf_is_colimCocone HK isclCC)
    (codKfCC := make_ColimCocone _ _ _ iscodKfCC) :
  colimIn codKfCC v · arrow_mor11 (Kcolim_colimL1_mor HK isclCC)
  = PushoutIn1 (morcls_lp_coprod_diagram_pushout CC J (dob d v))
  · colimIn (CC _ (project_diagram11 (mapdiagram (fact_L F1) d))) v.
Proof.
  set (isHKCC := HK isclCC).
  set (HKCC := make_ColimCocone _ _ _ isHKCC).
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          exact (arrow_mor11_eq (colimArrowCommutes HKCC _ _ v)).
  etrans. apply (colimArrowCommutes (CC _ (project_diagram11 (mapdiagram K d)))).
  reflexivity.
Qed.

Lemma L1_colim_L1_map_is_inverse_in_precat
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  is_inverse_in_precat
    (colimArrow (arrow_colims CC _ (mapdiagram (fact_L F1) d)) _ (mapcocone (fact_L F1) d ccf))
    (L1_colim_L1_map HK isclCC).
Proof.
  set (isHKCC := HK isclCC).
  set (HKCC := make_ColimCocone _ _ _ isHKCC).

  set (isKfCC := L1_colim_L1_map_dom_Kf_is_colimCocone HK isclCC).
  set (KfCC := make_ColimCocone _ _ _ isKfCC).
  set (domfiscc := dom_colim_dom_L1_isColimCocone isclCC).
  set (domfcc := make_ColimCocone _ _ _ domfiscc).
  set (iscodKfCC := L1_colim_L1_map_cod_Kf_is_colimCocone HK isclCC).
  set (codKfCC := make_ColimCocone _ _ _ iscodKfCC).
  split.
  - apply pathsinv0.
    apply colim_endo_is_identity.
    intro v.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (colimArrowCommutes).
    use arrow_mor_eq.
    * exact (colimIn00_L1_colim_L1_commutes HK isclCC v).
    * use (MorphismsOutofPushoutEqual (isPushout_Pushout (morcls_lp_coprod_diagram_pushout CC J (dob d v)))).
      + etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply (PushoutArrow_PushoutIn1).
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply PushoutArrow_PushoutIn1.

        exact (colimIn11_Kcolim_colimL1_commutes HK isclCC v).
      + etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply (PushoutArrow_PushoutIn2).
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply PushoutArrow_PushoutIn2.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                exact (colimIn00_L1_colim_L1_commutes HK isclCC v).
        etrans. apply (colimArrowCommutes (CC _ (project_diagram00 d))).
        reflexivity.
  - use arrow_mor_eq.
    * apply pathsinv0.
      use (colim_endo_is_identity _ domfcc).
      intro v.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              exact (colimIn00_L1_colim_L1_commutes HK isclCC v).
      etrans. apply (colimArrowCommutes (CC _ (project_diagram00 (mapdiagram (fact_L F1) d)))).
      reflexivity.
    * use (MorphismsOutofPushoutEqual (isPushout_Pushout (morcls_lp_coprod_diagram_pushout CC J f))).
      + etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply PushoutArrow_PushoutIn1.
        apply pathsinv0.
        etrans. apply id_right.
        apply pathsinv0.

        use (colimArrowUnique' codKfCC).
        intro v.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                exact (colimIn11_Kcolim_colimL1_commutes HK isclCC v).
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply (colimArrowCommutes (CC _ (project_diagram11 (mapdiagram (fact_L F1) d)))).
        etrans. apply PushoutArrow_PushoutIn1.
        reflexivity.
      + etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply PushoutArrow_PushoutIn2.
        apply pathsinv0.
        etrans. apply id_right.
        apply pathsinv0.
        use (colimArrowUnique' domfcc).
        intro v.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                etrans. apply assoc.
                apply cancel_postcomposition.
                exact (colimIn00_L1_colim_L1_commutes HK isclCC v).
        etrans. apply cancel_postcomposition.
                apply (colimArrowCommutes (CC _ (project_diagram00 d))).
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply (colimArrowCommutes (CC _ (project_diagram11 (mapdiagram (fact_L F1) d)))).
        etrans. apply PushoutArrow_PushoutIn2.
        reflexivity.
Qed.

(* Main result *)
Lemma L1_preserves_colim_if_K_preserves_colim
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} (ccf : cocone d f) :
  preserves_colimit K _ _ ccf
  -> preserves_colimit (fact_L F1) _ _ ccf.
Proof.
  intros HK isclCC.

  set (isHKCC := HK isclCC).
  set (HKCC := make_ColimCocone _ _ _ isHKCC).

  use (is_z_iso_isColim _ (arrow_colims CC _ (mapdiagram (fact_L F1) d))).
  exists (L1_colim_L1_map HK isclCC).
  exact (L1_colim_L1_map_is_inverse_in_precat HK isclCC).
Defined.

(* applying the main result *)
Lemma L1_small_if_K_small :
  preserves_colimits_of_shape K nat_graph
  -> preserves_colimits_of_shape (fact_L F1) nat_graph.
Proof.
  intro HK.
  intros d cl cc.
  apply L1_preserves_colim_if_K_preserves_colim.
  apply HK.
Qed.

End OSCSmall.
