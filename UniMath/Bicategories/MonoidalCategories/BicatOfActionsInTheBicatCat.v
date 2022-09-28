Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.
(*
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
*)
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalSectionsWhiskered.
Require Import UniMath.Bicategories.MonoidalCategories.EndofunctorsWhiskeredMonoidal.

Require Import UniMath.Bicategories.MonoidalCategories.WhiskeredMonoidalFromBicategory.
Require Import UniMath.Bicategories.MonoidalCategories.ActionBasedStrongFunctorsWhiskeredMonoidal.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.

Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.Bicategories.MonoidalCategories.BicatOfActionsInBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Import Bicat.Notations.
Import BifunctorNotations.
Import DisplayedBifunctorNotations.

Local Open Scope cat.

About monoidal_from_bicat_and_ob.


(* Definition bicatactionbicat : bicat := total_bicat bidisp_actionbicat_disp_bicat. *)

(* object in bicatactionbicat := ∑ C : Cat, (∑ FA: functor V (category_from_bicat_and_ob a0),
                fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA)). *)

Section ActegoriesReorderd.

  Context {V : category} (Mon_V : monoidal V).

  Definition actegory_reordered : UU
    := ∑ C : category,
        (∑ a : action (V := V) C,
            (∑ alf : (∑ alf : (actor_data Mon_V a × action_unitor_data Mon_V a),
                action_unitor_nat Mon_V (pr2 alf)
                                  ×
                                  (
                                    actor_nat_leftwhisker Mon_V (pr1 alf) ×
                                    actor_nat_rightwhisker Mon_V (pr1 alf) ×
                                    actor_nat_leftrightwhisker Mon_V (pr1 alf)
                                  )),
                  ∑ asf : (actorinv_data Mon_V a × action_unitorinv_data Mon_V a),
                    action_unitor_iso_law Mon_V (pr21 alf) (pr2 asf) × actor_iso_law Mon_V (pr11 alf) (pr1 asf) × actegory_triangle_identity Mon_V (pr21 alf) (pr11 alf) × actegory_pentagon_identity Mon_V (pr11 alf)
            )
        ).

  Definition actegory_reordered_action (a : actegory_reordered)
    : action (V := V) (pr1 a) := pr12 a.
  Definition actegory_reordered_actor_data (a : actegory_reordered)
    : actor_data Mon_V (actegory_reordered_action a) := pr11 (pr122 a).
  Definition actegory_reordered_unitor_data (a : actegory_reordered)
    : action_unitor_data Mon_V (actegory_reordered_action a) := pr21 (pr122 a).
  Definition actegory_reordered_unitor_nat (a : actegory_reordered)
    : action_unitor_nat Mon_V (actegory_reordered_unitor_data a) := pr12 (pr122 a).
  Definition actegory_reordered_actor_nat (a : actegory_reordered)
    : (actor_nat_leftwhisker Mon_V (actegory_reordered_actor_data a)
                             × actor_nat_rightwhisker Mon_V (actegory_reordered_actor_data a)
                             × actor_nat_leftrightwhisker Mon_V (actegory_reordered_actor_data a))
    := pr22 (pr122 a).
  Definition actegory_reordered_actorinv_data (a : actegory_reordered)
    : actorinv_data Mon_V (actegory_reordered_action a) := pr11 (pr222 a).
  Definition actegory_reordered_unitorinv_data (a : actegory_reordered)
    : action_unitorinv_data Mon_V (actegory_reordered_action a) := pr21 (pr222 a).
  Definition actegory_reordered_unitor_iso (a : actegory_reordered)
    : action_unitor_iso_law Mon_V
                            (actegory_reordered_unitor_data a)
                            (actegory_reordered_unitorinv_data a)
    := pr12 (pr222 a).
  Definition actegory_reordered_actor_iso (a : actegory_reordered)
    : actor_iso_law Mon_V
                            (actegory_reordered_actor_data a)
                            (actegory_reordered_actorinv_data a)
    := pr122 (pr222 a).
  Definition actegory_reordered_triangle (a : actegory_reordered)
    : actegory_triangle_identity Mon_V
                            (actegory_reordered_unitor_data a)
                            (actegory_reordered_actor_data a)
    := pr1 (pr222 (pr222 a)).
  Definition actegory_reordered_pentagon (a : actegory_reordered)
    : actegory_pentagon_identity Mon_V (actegory_reordered_actor_data a)
    := pr2 (pr222 (pr222 a)).

  Definition actegory_reorderd_equiv_actegory
    : (∑ C : category, actegory Mon_V C) ≃ actegory_reordered.
  Proof.
    apply weqfibtototal.
    intro C.
    use weq_iso.
    - intro act.
      exists (actegory_action Mon_V act).
      use tpair.
      exists (actegory_actordata act ,, actegory_unitordata act).
      {
        repeat split.
        apply actegory_unitornat.
        apply actegory_actornatleft.
        apply actegory_actornatright.
        apply actegory_actornatleftright.
      }
      exists (actegory_actorinvdata act ,, actegory_unitorinvdata act).
      split.
      apply actegory_unitorisolaw.
      split.
      apply actegory_actorisolaw.
      split.
      apply actegory_triangleidentity.
      apply actegory_pentagonidentity.
    - intro act.
      use tpair.
      + exists (actegory_reordered_action (C,,act)).
        exists (actegory_reordered_unitor_data (C,,act)).
        exists (actegory_reordered_unitorinv_data (C,,act)).
        exists (actegory_reordered_actor_data (C,,act)).
        exact (actegory_reordered_actorinv_data (C,,act)).
      + repeat split
        ; try (apply (actegory_reordered_unitor_nat (C,,act)))
        ; try (apply (actegory_reordered_unitor_iso (C,,act)))
        ; try (apply (actegory_reordered_actor_nat (C,,act)))
        ; try (apply (actegory_reordered_actor_iso (C,,act))).
        exact (actegory_reordered_triangle (C,,act)).
        exact (actegory_reordered_pentagon (C,,act)).
    - intro ; apply idpath.
    - intro ; apply idpath.
  Defined.

End ActegoriesReorderd.

Section ActegoriesReorderedInv.

  Context {V : category} (Mon_V : monoidal V).

  Definition actegory_reorderd_inverses_data {C : category} (a : action (V := V) C)
    : UU := actorinv_data Mon_V a × action_unitorinv_data Mon_V a.

  Definition actegory_reorderd_inverses_actor
             {C : category} {a : action (V := V) C}
             (i : actegory_reorderd_inverses_data a)
    : actorinv_data Mon_V a := pr1 i.
  Definition actegory_reorderd_inverses_unitor
             {C : category} {a : action (V := V) C}
             (i : actegory_reorderd_inverses_data a)
    : action_unitorinv_data Mon_V a := pr2 i.

  Definition actegory_reordered_inverses_nat
             {C : category} {a : action (V := V) C}
             (i : actegory_reorderd_inverses_data a)
    : UU := action_unitorinv_nat Mon_V (actegory_reorderd_inverses_unitor i)
      × ∏ (v w : V) (z z' : C) (h : C⟦z,z'⟧),
      (v ⊗^{a}_{l} (w ⊗^{a}_{l} h)) · (actegory_reorderd_inverses_actor i v w z')
      = (actegory_reorderd_inverses_actor i v w z) · ((v ⊗_{Mon_V} w) ⊗^{a}_{l} h)
      × ∏ (v v' w : V) (z: C) (f : V⟦v,v'⟧),
      (f ⊗^{a}_{r} (w ⊗_{a} z)) ·  (actegory_reorderd_inverses_actor i v' w z)
      = (actegory_reorderd_inverses_actor i v w z) · ((f ⊗^{Mon_V}_{r} w) ⊗^{a}_{r} z)
      × ∏ (v w w' : V) (z : C) (g : V⟦w,w'⟧),
      (v ⊗^{a}_{l} (g ⊗^{a}_{r} z)) · (actegory_reorderd_inverses_actor i v w' z)
      = (actegory_reorderd_inverses_actor i v w z) · ((v ⊗^{Mon_V}_{l} g) ⊗^{a}_{r} z).

  Definition actegory_reorderd_inverses
             {C : category} (a : action (V := V) C)
    : UU := ∑ i : actegory_reorderd_inverses_data a, actegory_reordered_inverses_nat i.

  Definition actegory_reorderd : UU
    := ∑ C : category,
        (∑ a : action (V := V) C,
            (∑ asf : actegory_reorderd_inverses a,
                (∑ alf : (actor_data Mon_V a × action_unitor_data Mon_V a),
                    action_unitor_iso_law Mon_V (pr2 alf) (pr21 asf)
                    × actor_iso_law Mon_V (pr1 alf) (pr11 asf)
                    × actegory_triangle_identity Mon_V (pr2 alf) (pr1 alf)
                    × actegory_pentagon_identity Mon_V (pr1 alf)
                )
            )
        ).

End ActegoriesReorderedInv.

Section ActegoryToObject.

  Context {V : category}.
  Context {Mon_V : monoidal V}.

  (* Notation "X ⊗ Y" := (X ⊗_{ Mon_V } Y). *)

  Import ActegoryNotations.

  (*Lemma action_equiv_object {C : category}
    : V ⟶ precategory_data_from_bicat_and_ob (C : bicat_of_cats)
        ≃ action (V := V) C.
  Proof.
    exact (weqinvweq _ _ (bifunctor_equiv_functorintoendofunctorcat V C C)).
  Defined.

  Definition object_equiv_actegory_reorderd
    : ob (bicatactionbicat (monoidal_swapped Mon_V) bicat_of_cats)
         ≃ actegory_reorderd Mon_V.
  Proof.
    apply weqfibtototal.
    intro C.
    use weqtotal2.
    { apply action_equiv_object. }
    intro act.
    use weq_iso.
    - intro fm.
      repeat (use tpair).
      + exact (λ v w c, pr1 (fmonoidal_preservestensordata fm w v) c).
      + exact (λ c, pr1 (fmonoidal_preservesunit fm) c).
      + intros c1 c2 f.
        cbn.
        admit.
      + intro ; intros.
        cbn.
        admit.
      + exact (λ v w c, pr11 (fmonoidal_preservestensorstrongly fm w v) c).
      + exact (λ c, pr11 (fmonoidal_preservesunitstrongly fm) c).
      + cbn.
        (*Check (fmonoidal_preservesunitstrongly fm).

        intro c. apply (pr2 (z_iso_inv (fmonoidal_preservesunitstrongly fm) c)).*)
        admit.
      + intros v w c.
        set (i := pr2 (z_iso_inv (pointwise_z_iso_from_preserves_tensor_strongly (pr12 fm) w v))).
        split.
        * apply (toforallpaths _ _ _ (base_paths _ _ (pr12 i)) c).
        * apply (toforallpaths _ _ _ (base_paths _ _ (pr22 i)) c).
      + intros c1 c2.
        cbn.
        admit.
      + intros v1 v2 v3 c.
        cbn.
        admit.
    - intro a.
      repeat (use tpair).
      + intros v1 v2.
        exists (λ c, pr111 a v2 v1 c).
        exact (λ c1 c2 f, pr1 (pr221 a v2 v1 c1 c2 f)).
      + exact (λ c, pr211 a c).
      + exact (λ c1 c2 f, ! pr121 a c1 c2 f).
      + intros v1 v2 v3 g.
        use nat_trans_eq.
        { apply homset_property. }
        intro c.
        cbn.
        admit.
      + (* preserves_tensor_nat_right *)
        admit.
      + admit.
      + admit.
      + admit.
      + cbn.
        unfold preserves_tensor_strongly.
        intros v w.
        use tpair.
        * cbn.
          use make_nat_trans.


          (*Check (actegory_unitorinvnat Mon_V _ c1 c2 f).*)
          (* apply maponpaths.
      cbn.
      unfold monoidal_unit.
      unfold functoronmorphisms1.
      etrans.
      2: {
        apply maponpaths_2.
        apply (! bifunctor_rightid _ _  _).
      }
      apply (! id_left _).

        apply  fmonoidal_preservesleftunitalityinv .




      exact (λ c, pr11 (fmonoidal_preservesunitstrongly fm) c).
      + intro ; intros.
        cbn.
        apply TODO.
      + intro ; intros ; cbn. apply TODO.
      + intro ; intros ; cbn. apply TODO.
      + intro ; intros ; cbn. apply TODO.
      + exact (λ v w c, pr1 (fmonoidal_preservestensordata fm w v) c).
      + exact (λ c, pr1 (fmonoidal_preservesunit fm) c).
      + cbn. apply TODO.
      + apply TODO.
      + apply TODO.
      + apply TODO.
    - intro a.
      repeat (use tpair).
      + intros v w.
        exists (λ c, pr112 a w v c).
        intros c1 c2 f.
        cbn.
        *)


  Admitted.



*)


(* End ActegoriesReorderd.*)





(*Definition actegory_reorderd_equiv_actegory
    : (∑ C : category, actegory (monoidal_swapped Mon_V) C) ≃ actegory_reorderd.
  Proof.
    apply weqfibtototal.
    intro C.
    use weq_iso.
    - intro act.
      exists (actegory_action Mon_V act).
      use tpair.
      exists (actegory_actorinvdata act ,, actegory_unitorinvdata act).
      {
        repeat split.
        apply actegory_unitorinvnat.
        apply actorinv_nat_leftwhisker.
        apply actorinv_nat_rightwhisker.
        apply actorinv_nat_leftrightwhisker.
      }

      exists (actegory_actordata act ,, actegory_unitordata act).
      split.
      apply actegory_unitorisolaw.
      split.
      apply actegory_actorisolaw.
      split.
      apply actegory_triangleidentity.
      apply actegory_pentagonidentity.
    - intro act.
      use tpair.
      + exists (pr1 act).
        exists (pr2 (pr122 act)).
        exists (pr2 (pr112 act)).
        exists (pr1 (pr122 act)).
        exact (pr1 (pr112 act)).
      + repeat split
        ; try (apply (pr222 act)).
        apply TODO.
        apply TODO.
        apply TODO.
        apply TODO.
    - admit.
    - admit.
  Admitted.*)








Section ActegoriesEquivObjects.

  Lemma isaprop_fmonoidal_laxlaws {V W : category}
        {Mon_V : monoidal V} {Mon_W : monoidal W}
        {F : functor V W}
        (pt : preserves_tensordata Mon_V Mon_W F)
        (pu : preserves_unit Mon_V Mon_W F)
    : isaprop (fmonoidal_laxlaws (pt,,pu)).
  Proof.
    repeat apply isapropdirprod ; repeat (apply impred_isaprop ; intro) ; apply homset_property.
  Qed.

  Lemma isaprop_fmonoidal_laws {V W : category}
        {Mon_V : monoidal V} {Mon_W : monoidal W}
        {F : functor V W}
        (pt : preserves_tensordata Mon_V Mon_W F)
        (pu : preserves_unit Mon_V Mon_W F)
    : isaprop (fmonoidal_stronglaws pt pu).
  Proof.
    apply isapropdirprod ; (repeat (apply impred_isaprop ; intro) ; apply isaprop_is_z_isomorphism).
  Qed.

  Context {V : category} (Mon_V : monoidal V).

  Definition actegory_equiv_object
    : ob (bicatactionbicat (monoidal_swapped Mon_V) bicat_of_cats)
         ≃ ∑ C : category, actegory Mon_V C.
  Proof.
    use weq_iso.
    - exact (λ a, (_ ,, actegory_from_object (monoidal_swapped Mon_V) a)).
    - exact (λ a, (_ ,, pr2 (actegory_to_object (pr2 a)))).
    - intro a.
      use total2_paths_f.
      { apply idpath. }
      use total2_paths_f.
      { exact (bifunctor_from_to (pr12 a)). }
      use total2_paths_f.
      2: { apply isaprop_fmonoidal_laws. }
      use total2_paths_f.
      2: { apply isaprop_fmonoidal_laxlaws. }
      use total2_paths_f.
      + cbn.

        match goal with |[ |- pr111 (transportf _ _ ?A) = _ ] => set (Z := A) end.
        match goal with |[ |- pr111 (transportf _ ?A _) = _ ] => set (B := A) end.

        apply funextsec ; intro v1.
        apply funextsec ; intro v2.
        unfold fmonoidal ; rewrite pr1_transportf.
        unfold fmonoidal_lax ; rewrite pr1_transportf.
        unfold fmonoidal_data ; unfold dirprod ; rewrite pr1_transportf.


        use nat_trans_eq.
        { apply homset_property. }
        intro c.
        unfold preserves_tensordata.

        (* refine (idpath (pr1 (transportf
    (λ x : V ⟶ precategory_data_from_bicat_and_ob (pr1 a),
     preserves_tensordata (monoidal_swapped Mon_V) (monoidal_from_bicat_and_ob (pr1 a)) x)
    (bifunctor_from_to (pr12 a)) (pr111 Z) v1 v2) c ) @ _). *)










        match goal with |[ |- ?LHS = _ ] => set (L := LHS) end.
        match goal with |[ |- _ = ?RHS ] => set (R := RHS) end.


        admit.
      + Check   pr211 (pr22 a).
        rewrite transportf_const.
        cbn.
        unfold fmonoidal.
        rewrite pr1_transportf.
        unfold fmonoidal_lax ; rewrite pr1_transportf.
        unfold fmonoidal_data.
        rewrite pr2_transportf.
        unfold preserves_unit.

        use total2_paths_f.
        2: { apply isaprop_is_nat_trans ; apply homset_property. }

        cbn.
        unfold nat_trans.
        rewrite pr1_transportf.
        apply funextsec ; intro c.
        cbn.
        unfold nat_trans_data.
        rewrite transportf_sec_constant.
        unfold unitorinv_from_object.
        unfold fmonoidal_preservesunit.
        cbn.

        match goal with |[ |- transportf _ _ ?cc = _ ] => set (L := cc) end.
        cbn in L.
        match goal with |[ |- _ = ?cc0 ] => set (L0 := cc0) end.
        cbn in L0.
        rewrite functtransportf.

        assert (pf0 : (maponpaths (λ x : V ⟶ precategory_data_from_bicat_and_ob (pr1 a), pr1 (x (monoidal_unit Mon_V)) c)
                             (bifunctor_from_to (pr12 a)))  = idpath _).
        {
          admit.
        }
        etrans. {
          apply maponpaths_2.
          exact pf0.
        }
        apply idpath.




    - intro act.
      cbn.
      use total2_paths_f.
      { apply idpath. }
      use total2_paths_f.
      2: { apply isaprop_actegory_laws. }
      use total2_paths_f.
      { exact (bifunctor_to_from _). }
      use total2_paths_f.
      {
        unfold dirprod.
        rewrite pr1_transportf.
        apply funextsec ; intro c.
        cbn.
        unfold action_unitor_data.
        rewrite transportf_sec_constant.
        unfold unitor_from_object.
        cbn.
        unfold actegory_unitordata.


        Check  (pr121 (pr2 act)) c.
        Check transportf_set.
        Check  (bifunctor_to_from (pr2 act)).
        Check pr2 (pr2 act).



        admit.
      }
      use total2_paths_f.
      {
        unfold dirprod.
        rewrite pr1_transportf.
        rewrite transportf_const.
        simpl.
        etrans. {
          apply maponpaths.
          apply (pr2_transportf (A :=  action (pr1 act)) (B1 := λ x,  action_unitor_data Mon_V x)
                                (B2 := λ x, ∑ (_ : action_unitorinv_data Mon_V x), ∑ (_ : actor_data Mon_V x), actorinv_data Mon_V x)).
        }
        rewrite pr1_transportf.
        simpl.
        unfold unitorinv_from_object.
        cbn.
        unfold actegory_unitorinvdata.
        apply funextsec ; intro c.
        simpl.
        cbn.
        Search (transportf (λ _ : _, _) _ _).
        unfold action_unitorinv_data.
        rewrite transportf_sec_constant.
        cbn.

        Check  (bifunctor_to_from (pr2 act)).


        admit.
      }
      use total2_paths_f.
      {
        simpl.
        rewrite transportf_const.
        simpl.
        cbn.
        rewrite pr2_transportf.
        rewrite transportf_const.
        simpl.
        rewrite pr2_transportf.
        rewrite pr2_transportf.
        unfold dirprod.
        rewrite pr1_transportf.
        simpl.
        apply funextsec ; intro v ;
        apply funextsec ; intro w ;
          apply funextsec ; intro c.
        admit.
      }
      admit.










Section ObjectToActegoryToObject.

  Context {V : category}.
  Context {Mon_V : monoidal V}.

  Notation "X ⊗ Y" := (X ⊗_{ Mon_V } Y).

  Import ActegoryNotations.

  (*Local Notation ACAT := (bicatactionbicat Mon_V bicat_of_cats).*)
  Context {C : bicatactionbicat Mon_V bicat_of_cats}.

  Local Notation action_C := (pr12 C).
  Local Notation action_fmon_lax := (pr122 C).
  Local Notation action_fmon_strong := (pr222 C).

  Definition obj_to_act_to_obj_is_id
    : actegory_to_object (actegory_from_object C) = C.
