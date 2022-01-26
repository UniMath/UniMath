(**
“Displayed equivalences” of displayed (pre)categories
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

(* TODO: move somewhere.  Not sure where? [Constructions]? *)
Section Essential_Surjectivity.

Definition fiber_functor_ess_split_surj
    {C C' : category} {D} {D'}
    {F : functor C C'} (FF : disp_functor F D D')
    (H : disp_functor_ff FF)
    {X : disp_functor_ess_split_surj FF}
    {Y : is_op_isofibration D}
  (* TODO: change to [is_isofibration], once [is_isofibration_iff_is_op_isofibration] is provided *)
    (x : C)
  : ∏ yy : D'[{F x}], ∑ xx : D[{x}],
                iso (fiber_functor FF _ xx) yy.
Proof.
  intro yy.
  set (XR := X _ yy).
  destruct XR as [c'' [i [xx' ii]]].
  set (YY := Y _ _ i xx').
  destruct YY as [ dd pe ].
  use tpair.
  - apply dd.
  -
    (* now need disp_functor_on_iso_disp *)
    set (XR := disp_functor_on_iso_disp FF pe).
    set (XR' := iso_inv_from_iso_disp XR).
    (* now need composition of iso_disps *)
    apply  (invweq (iso_disp_iso_fiber _ _ _ _)).
    set (XRt := iso_disp_comp XR' ii).
    transparent assert (XH :
           (iso_comp (iso_inv_from_iso (functor_on_iso F i))
             (functor_on_iso F i) = identity_iso _ )).
    { apply eq_iso. cbn. simpl. unfold precomp_with.
      etrans. apply maponpaths_2. apply id_right.
      etrans. eapply pathsinv0. apply functor_comp.
      etrans. 2: apply functor_id.
      apply maponpaths. apply iso_after_iso_inv.
   }
    set (XRT := transportf (λ r, iso_disp r (FF x dd) yy )
                           XH).
    apply XRT.
    assumption.
Defined.

End Essential_Surjectivity.

(** * General definition of displayed adjunctions and equivalences *)

(** * Main definitions *)

(** ** Adjunctions *)
Section Adjunctions.

(** In general, one can define displayed equivalences/adjunctions over any equivalences/adjunctions between the bases (and probably more generally still).  For now we just give the case over a single base precategory — i.e. over an identity functor.

We give the “bidirectional” version first, and then the “handed” versions afterwards, with enough coercions between the two to (hopefully) make it easy to work with both versions. *)

(* TODO: consider carefully the graph of coercions in this section; make them more systematic, and whatever we decide on, DOCUMENT the system clearly. *)



(** Triangle identies for an adjunction *)

(** Note: the statements of these axioms include [_statement_] to distinguish them from the _instances_ of these statements given by the access functions of [form_adjunction].

This roughly follows the pattern of [univalenceStatement], [funextfunStatement], etc., but departs from it slightly to follow our more general convention of using underscores instead of camelcase.
*)


(** The “left-handed” version: right adjoints to a given functor *)



(* TODO: add the dual-handedness version, i.e. indexed over GG instead of FF. *)
End Adjunctions.




(** *** Converse functor *)

(* TODO: does [Local Definition] actually keep it local?  It seems not — e.g. [Print GG_data] still works after the section closes. Is there a way to actually keep them local?  If not, find less generic names for [GG] and its components. *)

(*
Local Definition GG_data : disp_functor_data (functor_identity _ ) D D'.
Proof.
  use tpair.
  + intros x xx. exact (pr1 (FF_split x xx)).
  + intros x y xx yy f ff; simpl.
    set (Hxx := FF_split x xx).
    set (Hyy := FF_split y yy).
    apply FFinv.
    refine (transportf (mor_disp _ _) _ _). Focus 2.
    exact ((pr2 Hxx ;; ff) ;; inv_mor_disp_from_iso (pr2 Hyy)).
    cbn. etrans. apply id_right. apply id_left.
Defined.
*)

(*
Local Lemma GG_ax : disp_functor_axioms GG_data.
Proof.
  split; simpl.
  + intros x xx.
    apply invmap_eq. cbn.
    etrans. Focus 2. apply @pathsinv0, (disp_functor_id FF).
    etrans. apply maponpaths.
      etrans. apply maponpaths_2, id_right_disp.
      etrans. apply mor_disp_transportf_postwhisker.
      apply maponpaths, (inv_mor_after_iso_disp (pr2 (FF_split _ _))).
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    unfold transportb. apply maponpaths_2, homset_property.
  + intros x y z xx yy zz f g ff gg.
    apply invmap_eq. cbn.
    etrans. Focus 2. apply @pathsinv0.
      etrans. apply (disp_functor_comp FF).
      etrans. apply maponpaths.
        etrans. apply maponpaths; use homotweqinvweq.
        apply maponpaths_2; use homotweqinvweq.
      etrans. apply maponpaths.
        etrans. apply mor_disp_transportf_prewhisker.
        apply maponpaths.
        etrans. apply mor_disp_transportf_postwhisker.
        apply maponpaths.
        etrans. apply maponpaths, assoc_disp_var.
        etrans. apply mor_disp_transportf_prewhisker.
        apply maponpaths.
        etrans. apply assoc_disp.
        apply maponpaths.
        etrans. apply maponpaths_2.
          etrans. apply assoc_disp_var.
          apply maponpaths.
          etrans. apply maponpaths.
            refine (iso_disp_after_inv_mor (pr2 (FF_split _ _))).
          etrans. apply mor_disp_transportf_prewhisker.
          etrans. apply maponpaths, id_right_disp.
          apply transport_f_f.
        etrans. apply maponpaths_2, transport_f_f.
        apply mor_disp_transportf_postwhisker.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      etrans. apply transport_f_f.
      (* A trick to hide the huge equality term: *)
      apply maponpaths_2. shelve.
    etrans. apply maponpaths.
      etrans. apply maponpaths_2, assoc_disp.
      etrans. apply mor_disp_transportf_postwhisker.
      apply maponpaths. apply assoc_disp_var.
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    apply maponpaths_2, homset_property.
    Unshelve. Focus 2. apply idpath.
Qed.
*)
(*
Definition GG : disp_functor _ _ _ := (_ ,, GG_ax).
*)
(*
Definition ε_ses_ff_data
  : disp_nat_trans_data (nat_trans_id _ )
      (disp_functor_composite GG FF) (disp_functor_identity _ )
:= λ x xx, (pr2 (FF_split x xx)).
*)
(*
Lemma ε_ses_ff_ax : disp_nat_trans_axioms ε_ses_ff_data.
Proof.
  intros x y f xx yy ff. cbn. unfold ε_ses_ff_data.
  etrans. apply maponpaths_2; use homotweqinvweq.
  etrans. apply mor_disp_transportf_postwhisker.
  etrans. apply maponpaths.
    etrans. apply assoc_disp_var.
    apply maponpaths.
    etrans. apply maponpaths.
      apply (iso_disp_after_inv_mor (pr2 (FF_split _ _))).
    etrans. apply mor_disp_transportf_prewhisker.
    apply maponpaths, id_right_disp.
  etrans. apply transport_f_f.
  etrans. apply transport_f_f.
  etrans. apply transport_f_f.
  unfold transportb. apply maponpaths_2, homset_property.
Qed.
*)
(*
Definition ε_ses_ff
  : disp_nat_trans (nat_trans_id _ )
      (disp_functor_composite GG FF) (disp_functor_identity _ )
:= (ε_ses_ff_data,, ε_ses_ff_ax).
*)
(*
Definition η_ses_ff_data
  : disp_nat_trans_data (nat_trans_id _)
      (disp_functor_identity _ ) (disp_functor_composite FF GG).
Proof.
  intros x xx. cbn.
  apply FFinv.
  refine (inv_mor_disp_from_iso (pr2 (FF_split _ _))).
Defined.
*)
(*
Definition η_ses_ff_ax
  : disp_nat_trans_axioms η_ses_ff_data.
Proof.
  intros x y f xx yy ff. cbn. unfold η_ses_ff_data.
  (* This feels a bit roundabout.  Can it be simplified? *)
  apply @pathsinv0.
  etrans. eapply maponpaths.
    etrans. apply @pathsinv0, disp_functor_ff_inv_compose.
    apply maponpaths.
    etrans. apply mor_disp_transportf_prewhisker.
    apply maponpaths.
    etrans. apply assoc_disp.
    apply maponpaths.
    etrans. apply maponpaths_2.
      etrans. apply assoc_disp.
      apply maponpaths.
      etrans.
        apply maponpaths_2, (iso_disp_after_inv_mor (pr2 (FF_split _ _))).
      etrans. apply mor_disp_transportf_postwhisker.
      etrans. apply maponpaths, id_left_disp.
      apply transport_f_f.
    etrans. apply maponpaths_2, transport_f_f.
    apply mor_disp_transportf_postwhisker.
  etrans. apply maponpaths.
    etrans. apply maponpaths.
      etrans. apply transport_f_f.
      apply transport_f_f.
    apply FFinv_transportf.
  etrans. apply transport_f_f.
  apply transportf_comp_lemma_hset.
    apply homset_property.
  etrans. apply (disp_functor_ff_inv_compose _ FF_ff).
  apply maponpaths_2, homotinvweqweq.
Qed.
*)
(*
Definition η_ses_ff
  : disp_nat_trans (nat_trans_id _)
      (disp_functor_identity _ ) (disp_functor_composite FF GG)
:= (_ ,, η_ses_ff_ax).
*)
(*
Definition GGεη : right_adjoint_over_id_data FF
  := (GG,, (η_ses_ff,, ε_ses_ff)).
*)
(*
Lemma form_equiv_GGεη : form_equiv_over_id GGεη.
Proof.
  split; intros x xx; cbn.
  - unfold η_ses_ff_data.
    apply (@FFinv_on_iso_is_iso _ _ _ _ (identity_iso _)).
    eapply is_iso_disp_independent_of_is_iso.
    exact (@is_iso_inv_from_iso_disp _ _ _ _ (identity_iso _) _ _ _).
  - unfold ε_ses_ff_data.
    apply is_iso_disp_from_iso.
Qed.
*)
(*
Lemma tri_1_GGεη : triangle_1_statement_over_id GGεη.
Proof.
  intros x xx; cbn.
  unfold ε_ses_ff_data, η_ses_ff_data.
  etrans. apply maponpaths_2; use homotweqinvweq.
  etrans. exact (iso_disp_after_inv_mor (pr2 (FF_split _ _))).
  apply maponpaths_2, homset_property.
Qed.
*)
(*
Lemma tri_2_GGεη : triangle_2_statement_over_id GGεη.
Proof.
  apply triangle_2_from_1_for_equiv_over_id.
  apply form_equiv_GGεη.
  apply tri_1_GGεη.
Qed.
*)
(*
Theorem is_equiv_from_ff_ess_over_id : is_equiv_over_id FF.
Proof.
  simple refine ((GGεη,, _) ,, _).
  split. apply tri_1_GGεη. apply tri_2_GGεη.
  apply form_equiv_GGεη.
Defined.
*)

(** ** Inverses and composition of adjunctions/equivalences *)
(*
Section Nat_Trans_Disp_Inv.

Context {C : category} {D' D : disp_cat C}
        {FF GG : disp_functor (functor_identity _) D' D}
        (alpha : disp_nat_trans (nat_trans_id _ ) FF GG)
        (Ha : ∏ x xx, is_iso_disp (identity_iso _ ) (alpha x xx)).

(*
Lemma inv_ax : disp_nat_trans_axioms
    (λ (x : C) (xx : D' x), @inv_mor_disp_from_iso _ _ _ _ (identity_iso _ ) _  _ _ (Ha x xx)).
*)

Local Lemma inv_ax : @disp_nat_trans_axioms C C (functor_identity_data C)
    (functor_identity_data C) (@nat_trans_id C C (functor_identity_data C))
    D' D GG FF
    (λ (x : C) (xx : D' x),
     @inv_mor_disp_from_iso C D ((functor_identity C) x)
       ((functor_identity C) x) (@identity_iso C ((functor_identity C) x))
       (FF x xx) (GG x xx) (alpha x xx) (Ha x xx)).
Proof.
     intros x y f xx yy ff.
    apply pathsinv0.
    apply Utilities.transportf_pathsinv0.
    apply pathsinv0.
    set (XR := @iso_disp_precomp).
    specialize (XR _ _ _ _ (identity_iso _ ) _ _ (alpha x xx ,, Ha x xx) ).
    match goal with |[|- ?EE = _ ] => set (E := EE) end. cbn in E.
    specialize (XR _ (identity x ;; f)%mor (FF y yy)).
    set (R := make_weq _ XR).
    apply (invmaponpathsweq R).
    unfold R. unfold E. cbn.
    etrans. apply assoc_disp.
    etrans. apply maponpaths. apply maponpaths_2.
            apply (inv_mor_after_iso_disp (Ha x xx)).
    etrans. apply maponpaths.
            apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans.            apply mor_disp_transportf_prewhisker.
    etrans. apply maponpaths.
            apply assoc_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths_2.
            apply (disp_nat_trans_ax_var alpha).
    etrans. apply maponpaths.
            apply mor_disp_transportf_postwhisker.
    etrans.    apply transport_f_f.
    etrans. apply maponpaths. apply assoc_disp_var.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths.
            apply (inv_mor_after_iso_disp (Ha _ _ )).
    etrans. apply maponpaths.
            apply mor_disp_transportf_prewhisker.

     etrans. apply transport_f_f.
    etrans. apply maponpaths. apply id_right_disp.
    etrans. apply transport_f_f.
    apply maponpaths_2.
    apply homset_property.
Qed.

Local Definition inv : disp_nat_trans (nat_trans_id _ ) GG FF.
Proof.
  use tpair.
  - intros x xx.
    apply (inv_mor_disp_from_iso (Ha _ _ )).
  - apply inv_ax.
Defined.

End Nat_Trans_Disp_Inv.

Section Displayed_Equiv_Inv.

Context {C : category} {D' D : disp_cat C}
        (FF : disp_functor (functor_identity _) D' D)
        (isEquiv : is_equiv_over_id FF).

Let GG : disp_functor _ D D' := right_adjoint_of_is_equiv_over_id isEquiv.
Let η : disp_nat_trans (nat_trans_id (functor_identity C))
                       (disp_functor_identity D')
                       (disp_functor_composite FF GG)
  := unit_over_id isEquiv.

Let ε :  disp_nat_trans
           (nat_trans_id (functor_identity C))
           (disp_functor_composite GG FF)
           (disp_functor_identity D)
  := counit_over_id isEquiv.

Definition η_inv : disp_nat_trans (nat_trans_id (functor_identity C))
    (disp_functor_identity D) (disp_functor_composite GG FF).
Proof.
  apply (inv ε).
  apply (is_iso_counit_over_id isEquiv).
Defined.

Definition ε_inv :
 disp_nat_trans
    (nat_trans_id
       (functor_identity C))
    (disp_functor_composite FF GG) (disp_functor_identity D').
Proof.
  apply (inv η). cbn.
  apply (is_iso_unit_over_id isEquiv).
Defined.

Definition inv_adjunction_data : disp_adjunction_id_data D D'.
Proof.
  exists GG.
  exists FF.
  exists η_inv.
  exact ε_inv.
Defined.

Lemma form_equiv_inv_adjunction_data : form_equiv_over_id inv_adjunction_data.
Proof.
  cbn. use tpair.
    + intros. cbn.
      set (XR:= @is_iso_inv_from_is_iso_disp).
      specialize (XR _ D _  _ _ _ _ _ (  is_iso_counit_over_id (pr2 isEquiv) x xx)).
      cbn in XR.
      eapply is_iso_disp_independent_of_is_iso.
      apply XR.
    + intros. cbn.
      set (XR:= @is_iso_inv_from_is_iso_disp).
      specialize (XR _ D' _  _ _ _ _ _ (  is_iso_unit_over_id (pr2 isEquiv) x xx)).
      cbn in XR.
      eapply is_iso_disp_independent_of_is_iso.
      apply XR.
Qed.

Lemma inv_triangle_1_statement_over_id
  : triangle_1_statement_over_id inv_adjunction_data.
Proof.
  intros x xx. cbn.
        set (XR:= @iso_disp_precomp).
        set (Gepsxxx := (#GG (ε x xx))).
        set (RG := @disp_functor_on_is_iso_disp _ _ (functor_identity C)).
        specialize (RG _ _ GG).
        specialize (RG _ _ _ _ (identity_iso _ )  (ε x xx)).
        specialize (RG (is_iso_counit_over_id (pr2 isEquiv) x xx)).
        transparent assert (Ge : (iso_disp (identity_iso x)
                                  (GG _ (FF _ (GG _ xx))) (GG _ xx))).
        { apply (make_iso_disp (f:=identity_iso _ ) Gepsxxx).
          eapply is_iso_disp_independent_of_is_iso.
          apply RG.
        }

        match goal with |[|- ?EE = _ ] => set (E := EE) end. cbn in E.
        specialize (XR _ _ _ _ _ _ _ Ge).
        specialize (XR _ (identity x ;; identity x )%mor  (GG x xx)).
        apply (invmaponpathsweq (make_weq _ XR)).
        unfold E; clear E.
        cbn.
        clear RG XR Ge.
        unfold Gepsxxx.
        etrans. apply assoc_disp.
        etrans. apply maponpaths. apply maponpaths_2.
                eapply pathsinv0. apply (disp_functor_comp_var GG).
        etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
        etrans. apply transport_f_f.
        etrans. apply maponpaths. apply maponpaths_2.
                apply maponpaths.
                apply (inv_mor_after_iso_disp (is_iso_counit_over_id (pr2 isEquiv) x xx)).
        etrans. apply maponpaths. apply maponpaths_2.
                apply (disp_functor_transportf _ GG).
        etrans. apply maponpaths. apply  mor_disp_transportf_postwhisker.
        etrans. apply ( transport_f_f _ _ _ _ ).
        etrans. apply maponpaths. apply maponpaths_2.
                apply (disp_functor_id GG).
        etrans. apply maponpaths. apply  mor_disp_transportf_postwhisker.
        etrans. apply transport_f_f.
        etrans. apply maponpaths. apply id_left_disp.
        etrans. apply transport_f_f.

        match goal with |[|- transportf _ ?EE _ = _ ] => generalize EE end.
        intro EE.

        set (XR:= @iso_disp_precomp).
        set (etaGxxx := η _ (GG x xx)).
        transparent assert (Ge : (iso_disp (identity_iso x)
                                  (GG _ xx) (GG _ (FF _ (GG _ xx))) )).
        { apply (make_iso_disp (f:=identity_iso _ ) etaGxxx).
          eapply is_iso_disp_independent_of_is_iso.
          apply (is_iso_unit_over_id (pr2 isEquiv) ).
        }

        match goal with |[|- ?EE = _ ] => set (E := EE) end. cbn in E.
        specialize (XR _ _ _ _ _ _ _ Ge).
        specialize (XR _ (identity x ;; (identity x ;; identity x) )%mor  (GG x xx)).
        apply (invmaponpathsweq (make_weq _ XR)).

        cbn. unfold etaGxxx.
        unfold E.
        clear E. clear XR Ge etaGxxx.
        clear Gepsxxx.

        etrans. apply  mor_disp_transportf_prewhisker.
        etrans. apply maponpaths.
           apply (inv_mor_after_iso_disp (is_iso_unit_over_id (pr2 isEquiv) x _ )).
        etrans. apply transport_f_f.
        apply pathsinv0.
        etrans. apply maponpaths. apply  mor_disp_transportf_prewhisker.
        etrans. apply mor_disp_transportf_prewhisker.
        etrans. apply maponpaths.
                apply maponpaths. apply id_right_disp.
        etrans. apply maponpaths. apply  mor_disp_transportf_prewhisker.
        etrans. apply transport_f_f.
        set (XR := triangle_2_over_id isEquiv).
        unfold triangle_1_statement_over_id in XR.
        cbn in XR.
        etrans. apply maponpaths. apply XR.
        etrans. apply transport_f_f.
        apply maponpaths_2.
        apply homset_property.
Qed.

Lemma inv_triangle_2_statement_over_id
  : triangle_2_statement_over_id inv_adjunction_data.
Proof.
  apply triangle_2_from_1_for_equiv_over_id.
  - apply form_equiv_inv_adjunction_data.
  - apply inv_triangle_1_statement_over_id.
Qed.


Definition equiv_inv : is_equiv_over_id GG.
Proof.
  use tpair.
  - use tpair.
    + exact (FF,, (η_inv,, ε_inv)).
    + use tpair. cbn. apply inv_triangle_1_statement_over_id.
      apply inv_triangle_2_statement_over_id.
  - apply form_equiv_inv_adjunction_data.
Defined.

End Displayed_Equiv_Inv.
*)

(*
Section Displayed_Equiv_Compose.

(* TODO: give composites of displayed equivalences. *)

End Displayed_Equiv_Compose.
*)

(** ** Induced adjunctions/equivalences of fiber cats *)
Section Equiv_Fibers.

Context {C C' : category}.
(*
Definition fiber_is_left_adj
  {A : adjunction C C'}
  {D : disp_cat C} {D' : disp_cat C'}
  {FF : disp_functor (left_functor A) D D'}
  (EFF : right_adjoint_over FF)
  (c : C)
: is_left_adjoint (fiber_functor FF c).
Proof.
  destruct EFF as [[GG [η ε]] axs]; simpl in axs.
  use tpair.
  set (XR := fiber_functor GG (left_functor A c)).
  exists (fiber_functor GG _).
  exists (fiber_nat_trans η _,
          fiber_nat_trans ε _).
  use tpair; cbn.
  + unfold triangle_1_statement.
    intros d; cbn.
    set (thisax := pr1 axs c d); clearbody thisax; clear axs.
    etrans. apply maponpaths, thisax.
    etrans. apply transport_f_b.
    refine (@maponpaths_2 _ _ _ _ _ (paths_refl _) _ _).
    apply homset_property.
  + unfold triangle_2_statement.
    intros d; cbn.
    set (thisax := pr2 axs c d); clearbody thisax; clear axs.
    etrans. apply maponpaths, thisax.
    etrans. apply transport_f_b.
    refine (@maponpaths_2 _ _ _ _ _ (paths_refl _) _ _).
    apply homset_property.
Defined.
*)
(*
Definition fiber_equiv {D D' : disp_cat C}
  {FF : disp_functor (functor_identity _) D D'}
  (EFF : is_equiv_over_id FF)
  (c : C)
: adj_equivalence_of_cats (fiber_functor FF c).
Proof.
  exists (fiber_is_left_adj EFF c).
  destruct EFF as [[[GG [η ε]] tris] isos]; cbn in isos; cbn.
  use tpair.
  + intros d.
    apply is_iso_fiber_from_is_iso_disp.
    apply (is_iso_unit_over_id isos).
  + intros d.
    apply is_iso_fiber_from_is_iso_disp.
    apply (is_iso_counit_over_id isos).
Defined.
*)
End Equiv_Fibers.

(* *)
