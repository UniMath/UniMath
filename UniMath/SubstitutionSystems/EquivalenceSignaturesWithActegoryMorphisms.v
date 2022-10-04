(** Links signatures to lax morphisms in suitable actegories, by exploiting the already established link with action-based strength (in the non-whiskered setting)

Author: Ralph Matthes 2022

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.Bicategories.MonoidalCategories.PointedFunctorsMonoidal.
Require Import UniMath.Bicategories.MonoidalCategories.Actions.
Require Import UniMath.Bicategories.MonoidalCategories.ConstructionOfActions.
Require Import UniMath.Bicategories.MonoidalCategories.ActionOfEndomorphismsInBicat.
Require Import UniMath.Bicategories.MonoidalCategories.ActionBasedStrength.
Require Import UniMath.Bicategories.MonoidalCategories.MonoidalFromBicategory.
Require Import UniMath.Bicategories.MonoidalCategories.ActionBasedStrongFunctorCategory.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.SubstitutionSystems.Signatures.

Require Import UniMath.SubstitutionSystems.ActionBasedStrengthOnHomsInBicat.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.Bicategories.MonoidalCategories.PointedFunctorsWhiskeredMonoidal.
Require Import UniMath.Bicategories.MonoidalCategories.ActionOfEndomorphismsInBicatWhiskered.
Require Import UniMath.Bicategories.MonoidalCategories.BicatOfActegories.

Import Bicat.Notations.
Import MonoidalNotations.

Local Open Scope cat.

Section A.

  Context (C D D' : category).

  Local Definition Mon_endo' : monoidal_cat := swapping_of_monoidal_cat (monoidal_cat_of_pointedfunctors C).
  Local Definition domain_action : Actions.action Mon_endo' (hom(C:=bicat_of_cats) C D')
    := ActionBasedStrengthOnHomsInBicat.ab_strength_domain_action(C:=bicat_of_cats) C D' (ActionBasedStrengthOnHomsInBicat.forget C).
 Local Definition target_action : Actions.action Mon_endo' (hom(C:=bicat_of_cats) C D)
    := ActionBasedStrengthOnHomsInBicat.ab_strength_target_action(C:=bicat_of_cats) C D (ActionBasedStrengthOnHomsInBicat.forget C).

 Lemma weqSignatureABStrength : Signature C D D' ≃ actionbased_strong_functor Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D') (ActionBasedStrengthOnHomsInBicat.target_action C D).
 Proof.
   use weq_iso.
   - apply ab_strong_functor_from_signature.
   - apply signature_from_strong_functor.
   - apply roundtrip1_ob_as_equality.
   - apply roundtrip2_ob_as_equality.
 Defined.

 (* Local Definition endo : category := [C,C]. would not be okay for convertibility *)
 Local Definition endofrombicat : category := ActionOfEndomorphismsInBicatWhiskered.endocat(C:=bicat_of_cats) C.
 Local Definition Mon_endo : monoidal endofrombicat := ActionOfEndomorphismsInBicatWhiskered.Mon_endo(C:=bicat_of_cats) C.
 Local Definition ptdendo : category := coslice_cat_total (ActionOfEndomorphismsInBicatWhiskered.endocat(C:=bicat_of_cats) C)
                                          I_{Mon_endo}.
 Local Definition Mon_ptdendo : monoidal ptdendo
   := monoidal_pointed_objects Mon_endo.

 Local Definition actegoryPtdEndosOnFunctors (E : category) : actegory Mon_ptdendo [C,E]
   := lifted_actegory Mon_endo (actegoryfromprecomp C E) (monoidal_pointed_objects Mon_endo)
        (forget_monoidal_pointed_objects_monoidal Mon_endo).

 Section AA.

   Context (H : [C, D'] ⟶ [C, D]).

   Lemma functor_comp_id_lax_specialized (F F' : C ⟶ D') (α: F ⟹ F') (β: F' ⟹ F)
     : nat_trans_comp α β  = nat_trans_id F -> nat_trans_comp (#H α) (#H β) =  nat_trans_id (pr1 (H F)).
   Proof.
     intro e.
     intermediate_path (#H (nat_trans_id F)).
     - rewrite <- e.
       change ( (# H α) · (# H β) = # H ((α:[C,D']⟦ F, F' ⟧) · (β:[C,D']⟦ F', F ⟧)) ).
       apply (! functor_comp _ _ _).
     - apply functor_id_id.
       apply idpath.
   Qed.

 Lemma weqABStrengthLaxMorphismActegories :
   actionbased_strength Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D')
                                  (ActionBasedStrengthOnHomsInBicat.target_action C D) H
   ≃ lineator_lax Mon_ptdendo (actegoryPtdEndosOnFunctors D') (actegoryPtdEndosOnFunctors D) H.
 Proof.
   unfold actionbased_strength.
   unfold actionbased_strength_nat.
   unfold nat_trans.
   eapply weqcomp.
   apply weqtotal2asstor.
(*
   set (P := is_nat_trans (actionbased_strength_dom Mon_endo' (ActionBasedStrengthOnHomsInBicat.target_action C D) H)
               (actionbased_strength_codom Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D') H)).
   set (Q := fun (ζ: actionbased_strength_nat Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D')
         (ActionBasedStrengthOnHomsInBicat.target_action C D) H) => actionbased_strength_triangle_eq Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D')
     (ActionBasedStrengthOnHomsInBicat.target_action C D) H ζ
   × actionbased_strength_pentagon_eq Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D')
   (ActionBasedStrengthOnHomsInBicat.target_action C D) H ζ).
   (* a test for speeding up - not very successful (one would then use [Q'] in place of [Q] in the invocation of [weqtotal2asstor]):
      set (Q' := fun ζ: ∑ t: nat_trans_data (actionbased_strength_dom Mon_endo' (ActionBasedStrengthOnHomsInBicat.target_action C D) H)
                            (actionbased_strength_codom Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D') H),
                    is_nat_trans (actionbased_strength_dom Mon_endo' (ActionBasedStrengthOnHomsInBicat.target_action C D) H)
             (actionbased_strength_codom Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D') H) t  => Q ζ). *)
   exact (weqtotal2asstor P Q).
*)
   cbn.
   unfold actionbased_strength_triangle_eq, actionbased_strength_pentagon_eq.
   cbn.
   unfold lineator_lax.
   use weqbandf.
   - use weq_iso.
     + intros α v f. exact (α (f,,v)).
     + intros β fv. induction fv as [f v]. exact (β v f).
     + intro α. cbn. apply idpath.
     + intro β. cbn. apply idpath.
   - intro γ. cbn.
     use weqimplimpl.
     4: { apply isaprop_lineator_laxlaws. }
     3: { apply isapropdirprod ; [| apply isapropdirprod]; repeat (apply impred; intro); apply isaset_nat_trans; apply D. }
     + intro Hyps.
       induction Hyps as [Hypnat [Hyptriangle Hyppentagon]].
       red in Hypnat; cbn in Hypnat.
       repeat split.
       * intros v f1 f2 β.
         cbn.
         apply (nat_trans_eq D).
         intro x.
         cbn.
         assert (Hypnatinst := toforallpaths _ _ _ (maponpaths pr1 (Hypnat (f1,,v) (f2,,v)
                                                                      (β,,identity(C:=PointedFunctors.category_Ptd C) v))) x).
         cbn in Hypnatinst.
         rewrite (functor_id (H f1)) in Hypnatinst.
         rewrite post_whisker_identity in Hypnatinst.
         rewrite id_left in Hypnatinst.
         etrans.
         { exact Hypnatinst. }
         apply maponpaths.
         apply (maponpaths (fun z => pr1(# H z) x)).
         apply (@id_left [C,D'] _ _ ((pre_whisker (pr11 v)) β: functor_composite (pr1 v) f1 ⟹ functor_composite (pr1 v) f2)).
       * intros v1 v2 f α.
         cbn.
         apply (nat_trans_eq D).
         intro x.
         cbn.
         assert (Hypnatinst0 := Hypnat (f,,v1) (f,,v2)).
         transparent assert (αbetter : (PointedFunctors.category_Ptd C ⟦v1,v2⟧)).
         { use tpair.
           - exact (pr1 α).
           - intro c. unfold PointedFunctors.ptd_pt. apply (toforallpaths _ _ _ (maponpaths pr1 (pr2 α)) c).
         }
         assert (Hypnatinst := toforallpaths _ _ _ (maponpaths pr1
                             (Hypnat (f,,v1) (f,,v2) (catbinprodmor (identity(C:=functor_category C D') f) αbetter))) x).
         cbn in Hypnatinst.
         rewrite (functor_id (H)) in Hypnatinst.
         rewrite pre_whisker_identity in Hypnatinst.
         rewrite id_right in Hypnatinst.
         etrans.
         { exact Hypnatinst. }
         apply maponpaths.
         apply (maponpaths (fun z => pr1(# H z) x)).
         apply (@id_right [C,D'] _ _ ((post_whisker (pr1 α)) f: functor_composite (pr1 v1) f ⟹ functor_composite (pr1 v2) f)).
       * clear Hyptriangle.
         intros v w f.
         cbn.
         repeat rewrite post_whisker_identity.
         apply (nat_trans_eq D).
         intro x.
         cbn.
         assert (Hyppentagoninst0 := Hyppentagon f w v).
         clear Hyppentagon.
         repeat rewrite post_whisker_identity in Hyppentagoninst0.
         repeat rewrite pre_whisker_identity in Hyppentagoninst0.
         assert (Hyppentagoninst := toforallpaths _ _ _ (maponpaths pr1 Hyppentagoninst0) x).
         clear Hyppentagoninst0.
         cbn in Hyppentagoninst.
         rewrite id_right.
         rewrite id_left.
         do 4 rewrite id_left in Hyppentagoninst.
         unfold PointedFunctorsComposition.ptd_compose in Hyppentagoninst.
         cbn in Hyppentagoninst.
         unfold post_whisker_in_funcat, pre_whisker_in_funcat, PointedFunctors.ptd_pt in Hyppentagoninst.
         (* "morally", hypothesis and goal are the same. *)
         (* match goal with |[ H1 : _  = _ · ?f |- _ = _   ] => set (Hf := f) end. *)
         set (aux1 := pr1 (#H (identity(C:=[C,D']) (functor_composite (pr1 v) ((pr1 w) · f)) ·
                                 (identity _ · identity(C:=[C,D']) (functor_compose (pr1 v) (pr1 w) ∙ f)))) x).
         (* assert (auxH : Hf = aux1).
         { apply idpath. } *)
         match goal with |[ H1 : _  = _ · ?f |- _ = _   ] => change f with aux1 in H1 end.
         unfold aux1 in Hyppentagoninst.
         clear aux1.
         rewrite (functor_comp H) in Hyppentagoninst.
         rewrite id_left in Hyppentagoninst.
         rewrite (functor_id H) in Hyppentagoninst.
         rewrite id_left in Hyppentagoninst.
         (* match goal with | [ |- ?l _ · _ = _ ] => set (Hl := l) end. *)
         set (aux2 := nat_trans_data_from_nat_trans_funclass (γ (f,,functor_compose (pr1 v) (pr1 w),,
               identity(C:=[C,C]) _ · nat_trans_comp (post_whisker_in_funcat C C C (PointedFunctors.ptd_pt C v)
                        (functor_identity C)) (pre_whisker_in_funcat C C C (pr1 v) (PointedFunctors.ptd_pt C w))))).
         (* assert (auxH : Hl = aux2).
         { apply idpath. } *)
         match goal with | [ |- ?l _ · _ = _ ] => change l with aux2 end.
         unfold aux2.
         rewrite id_left.
         clear aux2.
         etrans.
         { apply cancel_postcomposition.
           exact Hyppentagoninst. }
         clear Hyppentagoninst.
         repeat rewrite assoc'.
         apply maponpaths.
         etrans.
         2: { apply id_right. }
         apply maponpaths.
         (* only # H applied to identities remains *)
         match goal with | [ |- _ ?l1 _ · _ ?l2 _ = _] => set (Hl1 := l1); set (Hl2 := l2)  end.
         assert (aux5: Hl1 · Hl2 = identity _).
         { apply functor_comp_id.
           apply (nat_trans_eq D').
           intro x'.
           cbn.
           rewrite id_left.
           apply id_left. }
         exact (toforallpaths _ _ _ (maponpaths pr1 aux5) x).
       * clear Hyppentagon.
         intro f.
         cbn.
         do 2 rewrite post_whisker_identity.
         unfold TotalDisplayedMonoidalWhiskered.total_unit.
         apply (nat_trans_eq D).
         intro x.
         cbn.
         rewrite id_left.
         assert (Hyptriangleinst0 := Hyptriangle f).
         clear Hyptriangle.
         repeat rewrite pre_whisker_identity in Hyptriangleinst0.
         assert (Hyptriangleinst := toforallpaths _ _ _ (maponpaths pr1 Hyptriangleinst0) x).
         clear Hyptriangleinst0.
         cbn in  Hyptriangleinst.
         rewrite (functor_id (H f)) in Hyptriangleinst.
         do 2 rewrite id_left in Hyptriangleinst.
         etrans.
         2: { exact Hyptriangleinst. }
         clear Hyptriangleinst.
         apply maponpaths.
         (* match goal with | [ |- ?l _ = _ ] => set (Hl := l) end. *)
         set (aux3 := nat_trans_data_from_nat_trans_funclass
                        (# H ((identity (functor_compose (functor_identity C) f)) · (identity f)))).
         (* assert (Hl = aux3).
         { apply idpath. } *)
         match goal with | [ |- ?l _ = _ ] => change l with aux3 end.
         unfold aux3; clear aux3.
         rewrite id_left. rewrite functor_id.
         (* only # H applied to identities remains *)
         (* match goal with | [ |- _ = _ ?r _ ] => set (Hr := r) end. *)
         set (argtoH := nat_trans_comp
             (nat_trans_comp
                (post_whisker
                   (nat_z_iso_to_trans_inv
                      (make_nat_z_iso (functor_identity C) (functor_identity C) (nat_trans_id (functor_identity_data C))
                         (is_nat_z_iso_nat_trans_id (functor_identity C)))) f)
                (nat_trans_id (functor_composite_data (functor_identity_data C) (pr1 f)))) (nat_trans_id (pr1 f))).
         (* assert (G1: Hr = # H argtoH).
         { apply idpath. } *)
         match goal with | [ |- _ = _ ?r _ ] => change r with (# H argtoH) end.
         assert (G2: # H argtoH = identity(C:=[C,D]) (H (functor_identity C ∙ f))).
         { apply functor_id_id.
           apply nat_trans_eq_alt; intro c.
           cbn.
           do 2 rewrite id_right.
           apply functor_id.
         }
         rewrite G2.
         apply idpath.
     + (* the other direction that is very similar in spirit (but the two naturality laws give the composite one) *)
       intro Hyps. induction Hyps as [Hypnatleft [Hypnatright [Hypactor Hypunitor]]].
       repeat split.
       * red. intros f1v1 f2v2 βα. induction f1v1 as [f1 v1]; induction f2v2 as [f2 v2]; induction βα as [β α].
         cbn.
         red in Hypnatleft.
         assert (Hypnatleftinst := Hypnatleft v2 f1 f2 β).
         clear Hypnatleft.
         cbn in Hypnatleftinst.
         transparent assert (αbetter : (ptdendo ⟦v1,v2⟧)).
         { use tpair.
           - exact (pr1 α).
           - cbn. apply (nat_trans_eq C). intro c. cbn. apply (pr2 α).
         }
         assert (Hypnatrightinst := Hypnatright v1 v2 f1 αbetter).
         clear Hypnatright.
         cbn in Hypnatrightinst.
         change (((post_whisker_in_funcat _ _ _ (pr1 α) (H f1)) · (pre_whisker_in_funcat _ _ _ (pr1 v2) (# H β))) · (γ (f2,, v2)) =
                   nat_trans_comp (γ (f1,, v1)) (# H ((post_whisker_in_funcat _ _ _ (pr1 α) f1) · (pre_whisker_in_funcat _ _ _ (pr1 v2) β)))).
         rewrite assoc'.
         rewrite functor_comp.
         etrans.
         { apply maponpaths. exact Hypnatleftinst. }
         clear Hypnatleftinst.
         apply (nat_trans_eq D); intro x.
         cbn.
         repeat rewrite assoc.
         apply cancel_postcomposition.
         exact (toforallpaths _ _ _ (maponpaths pr1 Hypnatrightinst) x).
       * clear Hypnatleft Hypnatright Hypactor.
         intro f.
         do 2 rewrite pre_whisker_identity.
         apply (nat_trans_eq D); intro x. cbn.
         rewrite (functor_id (H f)).
         do 2 rewrite id_left.
         assert (Hypunitorinst0 := Hypunitor f).
         cbn in Hypunitorinst0.
         do 2 rewrite post_whisker_identity in Hypunitorinst0.
         assert (Hypunitorinst := toforallpaths _ _ _ (maponpaths pr1 Hypunitorinst0) x).
         clear Hypunitorinst0.
         cbn in Hypunitorinst.
         rewrite id_right in Hypunitorinst.
         unfold TotalDisplayedMonoidalWhiskered.total_unit in Hypunitorinst.
         etrans.
         2: { exact Hypunitorinst. }
         clear Hypunitorinst.
         apply maponpaths.
         (* only # H applied to identities remains *)
         (* match goal with | [ |- _ = _ ?r _ ] => set (Hr := r) end. *)
         set (aux3 := # H ((identity (functor_compose (functor_identity C) f)) · (identity(C:=[C,D']) f))).
         match goal with | [ |- _ = _ ?r _ ] => change r with aux3 end.
         unfold aux3; clear aux3.
         rewrite id_left.
         rewrite functor_id.
         set (argtoH := nat_trans_comp
             (nat_trans_comp
                (post_whisker
                   (nat_z_iso_to_trans_inv
                      (make_nat_z_iso (functor_identity C) (functor_identity C) (nat_trans_id (functor_identity_data C))
                         (is_nat_z_iso_nat_trans_id (functor_identity C)))) f)
                (nat_trans_id (functor_composite_data (functor_identity_data C) (pr1 f)))) (nat_trans_id (pr1 f))).
         match goal with | [ |- _ ?l _ = _ ] => change l with (# H argtoH) end.
         assert (G2': # H argtoH = identity(C:=[C,D]) (H (functor_identity C ∙ f))).
         { apply functor_id_id.
           apply nat_trans_eq_alt; intro c.
           cbn.
           do 2 rewrite id_right.
           apply functor_id.
         }
         rewrite G2'.
         apply idpath.
       * (* the pentagon law as last remaining proof obligation *)
         clear Hypnatleft Hypnatright Hypunitor.
         intros f w v.
         assert (Hypactorinst0 := Hypactor v w f).
         cbn in Hypactorinst0.
         repeat rewrite post_whisker_identity in Hypactorinst0.
         do 3 rewrite post_whisker_identity.
         do 2 rewrite pre_whisker_identity.
         apply (nat_trans_eq D); intro x. cbn.
         repeat rewrite id_left.
         assert (Hypactorinst := toforallpaths _ _ _ (maponpaths pr1 Hypactorinst0) x).
         clear Hypactorinst0. cbn in Hypactorinst.
         do 2 rewrite id_left in Hypactorinst.
         etrans.
         2: { apply cancel_postcomposition.
              exact Hypactorinst. }
         clear Hypactorinst.
         rewrite assoc'.
         etrans.
         { apply pathsinv0, id_right. }
         (* match goal with | [ |- _ = ?r _ · _ ] => set (Hr := r) end. *)
         set (aux6 := nat_trans_data_from_nat_trans_funclass (γ (f,,functor_compose (pr1 v) (pr1 w),,
               identity(C:=[C,C]) _ · nat_trans_comp (post_whisker_in_funcat C C C (PointedFunctors.ptd_pt C v)
                        (functor_identity C)) (pre_whisker_in_funcat C C C (pr1 v) (PointedFunctors.ptd_pt C w))))).
         (* assert (auxH : Hr = aux6).
         { apply idpath. } *)
         match goal with | [ |- _ = ?r _ · _ ] => change r with aux6 end.
         unfold aux6. clear aux6.
         rewrite id_left.
         apply maponpaths.
         (* only # H applied to identities remains *)
         (* match goal with |[ |- _  = _ · ?f ] => set (Hf := f) end. *)
         set (aux5' := pr1 (#H (identity(C:=[C,D']) (functor_composite (pr1 v) (functor_composite (pr1 w) f)) ·
                                  (identity (C:=[C,D'])(functor_composite (functor_composite (pr1 v) (pr1 w)) f) ·
                                     identity(C:=[C,D']) (functor_compose (pr1 v) (pr1 w) ∙ f)))) x).
         (* assert (auxH : Hf = aux5').
         { apply idpath. } *)
         match goal with |[ |- _  = _ · ?f ] => change f with aux5' end.
         unfold aux5'. clear aux5'.
         rewrite (functor_comp H).
         rewrite id_left.
         rewrite (functor_id H).
         rewrite id_left.
         apply pathsinv0.
         match goal with | [ |- _ ?l1 _ · _ ?l2 _ = _] => set (Hl1 := l1); set (Hl2 := l2) end.
         (* It looked like being stuck. One cannot proceed as in the opposite direction stating aux7: Hl1 · Hl2 = identity _ because this does not type-check.
            But one can state: *)
         assert (aux7: nat_trans_comp Hl1 Hl2 = nat_trans_id _).
         2: { exact (toforallpaths _ _ _ (maponpaths pr1 aux7) x). }
         (* but how can we prove it? Is there something like functor_comp_id available?
            Yes, specialized for the situation with endofunctor categories as domain a codomain *)
         apply functor_comp_id_lax_specialized.
         apply nat_trans_eq_alt.
         intro x'.
         cbn.
         rewrite id_left.
         apply id_left.
 Defined.

End AA.

 Lemma weqSignatureLaxMorphismActegories :
   Signature C D D' ≃ hom(C:=actbicat Mon_ptdendo) ([C, D'],,actegoryPtdEndosOnFunctors D') ([C, D],,actegoryPtdEndosOnFunctors D).
 Proof.
   apply (weqcomp weqSignatureABStrength).
   apply weqfibtototal.
   intro H.
   apply weqABStrengthLaxMorphismActegories.
 Defined.

End A.
