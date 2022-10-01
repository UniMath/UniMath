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

 Lemma weqABStrengthLaxMorphismActegories :
   actionbased_strength Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D')
                                  (ActionBasedStrengthOnHomsInBicat.target_action C D) H
   ≃ lineator_lax Mon_ptdendo (actegoryPtdEndosOnFunctors D') (actegoryPtdEndosOnFunctors D) H.
 Proof.
   unfold actionbased_strength.
   unfold actionbased_strength_nat.
   unfold nat_trans.
   eapply weqcomp.
   set (P := is_nat_trans (actionbased_strength_dom Mon_endo' (ActionBasedStrengthOnHomsInBicat.target_action C D) H)
               (actionbased_strength_codom Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D') H)).
   set (Q := fun (ζ: actionbased_strength_nat Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D')
         (ActionBasedStrengthOnHomsInBicat.target_action C D) H) => actionbased_strength_triangle_eq Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D')
     (ActionBasedStrengthOnHomsInBicat.target_action C D) H ζ
   × actionbased_strength_pentagon_eq Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D')
   (ActionBasedStrengthOnHomsInBicat.target_action C D) H ζ).
   set (Q' := fun ζ: ∑ t: nat_trans_data (actionbased_strength_dom Mon_endo' (ActionBasedStrengthOnHomsInBicat.target_action C D) H)
                            (actionbased_strength_codom Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D') H),
                    is_nat_trans (actionbased_strength_dom Mon_endo' (ActionBasedStrengthOnHomsInBicat.target_action C D) H)
             (actionbased_strength_codom Mon_endo' (ActionBasedStrengthOnHomsInBicat.domain_action C D') H) t  => Q ζ).
   exact (weqtotal2asstor P Q').
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
         assert (Hypnatinst := toforallpaths _ _ _ (maponpaths pr1 (Hypnat (f1,,v) (f2,,v) (β,,identity(C:=PointedFunctors.category_Ptd C) v))) x).
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
       * intros v w f.
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
         cbn in Hyppentagoninst.
         rewrite id_right.
         rewrite id_left.
         do 4 rewrite id_left in Hyppentagoninst.
         unfold PointedFunctorsComposition.ptd_compose in Hyppentagoninst.
         cbn in Hyppentagoninst.
         unfold post_whisker_in_funcat, pre_whisker_in_funcat, PointedFunctors.ptd_pt in Hyppentagoninst.
         (* "morally", hypothesis and goal are the same *)

 Admitted.

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
