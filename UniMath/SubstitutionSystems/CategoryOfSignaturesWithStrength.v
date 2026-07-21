Require Import UniMath.Foundations.All.

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.

Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.

Require Import UniMath.CategoryTheory.coslicecat.

Require Import UniMath.SubstitutionSystems.SigmaMonoids.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section CategoryOfSignaturesWithStrength.
  Context {V : category} (Mon_V : monoidal V).

  Local Definition PtdV : category := coslice_cat_total V I_{Mon_V}.
  Local Definition Mon_PtdV : monoidal PtdV := monoidal_pointed_objects Mon_V.
  Local Definition Act : actegory Mon_PtdV V := actegory_with_canonical_pointed_action Mon_V.

  Definition pointedtensorialstrength_disp_cat_ob_mor
    : disp_cat_ob_mor [V, V].
  Proof.
    use tpair; cbn.
    - exact (pointedtensorialstrength Mon_V).
    - intros H H' θ θ' α; exact (is_linear_nat_trans θ θ' α).
  Defined.

  Lemma pointedtensorialstrength_disp_cat_id_comp
    : disp_cat_id_comp [V,V] pointedtensorialstrength_disp_cat_ob_mor.
  Proof.
    split; cbn.
    - intros ? ?; use is_linear_nat_trans_identity.
    - intros ? ? ? ? ? ? ? ?; use is_linear_nat_trans_comp.
  Qed.

  Definition pointedtensorialstrength_disp_cat_data : disp_cat_data [V, V]
    := pointedtensorialstrength_disp_cat_ob_mor ,, 
        pointedtensorialstrength_disp_cat_id_comp.

  Lemma pointedtensorialstrength_disp_cat_axioms 
    : disp_cat_axioms [V , V] pointedtensorialstrength_disp_cat_data.
  Proof.
    repeat split; cbn.
    - intros; use proofirrelevance; use isaprop_is_linear_nat_trans.
    - intros; use proofirrelevance; use isaprop_is_linear_nat_trans.
    - intros; use proofirrelevance; use isaprop_is_linear_nat_trans.
    - intros; use isasetaprop; use isaprop_is_linear_nat_trans.
  Qed.

  Definition pointedtensorialstrength_disp_cat : disp_cat [V, V] 
    := pointedtensorialstrength_disp_cat_data ,,
        pointedtensorialstrength_disp_cat_axioms.

  Definition pointedtensorialstrength_cat : category
    := total_category pointedtensorialstrength_disp_cat.

  Let forgetful : pointedtensorialstrength_cat ⟶ [V, V]
    := pr1_category _.

  Section Limits.
    Context {g : graph}.
    Context (lims_g : Lims_of_shape g V).
    Context (F : diagram g pointedtensorialstrength_cat).
    Let F' := mapdiagram forgetful F.

    Definition limit_sig_functor_cone : LimCone F'
      := LimsFunctorCategory_of_shape g V _ lims_g _.

    Definition limit_sig_functor : V ⟶ V 
      := lim limit_sig_functor_cone.

    Lemma limit_sig_strength_forms_cone (A : PtdV) (B : V)
      : forms_cone (diagram_pointwise F' (pr1 A ⊗_{ Mon_V} B))
          (λ v, pr1 A ⊗^{ Mon_V}_{l} limOut (lims_g (diagram_pointwise F' B)) v 
                  · (pr12 (dob F v)) A B).
    Proof.
      intros u v e; etrans.
      { rewrite <- assoc; refine (maponpaths _ (pr2 (dmor F e) _ _)). }
      cbn; rewrite assoc, <- (bifunctor_leftcomp Mon_V).
      use (maponpaths (λ x, pr1 A ⊗^{Mon_V}_{l} x · _) _).
      use limOutCommutes.
    Qed.

    Definition limit_sig_strength_data
      : lineator_data Mon_PtdV Act Act limit_sig_functor.
    Proof.
      intros A B; use limArrow.
      use make_cone; [|use limit_sig_strength_forms_cone].
    Defined.

    Lemma limit_sig_strength_nat_left
      : lineator_nat_left _ _ _ _ limit_sig_strength_data.
    Proof.
      intros A B C f; use arr_to_LimCone_eq; intro u; cbn.
      etrans.
      { rewrite <- assoc; refine (maponpaths _ (limArrowCommutes (lims_g (diagram_pointwise F' _)) _ _ _)). }
      etrans; swap 1 2.
      { rewrite <- assoc; refine (!maponpaths _ _); use (limOfArrowsOut _ _ _ (lims_g (diagram_pointwise F' _))). }
      cbn; do 2 rewrite assoc.
      etrans; swap 1 2.
      { refine (!maponpaths (λ x, x · _) (limArrowCommutes (lims_g (diagram_pointwise F' _)) _ _ _)). }
      cbn; rewrite <- (bifunctor_leftcomp Mon_V); etrans.
      { refine (maponpaths (λ x, pr1 A ⊗^{Mon_V}_{l} x · _) _); use (limOfArrowsOut _ _ _ (lims_g (diagram_pointwise F' _))). }
      cbn; rewrite (bifunctor_leftcomp Mon_V), <- assoc, <- assoc.
      use maponpaths.
      use (lineator_linnatleft _ _ _ _ (pr2 (dob F u))).
    Qed.

    Lemma limit_sig_strength_nat_right
      : lineator_nat_right _ _ _ _ limit_sig_strength_data.
    Proof.
      intros A B C f; use arr_to_LimCone_eq; intro u; cbn.
      etrans.
      { rewrite <- assoc; refine (maponpaths _ (limArrowCommutes (lims_g (diagram_pointwise F' _)) _ _ _)). }
      etrans; swap 1 2.
      { rewrite <- assoc; refine (!maponpaths _ _); use (limOfArrowsOut _ _ _ (lims_g (diagram_pointwise F' _))). }
      cbn; do 2 rewrite assoc.
      etrans; swap 1 2.
      { refine (!maponpaths (λ x, x · _) (limArrowCommutes (lims_g (diagram_pointwise F' _)) _ _ _)). }
      cbn; etrans; swap 1 2.
      { rewrite <- assoc; refine (maponpaths _ _); use (lineator_linnatright _ _ _ _ (pr2 (dob F u))). }
      cbn; rewrite assoc; use (maponpaths (λ x, x · _)).
      use (bifunctor_equalwhiskers Mon_V).
    Qed.

    Lemma limit_sig_strength_preserves_actor
      : preserves_actor _ _ _ _ limit_sig_strength_data.
    Proof.
      intros A B C.
      use arr_to_LimCone_eq; intro u; cbn.
      etrans.
      { rewrite <- assoc; refine (maponpaths _ _); use (limOfArrowsOut _ _ _ (lims_g (diagram_pointwise F' _))). }
      cbn; rewrite assoc; etrans.
      { refine (maponpaths (λ x, x · _) _); use (limArrowCommutes (lims_g (diagram_pointwise F' _))). }
      symmetry; etrans.
      { rewrite <- assoc; refine (maponpaths _ _); use (limArrowCommutes (lims_g (diagram_pointwise F' _))). }
      unfold reindexed_actor_data; cbn.
      rewrite (bifunctor_rightid Mon_V), id_left, assoc, (bifunctor_rightid Mon_V), id_left.
      etrans.
      { refine (maponpaths (λ x, x · _) _); rewrite <- assoc, <- (bifunctor_leftcomp Mon_V); do 2 refine (maponpaths _ _).
        use (limArrowCommutes (lims_g (diagram_pointwise F' _))). }
      cbn.
      rewrite (bifunctor_leftcomp Mon_V), assoc, monoidal_associatornatleft.
      repeat rewrite <- assoc; use maponpaths; repeat rewrite assoc.
      symmetry.
      rewrite <- id_left, assoc, assoc, <- (bifunctor_rightid Mon_V).
      etrans; swap 1 2.
      { use (lineator_preservesactor _ _ _ _ (pr2 (dob F u))). }
      cbn; unfold reindexed_actor_data; cbn.
      do 2 use maponpaths.
      now rewrite (bifunctor_rightid Mon_V), id_left.
    Qed.

    Lemma limit_sig_strength_preserves_unitor
      : preserves_unitor _ _ _ _ limit_sig_strength_data.
    Proof.
      intro A; use arr_to_LimCone_eq; intro u; cbn.
      unfold reindexed_action_unitor_data; cbn.
      etrans.
      { rewrite <- assoc; refine (maponpaths _ _); use (limOfArrowsOut _ _ _ (lims_g (diagram_pointwise F' _))). }
      cbn; rewrite assoc; do 2 rewrite (bifunctor_rightid Mon_V), id_left.
      etrans.
      { refine (maponpaths (λ x, x · _) _); use (limArrowCommutes (lims_g (diagram_pointwise F' _))). }
      cbn; rewrite <- monoidal_leftunitornat, <- assoc; use maponpaths.
      rewrite <- id_left, <- (bifunctor_rightid Mon_V).
      etrans; swap 1 2.
      { use (lineator_preservesunitor _ _ _  _ (pr2 (dob F u))). }
      cbn; unfold reindexed_action_unitor_data; cbn.
      now rewrite (bifunctor_rightid Mon_V), id_left.
    Qed.

    Lemma limit_sig_strength_laws
      : lineator_laxlaws _ _ _ _ limit_sig_strength_data.
    Proof.
      repeat split.
      - exact limit_sig_strength_nat_left.
      - exact limit_sig_strength_nat_right.
      - exact limit_sig_strength_preserves_actor.
      - exact limit_sig_strength_preserves_unitor.
    Qed.


    Definition limit_sig_strength 
      : pointedtensorialstrength Mon_V limit_sig_functor
      := _ ,, limit_sig_strength_laws.

    Definition limit_signature_with_strength : pointedtensorialstrength_cat
      := _ ,, limit_sig_strength.

    Definition limit_signature_with_strength_out (v : vertex g)
      : pr11 limit_signature_with_strength ⟹ pr11 (dob F v)
      := limOut limit_sig_functor_cone v.

    Definition limit_signature_with_strength_cone
      : cone F limit_signature_with_strength.
    Proof.
      use make_cone.
      - intro v; use tpair; cbn. use make_nat_trans.
        + intro; use limit_signature_with_strength_out.
        + abstract (
            intros ? ? ?; use (limOfArrowsOut _ _ _ (lims_g (diagram_pointwise F' _)))
          ).
        + abstract (
            intros ? ?; use (limArrowCommutes (lims_g (diagram_pointwise F' _)))
          ).
      - abstract (
          intros ? ? ?;
          use invmap; [|use path_sigma_hprop|];
          [ use isaprop_is_linear_nat_trans
          | use invmap; [|use path_sigma_hprop|];
            [ use isaprop_is_nat_trans; use homset_property
            | use funextsec; intro; use limOutCommutes
            ]]
        ).
    Defined.

    Section FixACone.
      Context (H' : V ⟶ V) (θ' : pointedtensorialstrength Mon_V H').
      Context (cc : cone F (H' ,, θ')).
       
      Definition limit_signature_with_strength_arrow_data
        : H' ⟹ limit_sig_functor
        := limArrow _ _ (mapcone forgetful F cc).

      Lemma limit_signature_with_strength_arrow_is_mor
        : is_linear_nat_trans θ' limit_sig_strength 
          limit_signature_with_strength_arrow_data.
      Proof.
        intros A B; use arr_to_LimCone_eq; intro u; cbn.
        etrans.
        { rewrite <- assoc; refine (maponpaths _ _); use (limArrowCommutes (lims_g (diagram_pointwise F' _))). }
        cbn; symmetry; etrans.
        { rewrite <- assoc; refine (maponpaths _ _); use (limArrowCommutes (lims_g (diagram_pointwise F' _))). }
        cbn; rewrite assoc, <- (bifunctor_leftcomp Mon_V); etrans.
        { refine (maponpaths (λ x, pr1 A ⊗^{Mon_V}_{l} x · _) _); use (limArrowCommutes (lims_g (diagram_pointwise F' _))). }
        use (!pr2 (coneOut cc u) A B).
      Qed.

      Definition limit_signature_with_strength_arrow
        : pointedtensorialstrength_cat ⟦ H',, θ', limit_signature_with_strength ⟧
        := limit_signature_with_strength_arrow_data ,,
           limit_signature_with_strength_arrow_is_mor.

      Lemma limit_signature_with_strength_arrow_is_cone_mor
        : is_cone_mor cc limit_signature_with_strength_cone limit_signature_with_strength_arrow.
      Proof.
        intro u.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_linear_nat_trans.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_nat_trans; use homset_property.
        use funextsec; intro A.
        use (limArrowCommutes (lims_g (diagram_pointwise F' _))).
      Qed.
      
      Context (f_Hf : 
        ∑(f : pointedtensorialstrength_cat ⟦ H',, θ', limit_signature_with_strength ⟧),
        is_cone_mor cc limit_signature_with_strength_cone f
      ).

      Let f : pointedtensorialstrength_cat ⟦ H',, θ', limit_signature_with_strength ⟧
        := pr1 f_Hf.

      Let Hf : is_cone_mor cc limit_signature_with_strength_cone f
        := pr2 f_Hf.

      Lemma limit_signature_with_strength_arrow_unique
        : f = limit_signature_with_strength_arrow.
      Proof.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_linear_nat_trans.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_nat_trans; use homset_property.
        use funextsec; intro A; use limArrowUnique; intro u; cbn.
        exact (maponpaths (λ x, pr11 x A) (Hf u)).
      Qed.

      Lemma limit_signature_with_strength_arrow_unique_pair
        : f_Hf = (_ ,, limit_signature_with_strength_arrow_is_cone_mor).
      Proof.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_cone_mor.
        use limit_signature_with_strength_arrow_unique.
      Qed.
    End FixACone.

    Definition limit_signature_with_strength_cone_is_lim_cone
      : isLimCone F _ limit_signature_with_strength_cone
      := λ _ A, 
        (_ ,, limit_signature_with_strength_arrow_is_cone_mor _ _ A) ,,
        limit_signature_with_strength_arrow_unique_pair _ _ A.

    Definition limit_signature_with_strength_lim_cone : LimCone F.
    Proof.
      use make_LimCone.
      - exact limit_signature_with_strength.
      - exact limit_signature_with_strength_cone.
      - exact limit_signature_with_strength_cone_is_lim_cone.
    Defined.
  End Limits.


  Theorem signature_with_strength_inherits_limits 
    (g : graph) (l : Lims_of_shape g V)
    : Lims_of_shape g pointedtensorialstrength_cat.
  Proof.
    exact (limit_signature_with_strength_lim_cone l).
  Defined.

End CategoryOfSignaturesWithStrength.
