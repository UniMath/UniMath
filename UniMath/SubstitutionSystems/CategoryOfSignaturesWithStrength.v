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

  (* Signatures with strength inherits their limits from the base category *)

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

  (* Signatures with strength inherits their colimits from the base category *)
  (* assuming A ⊗ - preserves those colimits (for A pointed)                 *)

  Section Colimits.
    Context {g : graph}.
    Context (colims_g : Colims_of_shape g V).
    Context (H_prod : ∏ A : PtdV, 
      preserves_colimits_of_shape (leftwhiskering_functor Mon_V (pr1 A)) g).
    Context (F : diagram g pointedtensorialstrength_cat).
    Let F' := mapdiagram forgetful F.

    Definition colimit_sig_functor_cocone : ColimCocone F'
      := ColimsFunctorCategory_of_shape g V _ colims_g _.

    Definition colimit_sig_functor : V ⟶ V 
      := colim colimit_sig_functor_cocone.

    Let H (A : V) : V := colimit_sig_functor A.

    (* Colim Cocone for H(A) *)
    Local Definition H_Cocone {A : V}
      : ColimCocone (diagram_pointwise F' A)
      := (colims_g (diagram_pointwise F' A)).

    (* Colim Cocone for A ⊗ H(B) *)
    Local Definition H_Cocone_Prod {A : PtdV} {B : V}
      : ColimCocone (mapdiagram (leftwhiskering_functor Mon_V (pr1 A)) (diagram_pointwise F' B))
      := make_ColimCocone _ _ _ (H_prod A _ _ _ (pr2 (colims_g (diagram_pointwise F' B)))).

    Goal ∏ A B, colim (@H_Cocone_Prod A B) = pr1 A ⊗_{Mon_V} H B. 
    Proof.
      intros; use idpath.
    Qed.

    Definition colimit_sig_strength_data 
      : lineator_data Mon_PtdV Act Act colimit_sig_functor.
    Proof.
      intros A B.
      use (colimOfArrows H_Cocone_Prod H_Cocone).
      - intro u; use (pr12 (dob F u)).
      - intros u v e; use (!pr2 (dmor F e) _ _).
    Defined.

    Lemma colimit_sig_strength_nat_left
      : lineator_nat_left _ Act Act _ colimit_sig_strength_data.
    Proof.
      intros A B C f; use (colimArrowUnique' H_Cocone_Prod).
      intro u; cbn; do 2 rewrite assoc.
      symmetry; etrans.
      { refine (maponpaths (λ x, x · _) _); use (colimOfArrowsIn _ _ H_Cocone_Prod). }
      cbn; rewrite <- assoc; etrans.
      { refine (maponpaths _ _); use (colimOfArrowsIn _ _ (colims_g (diagram_pointwise F' _))). }
      cbn; rewrite assoc, <- (bifunctor_leftcomp Mon_V).
      symmetry; etrans.
      { refine (maponpaths (λ x, pr1 A ⊗^{Mon_V}_{l} x · _) _); use (colimOfArrowsIn _ _ (colims_g (diagram_pointwise F' _))). }
      cbn; rewrite (bifunctor_leftcomp Mon_V), <- assoc.
      etrans.
      { refine (maponpaths _ _); use (colimOfArrowsIn _ _ H_Cocone_Prod). }
      cbn; rewrite assoc; use (maponpaths (λ x, x · _)).
      use (lineator_linnatleft _ _ _ _ (pr2 (dob F u))).
    Qed.

    Lemma colimit_sig_strength_nat_right
      : lineator_nat_right _ Act Act _ colimit_sig_strength_data.
    Proof.
      intros A B C f; use (colimArrowUnique' H_Cocone_Prod).
      intro u; cbn; do 2 rewrite assoc.
      symmetry; etrans.
      { refine (maponpaths (λ x, x · _) _); use (colimOfArrowsIn _ _ H_Cocone_Prod). }
      cbn; rewrite <- assoc; etrans.
      { refine (maponpaths _ _); use (colimOfArrowsIn _ _ (colims_g (diagram_pointwise F' _))). }
      cbn; rewrite assoc.
      symmetry; etrans.
      { refine (!maponpaths (λ x, x · _) _); use (bifunctor_equalwhiskers Mon_V). }
      cbn; unfold functoronmorphisms1; rewrite <- assoc.
      etrans.
      { refine (maponpaths _ _); use (colimOfArrowsIn _ _ H_Cocone_Prod). }
      cbn; rewrite assoc; use (maponpaths (λ x, x · _)).
      use (lineator_linnatright _ _ _ _ (pr2 (dob F u))).
    Qed.

    Lemma colimit_sig_strength_preserves_actor
      : preserves_actor _ Act Act _ colimit_sig_strength_data.
    Proof.
      intros A B C; set (AB := A ⊗_{Mon_PtdV} B).
      use (colimArrowUnique' (H_Cocone_Prod (A := AB))).
      intro u; cbn; unfold reindexed_actor_data; cbn.
      do 3 rewrite assoc; do 2 rewrite (bifunctor_rightid Mon_V), id_left.
      etrans.
      { refine (maponpaths (λ x, x · _) _); use (colimArrowCommutes (H_Cocone_Prod (A := AB))). }
      cbn; etrans.
      { rewrite <- assoc; refine (maponpaths _ _); use (colimOfArrowsIn _ _ H_Cocone). }
      cbn; rewrite assoc, <- monoidal_associatornatleft.
      symmetry; etrans.
      { rewrite <- assoc, <- assoc; refine (maponpaths _ _); rewrite assoc, <- (bifunctor_leftcomp Mon_V).
        refine (maponpaths (λ x, pr1 A ⊗^{Mon_V}_{l} x · _) _); use (colimOfArrowsIn _ _ H_Cocone_Prod). }
      rewrite (bifunctor_leftcomp Mon_V), assoc, assoc; etrans.
      { rewrite <- assoc; refine (maponpaths _ _); use (colimOfArrowsIn _ _ H_Cocone_Prod). }
      rewrite assoc; use (maponpaths (λ x, x · _)).
      symmetry; rewrite <- id_left, <- (bifunctor_rightid Mon_V), assoc, assoc.
      etrans; swap 1 2.
      { use (lineator_preservesactor _ _ _ _ (pr2 (dob F u))). }
      cbn; unfold reindexed_actor_data; cbn.
      do 2 use maponpaths.
      now rewrite (bifunctor_rightid Mon_V), id_left.
    Qed.

    Lemma colimit_sig_strength_preserves_unitor
      : preserves_unitor _ Act Act _ colimit_sig_strength_data.
    Proof.
      intro A; use (colimArrowUnique' (H_Cocone_Prod (A := I_{Mon_PtdV}))); intro u.
      rewrite assoc; etrans.
      { refine (maponpaths (λ x, x · _) _); use (colimOfArrowsIn _ _ H_Cocone_Prod). }
      cbn; unfold reindexed_action_unitor_data; cbn.
      do 2 rewrite (bifunctor_rightid Mon_V), id_left.
      rewrite monoidal_leftunitornat, <- assoc.
      etrans.
      { refine (maponpaths _ _); use (colimOfArrowsIn _ _ H_Cocone). }
      cbn; rewrite assoc; use (maponpaths (λ x, x · _)).
      rewrite <- id_left, <- (bifunctor_rightid Mon_V).
      etrans; swap 1 2.
      { use (lineator_preservesunitor _ _ _ _ (pr2 (dob F u))). }
      cbn; unfold reindexed_action_unitor_data; cbn.
      do 2 use maponpaths.
      now rewrite (bifunctor_rightid Mon_V), id_left.
    Qed.

    Lemma colimit_sig_strength_laws
      : lineator_laxlaws Mon_PtdV Act Act colimit_sig_functor colimit_sig_strength_data.
    Proof.
      repeat split.
      - exact colimit_sig_strength_nat_left.
      - exact colimit_sig_strength_nat_right.
      - exact colimit_sig_strength_preserves_actor.
      - exact colimit_sig_strength_preserves_unitor.
    Qed.

    Definition colimit_sig_strength 
      : pointedtensorialstrength Mon_V colimit_sig_functor
      := _ ,, colimit_sig_strength_laws.

    Definition colimit_signature_with_strength
      : pointedtensorialstrength_cat
      := _ ,, colimit_sig_strength.

    Definition colimit_signature_with_strength_in_data (v : vertex g)
      : pr1 (dob F' v) ⟹ colimit_sig_functor
      := colimIn colimit_sig_functor_cocone v.

    Lemma colimit_signature_with_strength_in_is_mor (v : vertex g)
      : is_linear_nat_trans (pr2 (dob F v)) colimit_sig_strength (colimit_signature_with_strength_in_data v).
    Proof.
      intros A bB. symmetry. use (colimOfArrowsIn _ _ H_Cocone_Prod).
    Qed.

    Definition colimit_signature_with_strength_in (v : vertex g)
      : dob F v --> colimit_signature_with_strength
      := colimit_signature_with_strength_in_data v ,,
         colimit_signature_with_strength_in_is_mor v.

    Lemma colimit_signature_with_strength_cocone_is_cocone
      : forms_cocone F colimit_signature_with_strength_in.
    Proof.
      intros u v e.
      use invmap; [|use path_sigma_hprop|].
      use isaprop_is_linear_nat_trans.
      use (colimInCommutes colimit_sig_functor_cocone).
    Qed.

    Definition colimit_signature_with_strength_cocone
      : cocone F colimit_signature_with_strength
      := make_cocone _ colimit_signature_with_strength_cocone_is_cocone.

    Section FixACocone.
      Context (H' : V ⟶ V) (θ' : pointedtensorialstrength Mon_V H').
      Context (cc : cocone F (H' ,, θ')).

      Definition colimit_signature_with_strength_arrow_data
        : colimit_sig_functor ⟹ H'
        := colimArrow _ _ (mapcocone forgetful F cc).

      Lemma colimit_signature_with_strength_arrow_is_mor
        : is_linear_nat_trans colimit_sig_strength θ' colimit_signature_with_strength_arrow_data.
      Proof.
        intros A bB. use (colimArrowUnique' H_Cocone_Prod).
        intro u; etrans.
        { rewrite assoc; refine (maponpaths (λ x, x ·_) _). use (colimOfArrowsIn _ _ H_Cocone_Prod). }
        simpl; etrans.
        { rewrite <- assoc; refine (maponpaths _ _). use (colimArrowCommutes H_Cocone). }
        cbn; rewrite assoc, <- (bifunctor_leftcomp Mon_V); symmetry; etrans.
        { refine (maponpaths (λ x, pr1 A ⊗^{Mon_V}_{l} x · _) _); use (colimArrowCommutes H_Cocone). }
        use (!pr2 (coconeIn cc u) _ _).
      Qed.

      Definition colimit_signature_with_strength_arrow
        : pointedtensorialstrength_cat⟦colimit_signature_with_strength, (H',,θ')⟧ 
        := colimit_signature_with_strength_arrow_data ,,
           colimit_signature_with_strength_arrow_is_mor.

      Lemma  colimit_signature_with_strength_arrow_is_cocone_mor
        : is_cocone_mor colimit_signature_with_strength_cocone cc
            colimit_signature_with_strength_arrow.
      Proof.
        intro u.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_linear_nat_trans.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_nat_trans; use homset_property.
        use funextsec; intro A.
        use (colimArrowCommutes (colims_g (diagram_pointwise F' _))).
      Qed.
      
      Context (f_Hf : 
        ∑(f : pointedtensorialstrength_cat ⟦colimit_signature_with_strength, H',, θ' ⟧),
        is_cocone_mor colimit_signature_with_strength_cocone cc f
      ).

      Let f : pointedtensorialstrength_cat ⟦colimit_signature_with_strength, H',, θ' ⟧
        := pr1 f_Hf.

      Let Hf : is_cocone_mor colimit_signature_with_strength_cocone  cc f
        := pr2 f_Hf.

      Lemma colimit_signature_with_strength_arrow_unique
        : f = colimit_signature_with_strength_arrow.
      Proof.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_linear_nat_trans.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_nat_trans; use homset_property.
        use funextsec; intro A; use colimArrowUnique; intro u; cbn.
        exact (maponpaths (λ x, pr11 x A) (Hf u)).
      Qed.

      Lemma colimit_signature_with_strength_arrow_unique_pair
        : f_Hf = (_ ,, colimit_signature_with_strength_arrow_is_cocone_mor).
      Proof.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_cocone_mor.
        use colimit_signature_with_strength_arrow_unique.
      Qed.
    End FixACocone.

    Definition colimit_signature_with_strength_cocone_is_colim_cocone
      : isColimCocone F _ colimit_signature_with_strength_cocone
      := λ _ A, 
        (_ ,, colimit_signature_with_strength_arrow_is_cocone_mor _ _ A) ,,
        colimit_signature_with_strength_arrow_unique_pair _ _ A.


    Definition colimit_signature_with_strength_colim_cocone : ColimCocone F.
    Proof.
      use make_ColimCocone.
      - exact colimit_signature_with_strength.
      - exact colimit_signature_with_strength_cocone.
      - exact colimit_signature_with_strength_cocone_is_colim_cocone.
    Defined.
  End Colimits.

  Theorem signature_with_strength_inherits_colimits 
    (g : graph) (cl : Colims_of_shape g V)
    (H_prod : ∏ A : PtdV, preserves_colimits_of_shape (leftwhiskering_functor Mon_V (pr1 A)) g)
    : Colims_of_shape g pointedtensorialstrength_cat.
  Proof.
    use (colimit_signature_with_strength_colim_cocone cl H_prod).
  Defined.
End CategoryOfSignaturesWithStrength.
