(***************************************************************************

 Category of signatures with (pointed tensorial) strength

 In this file, we define the category of signatures with a pointed tensorial
 strength, and prove their closure under colimits and limits.

 Contents
 1. Definitions
 2. Two examples of signatures with strength
 3. Limits are inherited from limits in V
 4. Colimits are inherited from colimits in V

 ***************************************************************************)


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

  (** 1. Definitions *)

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

  Definition pointedtensorialstrength_disp_cat : disp_cat [V, V].
  Proof.
    use (make_disp_cat_locally_prop (D:=pointedtensorialstrength_disp_cat_data)).
    red; intros; use isaprop_is_linear_nat_trans.
  Defined.

  Definition pointedtensorialstrength_cat : category
    := total_category pointedtensorialstrength_disp_cat.


  (** comments by Ralph Matthes *)
(*
  Require Import UniMath.Bicategories.Core.Bicat.

  Require Import UniMath.Bicategories.MonoidalCategories.BicatOfActegories.
  Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

  Local Definition mybicat : bicat := actbicat (monoidal_pointed_objects Mon_V).
  Local Definition myhomcat : category
    := hom(C:=mybicat) (V,,actegory_with_canonical_pointed_action Mon_V) (V,,actegory_with_canonical_pointed_action Mon_V).

  (** question: what is the relation between [pointedtensorialstrength_cat] and [myhomcat]?
      They should be isomorphic. And this for generic reasons since the ingredients are the same for the category and the bicategory construction. Here, we show equality of these categories in this specific instance.
   *)

  Local Definition myembedding : functor pointedtensorialstrength_cat myhomcat.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro ptdstr.
        exact ptdstr.
      + intros ptdst ptdstr' mor.
        exact mor.
    - split; red; intros.
      (* show_id_type.
         red in TYPE. *)
      + use total2_paths_f.
        * apply idpath.
        * cbn.
          (* show_id_type.
          red in TYPE. *)
          apply isaprop_bidisp_actbicat_disp_2cell_struct.
      + use total2_paths_f.
        * apply idpath.
        * cbn.
          apply isaprop_bidisp_actbicat_disp_2cell_struct.
  Defined.

  Local Lemma myisweq : isweq (functor_on_objects myembedding).
  Proof.
    apply idisweq.
  Defined.

  Local Lemma myfullyfaithful : fully_faithful myembedding.
  Proof.
    intros ptdst ptdstr'.
    apply idisweq.
  Defined.

  Require Import UniMath.CategoryTheory.catiso.

  Local Definition catiso_pointedtensorialstrength_cat_myhomcat : catiso pointedtensorialstrength_cat myhomcat.
  Proof.
    exists myembedding.
    split.
    - apply myfullyfaithful.
    - apply myisweq.
  Defined.

  Local Lemma pointedtensorialstrength_cat_equals_myhomcat : pointedtensorialstrength_cat = myhomcat.
  Proof.
    apply catiso_to_category_path.
    exact catiso_pointedtensorialstrength_cat_myhomcat.
  Qed.
*)
  (** end of comments by Ralph Matthes *)


  Let forgetful : pointedtensorialstrength_cat ⟶ [V, V]
    := pr1_category _.

  (** 2. Two examples of signatures with strength *)

  (* Id : V ⟶ V is a signature with strength whose strength  *)
  (* is trivial :  (Id A) ⊗ B = A ⊗ B = Id (A ⊗ B)           *)

  Lemma trivial_signature_with_strength_laws
    : lineator_laxlaws Mon_PtdV Act Act (functor_identity V) (λ _ _, identity _).
  Proof.
    repeat split.
    - intros ? ? ? ?; cbn; now rewrite id_right, id_left.
    - intros ? ? ? ?; cbn; now rewrite id_right, id_left.
    - intros A B C; cbn; unfold reindexed_actor_data; cbn.
      rewrite (bifunctor_rightid Mon_V), (bifunctor_leftid Mon_V).
      now repeat rewrite id_left, id_right.
    - intro A; cbn; unfold reindexed_action_unitor_data; cbn.
      now rewrite (bifunctor_rightid Mon_V), id_left.
  Qed.

  Definition trivial_signature_with_strength
    : pointedtensorialstrength Mon_V (functor_identity V)
    := _ ,, trivial_signature_with_strength_laws.

  Section ProductSignatureWithStrength.
    Context (H : V ⟶ V) (θ : pointedtensorialstrength Mon_V H) (D : V).

    (* Given a signature with strength (H,θ), then H(-) ⊗ D *)
    (* is also a signature with strength whose strength is  *)
    (* given by                                             *)
    (*                α⁻¹                θ                  *)
    (* A ⊗ (H B ⊗ D) ---> (A ⊗ H B) ⊗ D ---> H (A ⊗ B) ⊗ D  *)

    Definition product_signature_functor : V ⟶ V
      := H ∙ rightwhiskering_functor Mon_V D.

    Goal ∏ (A : V), product_signature_functor A = H A ⊗_{Mon_V} D.
    Proof.
      exact (λ _, idpath _).
    Qed.

    Definition product_signature_strength_mor (A : PtdV) (B : V)
      : pr1 A ⊗_{Mon_V} (H B ⊗_{Mon_V} D) --> H (pr1 A ⊗_{Mon_V} B) ⊗_{Mon_V} D
      := αinv^{_}_{_,_,_} · θ A B ⊗^{Mon_V}_{r} D.

    Lemma product_signature_strength_nat_left
      : lineator_nat_left _ Act Act product_signature_functor product_signature_strength_mor.
    Proof.
      intros A B C f; unfold product_signature_strength_mor; cbn.
      repeat rewrite assoc.
      rewrite (monoidal_associatorinvnatleftright Mon_V).
      repeat rewrite <- assoc; use maponpaths.
      do 2 rewrite <- (bifunctor_rightcomp Mon_V).
      use maponpaths.
      use (lineator_linnatleft _ _ _ _ θ).
    Qed.

    Lemma product_signature_strength_nat_right
      : lineator_nat_right _ Act Act product_signature_functor product_signature_strength_mor.
    Proof.
      intros A B C f; unfold product_signature_strength_mor; cbn.
      repeat rewrite assoc.
      rewrite (monoidal_associatorinvnatright Mon_V).
      repeat rewrite <- assoc; use maponpaths.
      do 2 rewrite <- (bifunctor_rightcomp Mon_V).
      use maponpaths.
      use (lineator_linnatright _ _ _ _ θ).
    Qed.

    Lemma product_signature_strength_preserves_actor
      : preserves_actor _ Act Act product_signature_functor product_signature_strength_mor.
    Proof.
      intros A B C.
      cbn; unfold product_signature_strength_mor, reindexed_actor_data; cbn.
      do 2 rewrite (bifunctor_rightid Mon_V), id_left.
      rewrite assoc.
      etrans.
      { rewrite <- assoc, <- (bifunctor_rightcomp Mon_V); do 2 refine (maponpaths _ _).
        etrans.
        { refine (!maponpaths (λ x, _ · #H x) _); now rewrite <- id_left, <- (bifunctor_rightid Mon_V). }
        use (lineator_preservesactor _ _ _ _ θ).
      }
      cbn; unfold reindexed_actor_data; cbn.
      do 3 rewrite (bifunctor_rightcomp Mon_V), assoc.
      do 2 rewrite (bifunctor_rightid Mon_V).
      rewrite id_right.
      use (maponpaths (λ x, x · _)).
      rewrite (bifunctor_leftcomp Mon_V), assoc; repeat rewrite <- assoc.
      rewrite (monoidal_associatorinvnatleftright Mon_V); repeat rewrite assoc.
      use (!maponpaths (λ x, x · _) _).
      (* Pentagon axiom *)
      etrans.
      { rewrite <- assoc; refine (!maponpaths _ _).
        rewrite <- id_right, <- (bifunctor_rightid Mon_V).
        rewrite <- (pr2 (monoidal_associatorisolaw _ _ _ _)).
        rewrite bifunctor_rightcomp, assoc.
        now rewrite (monoidal_pentagon_identity_inv Mon_V).
      }
      do 2 rewrite assoc; rewrite <- id_left, assoc.
      refine (maponpaths (λ x, x · _ · _) _).
      use (pr1 (monoidal_associatorisolaw _ _ _ _)).
    Qed.

    Lemma product_signature_strength_preserves_unitor
      : preserves_unitor _ Act Act product_signature_functor product_signature_strength_mor.
    Proof.
      intro A.
      cbn; unfold product_signature_strength_mor, reindexed_action_unitor_data; cbn.
      do 2 rewrite (bifunctor_rightid Mon_V), id_left; rewrite <- assoc, <- (bifunctor_rightcomp Mon_V).
      etrans.
      { do 2 refine (maponpaths _ _).
        etrans.
        { do 2 refine (maponpaths _ _); symmetry; now rewrite <- id_left, <- (bifunctor_rightid Mon_V). }
        use (lineator_preservesunitor _ _ _ _ θ A).
      }
      cbn; unfold reindexed_action_unitor_data; cbn.
      (* Triangle axiom *)
      rewrite (bifunctor_rightid Mon_V), id_left.
      rewrite <- id_left, <- (pr2 (monoidal_associatorisolaw _ _ _ _)), <- assoc.
      use (!maponpaths _ _); use right_whisker_with_lunitor.
    Qed.

    Lemma product_signature_strength_laws
      : lineator_laxlaws _ Act Act product_signature_functor product_signature_strength_mor.
    Proof.
      repeat split.
      - exact product_signature_strength_nat_left.
      - exact product_signature_strength_nat_right.
      - exact product_signature_strength_preserves_actor.
      - exact product_signature_strength_preserves_unitor.
    Qed.

    Definition product_signature_strength
      : pointedtensorialstrength Mon_V product_signature_functor
      := product_signature_strength_mor ,, product_signature_strength_laws.

  End ProductSignatureWithStrength.

  (** 3. Limits are inherited from limits in V *)
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
      etrans.
      2: { rewrite <- assoc; refine (!maponpaths _ _); use (limOfArrowsOut _ _ _ (lims_g (diagram_pointwise F' _))). }
      cbn; do 2 rewrite assoc.
      etrans.
      2: { refine (!maponpaths (λ x, x · _) (limArrowCommutes (lims_g (diagram_pointwise F' _)) _ _ _)). }
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
      etrans.
      2: { rewrite <- assoc; refine (!maponpaths _ _); use (limOfArrowsOut _ _ _ (lims_g (diagram_pointwise F' _))). }
      cbn; do 2 rewrite assoc.
      etrans.
      2: { refine (!maponpaths (λ x, x · _) (limArrowCommutes (lims_g (diagram_pointwise F' _)) _ _ _)). }
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
      etrans.
      2: { use (lineator_preservesactor _ _ _ _ (pr2 (dob F u))). }
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
      etrans.
      2: { use (lineator_preservesunitor _ _ _  _ (pr2 (dob F u))). }
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
      - intro v; use tpair; cbn.
        + use make_nat_trans.
          * intro; use limit_signature_with_strength_out.
          * abstract (
                intros ? ? ?; use (limOfArrowsOut _ _ _ (lims_g (diagram_pointwise F' _)))
              ).
        + abstract (
              intros ? ?; use (limArrowCommutes (lims_g (diagram_pointwise F' _)))
            ).
      - abstract (
            intros ? ? ?;
            use subtypePath;
            [ use isaprop_is_linear_nat_trans
            | apply nat_trans_eq; [use homset_property|]; intro; use limOutCommutes ]
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
        use subtypePath.
        { intro; use isaprop_is_linear_nat_trans. }
        apply nat_trans_eq; [use homset_property|]; intro A.
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
        use subtypePath.
        { use isaprop_is_linear_nat_trans. }
        apply nat_trans_eq; [use homset_property|]; intro A; use limArrowUnique; intro u; cbn.
        exact (maponpaths (λ x, pr11 x A) (Hf u)).
      Qed.

      Lemma limit_signature_with_strength_arrow_unique_pair
        : f_Hf = (_ ,, limit_signature_with_strength_arrow_is_cone_mor).
      Proof.
        use subtypePath.
        { use isaprop_is_cone_mor. }
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

  (** 4. Colimits are inherited from colimits in V *)

  (* assuming A ⊗ - preserves those colimits for A ∈ PtdV *)

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
      etrans.
      2: { use (lineator_preservesactor _ _ _ _ (pr2 (dob F u))). }
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
      etrans.
      2: { use (lineator_preservesunitor _ _ _ _ (pr2 (dob F u))). }
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
      use subtypePath.
      { use isaprop_is_linear_nat_trans. }
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
        use subtypePath.
        { use isaprop_is_linear_nat_trans. }
        apply nat_trans_eq; [use homset_property|]; intro A.
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
        use subtypePath.
        { use isaprop_is_linear_nat_trans. }
        apply nat_trans_eq; [use homset_property|]; intro A; use colimArrowUnique; intro u; cbn.
        exact (maponpaths (λ x, pr11 x A) (Hf u)).
      Qed.

      Lemma colimit_signature_with_strength_arrow_unique_pair
        : f_Hf = (_ ,, colimit_signature_with_strength_arrow_is_cocone_mor).
      Proof.
        use subtypePath.
        { use isaprop_is_cocone_mor. }
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
