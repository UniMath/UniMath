(** * Restriction of an adjuction to an equivalence *)

(** ** Contents
  - Restriction of an adjunction to an equivalence
 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.Propositions.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

(** ** Restriction of an adjunction to an equivalence *)

(** Restriction of an adjunction to the subcategories where the unit
    and counit are isos forms an equivalence *)

(** The full subcategory of [C] for which [eta] is an isomorphism *)
Definition full_subcat_nat_trans_is_iso {C D : category}
           {F : functor C D} {G : functor C D} (eta : nat_trans F G) :
  sub_precategories C.
Proof.
  apply full_sub_precategory.
  intro c; use make_hProp.
  - exact (is_iso (eta c)).
  - apply isaprop_is_iso.
Defined.

Section Restriction.
  Context {C D : category} {F : functor C D} {G : functor D C} (are : are_adjoints F G).

  Let η := adjunit are.
  Let ε := adjcounit are.

  Definition restricted_adjunction_left_adjoint :
    functor (full_subcat_nat_trans_is_iso η) (full_subcat_nat_trans_is_iso ε).
  Proof.
    use make_functor; [use make_functor_data|split].
    - (* Left adjoint data on objects *)
      * intros c'; pose (c := precategory_object_from_sub_precategory_object _ _ c').
        use tpair.
        -- exact (F c).
        -- cbn.
           (* need: ε (F c) is an iso *)
           apply is_iso_from_is_z_iso.
           use make_is_z_isomorphism.
           ++ exact (post_whisker η F _).
           ++ assert (HH : (post_whisker η F) c · ε (F c) = identity (F c)).
             { apply (triangle_id_left_ad are). }
             (* We know [# F (η x)] is invertible because [η x] is *)
             assert (inv : ∑ h, is_inverse_in_precat ((post_whisker η F) c) h).
             {
               use tpair.
               - exact (# F (inv_from_iso (make_iso _ (pr2 c')))).
               - apply (functor_is_inverse_in_precat_inv_from_iso F (make_iso _ (pr2 c'))).
             }
             split.
             ** (* Since [# F (η x)] is invertible and [ε (F c)] is its right inverse,
                   [ε (F c)] must be its left inverse. *)
                 pose (eq := right_inverse_of_iso_is_inverse ((post_whisker η F) c) ).
                 specialize (eq (pr1 inv) (pr2 inv) (ε (F c)) HH).
                 refine (maponpaths (fun z => z · _) eq @ _).
                 apply is_inverse_in_precat1.
                 apply is_inverse_in_precat_inv.
                 exact (pr2 inv).
             ** exact HH.
    - (* Left adjoint data on morphisms *)
      intros ? ? f; cbn.
      use tpair.
      + exact (# F (precategory_morphism_from_sub_precategory_morphism _ _ _ _ f)).
      + exact tt.
    - (* Left adjoint identity axiom *)
      intro; cbn.
      apply subtypePath; [intro; apply propproperty|].
      apply functor_id.
    - (* Left adjoint composition axiom *)
      intros ? ? ? ? ?; cbn.
      apply subtypePath; [intro; apply propproperty|].
      apply functor_comp.
  Defined.

  Definition restricted_adjunction_right_adjoint :
    functor (full_subcat_nat_trans_is_iso ε) (full_subcat_nat_trans_is_iso η).
  Proof.
    use make_functor; [use make_functor_data|split].
    - (* The definition of the right adjoint just mirrors that of the left *)
      (* Right adjoint data on objects *)
      intros d'; pose (d := precategory_object_from_sub_precategory_object _ _ d').
      use tpair.
      + exact (G d).
      + cbn.
        apply is_iso_from_is_z_iso.
        use make_is_z_isomorphism.
        * exact (post_whisker ε G _).
        * assert (HH : η (G d) · (post_whisker ε G) d = identity (G d)).
          { apply (triangle_id_right_ad are). }
          assert (inv : ∑ h, is_inverse_in_precat (post_whisker ε G d) h).
          {
            use tpair.
            - exact (# G (inv_from_iso (make_iso _ (pr2 d')))).
            - apply (functor_is_inverse_in_precat_inv_from_iso G (make_iso _ (pr2 d'))).
          }
          split.
          -- exact HH.
          -- pose (eq := left_inverse_of_iso_is_inverse ((post_whisker ε G) d)).
             specialize (eq (pr1 inv) (pr2 inv) (η (G d)) HH).
             refine (maponpaths (fun z => _ · z) eq @ _).
             apply is_inverse_in_precat1.
             exact (pr2 inv).
    - (* Right adjoint data on morphisms *)
        * intros ? ? f; cbn.
          use tpair.
          -- exact (# G (precategory_morphism_from_sub_precategory_morphism _ _ _ _ f)).
          -- exact tt.
    - (* Right adjoint identity axiom *)
      intro; cbn.
      apply subtypePath; [intro; apply propproperty|].
      apply functor_id.
    - (* Right adjoint composition axiom *)
      intros ? ? ? ? ?; cbn.
      apply subtypePath; [intro; apply propproperty|].
      apply functor_comp.
  Defined.

  Definition restricted_adjunction_unit :
    nat_trans (functor_identity (full_subcat_nat_trans_is_iso η))
              (restricted_adjunction_left_adjoint ∙ restricted_adjunction_right_adjoint).
  Proof.
    use make_nat_trans.
    - intro; cbn.
      use tpair.
      + apply η.
      + exact tt.
    - (* Unit is natural *)
      intros ? ? ?.
      apply subtypePath; [intro; apply propproperty|].
      apply (pr2 η).
  Defined.

  Definition restricted_adjunction_counit :
    nat_trans (restricted_adjunction_right_adjoint ∙ restricted_adjunction_left_adjoint)
              (functor_identity (full_subcat_nat_trans_is_iso ε)).
  Proof.
    use make_nat_trans.
    - intro; cbn.
      use tpair.
      + apply ε.
      + exact tt.
    - (* Counit is natural *)
      intros ? ? ?.
      apply subtypePath; [intro; apply propproperty|].
      apply (pr2 ε).
  Defined.

  Lemma are_adjoints_restricted_adjunction :
    are_adjoints restricted_adjunction_left_adjoint
                 restricted_adjunction_right_adjoint.
  Proof.
    use make_are_adjoints.
    - exact restricted_adjunction_unit.
    - exact restricted_adjunction_counit.
    - use make_form_adjunction.
      + (* 1st triangle identity *)
        intro; apply subtypePath; [intro; apply propproperty|].
        apply triangle_id_left_ad.
      + (* 2nd triangle identity *)
        intro; apply subtypePath; [intro; apply propproperty|].
        apply triangle_id_right_ad.
  Defined.

  Lemma restricted_adjunction_equivalence :
    equivalence_of_precats (full_subcat_nat_trans_is_iso η)
                           (full_subcat_nat_trans_is_iso ε).
  Proof.
    exists (adjunction_data_from_is_left_adjoint
         are_adjoints_restricted_adjunction).
    split.
    - intro a.
      pose (isomor := make_iso _ (pr2 a) :
                        iso (pr1 a) (pr1 (right_adjoint are_adjoints_restricted_adjunction
                                           (left_adjoint are_adjoints_restricted_adjunction a)))).
      apply (iso_in_precat_is_iso_in_subcat C _ _ _ isomor).
    - intro b.
      cbn.
      pose (isomor := make_iso _ (pr2 b) :
                        iso (pr1 (left_adjoint are_adjoints_restricted_adjunction
                                   (right_adjoint are_adjoints_restricted_adjunction b))) (pr1 b)).
      apply (iso_in_precat_is_iso_in_subcat _ _ _ _ isomor).
  Defined.

End Restriction.
