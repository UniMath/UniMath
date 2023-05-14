(** a generalization of heterogeneous substitution systems to monoidal categories in place of endofunctor categories

author: Ralph Matthes 2022
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Actegories.CoproductsInActegories.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.


Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.
(* Import ActegoryNotations. *)

Section hss.

  Context {V : category} (Mon_V : monoidal V).

  Local Definition PtdV : category := coslice_cat_total V I_{Mon_V}.
  Local Definition Mon_PtdV : monoidal PtdV := monoidal_pointed_objects Mon_V.
  Local Definition Act : actegory Mon_PtdV V := actegory_with_canonical_pointed_action Mon_V.

  Context (H : V ⟶ V).
  Context (θ : pointedtensorialstrength Mon_V H).

  Section TheProperty.

    Context (t : V) (η : I_{Mon_V} --> t) (τ : H t --> t).

  Definition gbracket_property_parts {z : V} (e : I_{Mon_V} --> z) (f : z --> t) (h : z ⊗_{Mon_V} t --> t) : UU :=
    (ru^{Mon_V}_{z} · f = z ⊗^{Mon_V}_{l} η · h) ×
      (θ (z,,e) t · #H h · τ =  z ⊗^{Mon_V}_{l} τ · h).

  Definition gbracket_parts_at {z : V} (e : I_{Mon_V} --> z) (f : z --> t) : UU :=
    ∃! h : z ⊗_{Mon_V} t --> t, gbracket_property_parts e f h.

  Definition gbracket : UU :=
    ∏ (Z : PtdV) (f : pr1 Z --> t), gbracket_parts_at (pr2 Z) f.

  Lemma isaprop_gbracket_property_parts {z : V} (e : I_{Mon_V} --> z) (f : z --> t) (h : z ⊗_{Mon_V} t --> t) :
    isaprop (gbracket_property_parts e f h).
  Proof.
    apply isapropdirprod; apply V.
  Qed.

  Lemma isaprop_gbracket : isaprop gbracket.
  Proof.
    apply impred_isaprop; intro Z.
    apply impred_isaprop; intro f.
    apply isapropiscontr.
  Qed.

  Section PropertyAsOneEquation.

    Context (CP : BinCoproducts V).

  Definition Const_plus_H (v : V) : functor V V := BinCoproduct_of_functors _ _ CP (constant_functor _ _ v) H.

  Definition gbracket_property_single {z : V} (e : I_{Mon_V} --> z) (f : z --> t) (h : z ⊗_{Mon_V} t --> t) : UU :=
    actegory_bincoprod_antidistributor Mon_PtdV CP Act (z,,e) I_{Mon_V} (H t) ·
      (z,,e) ⊗^{Act}_{l} (BinCoproductArrow (CP _ _) η τ) · h =
    BinCoproductOfArrows _ (CP _ _) (CP _ _) (ru_{Mon_V} z) (θ (z,,e) t) ·
      #(Const_plus_H z) h · BinCoproductArrow (CP _ _) f τ.

  Lemma isaprop_gbracket_property_single {z : V} (e : I_{Mon_V} --> z) (f : z --> t) (h : z ⊗_{Mon_V} t --> t) :
    isaprop (gbracket_property_single e f h).
  Proof.
    apply V.
  Qed.

  Lemma gbracket_property_single_equivalent {z : V} (e : I_{Mon_V} --> z) (f : z --> t) (h : z ⊗_{Mon_V} t --> t) :
    gbracket_property_parts e f h <-> gbracket_property_single e f h.
  Proof.
    split.
    - intros [Hη Hτ].
      use BinCoproductArrowsEq.
      + etrans.
        { repeat rewrite assoc.
          do 2 apply cancel_postcomposition.
          apply BinCoproductIn1Commutes. }
        etrans.
        { apply cancel_postcomposition.
          apply pathsinv0, (functor_comp (leftwhiskering_functor Act (z,,e))). }
        rewrite BinCoproductIn1Commutes.
        etrans.
        2: { repeat rewrite assoc.
             do 2 apply cancel_postcomposition.
             apply pathsinv0, BinCoproductOfArrowsIn1. }
        etrans.
        { apply pathsinv0, Hη. }
        repeat rewrite assoc'.
        apply maponpaths.
        rewrite assoc.
        etrans.
        2: { apply cancel_postcomposition.
             apply pathsinv0, BinCoproductOfArrowsIn1. }
        rewrite assoc'.
        rewrite id_left.
        apply pathsinv0, BinCoproductIn1Commutes.
      + etrans.
        { repeat rewrite assoc.
          do 2 apply cancel_postcomposition.
          apply BinCoproductIn2Commutes. }
        etrans.
        { apply cancel_postcomposition.
          apply pathsinv0, (functor_comp (leftwhiskering_functor Act (z,,e))). }
        rewrite BinCoproductIn2Commutes.
        etrans.
        2: { repeat rewrite assoc.
             do 2 apply cancel_postcomposition.
             apply pathsinv0, BinCoproductOfArrowsIn2. }
        etrans.
        { apply pathsinv0, Hτ. }
        repeat rewrite assoc'.
        apply maponpaths.
        rewrite assoc.
        etrans.
        2: { apply cancel_postcomposition.
             apply pathsinv0, BinCoproductOfArrowsIn2. }
        rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, BinCoproductIn2Commutes.
    - intro H1.
      split.
      + apply (maponpaths (fun m => BinCoproductIn1 (CP _ _) · m)) in H1.
        unfold actegory_bincoprod_antidistributor, bifunctor_bincoprod_antidistributor, bincoprod_antidistributor in H1.
        repeat rewrite assoc in H1.
        rewrite BinCoproductIn1Commutes in H1.
        assert (aux := functor_comp (leftwhiskering_functor Act (z,,e))
                         (BinCoproductIn1 (CP I_{ Mon_V} (H t)))
                         (BinCoproductArrow (CP I_{ Mon_V} (H t)) η τ)).
        cbn in aux.
        apply (maponpaths (fun m => m · h)) in aux.
        assert (H1' := aux @ H1).
        clear H1 aux.
        rewrite BinCoproductIn1Commutes in H1'.
        etrans.
        2: { apply pathsinv0, H1'. }
        clear H1'.
        etrans.
        2: { repeat rewrite assoc.
             do 2 apply cancel_postcomposition.
             apply pathsinv0, BinCoproductOfArrowsIn1. }
        repeat rewrite assoc'.
        apply maponpaths.
        rewrite assoc.
        etrans.
        2: { apply cancel_postcomposition.
             apply pathsinv0, BinCoproductOfArrowsIn1. }
        rewrite assoc'.
        rewrite id_left.
        apply pathsinv0, BinCoproductIn1Commutes.
      + apply (maponpaths (fun m => BinCoproductIn2 (CP _ _) · m)) in H1.
        unfold actegory_bincoprod_antidistributor, bifunctor_bincoprod_antidistributor, bincoprod_antidistributor in H1.
        repeat rewrite assoc in H1.
        rewrite BinCoproductIn2Commutes in H1.
        assert (aux := functor_comp (leftwhiskering_functor Act (z,,e))
                         (BinCoproductIn2 (CP I_{ Mon_V} (H t)))
                         (BinCoproductArrow (CP I_{ Mon_V} (H t)) η τ)).
        cbn in aux.
        apply (maponpaths (fun m => m · h)) in aux.
        assert (H1' := aux @ H1).
        clear H1 aux.
        rewrite BinCoproductIn2Commutes in H1'.
        etrans.
        2: { apply pathsinv0, H1'. }
        clear H1'.
        etrans.
        2: { repeat rewrite assoc.
             do 2 apply cancel_postcomposition.
             apply pathsinv0, BinCoproductOfArrowsIn2. }
        repeat rewrite assoc'.
        apply maponpaths.
        rewrite assoc.
        etrans.
        2: { apply cancel_postcomposition.
             apply pathsinv0, BinCoproductOfArrowsIn2. }
        rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, BinCoproductIn2Commutes.
  Qed.

  End PropertyAsOneEquation.

  End TheProperty.

  Definition ghss : UU := ∑ (t : V) (η : I_{Mon_V} --> t) (τ : H t --> t), gbracket t η τ.
  Coercion carrierghss (t : ghss) : V := pr1 t.

  Section FixAGhss.

  Context (gh : ghss).

  Definition eta_from_alg : I_{Mon_V} --> gh := pr12 gh.
  Definition tau_from_alg : H gh --> gh := pr122 gh.

  Definition ptd_from_gh : PtdV := (pr1 gh,,eta_from_alg).

  Local Notation η := eta_from_alg.
  Local Notation τ := tau_from_alg.

  Definition gfbracket (Z : PtdV) (f : pr1 Z --> gh) : pr1 Z ⊗_{Mon_V} gh --> gh :=
    pr1 (pr1 (pr222 gh Z f)).

  Notation "⦃ f ⦄_{ Z }" := (gfbracket Z f)(at level 0).

  Lemma gfbracket_unique {Z : PtdV} (f : pr1 Z --> gh)
    : ∏ α : pr1 Z ⊗_{Mon_V} gh --> gh, gbracket_property_parts gh η τ (pr2 Z) f α
   → α = ⦃f⦄_{Z}.
  Proof.
    intros α Hyp.
    apply path_to_ctr.
    assumption.
  Qed.

  Lemma gfbracket_η {Z : PtdV} (f : pr1 Z --> gh) :
    ru^{Mon_V}_{pr1 Z} · f = pr1 Z ⊗^{Mon_V}_{l} η · ⦃f⦄_{Z}.
  Proof.
    exact (pr1 ((pr2 (pr1 (pr222 gh Z f))))).
  Qed.

  Lemma gfbracket_τ {Z : PtdV} (f : pr1 Z --> gh) :
    θ Z gh · #H ⦃f⦄_{Z} · τ =  pr1 Z ⊗^{Mon_V}_{l} τ · ⦃f⦄_{Z}.
  Proof.
    exact (pr2 ((pr2 (pr1 (pr222 gh Z f))))).
  Qed.

  (** there is a restricted form of naturality in the [f] argument, only for pointed [f] *)
  Lemma gfbracket_natural {Z Z' : PtdV} (f : Z --> Z') (g : pr1 Z' --> gh) :
    pr1 f ⊗^{ Mon_V}_{r} gh · ⦃g⦄_{Z'} = ⦃pr1 f · g⦄_{Z}.
  Proof.
    apply gfbracket_unique.
    split.
    - etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           apply (bifunctor_equalwhiskers Mon_V). }
      unfold functoronmorphisms1.
      etrans.
      2: { rewrite assoc'.
           apply maponpaths.
           apply gfbracket_η. }
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0, monoidal_rightunitornat.
    - etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           apply (bifunctor_equalwhiskers Mon_V). }
      unfold functoronmorphisms1.
      etrans.
      2: { rewrite assoc'.
           apply maponpaths.
           apply gfbracket_τ. }
      rewrite functor_comp.
      repeat rewrite assoc.
      do 2 apply cancel_postcomposition.
      apply pathsinv0, (lineator_linnatright Mon_PtdV Act Act).
  Qed.

  (** As a consequence of naturality, we can compute [gfbracket f] from [gfbracket identity] for
      pointed morphisms [f] *)
  Lemma compute_gfbracket {Z : PtdV} (f : Z --> ptd_from_gh) :
    ⦃pr1 f⦄_{Z} = pr1 f ⊗^{ Mon_V}_{r} gh · ⦃identity gh⦄_{ptd_from_gh}.
  Proof.
    etrans.
    { rewrite <- (id_right (pr1 f)).
      apply pathsinv0, gfbracket_natural. }
    apply idpath.
  Qed.

  (** we are constructing a monoid in the monoidal base category *)

  Definition Ptd_from_ghss : PtdV := (pr1 gh,,η).

  Definition mu_from_ghss : gh ⊗_{Mon_V} gh --> gh := ⦃identity gh⦄_{Ptd_from_ghss}.

  Local Notation μ := mu_from_ghss.

  Definition μ_0 : I_{Mon_V} --> gh := η.

  Definition μ_0_Ptd : I_{Mon_PtdV} --> Ptd_from_ghss.
  Proof.
    exists μ_0.
    cbn. apply id_left.
  Defined.

  Definition μ_1 : I_{Mon_V} ⊗_{Mon_V} gh --> gh := ⦃μ_0⦄_{I_{Mon_PtdV}}.

  Lemma μ_1_is_instance_of_left_unitor : μ_1 = lu^{Mon_V}_{gh}.
  Proof.
    apply pathsinv0, (gfbracket_unique(Z:=I_{Mon_PtdV})).
    split.
    - cbn. unfold μ_0.
      rewrite monoidal_leftunitornat.
      apply cancel_postcomposition.
      apply pathsinv0, unitors_coincide_on_unit.
    - etrans.
      { apply cancel_postcomposition.
        apply pointedtensorialstrength_preserves_unitor.
        apply lineator_preservesunitor. }
      cbn.
      apply pathsinv0, monoidal_leftunitornat.
  Qed.

  Definition ghss_monoid_data : monoid_data Mon_V gh := μ,,μ_0.

  Lemma ghss_first_monoidlaw : monoid_laws_unit_right Mon_V ghss_monoid_data.
  Proof.
    red. cbn.
    etrans.
    { apply pathsinv0, (gfbracket_η(Z:=Ptd_from_ghss)). }
    apply id_right.
  Qed.


  Lemma ghss_second_monoidlaw_aux :
    ru^{Mon_V}_{I_{Mon_V}} · η = I_{Mon_V} ⊗^{Mon_V}_{l} η · (η ⊗^{Mon_V}_{r} gh · μ).
  Proof.
    rewrite assoc.
    etrans.
    2: { apply cancel_postcomposition.
         apply (bifunctor_equalwhiskers Mon_V). }
    unfold functoronmorphisms1.
    rewrite assoc'.
    etrans.
    2: { apply maponpaths.
         apply pathsinv0, ghss_first_monoidlaw. }
    apply pathsinv0, monoidal_rightunitornat.
  Qed.

  Lemma ghss_second_monoidlaw : monoid_laws_unit_left Mon_V ghss_monoid_data.
  Proof.
    red. cbn.
    etrans.
    2: { apply μ_1_is_instance_of_left_unitor. }
    apply (gfbracket_unique(Z:=I_{Mon_PtdV})).
    split.
    - exact ghss_second_monoidlaw_aux.
    - rewrite functor_comp.
      transitivity (μ_0 ⊗^{ Mon_V}_{r} H (pr1 gh) · θ Ptd_from_ghss (pr1 gh) · # H μ · τ). (* give this term due to efficiency problems *)
      { apply cancel_postcomposition.
        rewrite assoc.
        apply cancel_postcomposition.
        apply pathsinv0.
        set (aux := lineator_linnatright Mon_PtdV
                      (actegory_with_canonical_pointed_action Mon_V)
                      (actegory_with_canonical_pointed_action Mon_V)
                      H θ I_{ Mon_PtdV} Ptd_from_ghss (pr1 gh) μ_0_Ptd).
        cbn in aux.
        etrans.
        { exact aux. }
        apply idpath.
      }
      etrans.
      { do 2 rewrite assoc'.
        apply maponpaths.
        rewrite assoc.
        apply (gfbracket_τ(Z:=Ptd_from_ghss)).
      }
      repeat rewrite assoc.
      apply cancel_postcomposition.
      cbn.
      apply (bifunctor_equalwhiskers Mon_V).
  Qed.

  Definition gh_squared : PtdV := Ptd_from_ghss ⊗_{Mon_PtdV} Ptd_from_ghss.

  Definition μ_2 : gh ⊗_{Mon_V} gh --> gh := μ.

  Lemma μ_2_is_Ptd_mor : luinv^{Mon_V}_{I_{Mon_V}} · η ⊗^{Mon_V} η · μ_2 = η.
  Proof.
    rewrite assoc'.
    apply (z_iso_inv_on_right _ _ _ (nat_z_iso_pointwise_z_iso (leftunitor_nat_z_iso Mon_V) I_{ Mon_V})).
    cbn.
    rewrite unitors_coincide_on_unit.
    etrans.
    2: { apply pathsinv0, ghss_second_monoidlaw_aux. }
    rewrite assoc.
    apply cancel_postcomposition.
    apply (bifunctor_equalwhiskers Mon_V).
  Qed.

  Definition μ_2_Ptd : gh_squared --> Ptd_from_ghss := μ_2,,μ_2_is_Ptd_mor.

  Definition μ_3 : (gh ⊗_{Mon_V} gh) ⊗_{Mon_V} gh --> gh := ⦃μ_2⦄_{gh_squared}.

  Lemma ghss_third_monoidlaw_aux : θ (pr1 gh_squared,, pr2 gh_squared) gh · # H (μ ⊗^{Mon_V}_{r} gh) =
                                     μ_2 ⊗^{Mon_V}_{r} H gh · θ Ptd_from_ghss gh.
  Proof.
    apply pathsinv0.
    assert (aux := lineator_linnatright Mon_PtdV
                     (actegory_with_canonical_pointed_action Mon_V)
                     (actegory_with_canonical_pointed_action Mon_V)
                     H θ gh_squared Ptd_from_ghss gh μ_2_Ptd).
    simpl in aux. (* simpl not cbn for efficiency of Qed *)
    etrans.
    { exact aux. }
    apply idpath.
  Qed.

  Lemma ghss_third_monoidlaw : monoid_laws_assoc Mon_V ghss_monoid_data.
  Proof.
    red. cbn. apply pathsinv0.
    transitivity μ_3.
    - (** this case is the monoidal generalization of the second item on p.168 of Matthes & Uustalu, TCS 2004 *)
      apply (gfbracket_unique(Z:=gh_squared)).
      split.
      + cbn.
        etrans.
        2: { rewrite assoc.
             apply cancel_postcomposition.
             apply (bifunctor_equalwhiskers Mon_V). }
        unfold functoronmorphisms1.
        etrans.
        2: { rewrite assoc'.
             apply maponpaths.
             apply pathsinv0, ghss_first_monoidlaw.
        }
        apply pathsinv0, monoidal_rightunitornat.
      + etrans.
        { apply cancel_postcomposition.
          rewrite functor_comp.
          rewrite assoc.
          apply cancel_postcomposition.
          exact ghss_third_monoidlaw_aux.
        }
        etrans.
        { do 2 rewrite assoc'.
          apply maponpaths.
          rewrite assoc.
          apply (gfbracket_τ(Z:=Ptd_from_ghss)).
        }
        do 2 rewrite assoc.
        apply cancel_postcomposition.
        cbn.
        apply (bifunctor_equalwhiskers Mon_V).
    - (** this case is the monoidal generalization of the first item on p.168 of Matthes & Uustalu, TCS 2004 *)
      apply pathsinv0, (gfbracket_unique(Z:=gh_squared)).
      split.
      + cbn.
        etrans.
        2: { rewrite assoc.
             apply cancel_postcomposition.
             rewrite assoc.
             rewrite <- monoidal_associatornatleft.
             rewrite assoc'.
             apply maponpaths.
             apply (bifunctor_leftcomp Mon_V). }
        etrans.
        2: { apply cancel_postcomposition.
             do 2 apply maponpaths.
             apply pathsinv0, ghss_first_monoidlaw. }
        apply cancel_postcomposition.
        apply pathsinv0, left_whisker_with_runitor.
      + etrans.
        { apply cancel_postcomposition.
          rewrite assoc'.
          rewrite functor_comp.
          rewrite assoc.
          apply cancel_postcomposition.
          apply pointedtensorialstrength_preserves_actor.
          apply lineator_preservesactor. }
        cbn.
        etrans.
        { repeat rewrite assoc'.
          do 2 apply maponpaths.
          etrans.
          { rewrite assoc.
            apply cancel_postcomposition.
            rewrite functor_comp.
            rewrite assoc.
            apply cancel_postcomposition.
            apply pathsinv0, (lineator_linnatleft Mon_PtdV _ _ H θ Ptd_from_ghss _ _ μ).
          }
          repeat rewrite assoc'.
          apply maponpaths.
          rewrite assoc.
          apply (gfbracket_τ(Z:=Ptd_from_ghss)).
        }
        cbn.
        repeat rewrite assoc.
        apply cancel_postcomposition.
        etrans.
        { repeat rewrite assoc'.
          apply maponpaths.
          do 2 rewrite <- (bifunctor_leftcomp Mon_V).
          apply maponpaths.
          rewrite assoc.
          apply (gfbracket_τ(Z:=Ptd_from_ghss)).
        }
        cbn.
        rewrite (bifunctor_leftcomp Mon_V).
        repeat rewrite assoc.
        apply cancel_postcomposition.
        apply monoidal_associatornatleft.
  Qed.

  Definition ghss_monoid : monoid Mon_V gh.
  Proof.
    exists ghss_monoid_data.
    exact (ghss_second_monoidlaw,,ghss_first_monoidlaw,,ghss_third_monoidlaw).
  Defined.

  End FixAGhss.

End hss.
