Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section MonoidalSections.

  Import BifunctorNotations.
  Import MonoidalNotations.
  Import DisplayedBifunctorNotations.
  Import DisplayedMonoidalNotations.

  Variable C : category.
  Variable D : disp_cat C.
  Local Notation TD := (total_category D).
  Variable M : monoidal C.
  Variable DM : disp_monoidal D M.
  Local Notation TM := (total_monoidal DM).

  Definition section_preserves_tensor_data (sd : section_disp D) : UU
    := ∏ (x y : C),  sd x ⊗⊗_{ DM} sd y -->[ identity (x ⊗_{ M} y)] sd (x ⊗_{ M} y).

  Lemma sectionfunctor_preserves_tensordata {sd : section_disp D} (spt : section_preserves_tensor_data sd) : preserves_tensordata M TM (section_functor sd).
  Proof.
    intros x y.
    use tpair.
    - apply identity.
    - apply spt.
  Defined.

  Definition section_preserves_unit (sd : section_disp D) : UU
    :=  dI_{DM} -->[ identity I_{M}] sd I_{M}.

  Lemma sectionfunctor_preserves_unit {sd : section_disp D} (spu : section_preserves_unit sd) : preserves_unit M TM (section_functor sd).
  Proof.
    use tpair.
    - apply identity.
    - apply spu.
  Defined.

  Definition smonoidal_data (sd : section_disp D) : UU
    := (section_preserves_tensor_data sd) × (section_preserves_unit sd).
  Definition smonoidal_preserves_tensor {sd : section_disp D} (ms : smonoidal_data sd)
    : section_preserves_tensor_data sd := pr1 ms.
  Definition smonoidal_preserves_unit {sd : section_disp D} (ms : smonoidal_data sd)
    : section_preserves_unit sd := pr2 ms.

  Definition sectionfunctor_fmonoidal_data {sd : section_disp D} (spt : section_preserves_tensor_data sd) (spu : section_preserves_unit sd) : fmonoidal_data M TM (section_functor sd) := (sectionfunctor_preserves_tensordata spt,,sectionfunctor_preserves_unit spu).

  (* This notation comes from Constructions.v, but there is no Notation module, this has to be added *)
  Notation "# F" := (section_disp_on_morphisms F) (at level 3) : mor_disp_scope.

  Definition section_preserves_tensor_nat_left {sd : section_disp D} (spt : section_preserves_tensor_data sd) : UU
    := ∏ (x y1 y2 : C) (g : C⟦y1,y2⟧),
      (sd x ⊗⊗^{DM}_{l} #sd g) ;; spt x y2 = transportb _ (id_right (x ⊗^{M}_{l} g) @ pathsinv0 (id_left (x ⊗^{M}_{l} g))) (spt x y1 ;; #sd (x ⊗^{M}_{l} g)).

  Lemma sectionfunctor_preserves_tensor_nat_left {sd : section_disp D} {spt : section_preserves_tensor_data sd} (sptnl : section_preserves_tensor_nat_left spt) : preserves_tensor_nat_left (sectionfunctor_preserves_tensordata spt).
  Proof.
    intros x y1 y2 g.
    use total2_paths_b.
    - cbn.
      rewrite id_left.
      apply id_right.
    - cbn.
      rewrite sptnl.
      apply transportb_transpose_left.
      rewrite transport_f_b.
      apply pathsinv0.
      apply transportf_set.
      apply homset_property.
  Qed.

  Definition section_preserves_tensor_nat_right {sd : section_disp D} (spt : section_preserves_tensor_data sd) : UU
    := ∏ (x1 x2 y : C) (f : C⟦x1,x2⟧),
      (#sd f ⊗⊗^{DM}_{r} sd y) ;; spt x2 y = transportb _ (id_right (f ⊗^{M}_{r} y) @ pathsinv0 (id_left (f ⊗^{M}_{r} y))) (spt x1 y ;; #sd (f ⊗^{M}_{r} y)).

  Lemma sectionfunctor_preserves_tensor_nat_right {sd : section_disp D} {spt : section_preserves_tensor_data sd} (sptnl : section_preserves_tensor_nat_right spt) : preserves_tensor_nat_right (sectionfunctor_preserves_tensordata spt).
  Proof.
    intros x1 x2 y f.
    use total2_paths_b.
    - cbn.
      rewrite id_left.
      apply id_right.
    - cbn.
      rewrite sptnl.
      apply transportb_transpose_left.
      rewrite transport_f_b.
      apply pathsinv0.
      apply transportf_set.
      apply homset_property.
  Qed.

  (* This equality I should have somewhere, have to check in different files *)
  Definition equality_for_leftunitality (x : C) : identity I_{ M} ⊗^{ M}_{r} x · identity (I_{ M} ⊗_{ M} x) · lu^{ M }_{ x} = lu^{ M }_{ x}.
  Proof.
    rewrite assoc'.
    rewrite bifunctor_rightid.
    rewrite id_left.
    apply id_left.
  Qed.

  Definition section_preserves_leftunitality {sd : section_disp D} (spt : section_preserves_tensor_data sd) (spu : section_preserves_unit sd) : UU := ∏ (x : C),
       spu ⊗⊗^{ DM}_{r} sd x ;; spt I_{ M} x ;; # sd lu^{ M }_{ x} =
        transportb _
                   (equality_for_leftunitality x)
                   (dlu^{DM}_{sd x}).

  Definition sectionfunctor_preserves_leftunitality {sd : section_disp D} {spt : section_preserves_tensor_data sd} {spu : section_preserves_unit sd} (splu : section_preserves_leftunitality spt spu)
    : preserves_leftunitality (sectionfunctor_preserves_tensordata spt) (sectionfunctor_preserves_unit spu).
  Proof.
    intro x.
    use total2_paths_b.
    - cbn.
      rewrite assoc'.
      rewrite bifunctor_rightid.
      rewrite id_left.
      apply id_left.
    - cbn.
      rewrite splu.
      apply transportb_transpose_left.
      rewrite transport_f_b.
      apply pathsinv0.
      apply transportf_set.
      apply homset_property.
  Qed.

  (* This equality I should have somewhere, have to check in different files *)
  Definition equality_for_rightunitality (x : C) :
    x ⊗^{ M}_{l} identity I_{ M} · identity (x ⊗_{ M} I_{ M}) · ru^{ M }_{ x} = ru^{ M }_{ x}.
  Proof.
    rewrite assoc'.
    rewrite bifunctor_leftid.
    rewrite id_left.
    apply id_left.
  Qed.

  Definition section_preserves_rightunitality {sd : section_disp D} (spt : section_preserves_tensor_data sd) (spu : section_preserves_unit sd) : UU := ∏ (x : C),
       sd x ⊗⊗^{DM}_{l} spu ;; spt x I_{ M} ;; # sd ru^{ M }_{ x} =
        transportb _
                   (equality_for_rightunitality x)
                   (dru^{DM}_{sd x}).

  Definition sectionfunctor_preserves_rightunitality {sd : section_disp D} {spt : section_preserves_tensor_data sd} {spu : section_preserves_unit sd} (spru : section_preserves_rightunitality spt spu)
    : preserves_rightunitality (sectionfunctor_preserves_tensordata spt) (sectionfunctor_preserves_unit spu).
  Proof.
    intro x.
    use total2_paths_b.
    - cbn.
      rewrite assoc'.
      rewrite bifunctor_leftid.
      rewrite id_left.
      apply id_left.
    - cbn.
      rewrite spru.
      apply transportb_transpose_left.
      rewrite transport_f_b.
      apply pathsinv0.
      apply transportf_set.
      apply homset_property.
  Qed.

  (* This equality I should have somewhere, have to check in different files *)
  Definition equality_for_associativity (x y z : C) :
    identity (x ⊗_{ M} y) ⊗^{ M}_{r} z · identity ((x ⊗_{ M} y) ⊗_{ M} z) · α^{ M }_{ x, y, z} =
   α^{ M }_{ x, y, z} · x ⊗^{ M}_{l} identity (y ⊗_{ M} z) · identity (x ⊗_{ M} (y ⊗_{ M} z)).
  Proof.
    rewrite assoc'.
    rewrite bifunctor_leftid.
    rewrite id_left.
    rewrite id_right.
    rewrite id_right.
    rewrite bifunctor_rightid.
    apply id_left.
  Qed.

  Definition section_preserves_associativity {sd : section_disp D} (spt : section_preserves_tensor_data sd) : UU
    := ∏ (x y z : C), spt x y ⊗⊗^{ DM}_{r} sd z ;; spt (x ⊗_{ M} y) z ;; # sd α^{ M }_{ x, y, z}
                = transportb _
                    (equality_for_associativity x y z)
                    (dα^{ DM }_{ sd x, sd y, sd z} ;; sd x ⊗⊗^{ DM}_{l} spt y z ;; spt x (y ⊗_{ M} z)).

  Definition sectionfunctor_preserves_associativity {sd : section_disp D} {spt : section_preserves_tensor_data sd} (spa : section_preserves_associativity spt)
    : preserves_associativity (sectionfunctor_preserves_tensordata spt).
  Proof.
    intros x y z.
    use total2_paths_b.
    - cbn.
      rewrite assoc'.
      rewrite bifunctor_leftid.
      rewrite id_right.
      rewrite id_right.
      rewrite id_left.
      rewrite bifunctor_rightid.
      apply id_left.
    - cbn.
      rewrite spa.
      apply transportb_transpose_left.
      rewrite transport_f_b.
      apply pathsinv0.
      apply transportf_set.
      apply homset_property.
  Qed.

  Definition smonoidal_laxlaws {sd : section_disp D} (ms : smonoidal_data sd) : UU
    := (section_preserves_tensor_nat_left (smonoidal_preserves_tensor ms)) ×
       (section_preserves_tensor_nat_right (smonoidal_preserves_tensor ms)) ×
       (section_preserves_associativity (smonoidal_preserves_tensor ms)) ×
       (section_preserves_leftunitality (smonoidal_preserves_tensor ms) (smonoidal_preserves_unit ms)) ×
       (section_preserves_rightunitality (smonoidal_preserves_tensor ms) (smonoidal_preserves_unit ms)).

  Definition smonoidal_preserves_tensornatleft {sd : section_disp D} {ms : smonoidal_data sd} (msl : smonoidal_laxlaws ms) :
    section_preserves_tensor_nat_left (smonoidal_preserves_tensor ms) := pr1 msl.
  Definition smonoidal_preserves_tensornatright {sd : section_disp D} {ms : smonoidal_data sd} (msl : smonoidal_laxlaws ms) :
    section_preserves_tensor_nat_right (smonoidal_preserves_tensor ms) := pr1 (pr2 msl).
  Definition smonoidal_preserves_associativity {sd : section_disp D} {ms : smonoidal_data sd} (msl : smonoidal_laxlaws ms) :
    section_preserves_associativity (smonoidal_preserves_tensor ms) := pr1 (pr2 (pr2 msl)).
  Definition smonoidal_preserves_leftunitality {sd : section_disp D} {ms : smonoidal_data sd} (msl : smonoidal_laxlaws ms) :
    section_preserves_leftunitality (smonoidal_preserves_tensor ms) (smonoidal_preserves_unit ms) := pr1 (pr2 (pr2 (pr2 msl))).
  Definition smonoidal_preserves_rightunitality {sd : section_disp D} {ms : smonoidal_data sd} (msl : smonoidal_laxlaws ms) :
    section_preserves_rightunitality (smonoidal_preserves_tensor ms) (smonoidal_preserves_unit ms) := pr2 (pr2 (pr2 (pr2 msl))).

  Definition smonoidal_lax (sd : section_disp D) : UU := ∑ (ms : smonoidal_data sd), smonoidal_laxlaws ms.
  Definition smonoidal_sdata {sd : section_disp D} (sm : smonoidal_lax sd) : smonoidal_data sd := pr1 sm.
  Coercion smonoidal_sdata : smonoidal_lax >-> smonoidal_data.
  Definition smonoidal_slaxlaws {sd : section_disp D} (sm : smonoidal_lax sd) : smonoidal_laxlaws sm := pr2 sm.

  Definition sectionfunctor_fmonoidal_laxlaws {sd : section_disp D} {ms : smonoidal_data sd} (ml : smonoidal_laxlaws ms) :
    fmonoidal_laxlaws (sectionfunctor_fmonoidal_data (smonoidal_preserves_tensor ms) (smonoidal_preserves_unit ms))
    := (sectionfunctor_preserves_tensor_nat_left (smonoidal_preserves_tensornatleft ml),,
        sectionfunctor_preserves_tensor_nat_right (smonoidal_preserves_tensornatright ml),,
        sectionfunctor_preserves_associativity (smonoidal_preserves_associativity ml),,
        sectionfunctor_preserves_leftunitality (smonoidal_preserves_leftunitality ml),,
        sectionfunctor_preserves_rightunitality (smonoidal_preserves_rightunitality ml)
       ).

  Definition sectionfunctor_fmonoidal_lax {sd : section_disp D} (ms : smonoidal_lax sd) : fmonoidal_lax M TM (section_functor sd)
    := (sectionfunctor_fmonoidal_data (smonoidal_preserves_tensor ms) (smonoidal_preserves_unit ms),,sectionfunctor_fmonoidal_laxlaws (smonoidal_slaxlaws ms)).

  (* We now define a strong monoidal section and show that each such section induces a strong monoidal functor *)
  Definition smonoidal_strongtensor {sd : section_disp D} (spt : section_preserves_tensor_data sd) : UU
    := ∏ (x y : C), is_z_iso_disp
                        (Isos.identity_z_iso (x⊗_{M} y))
                        (spt x y).

  Definition smonoidal_strongunit   {sd : section_disp D} (spu : section_preserves_unit sd) : UU
    := is_z_iso_disp
                        (Isos.identity_z_iso (I_{M}))
                        spu.

  Definition smonoidal_stronglaws {sd : section_disp D} (ms : smonoidal_data sd) : UU
    := smonoidal_strongtensor (smonoidal_preserves_tensor ms)
                              × smonoidal_strongunit (smonoidal_preserves_unit ms).

  Definition smonoidal (sd : section_disp D) : UU
    := ∑ (ms : smonoidal_lax sd), smonoidal_stronglaws ms.

  Definition smonoidal_smonoidallax {sd : section_disp D} (sm : smonoidal sd)
    : smonoidal_lax sd := pr1 sm.
  Coercion smonoidal_smonoidallax : smonoidal >-> smonoidal_lax.

  Definition smonoidal_smonoidalstronglaws {sd : section_disp D} (sm : smonoidal sd)
    : smonoidal_stronglaws sm := pr2 sm.
  Definition smonoidal_smonoidalstrongtensor {sd : section_disp D} (sm : smonoidal sd)
    : smonoidal_strongtensor (smonoidal_preserves_tensor sm) := pr1 (smonoidal_smonoidalstronglaws sm).
  Definition smonoidal_smonoidalstrongunit {sd : section_disp D} (sm : smonoidal sd)
    : smonoidal_strongunit (smonoidal_preserves_unit sm) := pr2 (smonoidal_smonoidalstronglaws sm).

  Definition sectionfunctor_preservestensorstrongly {sd : section_disp D} {ms : smonoidal sd} (pfstrong : smonoidal_strongtensor (smonoidal_preserves_tensor ms))
    : preserves_tensor_strongly (sectionfunctor_preserves_tensordata (smonoidal_preserves_tensor ms)).
  Proof.
    intros x y.
    use tpair.
    - use tpair.
      + apply identity.
      + exact (pr1 (pfstrong x y)).
    - use tpair.
      + use total2_paths_b.
        * apply id_left.
        * apply (pr2 (pr2 (pfstrong x y))).
      + use total2_paths_b.
        * apply id_left.
        * apply (pr1 (pr2 (pfstrong x y))).
  Defined.

  Definition sectionfunctor_preservesunitstrongly {sd : section_disp D} {ms : smonoidal sd} (pfstrong : smonoidal_strongunit (smonoidal_preserves_unit ms))
    : preserves_unit_strongly (sectionfunctor_preserves_unit (smonoidal_preserves_unit ms)).
  Proof.
    use tpair.
    - use tpair.
      + apply identity.
      + exact (pr1 pfstrong).
    - use tpair.
      + use total2_paths_b.
        * apply id_left.
        * apply (pr22 pfstrong).
      + use total2_paths_b.
        * apply id_left.
        * apply (pr1 (pr2 pfstrong)).
  Defined.

  Definition sectionfunctor_fmonoidal {sd : section_disp D} (ms : smonoidal sd)  : fmonoidal M TM (section_functor sd)
    := (sectionfunctor_fmonoidal_lax ms ,,
        sectionfunctor_preservestensorstrongly (smonoidal_smonoidalstrongtensor ms) ,,
        sectionfunctor_preservesunitstrongly (smonoidal_smonoidalstrongunit ms)).

End MonoidalSections.
