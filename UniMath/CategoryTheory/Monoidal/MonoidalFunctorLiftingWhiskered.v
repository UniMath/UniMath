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

Section MonoidalFunctorLifting.

  Import BifunctorNotations.
  Import MonoidalNotations.
  Import DisplayedBifunctorNotations.
  Import DisplayedMonoidalNotations.

  Context {C' C : category} {F : functor C' C} {D : disp_cat C}.
  Local Notation TD := (total_category D).
  Context {M' : monoidal C'}
          {M : monoidal C}
          (Fm : fmonoidal_lax M' M F)
          (DM : disp_monoidal D M).
  Local Notation TM := (total_monoidal DM).

  Check functor_lifting.

  Context (sd : functor_lifting D F).

  Definition fl_preserves_tensor_data : UU
    := ∏ (x y : C'),   sd x ⊗⊗_{ DM} sd y -->[ fmonoidal_preservestensordata Fm x y] sd (x ⊗_{ M'} y).

  Lemma functorlifting_preserves_tensordata
        (sd_pt : fl_preserves_tensor_data)
    : preserves_tensordata M' TM (lifted_functor sd).
  Proof.
    intros x y.
    exists (fmonoidal_preservestensordata Fm x y).
    exact (sd_pt x y).
  Defined.

  Definition fl_preserves_unit : UU
    := dI_{ DM} -->[ fmonoidal_preservesunit Fm] sd I_{ M'}.

  Lemma functorlifting_preserves_unit
        (sp_pu : fl_preserves_unit)
    : preserves_unit M' TM (lifted_functor sd).
  Proof.
    exists (fmonoidal_preservesunit Fm).
    exact sp_pu.
  Defined.

  Definition flmonoidal_data : UU
    := fl_preserves_tensor_data × fl_preserves_unit.
  Definition flmonoidal_preserves_tensor_data (ms : flmonoidal_data)
    : fl_preserves_tensor_data := pr1 ms.
  Definition flmonoidal_preserves_unit (ms : flmonoidal_data)
    : fl_preserves_unit := pr2 ms.

  Definition functorlifting_monoidal_data
             (ms : flmonoidal_data)
    : fmonoidal_data M' TM (lifted_functor sd).
  Proof.
    exists (functorlifting_preserves_tensordata (flmonoidal_preserves_tensor_data ms)).
    exact (functorlifting_preserves_unit (flmonoidal_preserves_unit ms)).
  Defined.

  (* This notation comes from Constructions.v, but there is no Notation module, this has to be added *)
  Notation "# F" := (section_disp_on_morphisms F) (at level 3) : mor_disp_scope.

  Definition fl_preserves_tensor_nat_left
             (spt : fl_preserves_tensor_data) : UU
    := ∏ (x y1 y2 : C') (g : C'⟦y1,y2⟧),
      sd x ⊗⊗^{ DM}_{l} # sd g ;; spt x y2
      = transportb _
                   (fmonoidal_preservestensornatleft Fm x y1 y2 g)
                   (spt x y1 ;; # sd (x ⊗^{ M'}_{l} g)).

  Lemma functorlifting_preserves_tensor_nat_left
        {spt : fl_preserves_tensor_data} (sptnl : fl_preserves_tensor_nat_left spt)
    : preserves_tensor_nat_left (functorlifting_preserves_tensordata spt).
  Proof.
    intros x y1 y2 g.
    use total2_paths_b.
    - exact (fmonoidal_preservestensornatleft Fm x y1 y2 g).
    - exact (sptnl x y1 y2 g).
  Qed.

  Definition fl_preserves_tensor_nat_right
             (spt : fl_preserves_tensor_data)
    : UU
    := ∏ (x1 x2 y : C') (f : C'⟦x1,x2⟧),
      # sd f ⊗⊗^{ DM}_{r} sd y ;; spt x2 y
      = transportb _
                   (fmonoidal_preservestensornatright Fm x1 x2 y f)
                   (spt x1 y ;; # sd (f ⊗^{ M'}_{r} y)).

  Lemma functorlifting_preserves_tensor_nat_right
        {spt : fl_preserves_tensor_data}
        (sptnl : fl_preserves_tensor_nat_right spt)
    : preserves_tensor_nat_right (functorlifting_preserves_tensordata spt).
  Proof.
    intros x1 x2 y f.
    use total2_paths_b.
    - exact (fmonoidal_preservestensornatright Fm x1 x2 y f).
    - exact (sptnl x1 x2 y f).
  Qed.

  (* This equality I should have somewhere, have to check in different files *)
  (* Definition equality_for_leftunitality (x : C) : identity I_{ M} ⊗^{ M}_{r} x · identity (I_{ M} ⊗_{ M} x) · lu^{ M }_{ x} = lu^{ M }_{ x}.
  Proof.
    rewrite assoc'.
    rewrite bifunctor_rightid.
    rewrite id_left.
    apply id_left.
  Qed. *)

  Definition fl_preserves_leftunitality
             (spt : fl_preserves_tensor_data)
             (spu : fl_preserves_unit) : UU
    := ∏ (x : C'),
      spu ⊗⊗^{ DM}_{r} sd x ;; spt I_{ M'} x ;; # sd lu^{ M' }_{ x}
      = transportb _
                   (fmonoidal_preservesleftunitality Fm x)
                   dlu^{ DM }_{ sd x}.

  Definition functorlifting_preserves_leftunitality
             {spt : fl_preserves_tensor_data}
             {spu : fl_preserves_unit}
             (splu : fl_preserves_leftunitality spt spu)
    : preserves_leftunitality (functorlifting_preserves_tensordata spt) (functorlifting_preserves_unit spu).
  Proof.
    intro x.
    use total2_paths_b.
    - exact (fmonoidal_preservesleftunitality Fm x).
    - exact (splu x).
  Qed.

  (* This equality I should have somewhere, have to check in different files *)
  (* Definition equality_for_rightunitality (x : C) :
    x ⊗^{ M}_{l} identity I_{ M} · identity (x ⊗_{ M} I_{ M}) · ru^{ M }_{ x} = ru^{ M }_{ x}.
  Proof.
    rewrite assoc'.
    rewrite bifunctor_leftid.
    rewrite id_left.
    apply id_left.
  Qed. *)

  Definition fl_preserves_rightunitality
             (spt : fl_preserves_tensor_data)
             (spu : fl_preserves_unit)
    : UU := ∏ (x : C'),
      sd x ⊗⊗^{ DM}_{l} spu ;; spt x I_{ M'} ;; # sd ru^{ M' }_{ x}
      = transportb _
                   (fmonoidal_preservesrightunitality Fm x)
                   dru^{ DM }_{ sd x}.

  Definition functorlifting_preserves_rightunitality
             {spt : fl_preserves_tensor_data}
             {spu : fl_preserves_unit}
             (spru : fl_preserves_rightunitality spt spu)
    : preserves_rightunitality
        (functorlifting_preserves_tensordata spt) (functorlifting_preserves_unit spu).
  Proof.
    intro x.
    use total2_paths_b.
    - exact (fmonoidal_preservesrightunitality Fm x).
    - exact (spru x).
  Qed.

  (* This equality I should have somewhere, have to check in different files *)
  (* Definition equality_for_associativity (x y z : C) :
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
  Qed. *)

  Definition fl_preserves_associativity
             (spt : fl_preserves_tensor_data ) : UU
    := ∏ (x y z : C'),
      spt x y ⊗⊗^{ DM}_{r} sd z ;; spt (x ⊗_{ M'} y) z ;; # sd α^{ M' }_{ x, y, z}
      = transportb _
          (fmonoidal_preservesassociativity Fm x y z)
          (dα^{ DM }_{ sd x, sd y, sd z} ;; sd x ⊗⊗^{ DM}_{l} spt y z ;; spt x (y ⊗_{ M'} z)).

  Definition functorlifting_preserves_associativity
             {spt : fl_preserves_tensor_data}
             (spa : fl_preserves_associativity spt)
    : preserves_associativity (functorlifting_preserves_tensordata spt).
  Proof.
    intros x y z.
    use total2_paths_b.
    - exact (fmonoidal_preservesassociativity Fm x y z).
    - exact (spa x y z).
  Qed.

  Definition flmonoidal_laxlaws (ms : flmonoidal_data) : UU
    := (fl_preserves_tensor_nat_left (flmonoidal_preserves_tensor_data ms)) ×
       (fl_preserves_tensor_nat_right (flmonoidal_preserves_tensor_data ms)) ×
       (fl_preserves_associativity (flmonoidal_preserves_tensor_data ms)) ×
       (fl_preserves_leftunitality (flmonoidal_preserves_tensor_data ms) (flmonoidal_preserves_unit ms)) ×
       (fl_preserves_rightunitality (flmonoidal_preserves_tensor_data ms) (flmonoidal_preserves_unit ms)).

  Definition flmonoidal_preserves_tensornatleft
             {ms : flmonoidal_data} (msl : flmonoidal_laxlaws ms)
    : fl_preserves_tensor_nat_left (flmonoidal_preserves_tensor_data ms)
    := pr1 msl.
  Definition flmonoidal_preserves_tensornatright
             {ms : flmonoidal_data} (msl : flmonoidal_laxlaws ms)
    : fl_preserves_tensor_nat_right (flmonoidal_preserves_tensor_data ms)
    := pr1 (pr2 msl).
  Definition flmonoidal_preserves_associativity
             {ms : flmonoidal_data} (msl : flmonoidal_laxlaws ms)
    : fl_preserves_associativity (flmonoidal_preserves_tensor_data ms)
    := pr1 (pr2 (pr2 msl)).
  Definition flmonoidal_preserves_leftunitality
             {ms : flmonoidal_data} (msl : flmonoidal_laxlaws ms)
    : fl_preserves_leftunitality (flmonoidal_preserves_tensor_data ms) (flmonoidal_preserves_unit ms)
    := pr1 (pr2 (pr2 (pr2 msl))).
  Definition flmonoidal_preserves_rightunitality
             {ms : flmonoidal_data} (msl : flmonoidal_laxlaws ms)
    : fl_preserves_rightunitality (flmonoidal_preserves_tensor_data ms) (flmonoidal_preserves_unit ms)
    := pr2 (pr2 (pr2 (pr2 msl))).

  Definition flmonoidal_lax : UU
    := ∑ (ms : flmonoidal_data), flmonoidal_laxlaws ms.
  Definition flmonoidal_lax_to_data (sm : flmonoidal_lax)
    : flmonoidal_data := pr1 sm.
  Coercion flmonoidal_lax_to_data : flmonoidal_lax >-> flmonoidal_data.

  Definition flmonoidal_lax_to_laxlaws (sm : flmonoidal_lax)
    : flmonoidal_laxlaws sm := pr2 sm.

  Definition functorlifting_monoidal_laxlaws
             {ms : flmonoidal_data} (ml : flmonoidal_laxlaws ms) :
    fmonoidal_laxlaws (functorlifting_monoidal_data ms)
    := (functorlifting_preserves_tensor_nat_left (flmonoidal_preserves_tensornatleft ml),,
        functorlifting_preserves_tensor_nat_right (flmonoidal_preserves_tensornatright ml),,
        functorlifting_preserves_associativity (flmonoidal_preserves_associativity ml),,
        functorlifting_preserves_leftunitality (flmonoidal_preserves_leftunitality ml),,
        functorlifting_preserves_rightunitality (flmonoidal_preserves_rightunitality ml)
       ).

  Definition functorlifting_fmonoidal_lax (ms : flmonoidal_lax)
    : fmonoidal_lax M' TM (lifted_functor sd)
    := _ ,, functorlifting_monoidal_laxlaws (flmonoidal_lax_to_laxlaws ms).

  (* We now define a strong monoidal fl and show that each such fl induces a strong monoidal functor *)
  (* Definition smonoidal_strongtensor {sd : fl_disp D} (spt : fl_preserves_tensor_data sd) : UU
    := ∏ (x y : C), is_z_iso_disp
                        (Isos.identity_z_iso (x⊗_{M} y))
                        (spt x y).

  Definition smonoidal_strongunit   {sd : fl_disp D} (spu : fl_preserves_unit sd) : UU
    := is_z_iso_disp
                        (Isos.identity_z_iso (I_{M}))
                        spu.

  Definition smonoidal_stronglaws {sd : fl_disp D} (ms : smonoidal_data sd) : UU
    := smonoidal_strongtensor (smonoidal_preserves_tensor ms)
                              × smonoidal_strongunit (smonoidal_preserves_unit ms).

  Definition smonoidal (sd : fl_disp D) : UU
    := ∑ (ms : smonoidal_lax sd), smonoidal_stronglaws ms.

  Definition smonoidal_smonoidallax {sd : fl_disp D} (sm : smonoidal sd)
    : smonoidal_lax sd := pr1 sm.
  Coercion smonoidal_smonoidallax : smonoidal >-> smonoidal_lax.

  Definition smonoidal_smonoidalstronglaws {sd : fl_disp D} (sm : smonoidal sd)
    : smonoidal_stronglaws sm := pr2 sm.
  Definition smonoidal_smonoidalstrongtensor {sd : fl_disp D} (sm : smonoidal sd)
    : smonoidal_strongtensor (smonoidal_preserves_tensor sm) := pr1 (smonoidal_smonoidalstronglaws sm).
  Definition smonoidal_smonoidalstrongunit {sd : fl_disp D} (sm : smonoidal sd)
    : smonoidal_strongunit (smonoidal_preserves_unit sm) := pr2 (smonoidal_smonoidalstronglaws sm).

  Definition flfunctor_preservestensorstrongly {sd : fl_disp D} {ms : smonoidal sd} (pfstrong : smonoidal_strongtensor (smonoidal_preserves_tensor ms))
    : preserves_tensor_strongly (flfunctor_preserves_tensordata (smonoidal_preserves_tensor ms)).
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

  Definition flfunctor_preservesunitstrongly {sd : fl_disp D} {ms : smonoidal sd} (pfstrong : smonoidal_strongunit (smonoidal_preserves_unit ms))
    : preserves_unit_strongly (flfunctor_preserves_unit (smonoidal_preserves_unit ms)).
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

  Definition flmonoidal {sd : fl_disp D} (ms : smonoidal sd)  : fmonoidal M TM (fl_functor sd)
    := (flfunctor_fmonoidal_lax ms ,,
        flfunctor_preservestensorstrongly (smonoidal_smonoidalstrongtensor ms) ,,
        flfunctor_preservesunitstrongly (smonoidal_smonoidalstrongunit ms)). *)

End MonoidalFunctorLifting.
