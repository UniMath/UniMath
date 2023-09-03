Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
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
  Let TD : category := total_category D.
  Context {M' : monoidal C'}
          {M : monoidal C}
          (Fm : fmonoidal_lax M' M F)
          (DM : disp_monoidal D M).
  Let TM : monoidal TD := total_monoidal DM.

  Context (sd : functor_lifting D F).

  Definition fl_preserves_tensor_data : UU
    := ∏ (x y : C'), sd x ⊗⊗_{DM} sd y -->[fmonoidal_preservestensordata Fm x y] sd (x ⊗_{M'} y).

  Lemma functorlifting_preserves_tensordata
        (sd_pt : fl_preserves_tensor_data)
    : preserves_tensordata M' TM (lifted_functor sd).
  Proof.
    intros x y.
    exists (fmonoidal_preservestensordata Fm x y).
    exact (sd_pt x y).
  Defined.

  Definition fl_preserves_unit : UU
    := dI_{DM} -->[fmonoidal_preservesunit Fm] sd I_{M'}.

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
    split.
    - exact (functorlifting_preserves_tensordata (flmonoidal_preserves_tensor_data ms)).
    - exact (functorlifting_preserves_unit (flmonoidal_preserves_unit ms)).
  Defined.

  (* This notation comes from Constructions.v, but there is no Notation module, this has to be added *)
  Notation "# F" := (section_disp_on_morphisms F) (at level 3) : mor_disp_scope.

  Definition fl_preserves_tensor_nat_left
             (spt : fl_preserves_tensor_data) : UU
    := ∏ (x y1 y2 : C') (g : C'⟦y1,y2⟧),
      sd x ⊗⊗^{DM}_{l} # sd g ;; spt x y2
      = transportb _
                   (fmonoidal_preservestensornatleft Fm x y1 y2 g)
                   (spt x y1 ;; # sd (x ⊗^{M'}_{l} g)).

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
      # sd f ⊗⊗^{DM}_{r} sd y ;; spt x2 y
      = transportb _
                   (fmonoidal_preservestensornatright Fm x1 x2 y f)
                   (spt x1 y ;; # sd (f ⊗^{M'}_{r} y)).

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

  Definition fl_preserves_leftunitality
             (spt : fl_preserves_tensor_data)
             (spu : fl_preserves_unit) : UU
    := ∏ (x : C'),
      spu ⊗⊗^{DM}_{r} sd x ;; spt I_{M'} x ;; # sd lu^{M'}_{x}
      = transportb _
                   (fmonoidal_preservesleftunitality Fm x)
                   dlu^{DM}_{sd x}.

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

  Definition fl_preserves_rightunitality
             (spt : fl_preserves_tensor_data)
             (spu : fl_preserves_unit)
    : UU := ∏ (x : C'),
      sd x ⊗⊗^{DM}_{l} spu ;; spt x I_{M'} ;; # sd ru^{M'}_{x}
      = transportb _
                   (fmonoidal_preservesrightunitality Fm x)
                   dru^{DM}_{sd x}.

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

  Definition fl_preserves_associativity
             (spt : fl_preserves_tensor_data ) : UU
    := ∏ (x y z : C'),
      spt x y ⊗⊗^{DM}_{r} sd z ;; spt (x ⊗_{M'} y) z ;; # sd α^{M'}_{x, y, z}
      = transportb _
          (fmonoidal_preservesassociativity Fm x y z)
          (dα^{DM}_{sd x, sd y, sd z} ;; sd x ⊗⊗^{DM}_{l} spt y z ;; spt x (y ⊗_{M'} z)).

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
    := fl_preserves_tensor_nat_left (flmonoidal_preserves_tensor_data ms) ×
       fl_preserves_tensor_nat_right (flmonoidal_preserves_tensor_data ms) ×
       fl_preserves_associativity (flmonoidal_preserves_tensor_data ms) ×
       fl_preserves_leftunitality (flmonoidal_preserves_tensor_data ms) (flmonoidal_preserves_unit ms) ×
       fl_preserves_rightunitality (flmonoidal_preserves_tensor_data ms) (flmonoidal_preserves_unit ms).

  Definition flmonoidal_preserves_tensornatleft
             {ms : flmonoidal_data} (msl : flmonoidal_laxlaws ms)
    : fl_preserves_tensor_nat_left (flmonoidal_preserves_tensor_data ms)
    := pr1 msl.
  Definition flmonoidal_preserves_tensornatright
             {ms : flmonoidal_data} (msl : flmonoidal_laxlaws ms)
    : fl_preserves_tensor_nat_right (flmonoidal_preserves_tensor_data ms)
    := pr12 msl.
  Definition flmonoidal_preserves_associativity
             {ms : flmonoidal_data} (msl : flmonoidal_laxlaws ms)
    : fl_preserves_associativity (flmonoidal_preserves_tensor_data ms)
    := pr122 msl.
  Definition flmonoidal_preserves_leftunitality
             {ms : flmonoidal_data} (msl : flmonoidal_laxlaws ms)
    : fl_preserves_leftunitality (flmonoidal_preserves_tensor_data ms) (flmonoidal_preserves_unit ms)
    := pr122 (pr2 msl).
  Definition flmonoidal_preserves_rightunitality
             {ms : flmonoidal_data} (msl : flmonoidal_laxlaws ms)
    : fl_preserves_rightunitality (flmonoidal_preserves_tensor_data ms) (flmonoidal_preserves_unit ms)
    := pr222 (pr2 msl).

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

  (* We now define functor liftings of strong monoidal functors and show that they induce a strong monoidal functor *)
  Definition fl_strongtensor
             (spt : fl_preserves_tensor_data)
             (Fs : preserves_tensor_strongly (fmonoidal_preservestensordata Fm))
    : UU
    := ∏ (x y : C'), is_z_iso_disp
                        (_ ,, Fs x y)
                        (spt x y).

  Definition fl_strongunit
             (spu : fl_preserves_unit)
             (Fs : preserves_unit_strongly (fmonoidal_preservesunit Fm))
    : UU
    := is_z_iso_disp (_,, Fs) spu.

  Definition fl_stronglaws
             (ms : flmonoidal_lax)
             (Fs : fmonoidal_stronglaws (fmonoidal_preservestensordata Fm)
                                        (fmonoidal_preservesunit Fm))
    : UU
    := fl_strongtensor
         (flmonoidal_preserves_tensor_data ms)
         (fmonoidal_preservestensorstrongly ((Fm,,Fs) : fmonoidal M' M F))
         ×
         fl_strongunit
         (flmonoidal_preserves_unit ms)
         (fmonoidal_preservesunitstrongly ((Fm,,Fs) : fmonoidal M' M F)).

  Definition flmonoidal
             (Fs : fmonoidal_stronglaws (fmonoidal_preservestensordata Fm)
                                        (fmonoidal_preservesunit Fm))
    : UU
    := ∑ ms : flmonoidal_lax, fl_stronglaws ms Fs.

  Definition flmonoidal_to_flmonoidal_lax
             {Fs : fmonoidal_stronglaws (fmonoidal_preservestensordata Fm)
                                        (fmonoidal_preservesunit Fm)}
             (sm : flmonoidal Fs)
    : flmonoidal_lax := pr1 sm.
  Coercion flmonoidal_to_flmonoidal_lax : flmonoidal >-> flmonoidal_lax.

  Definition flmonoidal_to_fl_stronglaws
             {Fs : fmonoidal_stronglaws (fmonoidal_preservestensordata Fm)
                                        (fmonoidal_preservesunit Fm)}
             (sm : flmonoidal Fs)
    : fl_stronglaws sm Fs := pr2 sm.

  Definition flmonoidal_to_flmonoidalstrongtensor
             {Fs : fmonoidal_stronglaws (fmonoidal_preservestensordata Fm)
                                        (fmonoidal_preservesunit Fm)}
             (sm : flmonoidal Fs)
    : fl_strongtensor
         (flmonoidal_preserves_tensor_data sm)
         (fmonoidal_preservestensorstrongly ((Fm,,Fs) : fmonoidal M' M F))
    := pr1 (flmonoidal_to_fl_stronglaws sm).
  Definition flmonoidal_to_flmonoidalstrongunit
             {Fs : fmonoidal_stronglaws (fmonoidal_preservestensordata Fm)
                                        (fmonoidal_preservesunit Fm)}
             (sm : flmonoidal Fs)
    : fl_strongunit
         (flmonoidal_preserves_unit sm)
         (fmonoidal_preservesunitstrongly ((Fm,,Fs) : fmonoidal M' M F))
    := pr2 (flmonoidal_to_fl_stronglaws sm).

  Definition functorlifting_preservestensorstrongly
             {Fs : preserves_tensor_strongly (fmonoidal_preservestensordata Fm)}
             {ms : flmonoidal_lax}
             (pfstrong : fl_strongtensor (flmonoidal_preserves_tensor_data ms) Fs)
    : preserves_tensor_strongly (functorlifting_preserves_tensordata (flmonoidal_preserves_tensor_data ms)).
  Proof.
    intros x y.
    use tpair.
    - exists (pr1 (Fs x y)).
      exact (pr1 (pfstrong x y)).
    - use tpair.
      + use total2_paths_b.
        * exact (pr12 (Fs x y)).
        * exact (pr22 (pfstrong x y)).
      + use total2_paths_b.
        * exact (pr22 (Fs x y)).
        * exact (pr12 (pfstrong x y)).
  Defined.

  Definition functorlifting_preservesunitstrongly
             {Fs : preserves_unit_strongly (fmonoidal_preservesunit Fm)}
             {ms : flmonoidal_lax}
             (pfstrong : fl_strongunit (flmonoidal_preserves_unit ms) Fs)
    : preserves_unit_strongly (functorlifting_preserves_unit (flmonoidal_preserves_unit ms)).
  Proof.
    use tpair.
    - exists (pr1 Fs).
      exact (pr1 pfstrong).
    - use tpair.
      + use total2_paths_b.
        * exact (pr12 Fs).
        * exact (pr22 pfstrong).
      + use total2_paths_b.
        * exact (pr22 Fs).
        * exact (pr12 pfstrong).
  Defined.

  Definition functorlifting_fmonoidal
             {Fs : fmonoidal_stronglaws (fmonoidal_preservestensordata Fm)
                                        (fmonoidal_preservesunit Fm)}
             (fls : flmonoidal Fs)
    : fmonoidal M' TM (lifted_functor sd).
  Proof.
    exists (functorlifting_fmonoidal_lax fls).
    use tpair.
    - use functorlifting_preservestensorstrongly.
      + apply Fs.
      + apply fls.
    - use functorlifting_preservesunitstrongly.
      + apply Fs.
      + apply fls.
  Defined.

  Lemma isaprop_flmonoidal_laxlaws (fl : flmonoidal_data)
    : isaprop (flmonoidal_laxlaws fl).
  Proof.
    repeat (apply isapropdirprod) ; repeat (apply impred_isaprop ; intro) ; apply homsets_disp.
  Qed.

  Lemma isaprop_flmonoidal_stronglaws
        {Fm_strong : fmonoidal_stronglaws (pr11 Fm) (pr21 Fm)}
        (fl : flmonoidal Fm_strong)
    : isaprop (fl_stronglaws (pr1 fl) Fm_strong).
  Proof.
    apply isapropdirprod ; repeat (apply impred_isaprop ; intro) ; apply Isos.isaprop_is_z_iso_disp.
  Qed.

  Lemma flmonoidal_equality (fl1 fl2 : flmonoidal_lax)
    : (∏ x y : C', pr11 fl1 x y = pr11 fl2 x y) -> (pr21 fl1 = pr21 fl2) -> fl1 = fl2.
  Proof.
    intros pT pU.
    use total2_paths_f.
    2: apply isaprop_flmonoidal_laxlaws.
    use total2_paths_f.
    - do 2 (apply funextsec ; intro).
      apply pT.
    - cbn.
      rewrite transportf_const.
      exact pU.
  Qed.

  Lemma flmonoidal_strong_equality
        {Fm_strong : fmonoidal_stronglaws (pr11 Fm) (pr21 Fm)}
        (fl1 fl2 : flmonoidal Fm_strong)
    : (∏ x y : C', pr111 fl1 x y = pr111 fl2 x y) -> (pr211 fl1 = pr211 fl2) -> fl1 = fl2.
  Proof.
    intros pT pU.
    use total2_paths_f.
    - use flmonoidal_equality.
      + exact pT.
      + exact pU.
    - apply isaprop_flmonoidal_stronglaws.
  Qed.

End MonoidalFunctorLifting.
