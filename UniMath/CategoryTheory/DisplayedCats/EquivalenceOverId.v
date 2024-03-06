(*********************************************************************************

 Properties over equivalences over the identity

 In this file, we collect various properties of equivalences over the identity.

 Contents
 1. If a displayed functor is eso and ff, then its object map is an equivalence
 2. Essentially surjective functors are split essentially surjective
 3. Being an equivalence is a proposition
 4. Equivalences are (split) essentially surjective
 5. Equivalences are fully faithful
 6. Equivalences are cartesian
 7. Equivalences are opcartesian
 8. Equivalences over the identity and equivalences

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedFunctorEq.

Local Open Scope cat.
Local Open Scope mor_disp.

(**
 1. If a displayed functor is eso and ff, then its object map is an equivalence
 *)
Proposition isaprop_hfiber_ff_disp
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            (HD₁ : is_univalent_disp D₁)
            (HD₂ : is_univalent_disp D₂)
            {FF : disp_functor F D₁ D₂}
            (HFF : disp_functor_ff FF)
            (x : C₁)
            (yy : D₂(F x))
  : isaprop (hfiber (FF x) yy).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  induction φ₁ as [ ww₁ ι₁ ].
  induction φ₂ as [ ww₂ ι₂ ].
  enough (∑ (p : ww₁ = ww₂), maponpaths (FF x) p = ι₁ @ !ι₂) as p.
  {
    use total2_paths_f.
    - exact (pr1 p).
    - rewrite transportf_paths_FlFr.
      cbn.
      rewrite maponpaths_for_constant_function.
      rewrite pathscomp0rid.
      rewrite (pr2 p).
      rewrite pathscomp_inv.
      rewrite pathsinv0inv0.
      rewrite <- path_assoc.
      rewrite pathsinv0l.
      rewrite pathscomp0rid.
      apply idpath.
  }
  enough (∑ (p : z_iso_disp (identity_z_iso _) ww₁ ww₂),
          ♯FF p
          =
          transportb
            (λ z, _ -->[ z ] _)
            (functor_id F _)
            (pr1 (idtoiso_disp (idpath _) (ι₁ @ !ι₂)))) as p.
  {
    refine (isotoid_disp HD₁ (idpath _) (pr1 p) ,, _).
    use (invmaponpathsincl _ (isinclweq _ _ _ (HD₂ _ _ (idpath _) _ _))).
    cbn -[idtoiso_disp].
    use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ].
    refine (pr1_idtoiso_disp_functor _ _ @ _).
    rewrite idtoiso_isotoid_disp.
    use transportf_transpose_left.
    exact (pr2 p).
  }
  pose (disp_functor_ff_inv
          _
          HFF
          (transportb
             (λ z, _ -->[ z ] _)
             (functor_id F _)
             (pr1 (idtoiso_disp (idpath _) (ι₁ @ !ι₂)))))
    as ff.
  simple refine ((ff ,, _) ,, _).
  - apply FFinv_on_z_iso_is_z_iso.
    use is_z_iso_disp_transportb_fun_eq.
    apply idtoiso_disp.
  - apply FF_disp_functor_ff_inv.
Qed.

Proposition disp_ess_surj_ob_weq
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            (HD₁ : is_univalent_disp D₁)
            (HD₂ : is_univalent_disp D₂)
            {FF : disp_functor F D₁ D₂}
            (HFF₁ : disp_functor_disp_ess_surj FF)
            (HFF₂ : disp_functor_ff FF)
            (x : C₁)
  : isweq (FF x).
Proof.
  intros yy.
  use (factor_through_squash _ _ (HFF₁ x yy)).
  {
    apply isapropiscontr.
  }
  intros xx.
  induction xx as [ xx i ].
  use iscontraprop1.
  - exact (isaprop_hfiber_ff_disp HD₁ HD₂ HFF₂ x yy).
  - refine (xx ,, _).
    exact (isotoid_disp HD₂ (idpath _) i).
Qed.

(**
 2. Essentially surjective functors are split essentially surjective
 *)
Proposition disp_functor_disp_ess_surj_to_split
            {C : category}
            {D₁ D₂ : disp_cat C}
            (HD₁ : is_univalent_disp D₁)
            (HD₂ : is_univalent_disp D₂)
            {F : disp_functor (functor_identity C) D₁ D₂}
            (H₁ : disp_functor_disp_ess_surj F)
            (H₂ : disp_functor_ff F)
  : disp_functor_disp_ess_split_surj F.
Proof.
  intros x yy.
  refine (factor_through_squash _ (λ z, z) (H₁ x yy)).
  refine (isofhlevelweqf _ _ (isaprop_hfiber_ff_disp HD₁ HD₂ H₂ x yy)).
  use weqfibtototal.
  intro xx ; cbn.
  exact (make_weq _ (HD₂ x x (idpath _) _ _)).
Defined.

(**
 3. Being an equivalence is a proposition
 *)
Definition path_right_adjoint_over_id_data_help
           {C : category}
           {D₁ D₂ : disp_cat C}
           {F : disp_functor (functor_identity C) D₁ D₂}
           {HF₁ HF₂ : right_adjoint_over_id_data F}
           (p₁ : pr1 HF₁ = pr1 HF₂)
           (p₂ : ∏ (x : C) (xx : D₁ x),
                 pr12 HF₁ x xx
                 ;;
                 idtoiso_disp (idpath _) (maponpaths (λ z, pr11 z x (F x xx)) p₁)
                 =
                 transportf
                   (λ z, _ -->[ z ] _)
                   (!(id_right _))
                   (pr12 HF₂ x xx))
           (p₃ : ∏ (x : C) (xx : D₂ x),
                 pr22 HF₁ x xx
                 =
                 transportf
                   (λ z, _ -->[ z ] _)
                   (id_left _)
                   (♯F (idtoiso_disp (idpath _) (maponpaths (λ z, pr11 z x xx) p₁))
                    ;;
                    pr22 HF₂ x xx))
  : HF₁ = HF₂.
Proof.
  induction HF₁ as [ R₁ [ η₁ ε₁ ]].
  induction HF₂ as [ R₂ [ η₂ ε₂ ]].
  cbn in p₁.
  induction p₁.
  apply maponpaths.
  apply pathsdirprod.
  - use disp_nat_trans_eq.
    intros x xx.
    pose (q := p₂ x xx).
    cbn in q.
    rewrite id_right_disp in q.
    unfold transportb in q.
    refine (_ @ maponpaths (transportb _ _) q @ _).
    + rewrite transportbfinv.
      apply idpath.
    + rewrite transportbfinv.
      apply idpath.
  - use disp_nat_trans_eq.
    intros x xx.
    refine (p₃ x xx @ _) ; cbn.
    rewrite (disp_functor_id F).
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite id_left_disp.
    unfold transportb.
    rewrite transport_f_f.
    apply transportf_set.
    apply homset_property.
Qed.

Definition path_right_adjoint_over_id_data
           {C : category}
           {D₁ D₂ : disp_cat C}
           (HD₁ : is_univalent_disp D₁)
           (HD₂ : is_univalent_disp D₂)
           {F : disp_functor (functor_identity C) D₁ D₂}
           {HF₁ HF₂ : right_adjoint_over_id_data F}
           (p₁ : disp_nat_z_iso
                   (pr1 HF₁)
                   (pr1 HF₂)
                   (nat_z_iso_id (functor_identity C)))
           (p₂ : ∏ (x : C) (xx : D₁ x),
                 (pr12 HF₁) x xx ;; p₁ x (F x xx)
                 =
                 transportf
                   (λ z, _ -->[ z ] _)
                   (!(id_right _))
                   ((pr12 HF₂) x xx))
           (p₃ : ∏ (x : C) (xx : D₂ x),
                 pr22 HF₁ x xx
                 =
                 transportf
                   (λ z, _ -->[ z ] _)
                   (id_left _)
                   (♯F (p₁ x xx) ;; pr22 HF₂ x xx))
  : HF₁ = HF₂.
Proof.
  use path_right_adjoint_over_id_data_help.
  - exact (invmap (disp_functor_eq_weq _ _ HD₁) p₁).
  - intros x xx.
    refine (_ @ p₂ x xx).
    apply maponpaths.
    refine (_ @ maponpaths
                  (λ z, (pr11 z) x (F x xx))
                  (homotweqinvweq (disp_functor_eq_weq (pr1 HF₁) (pr1 HF₂) HD₁) p₁)).
    generalize (invmap (disp_functor_eq_weq (pr1 HF₁) (pr1 HF₂) HD₁) p₁).
    intro p.
    induction p ; cbn.
    apply idpath.
  - intros x xx.
    refine (p₃ x xx @ _).
    apply maponpaths.
    apply maponpaths_2.
    apply maponpaths.
    refine (!_).
    refine (_ @ maponpaths
                  (λ z, (pr11 z) x xx)
                  (homotweqinvweq (disp_functor_eq_weq (pr1 HF₁) (pr1 HF₂) HD₁) p₁)).
    generalize (invmap (disp_functor_eq_weq (pr1 HF₁) (pr1 HF₂) HD₁) p₁).
    intro p.
    induction p ; cbn.
    apply idpath.
Qed.

Section IsEquivOverIdIsProp.
  Context {C : category}
          {D₁ D₂ : disp_cat C}
          (HD₁ : is_univalent_disp D₁)
          (HD₂ : is_univalent_disp D₂)
          (F : disp_functor (functor_identity C) D₁ D₂).

  Section Defs.
    Context (HF₁ HF₂ : is_equiv_over_id F).

    Let R₁ : disp_functor (functor_identity C) D₂ D₁ := HF₁.
    Let η₁ : disp_nat_trans
              (nat_trans_id _)
              (disp_functor_identity _)
              (disp_functor_composite F R₁)
      := unit_over_id HF₁.
    Let ε₁ : disp_nat_trans
               (nat_trans_id _)
               (disp_functor_composite R₁ F)
               (disp_functor_identity _)
      := counit_over_id HF₁.

    Let R₂ : disp_functor (functor_identity C) D₂ D₁ := HF₂.
    Let η₂ : disp_nat_trans
              (nat_trans_id _)
              (disp_functor_identity _)
              (disp_functor_composite F R₂)
      := unit_over_id HF₂.
    Let ε₂ : disp_nat_trans
              (nat_trans_id _)
              (disp_functor_composite R₂ F)
              (disp_functor_identity _)
      := counit_over_id HF₂.

    Definition isaprop_is_equiv_over_id_nat_trans
      : disp_nat_trans (nat_z_iso_id (functor_identity C)) R₁ R₂
      := disp_nat_trans_over_id_comp
           (disp_nat_trans_over_id_prewhisker R₁ η₂)
           (disp_nat_trans_over_id_postwhisker R₂ ε₁).

    Proposition isaprop_is_equiv_over_id_is_nat_z_iso
      : is_disp_nat_z_iso
          (nat_z_iso_id (functor_identity C))
          isaprop_is_equiv_over_id_nat_trans.
    Proof.
      intros x xx ; cbn.
      pose (η₂ x (R₁ x xx) ;; ♯ R₂ (ε₁ x xx)).
      cbn in m.
      use (@is_z_iso_disp_transportf_fun_eq
             C D₁
             x x
             (z_iso_comp (identity_z_iso x) (identity_z_iso x))).
      use (z_iso_disp_comp (_ ,, _) (_ ,, _)).
      - apply HF₂.
      - exact (is_z_iso_disp_independent_of_is_z_iso
                 _ _
                 (pr2 (disp_functor_on_z_iso_disp
                         R₂
                         (make_z_iso_disp _ (is_z_iso_counit_over_id HF₁ x xx))))).
    Defined.

    Definition isaprop_is_equiv_over_id_nat_z_iso
      : disp_nat_z_iso R₁ R₂ (nat_z_iso_id (functor_identity C))
      := isaprop_is_equiv_over_id_nat_trans
         ,,
         isaprop_is_equiv_over_id_is_nat_z_iso.

    Proposition isaprop_is_equiv_over_id_eq_1
                (x : C)
                (xx : D₁ x)
      : η₁ x xx ;; isaprop_is_equiv_over_id_nat_z_iso x (F x xx)
        =
        transportf
          (λ z, _ -->[ z ] _)
          (!(id_right _))
          (η₂ x xx).
    Proof.
      cbn.
      rewrite mor_disp_transportf_prewhisker.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (disp_nat_trans_ax η₂).
      }
      unfold transportb.
      cbn.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply (disp_functor_comp_var R₂).
      }
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        exact (triangle_1_over_id HF₁ x xx).
      }
      unfold transportb.
      rewrite disp_functor_transportf.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    Qed.

    Proposition isaprop_is_equiv_over_id_eq_2
                (x : C)
                (xx : D₂ x)
      : ε₁ x xx
        =
        transportf
          (λ z, _ -->[ z ] _)
          (id_left _)
          (♯F (isaprop_is_equiv_over_id_nat_z_iso x xx) ;; ε₂ x xx).
    Proof.
      cbn.
      rewrite (disp_functor_transportf _ F).
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite disp_functor_comp.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply (disp_nat_trans_ax ε₂).
      }
      unfold transportb.
      cbn.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact (triangle_1_over_id HF₂ x (R₁ x xx)).
      }
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
    Qed.
  End Defs.

  Proposition isaprop_is_equiv_over_id
    : isaprop (is_equiv_over_id F).
  Proof.
    use invproofirrelevance.
    intros HF₁ HF₂.
    use subtypePath.
    {
      intro.
      apply isaprop_form_equiv_over_id.
    }
    use subtypePath.
    {
      intro.
      apply isaprop_form_disp_adjunction_id.
    }
    use (path_right_adjoint_over_id_data HD₁ HD₂).
    - exact (isaprop_is_equiv_over_id_nat_z_iso HF₁ HF₂).
    - exact (isaprop_is_equiv_over_id_eq_1 HF₁ HF₂).
    - exact (isaprop_is_equiv_over_id_eq_2 HF₁ HF₂).
  Qed.
End IsEquivOverIdIsProp.

Section PropertiesOfEquivOverId.
  Context {C : category}
          {D₁ : disp_cat C}
          {D₂ : disp_cat C}
          (LL : disp_functor (functor_identity _) D₁ D₂)
          (HLL : is_equiv_over_id LL).

  Let RR : disp_functor (functor_identity _) D₂ D₁ := HLL.
  Let η : disp_nat_trans
            (nat_trans_id _)
            (disp_functor_identity _)
            (disp_functor_composite LL RR)
    := unit_over_id HLL.
  Let ε : disp_nat_trans
            (nat_trans_id _)
            (disp_functor_composite RR LL)
            (disp_functor_identity _)
    := counit_over_id HLL.

  (**
   4. Equivalences are (split) essentially surjective
   *)
  Proposition is_equiv_over_id_to_split_ess_surj
    : disp_functor_disp_ess_split_surj LL.
  Proof.
    intros x yy.
    refine (RR x yy ,, ε x yy ,, _).
    exact (is_z_iso_counit_over_id HLL x yy).
  Defined.

  Proposition is_equiv_over_id_to_ess_surj
    : disp_functor_disp_ess_surj LL.
  Proof.
    intros x yy.
    apply hinhpr.
    apply is_equiv_over_id_to_split_ess_surj.
  Qed.

  (**
   5. Equivalences are fully faithful
   *)
  Proposition is_equiv_over_id_to_ff
    : disp_functor_ff LL.
  Proof.
    intros x y xx yy f.
    use isweq_iso.
    - cbn ; intro ff.
      refine (transportf
                (λ z, _ -->[ z ] _)
                _
                (η x xx
                 ;; ♯ RR ff
                 ;; inv_mor_disp_from_z_iso (is_z_iso_unit_over_id HLL y yy))).
      abstract
        (cbn ;
         rewrite id_left, id_right ;
         apply idpath).
    - abstract
        (intro ff ; cbn ;
         etrans ;
         [ apply maponpaths ;
           apply maponpaths_2 ;
           exact (disp_nat_trans_ax_var η ff)
         | ] ;
         cbn ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite transport_f_f ;
         rewrite assoc_disp_var ;
         rewrite transport_f_f ;
         etrans ;
         [ do 2 apply maponpaths ;
           exact (inv_mor_after_z_iso_disp (is_z_iso_unit_over_id (pr2 HLL) y yy))
         | ] ;
         cbn ;
         unfold transportb ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite transport_f_f ;
         rewrite id_right_disp ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply homset_property).
    - abstract
        (cbn ; intro ff ;
         rewrite (disp_functor_transportf _ LL) ;
         rewrite disp_functor_comp ;
         unfold transportb ;
         rewrite transport_f_f ;
         rewrite disp_functor_comp ;
         unfold transportb ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite transport_f_f ;
         etrans ;
           [ do 2 apply maponpaths ;
             apply triangle_1_over_id_alt
           | ] ;
         rewrite assoc_disp_var ;
         rewrite transport_f_f ;
         etrans ;
           [ do 2 apply maponpaths ;
             apply (disp_nat_trans_ax (counit_over_id HLL))
           | ] ;
         unfold transportb ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite transport_f_f ;
         cbn ;
         rewrite assoc_disp ;
         unfold transportb ;
         rewrite transport_f_f ;
         etrans ;
           [ apply maponpaths ;
             apply maponpaths_2 ;
             exact (triangle_1_over_id HLL x xx)
           | ] ;
         unfold transportb ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite transport_f_f ;
         rewrite id_left_disp ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply homset_property) ;
        rewrite triangle_1_over_id_alt.
  Qed.
End PropertiesOfEquivOverId.

(**
 6. Equivalences are cartesian
 *)
Section EquivIsCartesian.
  Context {C : category}
          {D₁ D₂ : disp_cat C}
          {L : disp_functor (functor_identity C) D₁ D₂}
          (HL : is_equiv_over_id L).

  Let R : disp_functor (functor_identity C) D₂ D₁ := HL.
  Let η : disp_nat_trans
            (nat_trans_id _)
            (disp_functor_identity _)
            (disp_functor_composite L R)
    := unit_over_id HL.
  Let ε : disp_nat_trans
            (nat_trans_id _)
            (disp_functor_composite R L)
            (disp_functor_identity _)
    := counit_over_id HL.

  Section Cartesian.
    Context {x y : C}
            {f : y --> x}
            {xx : D₁ x}
            {yy : D₁ y}
            {ff : yy -->[ f ] xx}
            (Hff : is_cartesian ff)
            {w : C}
            {g : w --> y}
            (ww : D₂ w)
            (hh : ww -->[ g · f ] L x xx).

    Proposition is_cartesian_equiv_over_id_unique
      : isaprop (∑ (gg : ww -->[ g ] L y yy), gg ;; ♯ L ff = hh).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply D₂.
      }
      use (invmaponpathsweq
             (make_weq
                _
                (is_equiv_over_id_to_ff _ (equiv_inv _ HL) _ _ _ _ _))).
      cbn.
      refine (id_right_disp_var _ @ _ @ !(id_right_disp_var _)).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!(transportf_transpose_left
                   (z_iso_disp_after_inv_mor (is_z_iso_unit_over_id HL y yy)))).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (!(transportf_transpose_left
                   (z_iso_disp_after_inv_mor (is_z_iso_unit_over_id HL y yy)))).
      }
      refine (!_).
      rewrite !mor_disp_transportf_prewhisker.
      apply maponpaths.
      rewrite !assoc_disp.
      apply maponpaths.
      apply maponpaths_2.
      use (cartesian_factorisation_unique Hff).
      rewrite !assoc_disp_var.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply (disp_nat_trans_ax_var
                 (disp_nat_z_iso_to_trans_inv
                    (α := nat_z_iso_id _)
                    (η ,, is_z_iso_unit_over_id HL))).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply (disp_nat_trans_ax_var
                 (disp_nat_z_iso_to_trans_inv
                    (α := nat_z_iso_id _)
                    (η ,, is_z_iso_unit_over_id HL))).
      }
      cbn.
      rewrite !mor_disp_transportf_prewhisker.
      apply maponpaths.
      rewrite !assoc_disp.
      apply maponpaths.
      apply maponpaths_2.
      refine (!(disp_functor_comp_var R _ _) @ _ @ disp_functor_comp_var R _ _).
      do 2 apply maponpaths.
      exact (pr2 φ₂ @ !(pr2 φ₁)).
    Qed.

    Definition is_cartesian_equiv_over_id_fact
      : ww -->[ g ] L y yy.
    Proof.
      pose (cartesian_factorisation
                Hff
                _
                (transportf
                   (λ z, _ -->[ z ] _)
                   (id_right _)
                   (♯R hh
                    ;;
                    inv_mor_disp_from_z_iso (is_z_iso_unit_over_id HL x xx))))
        as m.
      exact (transportf
               (λ z, _ -->[ z ] _)
               (id_left _)
               (inv_mor_disp_from_z_iso (is_z_iso_counit_over_id HL w ww)
                ;;
                ♯L m)).
    Defined.

    Proposition is_cartesian_equiv_over_id_comm
      : is_cartesian_equiv_over_id_fact ;; ♯ L ff = hh.
    Proof.
      unfold is_cartesian_equiv_over_id_fact ; cbn.
      rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply (disp_functor_comp_var L).
      }
      rewrite cartesian_factorisation_commutes.
      rewrite disp_functor_transportf.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite disp_functor_comp.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply triangle_1_over_id_alt.
        }
        apply (disp_nat_trans_ax ε).
      }
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (z_iso_disp_after_inv_mor (is_z_iso_counit_over_id (pr2 HL) w ww)).
      }
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      cbn.
      apply transportf_set.
      apply homset_property.
    Qed.
  End Cartesian.

  Proposition is_cartesian_equiv_over_id
    : is_cartesian_disp_functor L.
  Proof.
    intros x y f xx yy ff Hff w g ww hh.
    use iscontraprop1.
    - exact (is_cartesian_equiv_over_id_unique Hff ww hh).
    - simple refine (_ ,, _).
      + exact (is_cartesian_equiv_over_id_fact Hff ww hh).
      + exact (is_cartesian_equiv_over_id_comm Hff ww hh).
  Defined.
End EquivIsCartesian.

(**
 7. Equivalences are opcartesian
 *)
Section EquivIsOpcartesian.
  Context {C : category}
          {D₁ D₂ : disp_cat C}
          {L : disp_functor (functor_identity C) D₁ D₂}
          (HL : is_equiv_over_id L).

  Let R : disp_functor (functor_identity C) D₂ D₁ := HL.
  Let η : disp_nat_trans
            (nat_trans_id _)
            (disp_functor_identity _)
            (disp_functor_composite L R)
    := unit_over_id HL.
  Let ε : disp_nat_trans
            (nat_trans_id _)
            (disp_functor_composite R L)
            (disp_functor_identity _)
    := counit_over_id HL.

  Section Opcartesian.
    Context {x y : C}
            {f : y --> x}
            {xx : D₁ x}
            {yy : D₁ y}
            {ff : yy -->[ f ] xx}
            (Hff : is_opcartesian ff)
            {w : C}
            {g : x --> w}
            (ww : D₂ w)
            (hh : L y yy -->[ f · g ] ww).

    Proposition is_opcartesian_equiv_over_id_unique
      : isaprop (∑ (gg : L x xx -->[ g ] ww), ♯L ff ;; gg = hh).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply D₂.
      }
      use (invmaponpathsweq
             (make_weq
                _
                (is_equiv_over_id_to_ff _ (equiv_inv _ HL) _ _ _ _ _))).
      cbn.
      refine (id_left_disp_var _ @ _ @ !(id_left_disp_var _)).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        exact (!(transportf_transpose_left
                   (z_iso_disp_after_inv_mor (is_z_iso_unit_over_id HL _ _)))).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (!(transportf_transpose_left
                   (z_iso_disp_after_inv_mor (is_z_iso_unit_over_id HL _ _)))).
      }
      refine (!_).
      rewrite !mor_disp_transportf_postwhisker.
      apply maponpaths.
      rewrite !assoc_disp_var.
      do 2 apply maponpaths.
      use (opcartesian_factorisation_unique Hff).
      rewrite !assoc_disp.
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        exact (disp_nat_trans_ax η ff).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (disp_nat_trans_ax η ff).
      }
      cbn.
      unfold transportb.
      rewrite !mor_disp_transportf_postwhisker.
      apply maponpaths.
      rewrite !assoc_disp_var.
      do 2 apply maponpaths.
      refine (!(disp_functor_comp_var R _ _) @ _ @ disp_functor_comp_var R _ _).
      do 2 apply maponpaths.
      exact (pr2 φ₂ @ !(pr2 φ₁)).
    Qed.

    Definition is_opcartesian_equiv_over_id_fact
      : L x xx -->[ g ] ww.
    Proof.
      pose (opcartesian_factorisation
              Hff
              _
              (transportf
                 (λ z, _ -->[ z ] _)
                 (id_left _)
                 (η y yy
                  ;;
                  ♯R hh)))
        as m.
      exact (transportf
               (λ z, _ -->[ z ] _)
               (id_right _)
               (♯L m ;; ε w ww)).
    Defined.

    Proposition is_opcartesian_equiv_over_id_comm
      : ♯ L ff ;; is_opcartesian_equiv_over_id_fact = hh.
    Proof.
      unfold is_opcartesian_equiv_over_id_fact ; cbn.
      rewrite mor_disp_transportf_prewhisker.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        refine (!_).
        apply (disp_functor_comp_var L).
      }
      rewrite opcartesian_factorisation_commutes.
      rewrite disp_functor_transportf.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite disp_functor_comp.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        apply (disp_nat_trans_ax ε).
      }
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (triangle_1_over_id HL).
      }
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      cbn.
      apply transportf_set.
      apply homset_property.
    Qed.
  End Opcartesian.

  Proposition is_opcartesian_equiv_over_id
    : is_opcartesian_disp_functor L.
  Proof.
    intros x y f xx yy ff Hff w ww g hh.
    use iscontraprop1.
    - exact (is_opcartesian_equiv_over_id_unique Hff ww hh).
    - simple refine (_ ,, _).
      + exact (is_opcartesian_equiv_over_id_fact Hff ww hh).
      + exact (is_opcartesian_equiv_over_id_comm Hff ww hh).
  Defined.
End EquivIsOpcartesian.

(** * 8. Equivalences over the identity and equivalences *)
Section EquivalencesOverId.
  Context {C : category}
          {D₁ D₂ : disp_cat C}.

  Let F : adj_equiv C C
    := _ ,, identity_functor_is_adj_equivalence.

  Section ToEquiv.
    Context (L : disp_functor (functor_identity C) D₁ D₂)
            (FF : is_equiv_over_id L).

    Let R : disp_functor (functor_identity C) D₂ D₁ := pr1 FF.
    Let η : disp_nat_trans
              (adjunit F)
              (disp_functor_identity D₁)
              (disp_functor_composite L R)
      := pr1 (pr211 FF).
    Let ε : disp_nat_trans
              (adjcounit F)
              (disp_functor_composite R L)
              (disp_functor_identity D₂)
      := pr2 (pr211 FF).

    Definition is_equiv_over_id_to_is_equiv_over
      : is_equiv_over F L.
    Proof.
      simple refine (((R ,, (η ,, ε)) ,, _ ,, _) ,, _ ,, _).
      - abstract
          (intros x xx ; cbn ;
           refine (pr121 FF x xx @ _) ;
           apply maponpaths_2 ;
           apply homset_property).
      - abstract
          (intros x xx ; cbn ;
           refine (pr221 FF x xx @ _) ;
           apply maponpaths_2 ;
           apply homset_property).
      - intros x xx.
        apply FF.
      - intros x xx.
        apply FF.
    Defined.
  End ToEquiv.

  Section ToEquivId.
    Context (L : disp_functor (functor_identity C) D₁ D₂)
            (FF : is_equiv_over F L).

    Let R : disp_functor (functor_identity C) D₂ D₁ := pr1 FF.
    Let η : disp_nat_trans
              (adjunit F)
              (disp_functor_identity D₁)
              (disp_functor_composite L R)
      := pr1 (pr211 FF).
    Let ε : disp_nat_trans
              (adjcounit F)
              (disp_functor_composite R L)
              (disp_functor_identity D₂)
      := pr2 (pr211 FF).

    Definition is_equiv_over_to_is_equiv_over_id
      : is_equiv_over_id L.
    Proof.
      simple refine (((R ,, (η ,, ε)) ,, _ ,, _) ,, _ ,, _).
      - abstract
          (intros x xx ; cbn ;
           refine (pr121 FF x xx @ _) ;
           apply maponpaths_2 ;
           apply homset_property).
      - abstract
          (intros x xx ; cbn ;
           refine (pr221 FF x xx @ _) ;
           apply maponpaths_2 ;
           apply homset_property).
      - intros x xx.
        apply FF.
      - intros x xx.
        apply FF.
    Defined.
  End ToEquivId.
End EquivalencesOverId.
