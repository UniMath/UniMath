(*********************************************************************************

 Equality of displayed functors

 We are interested in the following bicategories:
 - The bicategory of displayed categories
 - The bicategory of fibrations over a fixed category
 - The bicategory of fibrations
 For each of these bicategories, we want to prove that it is univalent. That
 requires two things:
 - Proving that the identity of displayed functors is equivalent to the type of
   displayed natural isomorphisms between them
 - Proving that the identity of displayed categories is equivalent to the type of
   displayed adjoint equivalences between them.

 In this file, we look at the second of these two statements. The main idea of the
 proof is to characterize the identity relation for displayed categories step by
 step.

 In addition, there is one important trick in this proof: we characterize the
 identity relation for displayed categories lying over a fixed category `C` instead
 of displayed categories who lie over categories that are equal. This simplifies the
 construction, while no generality is lost.

 Contents
 1. Lemmas about equality of displayed functors
 2. Equality of displayed functors is the same as natural isomorphisms

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
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedFunctorEq.
Require Import UniMath.CategoryTheory.DisplayedCats.EquivalenceOverId.

Local Open Scope cat.
Local Open Scope mor_disp.

Section DisplayedCatEq.
  Context {C : category}
          (D₁ : disp_cat C)
          (D₂ : disp_cat C).

  (**
   1. Lemmas about equality of displayed categories
   *)
  Definition disp_cat_eq_step_1
    : D₁ = D₂ ≃ pr1 D₁ = pr1 D₂.
  Proof.
    use path_sigma_hprop.
    apply isaprop_disp_cat_axioms.
  Defined.

  Definition disp_cat_eq_step_2
    : pr1 D₁ = pr1 D₂ ≃ pr1 D₁ ╝ pr1 D₂.
  Proof.
    exact (total2_paths_equiv _ (pr1 D₁) (pr1 D₂)).
  Defined.

  Definition disp_cat_eq_step_3
    : pr1 D₁ ╝ pr1 D₂
      ≃
      ∑ (p : pr11 D₁ ╝ pr11 D₂),
      transportf (disp_cat_id_comp C) (total2_paths_f (pr1 p) (pr2 p)) (pr21 D₁) = pr21 D₂.
  Proof.
    exact (invweq
             (weqfp
                (invweq (total2_paths_equiv _ (pr11 D₁) (pr11 D₂)))
                (λ p,
                  transportf _ p (pr21 D₁) = pr21 D₂))).
  Defined.

  Definition disp_cat_eq_step_4_help
    : pr11 D₁ ╝ pr11 D₂
      ≃
      ∑ (pob : ∏ (x : C), D₁ x = D₂ x),
      ∏ (x y : C)
        (xx : D₁ x)
        (yy : D₁ y)
        (f : x --> y),
      xx -->[ f ] yy
      =
      eqweqmap (pob x) xx -->[ f ] eqweqmap (pob y) yy.
  Proof.
    use weqbandf.
    - exact (weqtoforallpaths _ _ _).
    - intro p.
      induction D₁ as [ [ [ D₁o D₁m ] [ D₁i D₁c ] ] D₁a ].
      induction D₂ as [ [ [ D₂o D₂m ] [ D₂i D₂c ] ] D₂a ].
      cbn in p.
      induction p.
      cbn.
      refine (weqonsecfibers _ _ (λ x, _) ∘ weqtoforallpaths _ _ _)%weq.
      refine (weqonsecfibers _ _ (λ y, _) ∘ weqtoforallpaths _ _ _)%weq.
      refine (weqonsecfibers _ _ (λ xx, _) ∘ weqtoforallpaths _ _ _)%weq.
      refine (weqonsecfibers _ _ (λ yy, _) ∘ weqtoforallpaths _ _ _)%weq.
      exact (weqtoforallpaths _ _ _)%weq.
  Defined.

  Definition disp_cat_id_comp_eq
             (pob : ∏ (x : C), D₁ x = D₂ x)
             (pmor : ∏ (x y : C)
                       (xx : D₁ x)
                       (yy : D₁ y)
                       (f : x --> y),
                     xx -->[ f ] yy
                     =
                     eqweqmap (pob x) xx -->[ f ] eqweqmap (pob y) yy)
    : UU
    := (∏ (x : C)
         (xx : D₁ x),
       eqweqmap
         (pmor x x xx xx (identity x))
         (id_disp xx)
       =
       id_disp (eqweqmap (pob x) xx))
      ×
      (∏ (x y z : C)
         (f : x --> y)
         (g : y --> z)
         (xx : D₁ x)
         (yy : D₁ y)
         (zz : D₁ z)
         (ff : xx -->[ f ] yy)
         (gg : yy -->[ g ] zz),
       eqweqmap
          (pmor _ _ _ _ _)
         (ff ;; gg)
       =
       eqweqmap (pmor _ _ _ _ f) ff ;; eqweqmap (pmor _ _ _ _ g) gg).

  Definition disp_cat_eq_step_4
    : (∑ (p : pr11 D₁ ╝ pr11 D₂),
       transportf
         (disp_cat_id_comp C)
         (total2_paths_f (pr1 p) (pr2 p))
         (pr21 D₁)
       =
       pr21 D₂)
      ≃
      ∑ (pob : ∏ (x : C), D₁ x = D₂ x),
      ∑ (pmor : ∏ (x y : C)
                  (xx : D₁ x)
                  (yy : D₁ y)
                  (f : x --> y),
                xx -->[ f ] yy
                =
                eqweqmap (pob x) xx -->[ f ] eqweqmap (pob y) yy),
      disp_cat_id_comp_eq pob pmor.
  Proof.
    refine (invweq (totalAssociativity _) ∘ _)%weq.
    use weqbandf.
    - exact disp_cat_eq_step_4_help.
    - intro p.
      unfold disp_cat_id_comp_eq ; cbn.
      induction D₁ as [ [ [ D₁o D₁m ] [ D₁i D₁c ] ] D₁a ].
      induction D₂ as [ [ [ D₂o D₂m ] [ D₂i D₂c ] ] D₂a ].
      cbn in p.
      induction p as [ p₁ p₂ ].
      cbn in p₁.
      induction p₁.
      cbn in p₂.
      induction p₂.
      cbn.
      refine (_ ∘ pathsdirprodweq)%weq.
      use weqdirprodf.
      + refine (weqonsecfibers _ _ (λ x, _) ∘ weqtoforallpaths _ _ _)%weq.
        exact (weqtoforallpaths _ _ _).
      + refine (weqonsecfibers _ _ (λ x, _) ∘ weqtoforallpaths _ _ _)%weq.
        refine (weqonsecfibers _ _ (λ y, _) ∘ weqtoforallpaths _ _ _)%weq.
        refine (weqonsecfibers _ _ (λ z, _) ∘ weqtoforallpaths _ _ _)%weq.
        refine (weqonsecfibers _ _ (λ f, _) ∘ weqtoforallpaths _ _ _)%weq.
        refine (weqonsecfibers _ _ (λ g, _) ∘ weqtoforallpaths _ _ _)%weq.
        refine (weqonsecfibers _ _ (λ xx, _) ∘ weqtoforallpaths _ _ _)%weq.
        refine (weqonsecfibers _ _ (λ yy, _) ∘ weqtoforallpaths _ _ _)%weq.
        refine (weqonsecfibers _ _ (λ zz, _) ∘ weqtoforallpaths _ _ _)%weq.
        refine (weqonsecfibers _ _ (λ ff, _) ∘ weqtoforallpaths _ _ _)%weq.
        exact (weqtoforallpaths _ _ _).
  Defined.

  Definition disp_cat_eq_functor
    : UU
    := ∑ (pob : ∏ (x : C), D₁ x ≃ D₂ x),
       ∑ (pmor : ∏ (x y : C)
                   (xx : D₁ x)
                   (yy : D₁ y)
                   (f : x --> y),
                 xx -->[ f ] yy
                 ≃
                 pob x xx -->[ f ] pob y yy),
       (∏ (x : C) (xx : D₁ x),
        pmor _ _ _ _ _ (id_disp xx)
        =
        id_disp (pob x xx))
       ×
       (∏ (x y z : C)
          (f : x --> y)
          (g : y --> z)
          (xx : D₁ x)
          (yy : D₁ y)
          (zz : D₁ z)
          (ff : xx -->[ f ] yy)
          (gg : yy -->[ g ] zz),
        pmor _ _ _ _ _ (ff ;; gg)
        =
        pmor _ _ _ _ _ ff ;; pmor _ _ _ _ _ gg).

  Definition disp_cat_eq_step_5
    : (∑ (pob : ∏ (x : C), D₁ x = D₂ x),
       ∑ (pmor : ∏ (x y : C)
                   (xx : D₁ x)
                   (yy : D₁ y)
                   (f : x --> y),
                 xx -->[ f ] yy
                 =
                 eqweqmap (pob x) xx -->[ f ] eqweqmap (pob y) yy),
        disp_cat_id_comp_eq pob pmor)
      ≃
      disp_cat_eq_functor.
  Proof.
    use weqbandf.
    - refine (weqonsecfibers _ _ (λ x, _)).
      exact (univalence _ _).
    - intro pob.
      use weqbandf.
      + cbn.
        refine (weqonsecfibers _ _ (λ x, _)).
        refine (weqonsecfibers _ _ (λ y, _)).
        refine (weqonsecfibers _ _ (λ xx, _)).
        refine (weqonsecfibers _ _ (λ yy, _)).
        refine (weqonsecfibers _ _ (λ f, _)).
        exact (univalence _ _).
      + cbn.
        intro pmor.
        exact (idweq _).
  Defined.

  Definition disp_cat_eq_step_6_left
    : disp_cat_eq_functor
      →
      ∑ (F : disp_functor (functor_identity C) D₁ D₂),
      (∏ (x : C), isweq (F x))
      ×
      disp_functor_ff F.
  Proof.
    intro FF.
    simple refine (_ ,, _ ,, _).
    - simple refine ((_ ,, _) ,, (_ ,, _)).
      + exact (λ x, pr1 FF x).
      + exact (λ x y xx yy f ff, pr12 FF x y xx yy f ff).
      + exact (λ x xx, pr122 FF x xx).
      + exact (λ x y z xx yy zz f g ff gg, pr222 FF x y z f g xx yy zz ff gg).
    - exact (λ x, pr2 (pr1 FF x)).
    - intros x y xx yy f.
      exact (pr2 (pr12 FF x y xx yy f)).
  Defined.

  Definition disp_cat_eq_step_6_right
    : (∑ (F : disp_functor (functor_identity C) D₁ D₂),
       (∏ (x : C), isweq (F x))
       ×
       disp_functor_ff F)
      →
      disp_cat_eq_functor.
  Proof.
    intro FF.
    induction FF as [ FF [ HF₁ HF₂ ]].
    simple refine (_ ,, _ ,, _ ,, _).
    - intro x.
      use make_weq.
      + exact (FF x).
      + exact (HF₁ x).
    - intros x y xx yy f.
      use make_weq.
      + exact (λ ff, ♯FF ff).
      + apply HF₂.
    - intros x xx ; cbn.
      exact (disp_functor_id FF xx).
    - intros x y z f g xx yy zz ff gg ; cbn.
      exact (disp_functor_comp FF ff gg).
  Defined.

  Definition disp_cat_eq_step_6
    : disp_cat_eq_functor
      ≃
      ∑ (F : disp_functor (functor_identity C) D₁ D₂),
      (∏ (x : C), isweq (F x))
      ×
      disp_functor_ff F.
  Proof.
    use weq_iso.
    - exact disp_cat_eq_step_6_left.
    - exact disp_cat_eq_step_6_right.
    - apply idpath.
    - apply idpath.
  Defined.

  Definition disp_cat_eq
    : D₁ = D₂
      ≃
      ∑ (F : disp_functor (functor_identity C) D₁ D₂),
      (∏ (x : C), isweq (F x))
      ×
      disp_functor_ff F
    := (disp_cat_eq_step_6
        ∘ disp_cat_eq_step_5
        ∘ disp_cat_eq_step_4
        ∘ disp_cat_eq_step_3
        ∘ disp_cat_eq_step_2
        ∘ disp_cat_eq_step_1)%weq.

  Context (HD₁ : is_univalent_disp D₁)
          (HD₂ : is_univalent_disp D₂).

  Definition disp_cat_eq_step_7
    : (∑ (F : disp_functor (functor_identity C) D₁ D₂),
       (∏ (x : C), isweq (F x))
       ×
       disp_functor_ff F)
      ≃
      ∑ (F : disp_functor (functor_identity C) D₁ D₂),
      disp_functor_disp_ess_surj F
      ×
      disp_functor_ff F.
  Proof.
    use weqfibtototal.
    intro FF.
    use weqimplimpl.
    - intros HFF.
      split.
      + intros x yy.
        apply hinhpr.
        refine (invmap (make_weq _ (pr1 HFF x)) yy ,, _).
        apply (idtoiso_disp (idpath _)) ; cbn.
        apply (homotweqinvweq (make_weq (FF x) (pr1 HFF x))).
      + exact (pr2 HFF).
    - intros HFF.
      split.
      + intro x.
        exact (disp_ess_surj_ob_weq HD₁ HD₂ (pr1 HFF) (pr2 HFF) x).
      + exact (pr2 HFF).
    - use isapropdirprod.
      + use impred ; intro.
        apply isapropisweq.
      + apply isaprop_disp_functor_ff.
    - apply isapropdirprod.
      + apply propproperty.
      + apply isaprop_disp_functor_ff.
  Defined.

  Definition disp_cat_eq_step_8
    : (∑ (F : disp_functor (functor_identity C) D₁ D₂),
       disp_functor_disp_ess_surj F
       ×
       disp_functor_ff F)
      ≃
      ∑ (F : disp_functor (functor_identity C) D₁ D₂),
      is_equiv_over_id F.
  Proof.
    use weqfibtototal.
    intro F.
    use weqimplimpl.
    - intros HF.
      use is_equiv_from_ff_ess_over_id.
      + exact (disp_functor_disp_ess_surj_to_split HD₁ HD₂ (pr1 HF) (pr2 HF)).
      + exact (pr2 HF).
    - intros HF.
      split.
      + exact (is_equiv_over_id_to_ess_surj F HF).
      + exact (is_equiv_over_id_to_ff F HF).
    - apply isapropdirprod.
      + apply propproperty.
      + apply isaprop_disp_functor_ff.
    - exact (isaprop_is_equiv_over_id HD₁ HD₂ F).
  Defined.

  Definition univ_disp_cat_eq
    : D₁ = D₂
      ≃
      ∑ (F : disp_functor (functor_identity C) D₁ D₂),
      is_equiv_over_id F
    := (disp_cat_eq_step_8
        ∘ disp_cat_eq_step_7
        ∘ disp_cat_eq_step_6
        ∘ disp_cat_eq_step_5
        ∘ disp_cat_eq_step_4
        ∘ disp_cat_eq_step_3
        ∘ disp_cat_eq_step_2
        ∘ disp_cat_eq_step_1)%weq.
End DisplayedCatEq.
