(********************************************************************************************

 The slice category is regular and exact

 One key theorem about regular categories is that they are closed under slicing.

 To prove this theorem, we characterize regular epimorphisms in the slice category `C/x` as
 regular epimorphisms in  `C`. Note that for this characterization we use that `C` is regular,
 because that allows us to characterize regular epimorphisms as extremal epimorphisms. With
 this in place, we can directly prove that the slice category is regular. In addition, we
 prove that the pullback functor and the codomain functor preserve regular epimorphisms under
 suitable assumptions.

 We also show that exact categories are closed under slicing. This proofs boils down to
 showing that every internal equivalence relation in `C/x` gives rise to one in `C`.

 Contents
 1. Regular epimorphisms in the slice category
 2. Regular categories are closed under slicing
 3. Preservation of regular epimorphisms by the pullback functor
 4. Preservation of regular epimorphisms by the codomain functor
 5. Exact category

 ********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpiFacts.
Require Import UniMath.CategoryTheory.RegularAndExact.ExactCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodMorphisms.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.

Local Open Scope cat.

(** * 1. Regular epimorphisms in the slice category *)
Definition to_regular_epi_in_slice
           {C : category}
           {x : C}
           {yg₁ zg₂ : C/x}
           {hp : yg₁ --> zg₂}
           (H : is_regular_epi (dom_mor hp))
  : is_regular_epi hp.
Proof.
  revert H.
  use factor_through_squash.
  {
    apply isaprop_is_regular_epi.
  }
  intros H.
  induction H as ( w & g₁ & g₂ & p & H ).
  use hinhpr.
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact (make_cod_fib_ob (g₁ · cod_mor yg₁)).
  - use make_cod_fib_mor.
    + exact g₁.
    + abstract
        (cbn ;
         apply idpath).
  - use make_cod_fib_mor.
    + exact g₂.
    + abstract
        (cbn ;
         rewrite <- (mor_eq hp) ; cbn ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         exact (!p)).
  - abstract
      (use eq_mor_cod_fib ;
       rewrite !comp_in_cod_fib ; cbn ;
       exact p).
  - use is_coequalizer_cod_fib.
    + exact p.
    + exact H.
Qed.

Definition from_regular_epi_in_slice
           {C : category}
           (PB : Pullbacks C)
           (EC : coeqs_of_kernel_pair C)
           (HC : regular_epi_pb_stable C)
           {x : C}
           {yg₁ zg₂ : C/x}
           {hp : yg₁ --> zg₂}
           (H : is_regular_epi hp)
  : is_regular_epi (dom_mor hp).
Proof.
  apply (is_regular_epi_strong_epi PB EC HC).
  apply (is_strong_epi_extremal_epi PB).
  intros z f g p Hg.
  pose (wh := (make_cod_fib_ob (g · cod_mor zg₂)) : C/x).
  assert (f · (g · cod_mor zg₂) = cod_mor yg₁) as q₁.
  {
    rewrite assoc.
    rewrite <- p.
    exact (mor_eq hp).
  }
  pose (φ := @make_cod_fib_mor _ _ yg₁ wh f q₁).
  assert (g · cod_mor zg₂ = cod_mor wh) as q₂.
  {
    apply idpath.
  }
  pose (ψ := @make_cod_fib_mor _ _ wh zg₂ g q₂).
  assert (hp = φ · ψ) as q₃.
  {
    use eq_mor_cod_fib.
    rewrite comp_in_cod_fib.
    cbn.
    exact p.
  }
  assert (isMonic ψ) as Hψ.
  {
    use is_monic_cod_fib.
    exact Hg.
  }
  pose (is_extremal_epi_strong_epi (is_strong_epi_regular_epi H) wh φ ψ q₃ Hψ) as H'.
  use make_is_z_isomorphism.
  - exact (pr11 H').
  - split.
    + refine (_ @ maponpaths dom_mor (pr12 H')).
      rewrite comp_in_cod_fib.
      apply idpath.
    + refine (_ @ maponpaths dom_mor (pr22 H')).
      rewrite comp_in_cod_fib.
      apply idpath.
Qed.

Definition regular_epi_in_slice_weq
           {C : category}
           (PB : Pullbacks C)
           (EC : coeqs_of_kernel_pair C)
           (HC : regular_epi_pb_stable C)
           {x : C}
           {yg₁ zg₂ : C/x}
           (hp : yg₁ --> zg₂)
  : is_regular_epi hp ≃ is_regular_epi (pr1 hp).
Proof.
  use weqimplimpl.
  - apply (from_regular_epi_in_slice PB EC HC).
  - apply to_regular_epi_in_slice.
  - apply isaprop_is_regular_epi.
  - apply isaprop_is_regular_epi.
Defined.

(** * 2. Regular categories are closed under slicing *)
Section SliceRegular.
  Context {C : category}
          (PB : Pullbacks C)
          (EC : coeqs_of_kernel_pair C)
          (HC : regular_epi_pb_stable C)
          (x : C).

  Section CoeqSlice.
    Context {yf zg : C/x}
            (hp : yf --> zg)
            (K : kernel_pair hp).

    Let y : C := cod_dom yf.
    Let z : C := cod_dom zg.
    Let f : y --> x := cod_mor yf.
    Let g : z --> x := cod_mor zg.
    Let h : y --> z := dom_mor hp.

    Let pk : C/x := PullbackObject K.
    Let p : C := cod_dom pk.
    Let k : p --> x := cod_mor pk.

    Let qπ₁ : pk --> yf := PullbackPr1 K.
    Let π₁ : p --> y := dom_mor qπ₁.
    Let qπ₂ : pk --> yf := PullbackPr2 K.
    Let π₂ : p --> y := dom_mor qπ₂.

    Proposition to_kernel_pair_slice_eq
      : π₁ · h = π₂ · h.
    Proof.
      refine (_ @ maponpaths dom_mor (PullbackSqrCommutes K) @ _).
      - rewrite comp_in_cod_fib.
        apply idpath.
      - rewrite comp_in_cod_fib.
        apply idpath.
    Qed.

    Definition to_kernel_pair_slice
      : kernel_pair h.
    Proof.
      use make_Pullback.
      - exact p.
      - exact π₁.
      - exact π₂.
      - exact to_kernel_pair_slice_eq.
      - use from_is_pullback_slice.
        + abstract
            (exact (PullbackSqrCommutes K)).
        + exact (isPullback_Pullback K).
    Defined.

    Let Coeq : Coequalizer π₁ π₂ := EC y z h to_kernel_pair_slice.

    Definition coeq_of_kernel_pair_slice_ob_mor
      : Coeq --> x.
    Proof.
      use CoequalizerOut.
      - exact f.
      - abstract
          (exact (mor_eq qπ₁ @ !(mor_eq qπ₂))).
    Defined.

    Definition coeq_of_kernel_pair_slice_ob
      : C/x.
    Proof.
      use make_cod_fib_ob.
      - exact Coeq.
      - exact coeq_of_kernel_pair_slice_ob_mor.
    Defined.

    Definition coeq_of_kernel_pair_slice_coeq_arr
      : yf --> coeq_of_kernel_pair_slice_ob.
    Proof.
      use make_cod_fib_mor.
      - apply CoequalizerArrow.
      - abstract
          (cbn ; unfold coeq_of_kernel_pair_slice_ob_mor ;
           rewrite CoequalizerCommutes ;
           apply idpath ).
    Defined.

    Proposition coeq_of_kernel_pair_slice_coeq_arr_eq
      : PullbackPr1 K · coeq_of_kernel_pair_slice_coeq_arr
        =
        PullbackPr2 K · coeq_of_kernel_pair_slice_coeq_arr.
    Proof.
      use eq_mor_cod_fib.
      rewrite !comp_in_cod_fib.
      apply CoequalizerEqAr.
    Qed.

    Definition coeq_of_kernel_pair_slice
      : Coequalizer (PullbackPr1 K) (PullbackPr2 K).
    Proof.
      use make_Coequalizer.
      - exact coeq_of_kernel_pair_slice_ob.
      - exact coeq_of_kernel_pair_slice_coeq_arr.
      - exact coeq_of_kernel_pair_slice_coeq_arr_eq.
      - use is_coequalizer_cod_fib.
        + apply (CoequalizerEqAr Coeq).
        + exact (isCoequalizer_Coequalizer Coeq).
    Defined.
  End CoeqSlice.

  Definition cod_fib_coeqs_of_kernel_pair
    : coeqs_of_kernel_pair (C/x)
    := λ yf zg hp K, coeq_of_kernel_pair_slice hp K.

  Definition cod_fib_regular_epi_pb_stable
    : regular_epi_pb_stable (C/x).
  Proof.
    intros a b c d f g π₁ π₂ p H Hf.
    use to_regular_epi_in_slice.
    apply (from_regular_epi_in_slice PB EC HC) in Hf.
    assert (dom_mor π₁ · dom_mor f = dom_mor π₂ · dom_mor g) as q.
    {
      rewrite <- !comp_in_cod_fib.
      apply maponpaths.
      exact p.
    }
    pose (from_is_pullback_slice _ _ _ _ q _ H) as H'.
    use (HC _ _ _ _ _ _ _ _ _ H').
    exact Hf.
  Qed.

  Definition is_regular_category_cod_fib
    : is_regular_category (C/x).
  Proof.
    repeat split.
    - apply codomain_fib_terminal.
    - apply codomain_fiberwise_pullbacks.
      exact PB.
    - exact cod_fib_coeqs_of_kernel_pair.
    - exact cod_fib_regular_epi_pb_stable.
  Defined.
End SliceRegular.

(** * 3. Preservation of regular epimorphisms by the pullback functor *)
Section PullbackStable.
  Context {C : category}
          (PB : Pullbacks C)
          (EC : coeqs_of_kernel_pair C)
          (HC : regular_epi_pb_stable C).

  Section PreservesFromStable.
    Context {x y : C}
            (f : x --> y)
            {zg₁ zg₂ : C/y}
            (hp : zg₁ --> zg₂).

    Let z₁ : C := cod_dom zg₁.
    Let z₂ : C := cod_dom zg₂.
    Let g₁ : z₁ --> y := cod_mor zg₁.
    Let g₂ : z₂ --> y := cod_mor zg₂.
    Let h : z₁ --> z₂ := dom_mor hp.

    Let P₁ : Pullback g₁ f := PB _ _ _ g₁ f.
    Let π₁ : P₁ --> z₁ := PullbackPr1 P₁.
    Let π₂ : P₁ --> x := PullbackPr2 P₁.

    Let P₂ : Pullback g₂ f := PB _ _ _ g₂ f.
    Let ρ₁ : P₂ --> z₂ := PullbackPr1 P₂.
    Let ρ₂ : P₂ --> x := PullbackPr2 P₂.

    Context (r : π₁ · h · g₂ = π₂ · f).

    Let k : P₁ --> P₂
      := PullbackArrow P₂ P₁ (π₁ · h) π₂ r.

    Lemma regular_epi_pb_stable_to_pb_preserves_pb_sqr_eq
      : π₁ · h = k · ρ₁.
    Proof.
      refine (!_).
      apply PullbackArrow_PullbackPr1.
    Qed.

    Lemma regular_epi_pb_stable_to_pb_preserves_pb_sqr
      : isPullback regular_epi_pb_stable_to_pb_preserves_pb_sqr_eq.
    Proof.
      intros w l l' q.
      use iscontraprop1.
      - use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use (MorphismsIntoPullbackEqual (isPullback_Pullback P₁)).
        + exact (pr12 ζ₁ @ !(pr12 ζ₂)).
        + pose (maponpaths (λ z, z · PullbackPr2 P₂) (pr22 ζ₁ @ !(pr22 ζ₂))) as qr.
          cbn in qr.
          rewrite !assoc' in qr.
          unfold k in qr.
          rewrite !PullbackArrow_PullbackPr2 in qr.
          exact qr.
      - simple refine (_ ,, _ ,, _).
        + use PullbackArrow.
          * exact l.
          * exact (l' · ρ₂).
          * refine (maponpaths (λ z, _ · z) (!(mor_eq hp)) @ _).
            rewrite !assoc.
            refine (maponpaths (λ z, z · _) q @ _).
            rewrite !assoc'.
            apply maponpaths.
            apply PullbackSqrCommutes.
        + apply PullbackArrow_PullbackPr1.
        + use (MorphismsIntoPullbackEqual (isPullback_Pullback P₂)).
          * unfold k.
            refine (assoc' _ _ _ @ _).
            rewrite PullbackArrow_PullbackPr1.
            refine (assoc _ _ _ @ _).
            rewrite PullbackArrow_PullbackPr1.
            exact q.
          * unfold k.
            refine (assoc' _ _ _ @ _).
            rewrite !PullbackArrow_PullbackPr2.
            apply idpath.
    Qed.

    Let HP' := regular_epi_pb_stable_to_pb_preserves_pb_sqr.
    Let P' := make_Pullback _ HP'.

    Lemma regular_epi_pb_stable_to_pb_preserves_lem
          (Hp : is_regular_epi hp)
      : is_regular_epi k.
    Proof.
      use (HC _ _ _ _ _ _ _ _ _ HP').
      apply (from_regular_epi_in_slice PB EC HC).
      exact Hp.
    Qed.
  End PreservesFromStable.

  Definition regular_epi_pb_stable_to_pb_preserves
             {x y : C}
             (f : x --> y)
    : preserves_regular_epi (cod_pb PB f).
  Proof.
    intros g h p Hp.
    use to_regular_epi_in_slice.
    rewrite cod_fiber_functor_on_mor.
    exact (regular_epi_pb_stable_to_pb_preserves_lem f p _ Hp).
  Qed.
End PullbackStable.

(** * 4. Preservation of regular epimorphisms by the codomain functor *)
Definition preserves_regular_epi_fiber_disp_cod
           {C₁ C₂ : category}
           (PB : Pullbacks C₁)
           (EC : coeqs_of_kernel_pair C₁)
           (HC : regular_epi_pb_stable C₁)
           (F : C₁ ⟶ C₂)
           (HF : preserves_regular_epi F)
           (x : C₁)
  : preserves_regular_epi (fiber_functor (disp_codomain_functor F) x).
Proof.
  intros fy gz hp Hf.
  use to_regular_epi_in_slice.
  rewrite disp_codomain_fiber_functor_mor.
  apply HF.
  exact (from_regular_epi_in_slice PB EC HC Hf).
Defined.

(** * 5. Exactness of the slice category *)
Proposition from_internal_relation_slice_monic
            {C : category}
            {x : C}
            {zf : C/x}
            (R : internal_relation zf)
            (w : C)
            (f g : w --> cod_dom R)
            (p : f · dom_mor (internal_relation_src R)
                 =
                 g · dom_mor (internal_relation_src R))
            (q : f · dom_mor (internal_relation_tar R)
                 =
                 g · dom_mor (internal_relation_tar R))
  : f = g.
Proof.
  use (maponpaths
         dom_mor
         (@internal_relation_monic
             _ _
             R
             (make_cod_fib_ob (f · cod_mor R))
             (make_cod_fib_mor _ _)
             (make_cod_fib_mor _ _)
             _ _)).
  - apply idpath.
  - cbn.
    rewrite <- !(mor_eq (internal_relation_src R)).
    rewrite !assoc.
    apply maponpaths_2.
    exact (!p).
  - use eq_mor_cod_fib.
    rewrite !comp_in_cod_fib.
    cbn.
    exact p.
  - use eq_mor_cod_fib.
    rewrite !comp_in_cod_fib.
    cbn.
    exact q.
Qed.

Definition from_internal_relation_slice
           {C : category}
           {x : C}
           {zf : C/x}
           (R : internal_relation zf)
  : internal_relation (cod_dom zf).
Proof.
  use make_internal_relation.
  - exact (cod_dom R).
  - exact (dom_mor (internal_relation_src R)).
  - exact (dom_mor (internal_relation_tar R)).
  - exact (from_internal_relation_slice_monic R).
Defined.

Proposition isrefl_from_internal_is_eqrel_slice
            {C : category}
            {x : C}
            {zf : C/x}
            (R : internal_eqrel zf)
  : internal_isrefl (from_internal_relation_slice R).
Proof.
  intros w g.
  pose (w' := make_cod_fib_ob (g · cod_mor zf)).
  assert (g · cod_mor zf = cod_mor w') as p.
  {
    apply idpath.
  }
  pose (g' := @make_cod_fib_mor _ _ w' zf g p).
  pose (r := isrefl_internal_eqrel R w' g' : internal_relation_to_arr_relation _ _ _).
  use make_internal_relation_to_arr_relation.
  - exact (dom_mor r).
  - refine (!(comp_in_cod_fib r _) @ _).
    rewrite (internal_relation_to_arr_relation_src r).
    apply idpath.
  - refine (!(comp_in_cod_fib r _) @ _).
    rewrite (internal_relation_to_arr_relation_tar r).
    apply idpath.
Qed.

Proposition issymm_from_internal_is_eqrel_slice
            {C : category}
            {x : C}
            {zf : C/x}
            (R : internal_eqrel zf)
  : internal_issymm (from_internal_relation_slice R).
Proof.
  intros w g₁ g₂ p.
  pose (w' := make_cod_fib_ob (g₁ · cod_mor zf)).
  induction p as [ h [ p₁ p₂ ]].
  cbn in h, p₁, p₂.
  assert (g₁ · cod_mor zf = cod_mor w') as q₁.
  {
    apply idpath.
  }
  pose (g₁' := @make_cod_fib_mor _ _ w' zf g₁ q₁).
  assert (g₂ · cod_mor zf = cod_mor w') as q₂.
  {
    cbn.
    rewrite <- p₁, <- p₂.
    rewrite !assoc'.
    rewrite (mor_eq (internal_relation_src R)).
    rewrite (mor_eq (internal_relation_tar R)).
    apply idpath.
  }
  pose (g₂' := @make_cod_fib_mor _ _ w' zf g₂ q₂).
  assert (internal_relation_to_arr_hrel R w' g₁' g₂') as H.
  {
    use make_internal_relation_to_arr_relation.
    - use make_cod_fib_mor.
      + exact h.
      + cbn.
        rewrite <- p₁.
        rewrite !assoc'.
        rewrite (mor_eq (internal_relation_src R)).
        apply idpath.
    - use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      cbn.
      exact p₁.
    - use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      cbn.
      exact p₂.
  }
  pose (r := issymm_internal_eqrel R w' g₁' g₂' H : internal_relation_to_arr_relation _ _ _).
  use make_internal_relation_to_arr_relation.
  - exact (dom_mor r).
  - refine (!(comp_in_cod_fib r _) @ _).
    rewrite (internal_relation_to_arr_relation_src r).
    apply idpath.
  - refine (!(comp_in_cod_fib r _) @ _).
    rewrite (internal_relation_to_arr_relation_tar r).
    apply idpath.
Qed.

Proposition istrans_from_internal_is_eqrel_slice
            {C : category}
            {x : C}
            {zf : C/x}
            (R : internal_eqrel zf)
  : internal_istrans (from_internal_relation_slice R).
Proof.
  intros w g₁ g₂ g₃ p q.
  pose (w' := make_cod_fib_ob (g₁ · cod_mor zf)).
  induction p as [ h [ p₁ p₂ ]].
  induction q as [ k [ q₁ q₂ ]].
  cbn in h, p₁, p₂, k, q₁, q₂.
  assert (g₁ · cod_mor zf = cod_mor w') as r₁.
  {
    apply idpath.
  }
  pose (g₁' := @make_cod_fib_mor _ _ w' zf g₁ r₁).
  assert (g₂ · cod_mor zf = cod_mor w') as r₂.
  {
    cbn.
    rewrite <- p₁, <- p₂.
    rewrite !assoc'.
    rewrite (mor_eq (internal_relation_src R)).
    rewrite (mor_eq (internal_relation_tar R)).
    apply idpath.
  }
  pose (g₂' := @make_cod_fib_mor _ _ w' zf g₂ r₂).
  assert (k · cod_mor R = h · cod_mor R) as lem.
  {
    etrans.
    {
      rewrite <- (mor_eq (internal_relation_src R)).
      rewrite !assoc.
      rewrite q₁.
      apply idpath.
    }
    rewrite <- (mor_eq (internal_relation_tar R)).
    rewrite !assoc.
    rewrite p₂.
    apply idpath.
  }
  assert (g₃ · cod_mor zf = cod_mor w') as r₃.
  {
    cbn.
    rewrite <- p₁, <- q₂.
    rewrite !assoc'.
    rewrite (mor_eq (internal_relation_src R)).
    rewrite (mor_eq (internal_relation_tar R)).
    exact lem.
  }
  pose (g₃' := @make_cod_fib_mor _ _ w' zf g₃ r₃).
  assert (internal_relation_to_arr_hrel R w' g₁' g₂') as H₁.
  {
    use make_internal_relation_to_arr_relation.
    - use make_cod_fib_mor.
      + exact h.
      + cbn.
        rewrite <- p₁.
        rewrite !assoc'.
        rewrite (mor_eq (internal_relation_src R)).
        apply idpath.
    - use eq_mor_cod_fib.
      rewrite comp_in_cod_fib ; cbn.
      exact p₁.
    - use eq_mor_cod_fib.
      rewrite comp_in_cod_fib ; cbn.
      exact p₂.
  }
  assert (internal_relation_to_arr_hrel R w' g₂' g₃') as H₂.
  {
    use make_internal_relation_to_arr_relation.
    - use make_cod_fib_mor.
      + exact k.
      + cbn.
        rewrite <- p₁.
        rewrite !assoc'.
        rewrite (mor_eq (internal_relation_src R)).
        exact lem.
    - use eq_mor_cod_fib.
      rewrite comp_in_cod_fib ; cbn.
      exact q₁.
    - use eq_mor_cod_fib.
      rewrite comp_in_cod_fib ; cbn.
      exact q₂.
  }
  pose (r := istrans_internal_eqrel R w' g₁' g₂' g₃' H₁ H₂).
  cbn in r.
  use make_internal_relation_to_arr_relation.
  - exact (dom_mor r).
  - refine (!(comp_in_cod_fib r _) @ _).
    rewrite (internal_relation_to_arr_relation_src r).
    apply idpath.
  - refine (!(comp_in_cod_fib r _) @ _).
    rewrite (internal_relation_to_arr_relation_tar r).
    apply idpath.
Qed.

Proposition from_internal_is_eqrel_slice
            {C : category}
            {x : C}
            {zf : C/x}
            (R : internal_eqrel zf)
  : internal_iseqrel (from_internal_relation_slice R).
Proof.
  repeat split.
  - exact (isrefl_from_internal_is_eqrel_slice R).
  - exact (issymm_from_internal_is_eqrel_slice R).
  - exact (istrans_from_internal_is_eqrel_slice R).
Qed.

Definition from_internal_eqrel_slice
           {C : category}
           {x : C}
           {zf : C/x}
           (R : internal_eqrel zf)
  : internal_eqrel (cod_dom zf).
Proof.
  use make_internal_eqrel.
  - exact (from_internal_relation_slice R).
  - exact (from_internal_is_eqrel_slice R).
Defined.

Section Exactness.
  Context {C : category}
          {x : C}
          {zf : C/x}
          (R : internal_eqrel zf)
          (Coeq : Coequalizer
                    (dom_mor (internal_relation_src R))
                    (dom_mor (internal_relation_tar R))).

  Definition internal_eqrel_coequalizer_ob
    : C/x.
  Proof.
    use make_cod_fib_ob.
    - exact Coeq.
    - use CoequalizerOut.
      + exact (cod_mor zf).
      + abstract
          (rewrite (mor_eq (internal_relation_src R)) ;
           rewrite (mor_eq (internal_relation_tar R)) ;
           apply idpath).
  Defined.

  Definition internal_eqrel_coequalizer_arr
    : zf --> internal_eqrel_coequalizer_ob.
  Proof.
    use make_cod_fib_mor.
    - exact (CoequalizerArrow Coeq).
    - abstract
        (cbn ;
         rewrite CoequalizerCommutes ;
         apply idpath).
  Defined.

  Proposition internal_eqrel_coequalizer_eq
    : internal_relation_src R · internal_eqrel_coequalizer_arr
      =
      internal_relation_tar R · internal_eqrel_coequalizer_arr.
  Proof.
    use eq_mor_cod_fib.
    rewrite !comp_in_cod_fib.
    apply CoequalizerEqAr.
  Qed.

  Definition internal_eqrel_coequalizer
    : Coequalizer (internal_relation_src R) (internal_relation_tar R).
  Proof.
    use make_Coequalizer.
    - exact internal_eqrel_coequalizer_ob.
    - exact internal_eqrel_coequalizer_arr.
    - exact internal_eqrel_coequalizer_eq.
    - use is_coequalizer_cod_fib.
      + apply CoequalizerEqAr.
      + exact (isCoequalizer_Coequalizer Coeq).
  Defined.
End Exactness.

Definition all_internal_eqrel_effective_fiber_disp_cod
           {C : category}
           (H : all_internal_eqrel_effective C)
           (x : C)
  : all_internal_eqrel_effective (C/x).
Proof.
  intros zf R.
  pose (HE := H _ (from_internal_eqrel_slice R)).
  pose (Coeq := pr1 HE).
  simple refine (_ ,, _).
  - exact (internal_eqrel_coequalizer R Coeq).
  - abstract
      (use to_is_pullback_slice ; [ | apply HE ]).
Defined.

Definition is_exact_disp_cod
           {C : category}
           (H : is_exact C)
           (x : C)
  : is_exact (C/x).
Proof.
  pose (H' := is_exact_to_is_regular H).
  split.
  - use is_regular_category_cod_fib.
    + exact (is_regular_category_pullbacks H').
    + exact (is_regular_category_coeqs_of_kernel_pair H').
    + exact (is_regular_category_regular_epi_pb_stable H').
  - use all_internal_eqrel_effective_fiber_disp_cod.
    exact (is_exact_to_all_internal_eqrel_effective H).
Qed.
