(***************************************************************************************

 Colimits in the slice category

 If a category `C` has colimits, then every slice category `C/x` also has colimits. We
 prove this for initial objects and binary coproducts. Note that the pullback functor
 does not necessarily preserve colimits. This would be the case if `C` is locally
 Cartesian closed, because then the pullback functor is a left adjoint. The pullback
 functor would preserve all finite coproducts if `C` is extensive, because that is one
 of the requirements of being an extensive category.

 Contents
 1. Initial object in the slice
 2. Binary coproducts in the slice
 3. Coequalizers in the slice

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.

Local Open Scope cat.

(** * 1. Initial object in the slice *)
Definition to_initial_slice
           {C : category}
           {y : C}
           (I : C/y)
           (H : isInitial C (cod_dom I))
  : isInitial (C/y) I.
Proof.
  intros f.
  pose (II := make_Initial _ H).
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use eq_mor_cod_fib ;
       use (InitialArrowEq (O := II))).
  - use make_cod_fib_mor.
    + exact (InitialArrow II _).
    + abstract
        (use (InitialArrowEq (O := II))).
Defined.

Definition initial_cod_fib
           {C : category}
           (y : C)
           (I : Initial C)
  : Initial (C/y).
Proof.
  use make_Initial.
  - use make_cod_fib_ob.
    + exact I.
    + apply InitialArrow.
  - use to_initial_slice.
    exact (pr2 I).
Defined.

(** * 2. Binary coproducts in the slice *)
Section IsBinCoproductSlice.
  Context {C : category}
          {y : C}
          {f g s : C/y}
          (ι₁ : f --> s)
          (ι₂ : g --> s)
          (H : isBinCoproduct C _ _ _ (dom_mor ι₁) (dom_mor ι₂)).

  Let coprod : BinCoproduct (cod_dom f) (cod_dom g)
    := make_BinCoproduct _ _ _ _ _ _ H.

  Section UMP.
    Context {h : C / y}
            (ρ₁ : f --> h)
            (ρ₂ : g --> h).

    Proposition to_bincoproduct_slice_unique
      : isaprop (∑ fg, ι₁ · fg = ρ₁ × ι₂ · fg = ρ₂).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use eq_mor_cod_fib.
      use (BinCoproductArrowsEq _ _ _ coprod).
      - cbn.
        refine (_ @ maponpaths dom_mor (pr12 φ₁ @ !(pr12 φ₂)) @ _).
        + rewrite comp_in_cod_fib.
          apply idpath.
        + rewrite comp_in_cod_fib.
          apply idpath.
      - cbn.
        refine (_ @ maponpaths dom_mor (pr22 φ₁ @ !(pr22 φ₂)) @ _).
        + rewrite comp_in_cod_fib.
          apply idpath.
        + rewrite comp_in_cod_fib.
          apply idpath.
    Qed.

    Definition to_bincoproduct_slice_mor_mor
      : cod_dom s --> cod_dom h.
    Proof.
      use (BinCoproductArrow coprod).
      - exact (dom_mor ρ₁).
      - exact (dom_mor ρ₂).
    Defined.

    Proposition to_bincoproduct_slice_mor_eq
      : to_bincoproduct_slice_mor_mor · cod_mor h = cod_mor s.
    Proof.
      unfold to_bincoproduct_slice_mor_mor.
      use (BinCoproductArrowsEq _ _ _ coprod).
      - rewrite !assoc.
        rewrite (BinCoproductIn1Commutes _ _ _ coprod) ; cbn.
        rewrite (mor_eq ρ₁), (mor_eq ι₁).
        apply idpath.
      - rewrite !assoc.
        rewrite (BinCoproductIn2Commutes _ _ _ coprod) ; cbn.
        rewrite (mor_eq ρ₂), (mor_eq ι₂).
        apply idpath.
    Qed.

    Definition to_bincoproduct_slice_mor
      : s --> h.
    Proof.
      use make_cod_fib_mor.
      - exact to_bincoproduct_slice_mor_mor.
      - exact to_bincoproduct_slice_mor_eq.
    Defined.

    Proposition to_bincoproduct_slice_mor_in1
      : ι₁ · to_bincoproduct_slice_mor = ρ₁.
    Proof.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      cbn.
      apply (BinCoproductIn1Commutes _ _ _ coprod).
    Qed.

    Proposition to_bincoproduct_slice_mor_in2
      : ι₂ · to_bincoproduct_slice_mor = ρ₂.
    Proof.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      cbn.
      apply (BinCoproductIn2Commutes _ _ _ coprod).
    Qed.
  End UMP.

  Definition to_bincoproduct_slice
    : isBinCoproduct (C/y) _ _ _ ι₁ ι₂.
  Proof.
    intros h ρ₁ ρ₂.
    use iscontraprop1.
    - exact (to_bincoproduct_slice_unique ρ₁ ρ₂).
    - simple refine (_ ,, _ ,, _).
      + exact (to_bincoproduct_slice_mor ρ₁ ρ₂).
      + apply to_bincoproduct_slice_mor_in1.
      + apply to_bincoproduct_slice_mor_in2.
  Defined.
End IsBinCoproductSlice.

Section BinCoproductSlice.
  Context {C : category}
          {y : C}
          (f g : C/y)
          (coprod : BinCoproduct (cod_dom f) (cod_dom g)).

  Definition cod_fib_coproduct_ob_mor
    : coprod --> y.
  Proof.
    use (BinCoproductArrow coprod).
    - exact (cod_mor f).
    - exact (cod_mor g).
  Defined.

  Definition cod_fib_coproduct_ob
    : C/y.
  Proof.
    use make_cod_fib_ob.
    - exact coprod.
    - exact cod_fib_coproduct_ob_mor.
  Defined.

  Definition cod_fib_coproduct_in1
    : f --> cod_fib_coproduct_ob.
  Proof.
    use make_cod_fib_mor.
    - exact (BinCoproductIn1 coprod).
    - abstract
        (apply BinCoproductIn1Commutes).
  Defined.

  Definition cod_fib_coproduct_in2
    : g --> cod_fib_coproduct_ob.
  Proof.
    use make_cod_fib_mor.
    - exact (BinCoproductIn2 coprod).
    - abstract
        (apply BinCoproductIn2Commutes).
  Defined.
End BinCoproductSlice.

Definition bincoproducts_cod_fib
           {C : category}
           (y : C)
           (H : BinCoproducts C)
  : BinCoproducts (C/y).
Proof.
  intros f g.
  pose (coprod := H (cod_dom f) (cod_dom g)).
  use make_BinCoproduct.
  - exact (cod_fib_coproduct_ob f g coprod).
  - exact (cod_fib_coproduct_in1 f g coprod).
  - exact (cod_fib_coproduct_in2 f g coprod).
  - use to_bincoproduct_slice.
    exact (isBinCoproduct_BinCoproduct _ coprod).
Defined.

(** * 3. Coequalizers in the slice *)
Section CoequalizerSlice.
  Context {C : category}
          (y : C)
          {f g h : C / y}
          (ρ₁ ρ₂ : f --> g)
          (i : g --> h)
          (p : ρ₁ · i = ρ₂ · i)
          (p' : dom_mor ρ₁ · dom_mor i = dom_mor ρ₂ · dom_mor i)
          (H : isCoequalizer (dom_mor ρ₁) (dom_mor ρ₂) (dom_mor i) p').

  Let coeq : Coequalizer (dom_mor ρ₁) (dom_mor ρ₂)
    := make_Coequalizer _ _ _ _ H.

  Section UMP.
    Context {wφ : C/y}
            (k : g --> wφ)
            (q : ρ₁ · k = ρ₂ · k).

    Proposition is_coequalizer_cod_fib_unique
      : isaprop (∑ φ, i · φ = k).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use eq_mor_cod_fib.
      use (CoequalizerOutsEq coeq).
      cbn.
      rewrite <- !comp_in_cod_fib.
      apply maponpaths.
      exact (pr2 φ₁ @ !(pr2 φ₂)).
    Qed.

    Definition is_coequalizer_cod_fib_mor
      : h --> wφ.
    Proof.
      use make_cod_fib_mor.
      - use (CoequalizerOut coeq).
        + exact (dom_mor k).
        + abstract
            (rewrite <- !comp_in_cod_fib ;
             exact (maponpaths dom_mor q)).
      - abstract
          (use (CoequalizerOutsEq coeq) ;
           rewrite !assoc ;
           rewrite (CoequalizerCommutes coeq) ;
           cbn ;
           rewrite (mor_eq k), (mor_eq i) ;
           apply idpath).
    Defined.

    Proposition is_coequalizer_cod_fib_eq
      : i · is_coequalizer_cod_fib_mor = k.
    Proof.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      cbn.
      apply (CoequalizerCommutes coeq).
    Qed.
  End UMP.

  Definition is_coequalizer_cod_fib
    : isCoequalizer ρ₁ ρ₂ i p.
  Proof.
    intros wφ k q.
    use iscontraprop1.
    - apply is_coequalizer_cod_fib_unique.
    - simple refine (_ ,, _).
      + exact (is_coequalizer_cod_fib_mor k q).
      + apply is_coequalizer_cod_fib_eq.
  Defined.
End CoequalizerSlice.

Section Coequalizer.
  Context {C : category}
          {y : C}
          (H : Coequalizers C)
          {f g : C/y}
          (ρ₁ ρ₂ : f --> g).

  Let coeq : Coequalizer (dom_mor ρ₁) (dom_mor ρ₂) := H _ _ (dom_mor ρ₁) (dom_mor ρ₂).

  Definition coequalizers_cod_fib_coeq
    : C/y.
  Proof.
    use make_cod_fib_ob.
    - exact coeq.
    - use CoequalizerOut.
      + exact (cod_mor g).
      + abstract
          (rewrite (mor_eq ρ₁), (mor_eq ρ₂) ;
           apply idpath).
  Defined.

  Definition coequalizers_cod_fib_map
    : g --> coequalizers_cod_fib_coeq.
  Proof.
    use make_cod_fib_mor.
    - apply CoequalizerArrow.
    - abstract
        (cbn ;
         apply (CoequalizerCommutes coeq)).
  Defined.

  Proposition coequalizers_cod_fib_eq
    : ρ₁ · coequalizers_cod_fib_map = ρ₂ · coequalizers_cod_fib_map.
  Proof.
    use eq_mor_cod_fib.
    rewrite !comp_in_cod_fib.
    apply CoequalizerEqAr.
  Qed.
End Coequalizer.

Definition coequalizers_cod_fib
           {C : category}
           (y : C)
           (H : Coequalizers C)
  : Coequalizers (C/y).
Proof.
  intros f g ρ₁ ρ₂.
  use make_Coequalizer.
  - exact (coequalizers_cod_fib_coeq H ρ₁ ρ₂).
  - apply coequalizers_cod_fib_map.
  - apply coequalizers_cod_fib_eq.
  - use is_coequalizer_cod_fib.
    + abstract
        (apply CoequalizerEqAr).
    + apply isCoequalizer_Coequalizer.
Defined.
