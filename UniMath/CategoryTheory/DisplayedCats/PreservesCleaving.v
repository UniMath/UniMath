(*********************************************************************************************

 Preservation of cleavings

 Suppose that we have a displayed functor `FF` over `F` between two cleavings `D₁` and `D₂`.
 We have two ways to state that `FF` preserves Cartesian lifts.

 The first way is by saying that `FF` is Cartesian, i.e., that it maps Cartesian morphisms in
 `D₁` to Cartesian morphisms in `D₂`. This is a weak way to say that `FF` preserves Cartesian
 lifts, because Cartesian lifts only are preserved up to isomorphism. Note that if we work
 with univalent categories, then this implies that Cartesian lifts are preserevd up to identity.

 The second way is strict in nature. More specifically, we say that the Cartesian lift of `yy`
 along some `f` is mapped by `FF` to the Cartesian lift of `FF yy` along `#F f`. Here we use
 strict equality of objects and morphisms, and thus this notion only makes sense if we are
 looking at setcategories.

 In this file, we define the second version, and we give some examples of functors that
 preserve cleavings.

 Content
 1. Preservation of cleavings
 2. Examples of functors that preserve cleavings

 *********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.

Local Open Scope cat.

(** * 1. Preservation of cleavings *)
Definition preserves_cleaving
           {C₁ C₂ : category}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           (I₁ : cleaving D₁)
           (I₂ : cleaving D₂)
           {F : C₁ ⟶ C₂}
           (FF : disp_functor F D₁ D₂)
  : UU
  := ∏ (x y : C₁)
       (f : x --> y)
       (yy : D₁ y),
     ∑ (p : FF x (cleaving_ob I₁ f yy)
            =
            cleaving_ob I₂ (#F f) (FF y yy)),
     (transportb
        _
        (id_left _)
        (♯ FF (cleaving_mor I₁ f yy))
      =
      idtoiso_disp (idpath _) p
      ;;
      cleaving_mor I₂ (functor_on_morphisms F f) (FF y yy))%mor_disp.

Definition make_preserves_cleaving
           {C₁ C₂ : category}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           (I₁ : cleaving D₁)
           (I₂ : cleaving D₂)
           {F : C₁ ⟶ C₂}
           (FF : disp_functor F D₁ D₂)
           (p : ∏ (x y : C₁)
                  (f : x --> y)
                  (yy : D₁ y),
                FF x (cleaving_ob I₁ f yy)
                =
                cleaving_ob I₂ (#F f) (FF y yy))
           (q : ∏ (x y : C₁)
                  (f : x --> y)
                  (yy : D₁ y),
                (transportb
                   _
                   (id_left _)
                   (♯ FF (cleaving_mor I₁ f yy))
                 =
                 idtoiso_disp (idpath _) (p x y f yy)
                 ;;
                 cleaving_mor I₂ (functor_on_morphisms F f) (FF y yy))%mor_disp)
  : preserves_cleaving I₁ I₂ FF.
Proof.
  exact (λ x y f yy, p x y f yy ,, q x y f yy).
Qed.

Proposition preserves_cleaving_ob
            {C₁ C₂ : category}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            {I₁ : cleaving D₁}
            {I₂ : cleaving D₂}
            {F : C₁ ⟶ C₂}
            {FF : disp_functor F D₁ D₂}
            (HFF : preserves_cleaving I₁ I₂ FF)
            {x y : C₁}
            (f : x --> y)
            (yy : D₁ y)
  : FF x (cleaving_ob I₁ f yy)
    =
    cleaving_ob I₂ (#F f) (FF y yy).
Proof.
  exact (pr1 (HFF x y f yy)).
Defined.

Proposition preserves_cleaving_mor
            {C₁ C₂ : category}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            {I₁ : cleaving D₁}
            {I₂ : cleaving D₂}
            {F : C₁ ⟶ C₂}
            {FF : disp_functor F D₁ D₂}
            (HFF : preserves_cleaving I₁ I₂ FF)
            {x y : C₁}
            (f : x --> y)
            (yy : D₁ y)
  : (transportb
       _
       (id_left _)
       (♯ FF (cleaving_mor I₁ f yy))
     =
     idtoiso_disp (idpath _) (preserves_cleaving_ob HFF f yy)
     ;;
     cleaving_mor I₂ (functor_on_morphisms F f) (FF y yy))%mor_disp.
Proof.
  exact (pr2 (HFF x y f yy)).
Defined.

Proposition preserves_cleaving_mor_alt
            {C₁ C₂ : category}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            {I₁ : cleaving D₁}
            {I₂ : cleaving D₂}
            {F : C₁ ⟶ C₂}
            {FF : disp_functor F D₁ D₂}
            (HFF : preserves_cleaving I₁ I₂ FF)
            {x y : C₁}
            (f : x --> y)
            (yy : D₁ y)
  : (♯ FF (cleaving_mor I₁ f yy)
     =
     transportf
       _
       (id_left _)
       (idtoiso_disp (idpath _) (preserves_cleaving_ob HFF f yy)
        ;;
        cleaving_mor I₂ (functor_on_morphisms F f) (FF y yy)))%mor_disp.
Proof.
  rewrite <- preserves_cleaving_mor.
  rewrite transportfbinv.
  apply idpath.
Qed.

Proposition isaprop_preserves_cleaving
            {C₁ C₂ : category}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            (I₁ : cleaving D₁)
            (I₂ : cleaving D₂)
            {F : C₁ ⟶ C₂}
            (FF : disp_functor F D₁ D₂)
            (H : ∏ (x : C₂), isaset (D₂ x))
  : isaprop (preserves_cleaving I₁ I₂ FF).
Proof.
  use impred ; intro x.
  use impred ; intro y.
  use impred ; intro f.
  use impred ; intro yy.
  use isaproptotal2.
  - intro.
    apply homsets_disp.
  - intros.
    apply H.
Qed.

(** * 2. Examples of functors that preserve cleavings *)
Proposition identity_preserves_cleaving
            {C : category}
            {D : disp_cat C}
            (I : cleaving D)
  : preserves_cleaving I I (disp_functor_identity D).
Proof.
  use make_preserves_cleaving.
  - intros x y f yy.
    apply idpath.
  - intros x y f yy ; cbn.
    rewrite id_left_disp.
    apply idpath.
Qed.

Proposition composition_preserves_cleaving
            {C₁ C₂ C₃ : category}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            {D₃ : disp_cat C₃}
            {I₁ : cleaving D₁}
            {I₂ : cleaving D₂}
            {I₃ : cleaving D₃}
            {F : C₁ ⟶ C₂}
            {FF : disp_functor F D₁ D₂}
            (HFF : preserves_cleaving I₁ I₂ FF)
            {G : C₂ ⟶ C₃}
            {GG : disp_functor G D₂ D₃}
            (HGG : preserves_cleaving I₂ I₃ GG)
  : preserves_cleaving I₁ I₃ (disp_functor_composite FF GG).
Proof.
  use make_preserves_cleaving.
  - intros x y f yy ; cbn.
    pose (preserves_cleaving_ob HFF f yy) as p.
    pose (preserves_cleaving_ob HGG (#F f) (FF y yy)) as q.
    exact (maponpaths (GG (F x)) p @ q).
  - intros x y f yy.
    cbn -[idtoiso_disp].
    rewrite (preserves_cleaving_mor_alt HFF f yy).
    rewrite disp_functor_transportf.
    unfold transportb.
    rewrite transport_f_f.
    rewrite disp_functor_comp.
    unfold transportb.
    rewrite transport_f_f.
    rewrite (preserves_cleaving_mor_alt HGG).
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite disp_functor_idtoiso_disp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply idtoiso_disp_comp.
    }
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    use transportf_set.
    apply homset_property.
Qed.

Proposition preserves_cleaving_reindex
            {C₁ C₂ : category}
            (F : C₁ ⟶ C₂)
            (D : disp_cat C₂)
            (I : cleaving D)
  : preserves_cleaving
      (cleaving_reindex_disp_cat F D I)
      I
      (reindex_disp_cat_disp_functor F D).
Proof.
  use make_preserves_cleaving.
  - intros x y f yy.
    apply idpath.
  - intros x y f yy ; cbn.
    rewrite id_left_disp.
    apply idpath.
Qed.

Proposition preserves_cleaving_lift_reindex
            {C₁ C₂ C₃ : category}
            {F : C₂ ⟶ C₁}
            {F' : C₃ ⟶ C₂}
            {D₁ : disp_cat C₁}
            {I₁ : cleaving D₁}
            {D₃ : disp_cat C₃}
            {I₃ : cleaving D₃}
            (FF : disp_functor (F' ∙ F) D₃ D₁)
            (HFF : preserves_cleaving I₃ I₁ FF)
  : preserves_cleaving
      I₃
      (cleaving_reindex_disp_cat F D₁ I₁)
      (lift_functor_into_reindex FF).
Proof.
  use make_preserves_cleaving.
  - intros x y f yy ; cbn.
    exact (preserves_cleaving_ob HFF f yy).
  - intros x y f yy ; cbn -[idtoiso_disp].
    etrans.
    {
      apply transportf_reindex.
    }
    etrans.
    {
      apply maponpaths.
      exact (preserves_cleaving_mor_alt HFF f yy).
    }
    rewrite transport_f_f.
    cbn -[idtoiso_disp].
    unfold transportb.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply idtoiso_reindex_disp_cat.
    }
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
Qed.
