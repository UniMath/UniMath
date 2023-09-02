
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Local Open Scope cat.
Local Open Scope mor_disp.

(** ** Displayed Natural Transformations *)
Section Disp_Nat_Trans.

  Definition disp_nat_trans_data
             {C' C : precategory_data}
             {F' F : functor_data C' C}
             (a : forall x, F' x --> F x)
             {D' : disp_cat_data C'}
             {D : disp_cat_data C}
             (R' : disp_functor_data F' D' D)
             (R : disp_functor_data F D' D) :=
    forall (x : C')  (xx : D' x),
      R' x  xx -->[ a x ] R x xx .

  Definition disp_nat_trans_axioms
             {C' C : precategory_data}
             {F' F : functor_data C' C}
             {a : nat_trans F' F}
             {D' : disp_cat_data C'}
             {D : disp_cat_data C}
             {R' : disp_functor_data F' D' D}
             {R : disp_functor_data F D' D}
             (b : disp_nat_trans_data a R' R) : UU
    :=
    forall (x' x : C') (f : x' --> x)
      (xx' : D' x') (xx : D' x)
      (ff : xx' -->[ f ] xx),
      ♯ R'  ff ;; b _ xx =
        transportb _ (nat_trans_ax a _ _ f ) (b _ xx' ;; ♯ R ff).

  Lemma isaprop_disp_nat_trans_axioms
        {C' C : category}
        {F' F : functor_data C' C}
        (a : nat_trans F' F)
        {D' : disp_cat_data C'}
        {D : disp_cat C}
        {R' : disp_functor_data F' D' D}
        {R : disp_functor_data F D' D}
        (b : disp_nat_trans_data a R' R)
    :
    isaprop (disp_nat_trans_axioms b).
  Proof.
    repeat (apply impred; intro).
    apply homsets_disp.
  Qed.

  Definition disp_nat_trans
             {C' C : precategory_data}
             {F' F : functor_data C' C}
             (a : nat_trans F' F)
             {D' : disp_cat_data C'}
             {D : disp_cat_data C}
             (R' : disp_functor_data F' D' D)
             (R : disp_functor_data F D' D) : UU :=
    ∑ b : disp_nat_trans_data a R' R,
        disp_nat_trans_axioms b.

  Definition disp_nat_trans_pr1
             {C' C : precategory_data}
             {F' F : functor_data C' C}
             {a : nat_trans F' F}
             {D' : disp_cat_data C'}
             {D : disp_cat_data C}
             {R' : disp_functor_data F' D' D}
             {R : disp_functor_data F D' D}
             (b : disp_nat_trans a R' R)
             {x : C'}  (xx : D' x):
    R' x  xx -->[ a x ] R x xx
    := pr1 b x xx.

  Coercion disp_nat_trans_pr1 : disp_nat_trans >-> Funclass.

  Definition disp_nat_trans_ax
             {C' C : precategory_data}
             {F' F : functor_data C' C}
             {a : nat_trans F' F}
             {D' : disp_cat_data C'}
             {D : disp_cat_data C}
             {R' : disp_functor_data F' D' D}
             {R : disp_functor_data F D' D}
             (b : disp_nat_trans a R' R)
             {x' x : C'}
             {f : x' --> x}
             {xx' : D' x'}
             {xx : D' x}
             (ff : xx' -->[ f ] xx):
    ♯ R'  ff ;; b _ xx =
      transportb _ (nat_trans_ax a _ _ f ) (b _ xx' ;; ♯ R ff)
    :=
    pr2 b _ _ f _ _ ff.

  Lemma disp_nat_trans_ax_var
        {C' C : precategory_data}
        {F' F : functor_data C' C}
        {a : nat_trans F' F}
        {D' : disp_cat_data C'}
        {D : disp_cat_data C}
        {R' : disp_functor_data F' D' D}
        {R : disp_functor_data F D' D}
        (b : disp_nat_trans a R' R)
        {x' x : C'}
        {f : x' --> x}
        {xx' : D' x'}
        {xx : D' x}
        (ff : xx' -->[ f ] xx):
    b _ xx' ;; ♯ R ff =
      transportf _ (nat_trans_ax a _ _ f) (♯ R'  ff ;; b _ xx).
  Proof.
    apply pathsinv0, transportf_pathsinv0.
    apply pathsinv0, disp_nat_trans_ax.
  Defined.


  (** identity disp_nat_trans *)

  Definition disp_nat_trans_id_ax
             {C' C : category}
             {F': functor_data C' C}
             {D' : disp_cat_data C'}
             {D : disp_cat C}
             (R' : disp_functor_data F' D' D)
    : @disp_nat_trans_axioms _ _ _ _
                             (nat_trans_id _ )
                             _ _ R' R' (λ (x : C') (xx : D' x), id_disp (R' x xx)).
  Proof.
    intros x' x f xx' xx ff;
      etrans; [ apply id_right_disp |];
      apply transportf_comp_lemma;
      apply pathsinv0.
    etrans; [apply id_left_disp |].
    unfold transportb.
    apply maponpaths_2, homset_property.
  Qed.


  Definition disp_nat_trans_id
             {C' C : category}
             {F': functor_data C' C}
             {D' : disp_cat_data C'}
             {D : disp_cat C}
             (R' : disp_functor_data F' D' D)
    : disp_nat_trans (nat_trans_id F') R' R'.
  Proof.
    use tpair.
    - intros x xx.
      apply id_disp.
    - apply disp_nat_trans_id_ax.
  Defined.

  (** composition of disp_nat_trans *)

  Definition disp_nat_trans_comp_ax
             {C' C : category}
             {F'' F' F : functor_data C' C}
             {a' : nat_trans F'' F'}
             {a : nat_trans F' F}
             {D' : disp_cat_data C'}
             {D : disp_cat C}
             {R'' : disp_functor_data F'' D' D}
             {R' : disp_functor_data F' D' D}
             {R : disp_functor_data F D' D}
             (b' : disp_nat_trans a' R'' R')
             (b : disp_nat_trans a R' R)
    : @disp_nat_trans_axioms _ _ _ _
                             (nat_trans_comp _ _ _ a' a) _ _ R'' R
                             (λ (x : C') (xx : D' x), b' x xx ;; b x xx).
  Proof.
    intros x' x f xx' xx ff;
      etrans; [ apply assoc_disp |];
      apply transportf_comp_lemma;
      apply transportf_pathsinv0; apply pathsinv0;
      rewrite (disp_nat_trans_ax b');
      etrans; [ apply mor_disp_transportf_postwhisker |];
      apply transportf_comp_lemma;
      apply pathsinv0;
      etrans; [ apply assoc_disp_var |];
      apply pathsinv0;
      apply transportf_comp_lemma;
      apply pathsinv0;
      rewrite (disp_nat_trans_ax_var b);
      rewrite mor_disp_transportf_prewhisker;
      apply transportf_comp_lemma;
      apply pathsinv0;
      etrans; [ apply assoc_disp_var |].
    apply maponpaths_2, homset_property.
  Qed.

  Definition disp_nat_trans_comp
             {C' C : category}
             {F'' F' F : functor_data C' C}
             {a' : nat_trans F'' F'}
             {a : nat_trans F' F}
             {D' : disp_cat_data C'}
             {D : disp_cat C}
             {R'' : disp_functor_data F'' D' D}
             {R' : disp_functor_data F' D' D}
             {R : disp_functor_data F D' D}
             (b' : disp_nat_trans a' R'' R')
             (b : disp_nat_trans a R' R)
    : disp_nat_trans (nat_trans_comp _ _ _ a' a) R'' R.
  Proof.
    use tpair.
    - intros x xx.
      apply (comp_disp (b' _ _ )  (b _ _ )).
    - apply disp_nat_trans_comp_ax.
  Defined.

  Definition disp_nat_trans_eq
             {C' C : category}
             {F' F : functor_data C' C}
             (a : nat_trans F' F)
             {D' : disp_cat_data C'}
             {D : disp_cat C}
             {R' : disp_functor_data F' D' D}
             {R : disp_functor_data F D' D}
             (b b' : disp_nat_trans a R' R)
    : (∏ x (xx : D' x), b x xx = b' x xx) → b = b'.
  Proof.
    intro H.
    apply subtypePath.
    { intro r.  apply isaprop_disp_nat_trans_axioms. }
    apply funextsec. intro x.
    apply funextsec.  intro xx.
    apply H.
  Qed.

End Disp_Nat_Trans.

Section Utilities.
  Lemma disp_nat_trans_transportf
        {C' C : category}
        {D' : disp_cat C'}
        {D : disp_cat C}
        (F' F : functor C' C)
        (a' a : nat_trans F' F)
        (p : a' = a )
        (FF' : disp_functor F' D' D)
        (FF : disp_functor F D' D)
        (b : disp_nat_trans a' FF' FF)
        (c' : C')
        (xx' : D' c')
    :
    pr1 (transportf (λ x, disp_nat_trans x FF' FF) p b) c' xx' =
      transportf (mor_disp (FF' c' xx') (FF c' xx'))
                 (nat_trans_eq_pointwise p _ )  (b c' xx').
  Proof.
    induction p.
    assert (XR : nat_trans_eq_pointwise (idpath a') c' = idpath _ ).
    { apply homset_property. }
    rewrite XR.
    apply idpath.
  Qed.

  Lemma disp_nat_trans_id_left
        {C' C : category}
        {D' : disp_cat C'}
        {D : disp_cat C}
        (F' F : functor C' C)
        (a : nat_trans F' F)
        (FF' : disp_functor F' D' D)
        (FF : disp_functor F D' D)
        (b : disp_nat_trans a FF' FF)
    :
    disp_nat_trans_comp (disp_nat_trans_id FF') b =
      transportb (λ f : nat_trans F' F, disp_nat_trans f FF' FF)
                 (id_left (a : [C', C] ⟦ _ , _ ⟧))
                 b.
  Proof.
    apply subtypePath.
    { intro. apply isaprop_disp_nat_trans_axioms. }
    apply funextsec; intro c'.
    apply funextsec; intro xx'.
    apply pathsinv0.
    etrans. apply disp_nat_trans_transportf.
    apply pathsinv0.
    etrans. apply id_left_disp.
    unfold transportb.
    apply maponpaths_2, homset_property.
  Qed.

  Lemma disp_nat_trans_id_right
        {C' C : category}
        {D' : disp_cat C'}
        {D : disp_cat C}
        (F' F : functor C' C)
        (a : nat_trans F' F)
        (FF' : disp_functor F' D' D)
        (FF : disp_functor F D' D)
        (b : disp_nat_trans a FF' FF)
    :
    disp_nat_trans_comp b (disp_nat_trans_id FF) =
      transportb (λ f : nat_trans F' F, disp_nat_trans f FF' FF)
                 (id_right (a : [C',C] ⟦ _ , _ ⟧))
                 b.
  Proof.
    apply subtypePath.
    { intro. apply isaprop_disp_nat_trans_axioms. }
    apply funextsec; intro c'.
    apply funextsec; intro xx'.
    apply pathsinv0.
    etrans. apply disp_nat_trans_transportf.
    apply pathsinv0.
    etrans. apply id_right_disp.
    unfold transportb.
    apply maponpaths_2, homset_property.
  Qed.

  Lemma disp_nat_trans_assoc
        {C' C : category}
        {D' : disp_cat C'}
        {D : disp_cat C}
        (x y z w : functor C' C)
        (f : nat_trans x y)
        (g : nat_trans y z)
        (h : nat_trans z w)
        (xx : disp_functor x D' D)
        (yy : disp_functor y D' D)
        (zz : disp_functor z D' D)
        (ww : disp_functor w D' D)
        (ff : disp_nat_trans f xx yy)
        (gg : disp_nat_trans g yy zz)
        (hh : disp_nat_trans h zz ww)
    :
    disp_nat_trans_comp ff (disp_nat_trans_comp gg hh) =
      transportb (λ f0 : nat_trans x w, disp_nat_trans f0 xx ww)
                 (assoc (f : [C', C] ⟦_,_⟧) g h)
                 (disp_nat_trans_comp (disp_nat_trans_comp ff gg) hh).
  Proof.
    apply subtypePath.
    { intro. apply isaprop_disp_nat_trans_axioms. }
    apply funextsec; intro c'.
    apply funextsec; intro xx'.
    apply pathsinv0.
    etrans. apply disp_nat_trans_transportf.
    apply pathsinv0.
    etrans. apply assoc_disp.
    unfold transportb.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Lemma isaset_disp_nat_trans
        {C' C : category}
        {D' : disp_cat C'}
        {D : disp_cat C}
        {x y : functor C' C}
        (f : nat_trans x y)
        (xx : disp_functor x D' D)
        (yy : disp_functor y D' D)
    :
    isaset (disp_nat_trans f xx yy).
  Proof.
    intros. simpl in *.
    apply (isofhleveltotal2 2).
    * do 2 (apply impred; intro).
      apply homsets_disp.
    * intro d.
      do 6 (apply impred; intro).
      apply hlevelntosn. apply homsets_disp.
  Qed.

  Definition pre_whisker_disp_nat_trans
             {C₁ C₂ C₃ : category}
             {F : C₁ ⟶ C₂}
             {G₁ G₂ : C₂ ⟶ C₃}
             {n : G₁ ⟹ G₂}
             {D₁ : disp_cat C₁}
             {D₂ : disp_cat C₂}
             {D₃ : disp_cat C₃}
             (FF : disp_functor F D₁ D₂)
             {GG₁ : disp_functor G₁ D₂ D₃}
             {GG₂ : disp_functor G₂ D₂ D₃}
             (nn : disp_nat_trans n GG₁ GG₂)
    : disp_nat_trans
        (pre_whisker F n)
        (disp_functor_composite FF GG₁)
        (disp_functor_composite FF GG₂).
  Proof.
    use tpair.
    - exact (λ x xx, nn (F x) (FF x xx)).
    - abstract
        (intros x y f xx yy ff ; cbn ;
         rewrite (disp_nat_trans_ax nn) ;
         apply maponpaths_2 ;
         apply C₃).
  Defined.

  Definition post_whisker_disp_nat_trans
             {C₁ C₂ C₃ : category}
             {F₁ F₂ : C₁ ⟶ C₂}
             {n : F₁ ⟹ F₂}
             {G : C₂ ⟶ C₃}
             {D₁ : disp_cat C₁}
             {D₂ : disp_cat C₂}
             {D₃ : disp_cat C₃}
             {FF₁ : disp_functor F₁ D₁ D₂}
             {FF₂ : disp_functor F₂ D₁ D₂}
             (nn : disp_nat_trans n FF₁ FF₂)
             (GG : disp_functor G D₂ D₃)
    : disp_nat_trans
        (post_whisker n G)
        (disp_functor_composite FF₁ GG)
        (disp_functor_composite FF₂ GG).
  Proof.
    use tpair.
    - exact (λ x xx, ♯ GG (nn x xx)).
    - abstract
        (intros x y f xx yy ff ; cbn ;
         rewrite <- !(disp_functor_comp_var GG) ;
         unfold transportb ;
         rewrite transport_f_f ;
         rewrite (disp_nat_trans_ax_var nn) ;
         rewrite disp_functor_transportf ;
         rewrite transport_f_f ;
         apply maponpaths_2 ;
         apply C₃).
  Defined.

End Utilities.

Section CompDispNatTransOverId.
  Context {C : category}
          {D₁ D₂ : disp_cat C}
          {FF GG HH : disp_functor (functor_identity C) D₁ D₂}
          (α : disp_nat_trans (nat_trans_id _) FF GG)
          (β : disp_nat_trans (nat_trans_id _) GG HH).

  Let disp_nat_trans_over_id_comp_data
    : disp_nat_trans_data (nat_trans_id _) FF HH.
  Proof.
    refine (λ x xx,
            transportf
              (λ z, _ -->[ z ] _)
              _
              (α x xx ;; β x xx)).
    abstract
      (cbn ;
       apply id_left).
  Defined.

  Definition disp_nat_trans_over_id_comp_axioms
    : disp_nat_trans_axioms disp_nat_trans_over_id_comp_data.
  Proof.
    intros x y f xx yy ff ; unfold disp_nat_trans_over_id_comp_data ; cbn.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (disp_nat_trans_ax α ff).
    }
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite assoc_disp_var.
    rewrite transport_f_f.
    etrans.
    {
      do 2 apply maponpaths.
      exact (disp_nat_trans_ax β ff).
    }
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition disp_nat_trans_over_id_comp
    : disp_nat_trans (nat_trans_id _) FF HH.
  Proof.
    simple refine (_ ,, _).
    - exact disp_nat_trans_over_id_comp_data.
    - exact disp_nat_trans_over_id_comp_axioms.
  Defined.
End CompDispNatTransOverId.

Section PreWhiskDispNatTransOverId.
  Context {C : category}
          {D₁ D₂ D₃ : disp_cat C}
          (FF : disp_functor (functor_identity C) D₁ D₂)
          {GG₁ GG₂ : disp_functor (functor_identity C) D₂ D₃}
          (α : disp_nat_trans (nat_trans_id _) GG₁ GG₂).

  Let disp_nat_trans_over_id_prewhisker_data
    : disp_nat_trans_data
        (nat_trans_id _)
        (disp_functor_composite FF GG₁)
        (disp_functor_composite FF GG₂)
    := λ x xx, α x (FF x xx).

  Definition disp_nat_trans_over_id_prewhisker_axioms
    : disp_nat_trans_axioms disp_nat_trans_over_id_prewhisker_data.
  Proof.
    intros x y f xx yy ff ; cbn.
    exact (disp_nat_trans_ax α (♯ FF ff)).
  Qed.

  Definition disp_nat_trans_over_id_prewhisker
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_composite FF GG₁)
        (disp_functor_composite FF GG₂).
  Proof.
    simple refine (_ ,, _).
    - exact disp_nat_trans_over_id_prewhisker_data.
    - exact disp_nat_trans_over_id_prewhisker_axioms.
  Defined.
End PreWhiskDispNatTransOverId.

Section PreWhiskDispNatTransOverId.
  Context {C : category}
          {D₁ D₂ D₃ : disp_cat C}
          {FF₁ FF₂ : disp_functor (functor_identity C) D₁ D₂}
          (GG : disp_functor (functor_identity C) D₂ D₃)
          (α : disp_nat_trans (nat_trans_id _) FF₁ FF₂).

  Let disp_nat_trans_over_id_postwhisker_data
    : disp_nat_trans_data
        (nat_trans_id _)
        (disp_functor_composite FF₁ GG)
        (disp_functor_composite FF₂ GG)
    := λ x xx, (♯ GG (α x xx)).

  Definition disp_nat_trans_over_id_postwhisker_axioms
    : disp_nat_trans_axioms disp_nat_trans_over_id_postwhisker_data.
  Proof.
    intros x y f xx yy ff ; unfold disp_nat_trans_over_id_postwhisker_data ; cbn.
    etrans.
    {
      refine (!_).
      exact (disp_functor_comp_var GG (♯ FF₁ ff) (α y yy)).
    }
    etrans.
    {
      do 2 apply maponpaths.
      exact (disp_nat_trans_ax α ff).
    }
    unfold transportb.
    rewrite disp_functor_transportf.
    rewrite transport_f_f.
    rewrite disp_functor_comp.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition disp_nat_trans_over_id_postwhisker
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_composite FF₁ GG)
        (disp_functor_composite FF₂ GG).
  Proof.
    simple refine (_ ,, _).
    - exact disp_nat_trans_over_id_postwhisker_data.
    - exact disp_nat_trans_over_id_postwhisker_axioms.
  Defined.
End PreWhiskDispNatTransOverId.

(** Pointwise inverse of displayed natural transformation *)
Section PointwiseInverse.
  Context {C C' : category}
          {F : C ⟶ C'}
          {D : disp_cat C} {D' : disp_cat C'}
          {FF : disp_functor F D D'} {GG : disp_functor F D D'}
          (αα : disp_nat_trans (nat_trans_id F) FF GG)
          (Hαα : ∏ (x : C) (xx : D x),
                 is_z_iso_disp
                   (identity_z_iso (pr1 F x))
                   (pr1 αα x xx)).

  Let pointwise_inverse_disp_nat_trans_data
    : disp_nat_trans_data (nat_trans_id F) GG FF
    := λ x xx, inv_mor_disp_from_z_iso (Hαα x xx).

  Definition pointwise_inverse_disp_nat_trans_axioms
    : disp_nat_trans_axioms pointwise_inverse_disp_nat_trans_data.
  Proof.
    intros x y f xx yy ff.
    use (precomp_with_z_iso_disp_is_inj (make_z_iso_disp _ (Hαα x xx))).
    simpl.
    refine (assoc_disp _ _ _ @ _).
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite assoc_disp.
    refine (!_).
    refine (transport_f_f _ _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (inv_mor_after_z_iso_disp (Hαα x xx)).
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply mor_disp_transportf_postwhisker.
      }
      etrans.
      {
        apply maponpaths.
        apply id_left_disp.
      }
      apply transport_f_f.
    }
    etrans.
    {
      apply transport_f_f.
    }
    assert (transportf
              (mor_disp (FF x xx) (GG y yy)) (nat_trans_ax (nat_trans_id F) x y f)
              (♯ FF ff;; pr1 αα y yy) =
            pr1 αα x xx;; ♯ GG ff)
      as X.
    {
      apply transportf_transpose_left.
      exact (pr2 αα x y f xx yy ff).
    }
    refine (!_).
    apply transportf_transpose_left.
    etrans.
    {
      apply maponpaths_2.
      exact (!X).
    }
    rewrite mor_disp_transportf_postwhisker.
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply assoc_disp_var.
        }
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply (inv_mor_after_z_iso_disp (Hαα y yy)).
          }
          etrans.
          {
            apply mor_disp_transportf_prewhisker.
          }
          etrans.
          {
            apply maponpaths.
            apply id_right_disp.
          }
          apply transport_f_f.
        }
        apply transport_f_f.
      }
      apply transport_f_f.
    }
    refine (!_).
    etrans.
    {
      apply transport_f_f.
    }
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition pointwise_inverse_disp_nat_trans
    : disp_nat_trans (nat_trans_id F) GG FF.
  Proof.
    simple refine (_ ,, _).
    - exact pointwise_inverse_disp_nat_trans_data.
    - exact pointwise_inverse_disp_nat_trans_axioms.
  Defined.
End PointwiseInverse.

Lemma pointwise_inverse_disp_nat_trans_over_id_left
      {C : category}
      {D : disp_cat C} {D' : disp_cat C}
      {FF GG : disp_functor (functor_identity _) D D'}
      (αα : disp_nat_trans (nat_trans_id _) FF GG)
      (Hαα : ∏ (x : C) (xx : D x),
             is_z_iso_disp
               (identity_z_iso x)
               (pr1 αα x xx))
  : disp_nat_trans_over_id_comp
      αα
      (pointwise_inverse_disp_nat_trans αα Hαα)
    =
    disp_nat_trans_id _.
Proof.
  use disp_nat_trans_eq.
  intros x xx ; cbn.
  etrans.
  {
    apply maponpaths.
    apply (inv_mor_after_z_iso_disp (Hαα x xx)).
  }
  unfold transportb.
  rewrite transport_f_f.
  apply transportf_set.
  apply homset_property.
Qed.

Lemma pointwise_inverse_disp_nat_trans_over_id_right
      {C : category}
      {D : disp_cat C} {D' : disp_cat C}
      {FF GG : disp_functor (functor_identity _) D D'}
      (αα : disp_nat_trans (nat_trans_id _) FF GG)
      (Hαα : ∏ (x : C) (xx : D x),
             is_z_iso_disp
               (identity_z_iso x)
               (pr1 αα x xx))
  : disp_nat_trans_over_id_comp
      (pointwise_inverse_disp_nat_trans αα Hαα)
      αα
    =
    disp_nat_trans_id _.
Proof.
  use disp_nat_trans_eq.
  intros x xx ; cbn.
  etrans.
  {
    apply maponpaths.
    apply (z_iso_disp_after_inv_mor (Hαα x xx)).
  }
  unfold transportb.
  rewrite transport_f_f.
  apply transportf_set.
  apply homset_property.
Qed.

Section disp_nat_iso.

Context {C C': category} {D: disp_cat C} {D': disp_cat C'} {F G: functor C C'}.


Definition is_disp_nat_z_iso {DF: disp_functor F D D'} {DG: disp_functor G D D'}
(α: nat_z_iso F G) (β: disp_nat_trans α DF DG) : UU
    := ∏ (c:C) (d:D c), is_z_iso_disp (nat_z_iso_pointwise_z_iso α c) (β c d).

Definition disp_nat_z_iso (DF: disp_functor F D D') (DG: disp_functor G D D')
  (α: nat_z_iso F G): UU
  := ∑ (β : disp_nat_trans α DF DG), is_disp_nat_z_iso α β.



Context {DF: disp_functor F D D'} {DG: disp_functor G D D'}.

Definition disp_nat_z_iso_to_trans {α: nat_z_iso F G}
(µ : disp_nat_z_iso DF DG α) : disp_nat_trans α DF DG
  := pr1 µ.

Coercion disp_nat_z_iso_to_trans : disp_nat_z_iso >-> disp_nat_trans.

End disp_nat_iso.

Proposition isaprop_is_disp_nat_z_iso
            {C₁ C₂ : category}
            {F G : C₁ ⟶ C₂}
            {τ : nat_z_iso F G}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            {FF : disp_functor F D₁ D₂}
            {GG : disp_functor G D₁ D₂}
            (ττ : disp_nat_trans τ FF GG)
  : isaprop (is_disp_nat_z_iso τ ττ).
Proof.
  repeat (use impred ; intro).
  apply isaprop_is_z_iso_disp.
Qed.


Section disp_nat_z_iso_inv.
Context {C C': category} {D: disp_cat C} {D': disp_cat C'} {F G: functor C C'}.
Context {DF: disp_functor F D D'} {DG: disp_functor G D D'}.

Local Open Scope mor_disp.

Lemma disp_nat_z_iso_to_trans_inv_data {α: nat_z_iso F G}
(β :disp_nat_z_iso DF DG α)
: disp_nat_trans_data (nat_z_iso_to_trans_inv α) DG DF.
Proof.
  intros c d.
  exact (pr1 (pr2 β c d)).
Defined.

Lemma disp_nat_z_iso_to_trans_inv_axioms {α: nat_z_iso F G}
(β :disp_nat_z_iso DF DG α)
: disp_nat_trans_axioms (disp_nat_z_iso_to_trans_inv_data β).
Proof.
  intros a b f x y Df.
  set (eq_nat_trans := nat_trans_ax (nat_z_iso_to_trans_inv α) a b f).
  apply (postcomp_with_z_iso_disp_is_inj _ _ (pr2 β b y)).
  etrans. apply assoc_disp_var.
  apply PartA.transportf_transpose_left.
  etrans. apply (maponpaths _ (pr1 (pr2 (pr2 β b y)))).
  etrans. apply mor_disp_transportf_prewhisker.
  apply PartA.transportf_transpose_left.
  etrans. apply id_right_disp.
  apply pathsinv0.
  etrans. apply transport_b_b.
  etrans. apply transport_b_b.
  apply PartA.transportf_transpose_left.
  etrans. apply assoc_disp_var.
  apply PartA.transportf_transpose_left.
  etrans. apply (maponpaths _ ((pr2 (pr1 β)) a b f x y Df)).
  etrans. apply mor_disp_transportf_prewhisker.
  apply PartA.transportf_transpose_left.
  etrans. apply assoc_disp.
  apply PartA.transportf_transpose_left.
  etrans. apply (maponpaths (λ Dg, Dg ;;  ♯ DG Df)
                 (pr1 (pr2 (pr2 β a x)))).
  etrans. apply mor_disp_transportf_postwhisker.
  apply PartA.transportf_transpose_left.
  etrans. apply id_left_disp.
  apply pathsinv0.
  etrans. apply transport_b_b.
  etrans. apply transport_b_b.
  etrans. apply transport_b_b.
  etrans. apply transport_b_b.
  etrans. apply transport_b_b.
  apply two_arg_paths.
  * apply uip.
    apply homset_property.
  * reflexivity.
Qed.

Definition disp_nat_z_iso_to_trans_inv {α: nat_z_iso F G}
(β :disp_nat_z_iso DF DG α)
  : disp_nat_trans (nat_z_iso_to_trans_inv α) DG DF
  := (disp_nat_z_iso_to_trans_inv_data β,, disp_nat_z_iso_to_trans_inv_axioms β).


Definition disp_nat_z_iso_inv {α: nat_z_iso F G}
(β :disp_nat_z_iso DF DG α)
  : disp_nat_z_iso  DG DF (nat_z_iso_inv α).
Proof.
  use tpair.
  - exact (disp_nat_z_iso_to_trans_inv β).
  - intros c d.
    exists (β c d).
    split.
    * exact (pr2 (pr2 (pr2 β c d))).
    * exact (pr1 (pr2 (pr2 β c d))).
Defined.

Local Open Scope cat.

Lemma nat_z_iso_iso_inv (α: nat_z_iso F G) (c:C) (d:D c)
    : α c · nat_z_iso_to_trans_inv α c = identity (F c).
Proof.
  apply (pr2 (pr2 α c)).
Qed.

Lemma disp_nat_z_iso_iso_inv {α: nat_z_iso F G}
(β: disp_nat_z_iso DF DG α) (c:C) (d:D c)
    : (β c d) ;; (disp_nat_z_iso_to_trans_inv β c d) =
      transportb (mor_disp (DF c d) (DF c d))
        (nat_z_iso_iso_inv α c d)
        (id_disp (DF c d)).
Proof.
  etrans. apply (pr2 (pr2 (pr2 β c d))).
  apply two_arg_paths.
  - apply uip.
    apply homset_property.
  - reflexivity.
Qed.

Lemma nat_z_iso_inv_iso (α: nat_z_iso F G) (c:C) (d:D c)
    : nat_z_iso_to_trans_inv α c · α c = identity (G c).
Proof.
  apply (pr2 (pr2 α c)).
Qed.

Lemma disp_nat_z_iso_inv_iso {α: nat_z_iso F G}
(β: disp_nat_z_iso DF DG α) (c:C) (d:D c)
    : (disp_nat_z_iso_to_trans_inv β c d) ;; (β c d) =
      transportb (mor_disp (DG c d) (DG c d))
        (nat_z_iso_inv_iso α c d)
        (id_disp (DG c d)).
Proof.
  etrans. apply (pr1 (pr2 (pr2 β c d))).
  apply two_arg_paths.
  - apply uip.
    apply homset_property.
  - reflexivity.
Qed.

Local Close Scope cat.
End disp_nat_z_iso_inv.
Local Close Scope mor_disp.



Section disp_nat_z_iso_comp.
Context {C C': category} {D: disp_cat C} {D': disp_cat C'} {F G H: functor C C'}.
Context {DF: disp_functor F D D'} {DG: disp_functor G D D'} {DH: disp_functor H D D'}.


Lemma disp_nat_trans_comp_inv {α: nat_z_iso F G} {α': nat_z_iso G H}
(β: disp_nat_z_iso DF DG α) (β': disp_nat_z_iso DG DH α') (c:C) (d:D c)
  : is_disp_inverse (nat_z_iso_pointwise_z_iso (nat_z_iso_comp α α') c)
        (disp_nat_trans_comp β β' c d)
        (disp_nat_trans_comp (disp_nat_z_iso_inv β') (disp_nat_z_iso_inv β) c d).
Proof.
  split.
  - etrans. apply assoc_disp.
    apply PartA.transportb_transpose_left.
    etrans. apply assoc4_disp.
    apply PartA.transportb_transpose_left.
    etrans. apply id_conjugation_disp.
    * apply disp_nat_z_iso_inv_iso.
    * apply disp_nat_z_iso_inv_iso.
    * unfold transportb.
      repeat rewrite transport_f_f.
      apply two_arg_paths.
      -- apply uip.
         apply homset_property.
      -- reflexivity.
  - etrans. apply assoc_disp.
     apply PartA.transportb_transpose_left.
     etrans. apply assoc4_disp.
     apply PartA.transportb_transpose_left.
     etrans. apply id_conjugation_disp.
     * apply disp_nat_z_iso_iso_inv.
     * apply disp_nat_z_iso_iso_inv.
     * unfold transportb.
       repeat rewrite transport_f_f.
       apply two_arg_paths.
       -- apply uip.
          apply homset_property.
       -- reflexivity.
Qed.

Definition disp_nat_z_iso_comp {α: nat_z_iso F G} {α': nat_z_iso G H}
(β: disp_nat_z_iso DF DG α) (β': disp_nat_z_iso DG DH α')
  : disp_nat_z_iso DF DH (nat_z_iso_comp α α') .
Proof.
  exists (disp_nat_trans_comp β β').
  intros c d.
  exists (disp_nat_trans_comp (disp_nat_z_iso_inv β') (disp_nat_z_iso_inv β) c d).
  apply disp_nat_trans_comp_inv.
Defined.

End disp_nat_z_iso_comp.
