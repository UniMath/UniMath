(*******************************************************************

 Results on the reindexing displayed category

 In this file, we collect results on the displayed category obtained
 by reindexing.

 Content:
 1. Transport lemma
 2. Characterization of displayed isomorphisms
 3. Univalence
 4. Characterization of cartesian morphisms
 5. Cleaving
 6. Functor from reindexing
 7. Mapping property

 ********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Local Open Scope cat.

(**
 1. Transport lemma
 *)
Definition transportf_reindex
           {C' C : category}
           {D : disp_cat C}
           {F : C' ⟶ C}
           {x y : C'}
           {xx : D(F x)} {yy : D(F y)}
           {f g : x --> y}
           (p : f = g)
           (ff : xx -->[ (# F)%Cat f] yy)
  : transportf
      (@mor_disp
         C'
         (reindex_disp_cat F D)
         _ _
         xx yy)
      p
      ff
    =
    transportf
      (@mor_disp
         C
         D
         _ _
         xx yy)
      (maponpaths (#F)%Cat p)
      ff.
Proof.
  induction p ; apply idpath.
Qed.

(**
 2. Characterization of displayed isomorphisms
 *)
Definition iso_disp_to_iso_disp_reindex
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D : disp_cat C₂}
           {x : C₁}
           {xx yy : D (F x)}
  : iso_disp (identity_iso (F x)) xx yy
    →
    @iso_disp
       _
       (reindex_disp_cat F D)
       _
       _
       (identity_iso x)
       xx
       yy.
Proof.
  intros i.
  use make_iso_disp.
  - exact (transportb
             (λ z, _ -->[ z ] _)
             (functor_id _ _)
             i).
  - simple refine (_ ,, _ ,, _).
    + exact (transportb
               (λ z, _ -->[ z ] _)
               (functor_id _ _)
               (inv_mor_disp_from_iso i)).
    + abstract
        (cbn ;
         unfold transportb ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite transport_f_f ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite transport_f_f ;
         refine (maponpaths (λ z, transportf _ _ z) (iso_disp_after_inv_mor i) @ _) ;
         unfold transportb ;
         rewrite !transport_f_f ;
         refine (!_) ;
         etrans ; [ apply transportf_reindex | ] ;
         rewrite transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
    + abstract
        (cbn ;
         unfold transportb ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite transport_f_f ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite transport_f_f ;
         refine (maponpaths (λ z, transportf _ _ z) (inv_mor_after_iso_disp i) @ _) ;
         unfold transportb ;
         rewrite !transport_f_f ;
         refine (!_) ;
         etrans ; [ apply transportf_reindex | ] ;
         rewrite transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
Defined.

Definition iso_disp_reindex_to_iso_disp
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D : disp_cat C₂}
           {x : C₁}
           {xx yy : D (F x)}
  : @iso_disp
       _
       (reindex_disp_cat F D)
       _
       _
       (identity_iso x)
       xx
       yy
    →
    iso_disp (identity_iso (F x)) xx yy.
Proof.
  intros i.
  use make_iso_disp.
  - exact (transportf
               (λ z, _ -->[ z ] _)
               (functor_id _ _)
               i).
  - simple refine (_ ,, _ ,, _).
    + exact (transportf
               (λ z, _ -->[ z ] _)
               (functor_id _ _)
               (inv_mor_disp_from_iso i)).
    + abstract
        (unfold transportb ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite !transport_f_f ;
         etrans ;
         [ apply maponpaths ;
           pose (iso_disp_after_inv_mor i) as p ;
           cbn in p ;
           exact (transportf_transpose_right p)
         | ] ;
         unfold transportb ;
         rewrite !transport_f_f ;
         etrans ;
         [ apply maponpaths ;
           apply transportf_reindex
         | ] ;
         rewrite !transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
    + abstract
        (unfold transportb ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite !transport_f_f ;
         etrans ;
         [ apply maponpaths ;
           pose (inv_mor_after_iso_disp i) as p ;
           cbn in p ;
           exact (transportf_transpose_right p)
         | ] ;
         unfold transportb ;
         rewrite !transport_f_f ;
         etrans ;
         [ apply maponpaths ;
           apply transportf_reindex
         | ] ;
         rewrite !transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
Defined.

Definition iso_disp_weq_iso_disp_reindex
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D : disp_cat C₂}
           {x : C₁}
           (xx yy : D (F x))
  : iso_disp (identity_iso (F x)) xx yy
    ≃
    @iso_disp
       _
       (reindex_disp_cat F D)
       _
       _
       (identity_iso x)
       xx
       yy.
Proof.
  use make_weq.
  - exact iso_disp_to_iso_disp_reindex.
  - use gradth.
    + exact iso_disp_reindex_to_iso_disp.
    + abstract
        (intros i ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_disp | ] ;
         cbn ;
         apply transportfbinv).
    + abstract
        (intros i ;
         use subtypePath ; [ intro ; apply isaprop_is_iso_disp | ] ;
         cbn ;
         apply transportbfinv).
Defined.

(**
 3. The univalence
 *)
Definition is_univalent_reindex_disp_cat
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (D : disp_cat C₂)
           (HD : is_univalent_disp D)
  : is_univalent_disp (reindex_disp_cat F D).
Proof.
  intros x y p xx yy.
  induction p.
  use weqhomot.
  - exact (iso_disp_weq_iso_disp_reindex xx yy
           ∘ make_weq
               (@idtoiso_disp _ D _ _ (idpath _) xx yy)
               (HD _ _ _ xx yy))%weq.
  - abstract
      (intros p ;
       induction p ;
       use subtypePath ; [ intro ; apply isaprop_is_iso_disp | ] ;
       apply idpath).
Defined.

Definition is_cartesian_in_reindex_disp_cat
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (D : disp_cat C₂)
           {x y : C₁}
           {f : x --> y}
           {xx : D (F x)}
           {yy : D (F y)}
           (ff : xx -->[ #F f ] yy)
           (Hff : is_cartesian ff)
  : @is_cartesian _ (reindex_disp_cat F D) y x f yy xx ff.
Proof.
  intros z g zz gg ; cbn in *.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply D | ] ;
       use (cartesian_factorisation_unique Hff) ;
       rewrite (transportf_transpose_right (pr2 φ₁)) ;
       rewrite (transportf_transpose_right (pr2 φ₂)) ;
       apply idpath).
  - simple refine (_ ,, _).
    + refine (cartesian_factorisation
                Hff
                (#F g)
                (transportf (λ z, _ -->[ z ] _) _ gg)).
      abstract
        (apply functor_comp).
    + abstract
        (cbn ;
         rewrite cartesian_factorisation_commutes ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply homset_property).
Defined.

Section IsCartesianFromReindexDispCat.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂)
          (D : disp_cat C₂)
          (HD : cleaving D)
          {x y : C₁}
          {f : x --> y}
          {xx : D (F x)}
          {yy : D (F y)}
          (ff : xx -->[ #F f ] yy)
          (Hff : @is_cartesian _ (reindex_disp_cat F D) y x f yy xx ff).

  Let ℓ : cartesian_lift yy (# F f) := HD (F y) (F x) (#F f) yy.
  Let m : xx -->[ identity (F x)] pr1 ℓ := cartesian_factorisation
                                    ℓ
                                    (identity _)
                                    (transportb
                                       (λ z, _ -->[ z ] _)
                                       (id_left _)
                                       ff).
  Let minv' : pr1 ℓ -->[ # F (identity x · f)] yy
    := transportb
         _
         (maponpaths (λ z, #F z) (id_left _))
         (pr12 ℓ).
  Let minv : pr1 ℓ -->[ identity (F x)] xx
    := transportf
         _
         (functor_id _ _)
         (cartesian_factorisation Hff _ minv').

  Local Lemma minv_m
    : (minv ;; m)%mor_disp
      =
      transportb
        (λ z, _ -->[ z ] _)
        (iso_after_iso_inv (make_iso _ (identity_is_iso C₂ (F x))))
        (id_disp ℓ).
  Proof.
    unfold minv, m.
    unfold transportb.
    use (cartesian_factorisation_unique ℓ).
    rewrite !mor_disp_transportf_postwhisker.
    rewrite id_left_disp.
    unfold transportb.
    rewrite transport_f_f.
    unfold m.
    rewrite assoc_disp_var.
    rewrite cartesian_factorisation_commutes.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    etrans.
    {
      apply maponpaths.
      pose (cartesian_factorisation_commutes
              Hff
              (identity x)
              (transportb
                 (mor_disp (pr1 ℓ) yy)
                 (maponpaths (λ z, _) (id_left f))
                 (pr12 ℓ))).
      cbn in p.
      apply (transportf_transpose_right p).
    }
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Local Lemma m_minv
    : (m ;; minv)%mor_disp
      =
      transportb
        (λ z, _ -->[ z ] _)
        (iso_inv_after_iso (make_iso _ (identity_is_iso C₂ (F x))))
        (id_disp xx).
  Proof.
    cbn.
    unfold m, minv.
    rewrite mor_disp_transportf_prewhisker.
    pose (cartesian_factorisation
            ℓ
            (identity _)
            (transportb
               (λ z, xx -->[ z] yy)
               (id_left ((# F)%Cat f))
               ff)
          ;;
          cartesian_factorisation
            Hff
            (identity _)
            (transportb
               (mor_disp (pr1 ℓ) yy)
               (maponpaths (λ z, (# F)%Cat z) (id_left f))
               (pr12 ℓ)))%mor_disp
      as m'.
    pose (@cartesian_factorisation_unique
            _ _ _ _ _ _ _ _
            Hff
            _
            (identity _)
            xx
            (transportf
               _
               (id_left _)
               m')
            (id_disp _))
      as p.
    cbn in p ; unfold transportb in p.
    simple refine (_
                   @ maponpaths
                       (transportf (λ z, _ -->[ z ] _) (functor_id _ _ @ !(id_left _)))
                       (p _)
                   @ _).
    - rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - cbn.
      unfold transportb.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      unfold m'.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        pose (cartesian_factorisation_commutes
                Hff
                (identity _)
                (transportb
                   (mor_disp (pr1 ℓ) yy)
                   (maponpaths (λ z : C₁ ⟦ x, y ⟧, (# F)%Cat z) (id_left f))
                   (pr12 ℓ)))
          as q.
        cbn in q.
        exact (transportb_transpose_right q).
      }
      unfold transportb.
      rewrite transport_f_f.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite transport_f_f.
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition is_cartesian_from_reindex_disp_cat
    : is_cartesian ff.
  Proof.
    use (disp_iso_to_is_cartesian _ ℓ).
    - apply identity.
    - apply identity_is_iso.
    - apply id_left.
    - exact m.
    - simple refine (_ ,, _ ,, _).
      + exact minv.
      + exact minv_m.
      + exact m_minv.
    - apply cartesian_factorisation_commutes.
  Defined.
End IsCartesianFromReindexDispCat.

(**
 5. Cleaving
 *)
Definition cleaving_reindex_disp_cat
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (D : disp_cat C₂)
           (HD : cleaving D)
  : cleaving (reindex_disp_cat F D).
Proof.
  intros x y f d.
  pose (HD (F x) (F y) (#F f) d) as lift.
  simple refine (_ ,, (_ ,, _)).
  - exact (pr1 lift).
  - exact (pr12 lift).
  - simpl.
    apply is_cartesian_in_reindex_disp_cat.
    exact (pr22 lift).
Defined.

(**
 6. Functor from reindexing
 *)
Definition reindex_disp_cat_disp_functor_data
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (D : disp_cat C₂)
  : disp_functor_data F (reindex_disp_cat F D) D.
Proof.
  simple refine (_ ,, _).
  - exact (λ _ xx, xx).
  - exact (λ _ _ _ _ _ ff, ff).
Defined.

Definition reindex_disp_cat_disp_functor_axioms
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (D : disp_cat C₂)
  : disp_functor_axioms (reindex_disp_cat_disp_functor_data F D).
Proof.
  split ; cbn ; intros ; apply idpath.
Qed.

Definition reindex_disp_cat_disp_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (D : disp_cat C₂)
  : disp_functor F (reindex_disp_cat F D) D.
Proof.
  simple refine (_ ,, _).
  - exact (reindex_disp_cat_disp_functor_data F D).
  - exact (reindex_disp_cat_disp_functor_axioms F D).
Defined.

Definition is_cartesian_reindex_disp_cat_disp_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (D : disp_cat C₂)
           (HD : cleaving D)
  : is_cartesian_disp_functor (reindex_disp_cat_disp_functor F D).
Proof.
  intros x y f xx yy ff Hff.
  apply is_cartesian_from_reindex_disp_cat.
  - exact HD.
  - exact Hff.
Defined.

(**
 7. Mapping property
 *)
Definition lift_functor_into_reindex_data
           {C₁ C₂ C₃ : category}
           {D₁ : disp_cat C₁}
           {D₃ : disp_cat C₃}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           (FF : disp_functor (F₁ ∙ F₂) D₁ D₃)
  : disp_functor_data F₁ D₁ (reindex_disp_cat F₂ D₃).
Proof.
  simple refine (_ ,, _).
  - exact (λ x xx, FF x xx).
  - exact (λ x y xx yy f ff, #FF ff)%mor_disp.
Defined.

Definition lift_functor_into_reindex_axioms
           {C₁ C₂ C₃ : category}
           {D₁ : disp_cat C₁}
           {D₃ : disp_cat C₃}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           (FF : disp_functor (F₁ ∙ F₂) D₁ D₃)
  : disp_functor_axioms (lift_functor_into_reindex_data FF).
Proof.
  split.
  - intros x xx ; cbn.
    unfold transportb.
    refine (!_).
    etrans.
    {
      apply transportf_reindex.
    }
    rewrite transport_f_f.
    refine (!_).
    rewrite (disp_functor_id FF).
    unfold transportb.
    apply maponpaths_2.
    apply homset_property.
  - intros x y z xx yy zz f g ff gg ; cbn.
    unfold transportb.
    refine (!_).
    etrans.
    {
      apply transportf_reindex.
    }
    rewrite transport_f_f.
    rewrite (disp_functor_comp FF).
    unfold transportb.
    apply maponpaths_2.
    apply homset_property.
Qed.

Definition lift_functor_into_reindex
           {C₁ C₂ C₃ : category}
           {D₁ : disp_cat C₁}
           {D₃ : disp_cat C₃}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           (FF : disp_functor (F₁ ∙ F₂) D₁ D₃)
  : disp_functor F₁ D₁ (reindex_disp_cat F₂ D₃).
Proof.
  simple refine (_ ,, _).
  - exact (lift_functor_into_reindex_data FF).
  - exact (lift_functor_into_reindex_axioms FF).
Defined.

Definition is_cartesian_lift_functor_into_reindex
           {C₁ C₂ C₃ : category}
           {D₁ : disp_cat C₁}
           {D₃ : disp_cat C₃}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           {FF : disp_functor (F₁ ∙ F₂) D₁ D₃}
           (HFF : is_cartesian_disp_functor FF)
  : is_cartesian_disp_functor (lift_functor_into_reindex FF).
Proof.
  intros x y f xx yy ff Hff.
  apply is_cartesian_in_reindex_disp_cat.
  apply HFF.
  exact Hff.
Defined.

Definition lift_functor_into_reindex_commute_data
           {C₁ C₂ C₃ : category}
           {D₁ : disp_cat C₁}
           {D₃ : disp_cat C₃}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           (FF : disp_functor (F₁ ∙ F₂) D₁ D₃)
  : disp_nat_trans_data
      (nat_trans_id _)
      (disp_functor_composite
         (lift_functor_into_reindex FF)
         (reindex_disp_cat_disp_functor _ _))
      FF
  := λ x xx, id_disp _.

Definition lift_functor_into_reindex_commute_axioms
           {C₁ C₂ C₃ : category}
           {D₁ : disp_cat C₁}
           {D₃ : disp_cat C₃}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           (FF : disp_functor (F₁ ∙ F₂) D₁ D₃)
  : disp_nat_trans_axioms (lift_functor_into_reindex_commute_data FF).
Proof.
  intros x y f xx yy ff ; unfold lift_functor_into_reindex_commute_data ; cbn.
  rewrite id_left_disp, id_right_disp.
  unfold transportb.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Definition lift_functor_into_reindex_commute
           {C₁ C₂ C₃ : category}
           {D₁ : disp_cat C₁}
           {D₃ : disp_cat C₃}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           (FF : disp_functor (F₁ ∙ F₂) D₁ D₃)
  : disp_nat_trans
      (nat_trans_id _)
      (disp_functor_composite
         (lift_functor_into_reindex FF)
         (reindex_disp_cat_disp_functor _ _))
      FF.
Proof.
  simple refine (_ ,, _).
  - exact (lift_functor_into_reindex_commute_data FF).
  - exact (lift_functor_into_reindex_commute_axioms FF).
Defined.

Definition lift_functor_into_reindex_disp_nat_trans_data
           {C₁ C₂ C₃ : category}
           {D₁ : disp_cat C₁}
           {D₃ : disp_cat C₃}
           {F₁ F₁' : C₁ ⟶ C₂}
           {α : F₁ ⟹ F₁'}
           {F₂ : C₂ ⟶ C₃}
           {FF₁ : disp_functor (F₁ ∙ F₂) D₁ D₃}
           {FF₂ : disp_functor (F₁' ∙ F₂) D₁ D₃}
           (αα : disp_nat_trans (post_whisker α _) FF₁ FF₂)
  : disp_nat_trans_data
      α
      (lift_functor_into_reindex_data FF₁)
      (lift_functor_into_reindex_data FF₂)
  := λ x xx, αα x xx.

Definition lift_functor_into_reindex_disp_nat_trans_axioms
           {C₁ C₂ C₃ : category}
           {D₁ : disp_cat C₁}
           {D₃ : disp_cat C₃}
           {F₁ F₁' : C₁ ⟶ C₂}
           {α : F₁ ⟹ F₁'}
           {F₂ : C₂ ⟶ C₃}
           {FF₁ : disp_functor (F₁ ∙ F₂) D₁ D₃}
           {FF₂ : disp_functor (F₁' ∙ F₂) D₁ D₃}
           (αα : disp_nat_trans (post_whisker α _) FF₁ FF₂)
  : disp_nat_trans_axioms (lift_functor_into_reindex_disp_nat_trans_data αα).
Proof.
  intros x y f xx yy ff ; cbn ; unfold lift_functor_into_reindex_disp_nat_trans_data.
  etrans.
  {
    apply maponpaths.
    exact (disp_nat_trans_ax αα ff).
  }
  unfold transportb.
  rewrite !transport_f_f.
  refine (!_).
  etrans.
  {
    apply transportf_reindex.
  }
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Definition lift_functor_into_reindex_disp_nat_trans
           {C₁ C₂ C₃ : category}
           {D₁ : disp_cat C₁}
           {D₃ : disp_cat C₃}
           {F₁ F₁' : C₁ ⟶ C₂}
           {α : F₁ ⟹ F₁'}
           {F₂ : C₂ ⟶ C₃}
           {FF₁ : disp_functor (F₁ ∙ F₂) D₁ D₃}
           {FF₂ : disp_functor (F₁' ∙ F₂) D₁ D₃}
           (αα : disp_nat_trans (post_whisker α _) FF₁ FF₂)
  : disp_nat_trans
      α
      (lift_functor_into_reindex_data FF₁)
      (lift_functor_into_reindex_data FF₂).
Proof.
  simple refine (_ ,, _).
  - exact (lift_functor_into_reindex_disp_nat_trans_data αα).
  - exact (lift_functor_into_reindex_disp_nat_trans_axioms αα).
Defined.
