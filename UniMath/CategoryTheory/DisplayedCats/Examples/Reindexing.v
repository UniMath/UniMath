(*******************************************************************

 Results on the reindexing displayed category

 In this file, we collect results on the displayed category obtained
 by reindexing.

 Content:
 1. Transport lemma
 2. Characterization of displayed isomorphisms
 3. Univalence
 4. Characterization of cartesian and opcartesian morphisms
 5. Cleaving
 6. Functor from reindexing
 7. Mapping property
 8. Reindexing along opfibrations gives pullbacks
 9. Reindexing of functors
 10. Reindexing of natural transformations
 11. Pseudofunctoriality of reindexing

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
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Local Open Scope cat.

(** ** Reindexing *)

Section Reindexing.
  Local Open Scope mor_disp.
  Local Open Scope cat.

  Context {C' C : category}
          (F : functor C' C)
          (D : disp_cat C).

  Definition reindex_disp_cat_ob_mor : disp_cat_ob_mor C'.
  Proof.
    exists (λ c, D (F c)).
    intros x y xx yy f. exact (xx -->[# F f] yy).
  Defined.

  Definition reindex_disp_cat_id_comp : disp_cat_id_comp C' reindex_disp_cat_ob_mor.
  Proof.
    apply tpair.
    - simpl; intros x xx.
      refine (transportb _ _ _).
      apply functor_id. apply id_disp.
    - simpl; intros x y z f g xx yy zz ff gg.
      refine (transportb _ _ _).
      apply functor_comp. exact (ff ;; gg).
  Defined.

  Definition reindex_disp_cat_data : disp_cat_data C'
    := (_ ,, reindex_disp_cat_id_comp).

  Definition reindex_disp_cat_axioms : disp_cat_axioms C' reindex_disp_cat_data.
  Proof.
    repeat apply tpair; cbn.
    - intros x y f xx yy ff.
      eapply pathscomp0. apply maponpaths, mor_disp_transportf_postwhisker.
      eapply pathscomp0. apply transport_b_f.
      eapply pathscomp0. apply maponpaths, id_left_disp.
      eapply pathscomp0. apply transport_f_b.
      eapply pathscomp0. 2: apply @pathsinv0, (functtransportb (# F)).
      unfold transportb; apply maponpaths_2, homset_property.
    - intros x y f xx yy ff.
      eapply pathscomp0. apply maponpaths, mor_disp_transportf_prewhisker.
      eapply pathscomp0. apply transport_b_f.
      eapply pathscomp0. apply maponpaths, id_right_disp.
      eapply pathscomp0. apply transport_f_b.
      eapply pathscomp0. 2: apply @pathsinv0, (functtransportb (# F)).
      unfold transportb; apply maponpaths_2, homset_property.
    - intros x y z w f g h xx yy zz ww ff gg hh.
      eapply pathscomp0. apply maponpaths, mor_disp_transportf_prewhisker.
      eapply pathscomp0. apply transport_b_f.
      eapply pathscomp0. apply maponpaths, assoc_disp.
      eapply pathscomp0. apply transport_f_b.
      apply pathsinv0.
      eapply pathscomp0. apply (functtransportb (# F)).
      eapply pathscomp0. apply transport_b_b.
      eapply pathscomp0. apply maponpaths, mor_disp_transportf_postwhisker.
      eapply pathscomp0. apply transport_b_f.
      unfold transportb; apply maponpaths_2, homset_property.
    - intros; apply homsets_disp.
  Qed.

  Definition reindex_disp_cat : disp_cat C'
    := (_ ,, reindex_disp_cat_axioms).

  (** ** A functor of displayed categories from reindexing *)

  Definition reindex_disp_functor : disp_functor F reindex_disp_cat D.
  Proof.
    use tpair.
    - use tpair.
      + cbn. intro x. exact (idfun _ ).
      + cbn. intros x x' d d' f.  exact (idfun _ ).
    - abstract (
          split;
          [intros; apply idpath |];
          intros; apply idpath
        ).
  Defined.
End Reindexing.

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
Definition z_iso_disp_to_z_iso_disp_reindex
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D : disp_cat C₂}
           {x : C₁}
           {xx yy : D (F x)}
  : z_iso_disp (identity_z_iso (F x)) xx yy
    →
    @z_iso_disp
       _
       (reindex_disp_cat F D)
       _
       _
       (identity_z_iso x)
       xx
       yy.
Proof.
  intros i.
  use make_z_iso_disp.
  - exact (transportb
             (λ z, _ -->[ z ] _)
             (functor_id _ _)
             i).
  - simple refine (_ ,, _ ,, _).
    + exact (transportb
               (λ z, _ -->[ z ] _)
               (functor_id _ _)
               (inv_mor_disp_from_z_iso i)).
    + abstract
        (cbn ;
         unfold transportb ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite transport_f_f ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite transport_f_f ;
         refine (maponpaths (λ z, transportf _ _ z) (z_iso_disp_after_inv_mor i) @ _) ;
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
         refine (maponpaths (λ z, transportf _ _ z) (inv_mor_after_z_iso_disp i) @ _) ;
         unfold transportb ;
         rewrite !transport_f_f ;
         refine (!_) ;
         etrans ; [ apply transportf_reindex | ] ;
         rewrite transport_f_f ;
         apply maponpaths_2 ;
         apply homset_property).
Defined.

Definition z_iso_disp_reindex_to_z_iso_disp
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D : disp_cat C₂}
           {x : C₁}
           {xx yy : D (F x)}
  : @z_iso_disp
       _
       (reindex_disp_cat F D)
       _
       _
       (identity_z_iso x)
       xx
       yy
    →
    z_iso_disp (identity_z_iso (F x)) xx yy.
Proof.
  intros i.
  use make_z_iso_disp.
  - exact (transportf
               (λ z, _ -->[ z ] _)
               (functor_id _ _)
               i).
  - simple refine (_ ,, _ ,, _).
    + exact (transportf
               (λ z, _ -->[ z ] _)
               (functor_id _ _)
               (inv_mor_disp_from_z_iso i)).
    + abstract
        (unfold transportb ;
         rewrite mor_disp_transportf_prewhisker ;
         rewrite mor_disp_transportf_postwhisker ;
         rewrite !transport_f_f ;
         etrans ;
         [ apply maponpaths ;
           pose (z_iso_disp_after_inv_mor i) as p ;
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
           pose (inv_mor_after_z_iso_disp i) as p ;
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

Definition z_iso_disp_weq_z_iso_disp_reindex
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D : disp_cat C₂}
           {x : C₁}
           (xx yy : D (F x))
  : z_iso_disp (identity_z_iso (F x)) xx yy
    ≃
    @z_iso_disp
       _
       (reindex_disp_cat F D)
       _
       _
       (identity_z_iso x)
       xx
       yy.
Proof.
  use make_weq.
  - exact z_iso_disp_to_z_iso_disp_reindex.
  - use gradth.
    + exact z_iso_disp_reindex_to_z_iso_disp.
    + abstract
        (intros i ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         cbn ;
         apply transportfbinv).
    + abstract
        (intros i ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
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
  - exact (z_iso_disp_weq_z_iso_disp_reindex xx yy
           ∘ make_weq
               (@idtoiso_disp _ D _ _ (idpath _) xx yy)
               (HD _ _ _ xx yy))%weq.
  - abstract
      (intros p ;
       induction p ;
       use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
       apply idpath).
Defined.

Definition univalent_reindex_cat
           {C₁ C₂ : univalent_category}
           (F : C₁ ⟶ C₂)
           (D : disp_univalent_category C₂)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (total_category (reindex_disp_cat F (pr1 D))).
  - use is_univalent_total_category.
    + exact (pr2 C₁).
    + exact (is_univalent_reindex_disp_cat F _ (pr2 D)).
Defined.

(**
 4. Characterization of cartesian and opcartesian morphisms
 *)
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
        (z_iso_after_z_iso_inv (make_z_iso' _ (identity_is_z_iso (F x))))
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
        (z_iso_inv_after_z_iso (make_z_iso' _ (identity_is_z_iso (F x))))
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
    use (z_iso_disp_to_is_cartesian _ ℓ).
    - apply identity.
    - apply identity_is_z_iso.
    - apply id_left.
    - exact m.
    - simple refine (_ ,, _ ,, _).
      + exact minv.
      + exact minv_m.
      + exact m_minv.
    - apply cartesian_factorisation_commutes.
  Defined.
End IsCartesianFromReindexDispCat.

Definition is_opcartesian_in_reindex_disp_cat
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (D : disp_cat C₂)
           {x y : C₁}
           {f : x --> y}
           {xx : D (F x)}
           {yy : D (F y)}
           (ff : xx -->[ #F f ] yy)
           (Hff : is_opcartesian ff)
  : @is_opcartesian _ (reindex_disp_cat F D) x y f xx yy ff.
Proof.
  intros z zz g gg ; cbn in *.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply D | ] ;
       use (opcartesian_factorisation_unique Hff) ;
       rewrite (transportf_transpose_right (pr2 φ₁)) ;
       rewrite (transportf_transpose_right (pr2 φ₂)) ;
       apply idpath).
  - simple refine (_ ,, _).
    + refine (opcartesian_factorisation
                Hff
                (#F g)
                (transportf (λ z, _ -->[ z ] _) _ gg)).
      abstract
        (apply functor_comp).
    + abstract
        (cbn ;
         rewrite opcartesian_factorisation_commutes ;
         unfold transportb ;
         rewrite transport_f_f ;
         apply transportf_set ;
         apply homset_property).
Defined.

Section IsOpCartesianFromReindexDispCat.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂)
          (D : disp_cat C₂)
          (HD : opcleaving D)
          {x y : C₁}
          {f : x --> y}
          {xx : D (F x)}
          {yy : D (F y)}
          (ff : xx -->[ #F f ] yy)
          (Hff : @is_opcartesian _ (reindex_disp_cat F D) x y f xx yy ff).

  Let ℓ : opcartesian_lift _ xx (# F f) := HD (F x) (F y) xx (#F f).
  Let m : pr1 ℓ -->[ identity (F y)] yy
    := opcartesian_factorisation
         (mor_of_opcartesian_lift_is_opcartesian _ ℓ)
         (identity _)
         (transportb
            (λ z, _ -->[ z ] _)
            (id_right _)
            ff).
  Let minv' : xx -->[ # F (f · identity y) ] pr1 ℓ
    := transportb
         _
         (maponpaths (λ z, #F z) (id_right _))
         (pr12 ℓ).
  Let minv : yy -->[ identity (F y)] pr1 ℓ
    := transportf
         _
         (functor_id _ _)
         (opcartesian_factorisation Hff _ minv').

  Local Lemma op_minv_m
    : (minv ;; m)%mor_disp
      =
      transportb
        (λ z, _ -->[ z ] _)
        (z_iso_after_z_iso_inv (make_z_iso' _ (identity_is_z_iso _)))
        (id_disp _).
  Proof.
    pose (p := @opcartesian_factorisation_unique
                 _ _ _ _ _ _ _ _
                 Hff
                 _
                 yy
                 (identity _)
                 (transportf
                    (λ z, _ -->[ z ] _)
                    (id_left _ @ !(functor_id _ _))
                    (minv ;; m)%mor_disp)
                 (id_disp _)).
    simple refine (_
            @ maponpaths
                (transportf (λ z, _ -->[ z ] _) (functor_id _ _ @ !(id_left _)))
                (p _)
            @ _) ; clear p.
    - rewrite transport_f_f.
      refine (!_).
      apply transportf_set.
      apply homset_property.
    - rewrite id_right_disp.
      cbn.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      unfold minv.
      rewrite assoc_disp.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        pose (opcartesian_factorisation_commutes Hff (identity _) minv') as p.
        cbn in p.
        exact (transportf_transpose_right p).
      }
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      unfold minv', m.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite opcartesian_factorisation_commutes.
      rewrite transport_f_f.
      refine (_ @ !(transportf_reindex _ ff)).
      apply maponpaths_2.
      apply homset_property.
    - cbn.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Local Lemma op_m_minv
    : (m ;; minv)%mor_disp
      =
      transportb
        (λ z, _ -->[ z ] _)
        (z_iso_inv_after_z_iso (make_z_iso' _ (identity_is_z_iso _)))
        (id_disp _).
  Proof.
    cbn.
    unfold m, minv.
    use (opcartesian_factorisation_unique
           (mor_of_opcartesian_lift_is_opcartesian _ ℓ)).
    unfold transportb.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite assoc_disp.
    rewrite opcartesian_factorisation_commutes.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    rewrite id_right_disp.
    unfold transportb.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      pose (opcartesian_factorisation_commutes Hff (identity _) minv') as p.
      cbn in p.
      apply (transportf_transpose_right p).
    }
    rewrite transport_f_f.
    unfold minv'.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Local Lemma is_opcartesian_from_reindex_disp_cat_help
    : ff
      =
      transportf
        (λ z, _ -->[ z ] _)
        (id_right _)
        (opcleaving_mor HD _ _ ;; m)%mor_disp.
  Proof.
    unfold m.
    rewrite opcartesian_factorisation_commutes.
    rewrite transportfbinv.
    apply idpath.
  Qed.

  Definition is_opcartesian_from_reindex_disp_cat
    : is_opcartesian ff.
  Proof.

    refine (transportb
              is_opcartesian
              is_opcartesian_from_reindex_disp_cat_help
              _).
    apply is_opcartesian_transportf.
    use is_opcartesian_comp_disp.
    - apply mor_of_opcartesian_lift_is_opcartesian.
    - use is_opcartesian_z_iso_disp.
      + apply identity_is_z_iso.
      + simple refine (_ ,, _ ,, _).
        * exact minv.
        * apply op_minv_m.
        * apply op_m_minv.
  Defined.
End IsOpCartesianFromReindexDispCat.

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

Definition opcleaving_reindex_disp_cat
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (D : disp_cat C₂)
           (HD : opcleaving D)
  : opcleaving (reindex_disp_cat F D).
Proof.
  intros x y d f.
  pose (HD (F x) (F y) d (#F f)) as lift.
  simple refine (_ ,, (_ ,, _)).
  - exact (pr1 lift).
  - exact (pr12 lift).
  - simpl.
    apply is_opcartesian_in_reindex_disp_cat.
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

Definition is_opcartesian_reindex_disp_cat_disp_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (D : disp_cat C₂)
           (HD : opcleaving D)
  : is_opcartesian_disp_functor (reindex_disp_cat_disp_functor F D).
Proof.
  intros x y f xx yy ff Hff.
  apply is_opcartesian_from_reindex_disp_cat.
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

Definition is_opcartesian_lift_functor_into_reindex
           {C₁ C₂ C₃ : category}
           {D₁ : disp_cat C₁}
           {D₃ : disp_cat C₃}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           {FF : disp_functor (F₁ ∙ F₂) D₁ D₃}
           (HFF : is_opcartesian_disp_functor FF)
  : is_opcartesian_disp_functor (lift_functor_into_reindex FF).
Proof.
  intros x y f xx yy ff Hff.
  apply is_opcartesian_in_reindex_disp_cat.
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
      (lift_functor_into_reindex FF₁)
      (lift_functor_into_reindex FF₂).
Proof.
  simple refine (_ ,, _).
  - exact (lift_functor_into_reindex_disp_nat_trans_data αα).
  - exact (lift_functor_into_reindex_disp_nat_trans_axioms αα).
Defined.

(**
 8. Reindexing along opfibrations gives pullbacks
 *)
Section ReindexIsPB.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂)
          (D₂ : disp_cat C₂)
          (HD₂ : iso_cleaving D₂).

  (** Universal property for functors *)
  Context {C₀ : category}
          (G : C₀ ⟶ total_category D₂)
          (H : C₀ ⟶ C₁)
          (α : nat_z_iso (H ∙ F) (G ∙ pr1_category D₂)).

  Definition reindex_pb_ump_1_data
    : functor_data
        C₀
        (total_category (reindex_disp_cat F D₂)).
  Proof.
    use make_functor_data.
    - exact (λ x, H x
                    ,,
                    pr1 (HD₂ _ _ (nat_z_iso_pointwise_z_iso α x) (pr2 (G x)))).
    - refine (λ x y f, # H f ,, _).
      refine (transportb
                (λ z, _ -->[ z ] _)
                _
                (pr2 (HD₂ _ _ (nat_z_iso_pointwise_z_iso α x) (pr2 (G x)))
                 ;;
                 (pr2 (#G f))%Cat
                 ;;
                 inv_mor_disp_from_z_iso
                   (pr2 (HD₂ _ _ (nat_z_iso_pointwise_z_iso α y) (pr2 (G y)))))%mor_disp).
      abstract
        (cbn ;
         use z_iso_inv_on_left ;
         refine (!_) ;
         exact (nat_trans_ax α _ _ f)).
  Defined.

  Definition reindex_pb_ump_1_is_functor
    : is_functor reindex_pb_ump_1_data.
  Proof.
    split.
    - intros x.
      use total2_paths_f ; cbn.
      + apply functor_id.
      + unfold transportb.
        etrans.
        {
          apply transportf_reindex.
        }
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          exact (transportb_transpose_right (fiber_paths (functor_id G x))).
        }
        unfold transportb.
        rewrite mor_disp_transportf_prewhisker.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply id_right_disp.
        }
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          exact (inv_mor_after_z_iso_disp
                   (pr2 (HD₂ _ _ (nat_z_iso_pointwise_z_iso α x) (pr2 (G x))))).
        }
        unfold transportb.
        rewrite transport_f_f.
        apply maponpaths_2.
        apply homset_property.
    - intros x y z f g.
      use total2_paths_f ; cbn.
      + apply functor_comp.
      + unfold transportb.
        etrans.
        {
          apply transportf_reindex.
        }
        rewrite mor_disp_transportf_postwhisker.
        rewrite mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          apply maponpaths.
          exact (transportb_transpose_right
                   (fiber_paths (functor_comp G f g))).
        }
        unfold transportb ; cbn.
        rewrite mor_disp_transportf_prewhisker.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite !assoc_disp_var.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        refine (!_).
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !assoc_disp.
          unfold transportb.
          rewrite transport_f_f.
          apply maponpaths.
          do 2 apply maponpaths_2.
          exact (z_iso_disp_after_inv_mor
                   (pr2 (HD₂ _ _ (nat_z_iso_pointwise_z_iso α y) (pr2 (G y))))).
        }
        unfold transportb.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite id_left_disp.
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite mor_disp_transportf_postwhisker.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        apply maponpaths_2.
        apply homset_property.
  Qed.

  Definition reindex_pb_ump_1
    : C₀ ⟶ total_category (reindex_disp_cat F D₂).
  Proof.
    use make_functor.
    - exact reindex_pb_ump_1_data.
    - exact reindex_pb_ump_1_is_functor.
  Defined.

  Definition reindex_pb_ump_1_pr1
    : reindex_pb_ump_1 ∙ pr1_category _ ⟹ H.
  Proof.
    use make_nat_trans.
    - exact (λ _, identity _).
    - abstract
        (intros x y f ; cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Definition reindex_pb_ump_1_pr1_nat_iso
    : nat_z_iso
        (reindex_pb_ump_1 ∙ pr1_category _)
        H.
  Proof.
    use make_nat_z_iso.
    - exact reindex_pb_ump_1_pr1.
    - intro.
      apply identity_is_z_iso.
  Defined.

  Definition reindex_pb_ump_1_pr2_nat_z_iso_data
    : nat_trans_data
        (reindex_pb_ump_1 ∙ total_functor (reindex_disp_cat_disp_functor F D₂))
        G
    := λ x, α x ,, pr12 (HD₂ _ _ (nat_z_iso_pointwise_z_iso α x) (pr2 (G x))).

  Definition reindex_pb_ump_1_pr2_is_nat_trans
    : is_nat_trans
        _ _
        reindex_pb_ump_1_pr2_nat_z_iso_data.
  Proof.
    intros x y f.
    use total2_paths_f ; cbn.
    - exact (nat_trans_ax α _ _ f).
    - unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite !assoc_disp_var.
      rewrite !transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        exact (z_iso_disp_after_inv_mor
                 (pr2 (HD₂ _ _ (nat_z_iso_pointwise_z_iso α y) (pr2 (G y))))).
      }
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite id_right_disp.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
  Qed.

  Definition reindex_pb_ump_1_pr2
    : reindex_pb_ump_1 ∙ total_functor (reindex_disp_cat_disp_functor F D₂) ⟹ G.
  Proof.
    use make_nat_trans.
    - exact reindex_pb_ump_1_pr2_nat_z_iso_data.
    - exact reindex_pb_ump_1_pr2_is_nat_trans.
  Defined.

  Definition reindex_pb_ump_1_pr2_nat_z_iso
    : nat_z_iso
        (reindex_pb_ump_1 ∙ total_functor (reindex_disp_cat_disp_functor F D₂))
        G.
  Proof.
    use make_nat_z_iso.
    - exact reindex_pb_ump_1_pr2.
    - intros x.
      use is_z_iso_total.
      + exact (pr2 (nat_z_iso_pointwise_z_iso α x)).
      + exact (pr22 (HD₂ _ _ (nat_z_iso_pointwise_z_iso α x) (pr2 (G x)))).
  Defined.

  (** Universal property for natural transformations *)
  Context (Φ₁ Φ₂ : C₀ ⟶ total_category (reindex_disp_cat F D₂))
          (τ₁ : Φ₁ ∙ pr1_category _ ⟹ Φ₂ ∙ pr1_category _)
          (τ₂ : Φ₁ ∙ total_functor (reindex_disp_cat_disp_functor F D₂)
                ⟹
                Φ₂ ∙ total_functor (reindex_disp_cat_disp_functor F D₂))
          (p : ∏ (x : C₀), pr1 (τ₂ x) = # F (τ₁ x)).

  Definition reindex_pb_ump_2_data
    : nat_trans_data Φ₁ Φ₂.
  Proof.
    refine (λ x, τ₁ x ,, _).
    exact (transportf
             (λ z, _ -->[ z ] _)
             (p x)
             (pr2 (τ₂ x))).
  Defined.

  Definition reindex_pb_ump_2_is_nat_trans
    : is_nat_trans Φ₁ Φ₂ reindex_pb_ump_2_data.
  Proof.
    intros x y f.
    use total2_paths_f ; cbn.
    - exact (nat_trans_ax τ₁ _ _ f).
    - unfold transportb.
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite transport_f_f.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        exact (transportb_transpose_right (fiber_paths (nat_trans_ax τ₂ _ _ f))).
      }
      unfold transportb.
      rewrite transport_f_f.
      cbn.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition reindex_pb_ump_2
    : Φ₁ ⟹ Φ₂.
  Proof.
    use make_nat_trans.
    - exact reindex_pb_ump_2_data.
    - exact reindex_pb_ump_2_is_nat_trans.
  Defined.

  Definition reindex_pb_ump_2_pr1
    : post_whisker
        reindex_pb_ump_2
        (pr1_category _)
      =
      τ₁.
  Proof.
    use nat_trans_eq.
    {
      intro ; apply homset_property.
    }
    intro x ; cbn.
    apply idpath.
  Qed.

  Definition reindex_pb_ump_2_pr2
    : post_whisker
        reindex_pb_ump_2
        (total_functor (reindex_disp_cat_disp_functor F D₂))
      =
      τ₂.
  Proof.
    use nat_trans_eq.
    {
      intro ; apply homset_property.
    }
    intro x ; cbn.
    use total2_paths_f ; cbn.
    - exact (!(p x)).
    - rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
  Qed.

  (** Universal property for equalities *)
  Context (n₁ n₂ : Φ₁ ⟹ Φ₂)
          (n₁_pr1 : post_whisker n₁ (pr1_category _) = τ₁)
          (n₁_pr2 : post_whisker
                      n₁
                      (total_functor (reindex_disp_cat_disp_functor F D₂))
                    =
                    τ₂)
          (n₂_pr1 : post_whisker n₂ (pr1_category _) = τ₁)
          (n₂_pr2 : post_whisker
                      n₂
                      (total_functor (reindex_disp_cat_disp_functor F D₂))
                    =
                    τ₂).

  Definition reindex_pb_ump_eq
    : n₁ = n₂.
  Proof.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use total2_paths_f.
    - pose (nat_trans_eq_pointwise n₁_pr1 x) as q₁.
      pose (nat_trans_eq_pointwise n₂_pr1 x) as q₂.
      cbn in q₁, q₂.
      exact (q₁ @ !q₂).
    - cbn.
      pose (nat_trans_eq_pointwise n₁_pr2 x) as q₁.
      pose (nat_trans_eq_pointwise n₂_pr2 x) as q₂.
      cbn in q₁, q₂.
      refine (_ @ fiber_paths (q₁ @ !q₂)).
      cbn.
      etrans.
      {
        apply transportf_reindex.
      }
      apply maponpaths_2.
      apply homset_property.
  Qed.
End ReindexIsPB.

(**
 9. Reindexing of functors
 *)
Section ReindexOfDispFunctor.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂)
          {D₁ D₂ : disp_cat C₂}
          (G : disp_functor (functor_identity _) D₁ D₂).

  Local Open Scope mor_disp.

  Definition reindex_of_disp_functor_data
    : disp_functor_data
        (functor_identity _)
        (reindex_disp_cat F D₁)
        (reindex_disp_cat F D₂).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, G (F x) xx).
    - exact (λ x y xx yy f ff, #G ff).
  Defined.

  Definition reindex_of_disp_functor_axioms
    : disp_functor_axioms reindex_of_disp_functor_data.
  Proof.
    split.
    - intros x xx ; cbn.
      unfold transportb.
      rewrite (disp_functor_transportf _ G).
      rewrite disp_functor_id.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros x y z xx yy zz f g ff gg ; cbn.
      unfold transportb.
      rewrite (disp_functor_transportf _ G).
      rewrite disp_functor_comp.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition reindex_of_disp_functor
    : disp_functor
        (functor_identity _)
        (reindex_disp_cat F D₁)
        (reindex_disp_cat F D₂).
  Proof.
    simple refine (_ ,, _).
    - exact reindex_of_disp_functor_data.
    - exact reindex_of_disp_functor_axioms.
  Defined.

  Definition reindex_of_disp_functor_is_cartesian_disp_functor
             (HD₁ : cleaving D₁)
             (HG : is_cartesian_disp_functor G)
    : is_cartesian_disp_functor reindex_of_disp_functor.
  Proof.
    intros x y f xx yy ff Hff.
    apply is_cartesian_in_reindex_disp_cat ; cbn.
    apply HG.
    use is_cartesian_from_reindex_disp_cat.
    - exact HD₁.
    - exact Hff.
  Defined.

  Definition reindex_of_disp_functor_is_opcartesian_disp_functor
             (HD₁ : opcleaving D₁)
             (HG : is_opcartesian_disp_functor G)
    : is_opcartesian_disp_functor reindex_of_disp_functor.
  Proof.
    intros x y f xx yy ff Hff.
    apply is_opcartesian_in_reindex_disp_cat ; cbn.
    apply HG.
    use is_opcartesian_from_reindex_disp_cat.
    - exact HD₁.
    - exact Hff.
  Defined.
End ReindexOfDispFunctor.

Definition reindex_of_cartesian_disp_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           {D₁ D₂ : disp_cat C₂}
           (G : cartesian_disp_functor (functor_identity _) D₁ D₂)
           (HD₁ : cleaving D₁)
  : cartesian_disp_functor
      (functor_identity _)
      (reindex_disp_cat F D₁)
      (reindex_disp_cat F D₂)
  := reindex_of_disp_functor F G
     ,,
     reindex_of_disp_functor_is_cartesian_disp_functor F G HD₁ (pr2 G).

Definition reindex_of_opcartesian_disp_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           {D₁ D₂ : disp_cat C₂}
           (G : opcartesian_disp_functor (functor_identity _) D₁ D₂)
           (HD₁ : opcleaving D₁)
  : opcartesian_disp_functor
      (functor_identity _)
      (reindex_disp_cat F D₁)
      (reindex_disp_cat F D₂)
  := reindex_of_disp_functor F G
     ,,
     reindex_of_disp_functor_is_opcartesian_disp_functor F G HD₁ (pr2 G).

(**
 10. Reindexing of natural transformations
 *)
Section ReindexOfDispNatTrans.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂)
          {D₁ D₂ : disp_cat C₂}
          {G₁ G₂ : disp_functor (functor_identity _) D₁ D₂}
          (α : disp_nat_trans
                 (nat_trans_id _)
                 G₁ G₂).

  Let reindex_of_disp_nat_trans_data
    : disp_nat_trans_data
        (nat_trans_id _)
        (reindex_of_disp_functor F G₁)
        (reindex_of_disp_functor F G₂)
    := λ x xx,
       transportb
         (λ z, _ -->[ z ] _)
         (functor_id F x)
         (α (F x) xx).

  Definition reindex_of_disp_nat_trans_axioms
    : disp_nat_trans_axioms reindex_of_disp_nat_trans_data.
  Proof.
    intros x y f xx yy ff ; cbn ; unfold reindex_of_disp_nat_trans_data.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      exact (disp_nat_trans_ax α ff).
    }
    unfold transportb.
    refine (!_).
    etrans.
    {
      apply transportf_reindex.
    }
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition reindex_of_disp_nat_trans
    : disp_nat_trans
        (nat_trans_id _)
        (reindex_of_disp_functor F G₁)
        (reindex_of_disp_functor F G₂).
  Proof.
    simple refine (_ ,, _).
    - exact reindex_of_disp_nat_trans_data.
    - exact reindex_of_disp_nat_trans_axioms.
  Defined.
End ReindexOfDispNatTrans.

(**
 11. Pseudofunctoriality of reindexing
 *)
Section ReindexOfId.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂)
          (D : disp_cat C₂).

  Let reindex_of_disp_functor_identity_data
    : disp_nat_trans_data
        (nat_trans_id _)
        (disp_functor_identity _)
        (reindex_of_disp_functor_data F (disp_functor_identity D))
    := λ x xx,
       transportb
         (λ z, _ -->[ z ] _)
         (functor_id F x)
         (id_disp _).

  Definition reindex_of_disp_functor_identity_axioms
    : disp_nat_trans_axioms reindex_of_disp_functor_identity_data.
  Proof.
    intros x y f xx yy ff ; cbn ; unfold reindex_of_disp_functor_identity_data.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite mor_disp_transportf_postwhisker.
    rewrite id_left_disp, id_right_disp.
    unfold transportb.
    rewrite !transport_f_f.
    refine (!_).
    etrans.
    {
      apply transportf_reindex.
    }
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition reindex_of_disp_functor_identity
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_identity _)
        (reindex_of_disp_functor F (disp_functor_identity D)).
  Proof.
    simple refine (_ ,, _).
    - exact reindex_of_disp_functor_identity_data.
    - exact reindex_of_disp_functor_identity_axioms.
  Defined.
End ReindexOfId.

Section ReindexOfComp.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂)
          {D₁ D₂ D₃ : disp_cat C₂}
          (G₁ : disp_functor (functor_identity _) D₁ D₂)
          (G₂ : disp_functor (functor_identity _) D₂ D₃).

  Let reindex_of_disp_functor_composite_data
    : disp_nat_trans_data
        (nat_trans_id _)
        (disp_functor_over_id_composite
           (reindex_of_disp_functor F G₁)
           (reindex_of_disp_functor F G₂))
        (reindex_of_disp_functor
           F
           (disp_functor_over_id_composite G₁ G₂))
    := λ x xx,
       transportb
         (λ z, _ -->[ z ] _)
         (functor_id F x)
         (id_disp _).

  Definition reindex_of_disp_functor_composite_axioms
    : disp_nat_trans_axioms reindex_of_disp_functor_composite_data.
  Proof.
    intros x y f xx yy ff ; cbn ; unfold reindex_of_disp_functor_composite_data.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite mor_disp_transportf_postwhisker.
    rewrite id_left_disp, id_right_disp.
    unfold transportb.
    rewrite !transport_f_f.
    refine (!_).
    etrans.
    {
      apply transportf_reindex.
    }
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition reindex_of_disp_functor_composite
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_over_id_composite
           (reindex_of_disp_functor F G₁)
           (reindex_of_disp_functor F G₂))
        (reindex_of_disp_functor
           F
           (disp_functor_over_id_composite G₁ G₂)).
  Proof.
    simple refine (_ ,, _).
    - exact reindex_of_disp_functor_composite_data.
    - exact reindex_of_disp_functor_composite_axioms.
  Defined.
End ReindexOfComp.
