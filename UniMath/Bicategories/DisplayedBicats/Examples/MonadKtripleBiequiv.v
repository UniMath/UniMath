(* ========================================================================= *)
(** * Biequivalence between Monads and Ktriples                              *)
(* ========================================================================= *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.AlgebraMap.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.

Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Monads.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.KleisliTriple.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.KleisliTriple.

Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.

Local Open Scope cat.
Local Open Scope bicategory_scope.

(* ------------------------------------------------------------------------- *)
(** ** Miscellanea                                                           *)
(* ------------------------------------------------------------------------- *)

Definition isaprop_eq_2cell
           {B : bicat}
           {a b : B}
           {f g : a --> b}
           (x y : f ==> g)
  : isaprop (x = y).
Proof.
  apply B.
Defined.

(* ------------------------------------------------------------------------- *)
(** ** Basic monadic constructions built from a Ktriple.                     *)
(* ------------------------------------------------------------------------- *)

Section Monad_of_Kleisli_Data.

Context {x : category} (k : kleisli_triple x).

Local Lemma unit_kleisli_natural
  : is_nat_trans (functor_identity_data x)
                 (functor_data_of_kleisli_triple k)
                 (unit_kt k).
Proof.
  intros a b f. cbn.
  refine (!_).
  apply (unit_bind k).
Qed.

Definition unit_kleisli
  : functor_identity x ⟹ functor_of_kleisli_triple k
  := make_nat_trans (functor_identity x)
                    (functor_of_kleisli_triple k)
                    (unit_kt k)
                    unit_kleisli_natural.

Local Lemma mu_kleisli_natural
  : is_nat_trans (functor_composite_data (functor_of_kleisli_triple k)
                                         (functor_of_kleisli_triple k))
                 (functor_of_kleisli_triple k)
                 (λ a, bind_kt k (identity (k a))).
Proof.
  intros a b f. cbn.
  do 2 rewrite (bind_bind k).
  apply maponpaths.
  rewrite assoc'.
  rewrite (unit_bind k).
  rewrite id_left.
  apply id_right.
Qed.

Definition mu_kleisli
  : functor_of_kleisli_triple k ∙ functor_of_kleisli_triple k
    ⟹
    functor_of_kleisli_triple k
  := make_nat_trans (functor_of_kleisli_triple k ∙ functor_of_kleisli_triple k)
                    (functor_of_kleisli_triple k)
                    _
                    mu_kleisli_natural.
End Monad_of_Kleisli_Data.

Section Monad_of_Kleisli_Data.

Context {x : univalent_category} (k : kleisli_triple x).

Definition unit_mu_kleisli
  : monad bicat_of_cats x.
Proof.
  use make_cat_monad.
  - exact (functor_of_kleisli_triple k).
  - exact (unit_kleisli k).
  - exact (mu_kleisli k).
  - abstract
      (cbn; intros;
       rewrite (bind_bind k);
       rewrite assoc';
       rewrite (unit_bind k);
       rewrite id_right;
       apply (bind_unit k)).
  - abstract
      (cbn; intros;
       apply (unit_bind k)).
  - abstract
      (cbn; intros;
       do 2 rewrite (bind_bind k);
       rewrite id_left;
       apply maponpaths;
       rewrite assoc';
       rewrite (unit_bind k);
       rewrite id_right; apply idpath).
Defined.

End Monad_of_Kleisli_Data.

(* ------------------------------------------------------------------------- *)
(** ** Pseudofunctor Ktriples to Monads.                                     *)
(* ------------------------------------------------------------------------- *)

Definition functor_of_kleisli_comm
      {x y : univalent_category}
      {f : x ⟶ y}
      {kx : kleisli_triple x}
      {ky : kleisli_triple y}
      (kf : kleisli_triple_on_functor kx ky f)
  : (functor_of_kleisli_triple kx ∙ f)
    ⟹
    (f ∙ functor_of_kleisli_triple ky).
Proof.
  use make_nat_trans.
  - exact (λ a, inv_from_iso (pr1 kf a)).
  - abstract
      (intros a b p;
       cbn;
       pose (pr22 kf) as H;
       cbn in H;
       rewrite H;
       rewrite !assoc';
       apply maponpaths;
       rewrite iso_inv_after_iso;
       rewrite id_right;
       apply maponpaths;
       rewrite functor_comp;
       rewrite !assoc';
       apply maponpaths;
       rewrite (pr12 kf);
       rewrite assoc';
       rewrite iso_inv_after_iso;
       apply id_right).
Defined.

Lemma functor_of_kleisli_comm_nat_iso
      {x y : univalent_category}
      {f : x ⟶ y}
      {kx : kleisli_triple x}
      {ky : kleisli_triple y}
      (kf : kleisli_triple_on_functor kx ky f)
  : is_nat_iso (functor_of_kleisli_comm kf).
Proof.
  intro a.
  apply is_iso_inv_from_iso.
Qed.

Definition functor_of_kleisli_iso
           {x y : univalent_category}
           {f : x ⟶ y}
           {kx : kleisli_triple x}
           {ky : kleisli_triple y}
           (kf : kleisli_triple_on_functor kx ky f)
  : nat_iso (functor_of_kleisli_triple kx ∙ f)
            (f ∙ functor_of_kleisli_triple ky).
Proof.
  use make_nat_iso.
  - exact (functor_of_kleisli_comm kf).
  - exact (functor_of_kleisli_comm_nat_iso kf).
Defined.

Definition unit_mu_kleisli_functor
           {C D : univalent_category}
           {F : C ⟶ D}
           {KC : kleisli_triple_disp_bicat C}
           {KD : kleisli_triple_disp_bicat D}
           (KF : KC -->[F] KD)
  : unit_mu_kleisli KC -->[ F] unit_mu_kleisli KD.
Proof.
  use make_cat_monad_mor ; cbn.
  - exact (functor_of_kleisli_iso KF).
  - abstract
      (intros X ; cbn ;
       rewrite (kleisli_triple_on_functor_unit_kt KF);
       rewrite assoc';
       rewrite iso_inv_after_iso;
       rewrite id_right;
       apply idpath).
  - abstract
      (intros X ; cbn ;
       rewrite (kleisli_triple_on_functor_bind_kt KF);
       rewrite !assoc';
       apply maponpaths;
       rewrite (bind_bind KD);
       rewrite !assoc';
       rewrite (unit_bind KD), id_right;
       rewrite iso_inv_after_iso, id_right;
       rewrite functor_id, id_left;
       apply idpath).
Defined.

Definition Ktriple_to_Monad
  : disp_psfunctor kleisli_triple_disp_bicat
                   (monad bicat_of_cats)
                   (id_psfunctor bicat_of_cats).
Proof.
  use make_disp_psfunctor.
  - apply disp_2cells_isaprop_monad.
    apply univalent_cat_is_univalent_2.
  - exact (disp_locally_groupoid_monad
             bicat_of_cats
             univalent_cat_is_univalent_2).
  - exact @unit_mu_kleisli.
  - exact @unit_mu_kleisli_functor.
  - abstract
      (cbn; intros x y f g α kx ky kf kg e;
       refine ((_,, (tt,, tt)),, tt);
       use nat_trans_eq; try apply homset_property;
       cbn; intro a;
       apply pathsinv0;
       apply iso_inv_on_left;
       rewrite assoc';
       rewrite <- e;
       rewrite assoc;
       rewrite iso_after_iso_inv;
       apply pathsinv0;
       apply id_left).
  - abstract
      (intros x kx;
       refine ((_,, (tt,, tt)),, tt);
       unfold alg_disp_cat_2cell;
       use nat_trans_eq; try apply homset_property;
       intro a; cbn;
       rewrite !id_left;
       rewrite (bind_bind kx);
       rewrite (unit_bind kx);
       apply pathsinv0;
       apply (bind_unit kx)).
  - abstract
      (simpl;
       intros x y z f g kx ky kz kf kg;
       refine ((_,, (tt,, tt)),, tt);
       use nat_trans_eq; try apply z;
       intro a; cbn;
       change (ob x) in a;
       rewrite !id_left;
       rewrite !id_right;
       rewrite assoc';
       rewrite (bind_bind kz);
       rewrite (unit_bind kz);
       rewrite (bind_unit kz);
       rewrite id_right;
       apply idpath).
Defined.


(* ------------------------------------------------------------------------- *)
(*  Kleisli_of_Monad                                                         *)
(* ------------------------------------------------------------------------- *)

Definition Monad_to_Ktriple_data {x : univalent_category}
           (m : monad bicat_of_cats x)
  : kleisli_triple_disp_bicat (id_psfunctor bicat_of_cats x).
Proof.
  use make_kleisli_triple.
  - apply m.
  - exact (pr1 (monad_unit m)).
  - exact (λ _ _ F, monad_bind m F).
  - intros A. apply (cat_monad_unit_bind m).
  - simpl. intros. apply (cat_monad_bind_unit m).
  - simpl. intros. apply (cat_monad_bind_bind m).
Defined.

(* NB: We need to take the inverse to match the definition used to build the biequivalence. *)
Definition monad_mor_natural_pointwise
           {C₁ C₂ : univalent_category}
           {F : C₁ ⟶ C₂}
           {M₁ : monad bicat_of_cats C₁}
           {M₂ : monad bicat_of_cats C₂}
           (FF : M₁ -->[F] M₂)
           (X : C₁)
  : iso ((monad_endo M₂ : C₂ ⟶ C₂) (F X)) (F ((monad_endo M₁ : C₁ ⟶ C₁) X))
  := CompositesAndInverses.nat_iso_to_pointwise_iso
       (nat_iso_inv (monad_mor_nat_iso FF)) X.

Lemma inv_monad_mor_natural_pointwise
      {C₁ C₂ : univalent_category}
      {F : C₁ ⟶ C₂}
      {M₁ : monad bicat_of_cats C₁}
      {M₂ : monad bicat_of_cats C₂}
      (FF : M₁ -->[F] M₂)
      (X : C₁)
  : inv_from_iso (monad_mor_natural_pointwise FF X)
    =
    CompositesAndInverses.nat_iso_to_pointwise_iso (monad_mor_nat_iso FF) X.
Proof.
  refine (!_).
  apply inv_iso_unique'.
  unfold precomp_with.
  apply iso_after_iso_inv.
Qed.

Definition Monad_to_Ktriple_functor
           {x y : univalent_category}
           {f : bicat_of_cats ⟦ x, y ⟧}
           {mx : (monad bicat_of_cats) x}
           {my : (monad bicat_of_cats) y}
           (mf : mx -->[ f] my)
  : Monad_to_Ktriple_data mx -->[ f ] Monad_to_Ktriple_data my.
Proof.
  use make_kleisli_triple_on_functor.
  - exact (monad_mor_natural_pointwise mf).
  - abstract (
        refine (λ (X : x), _); simpl;
        pose (nat_trans_eq_pointwise (monad_mor_unit mf) X) as mf_unit;
        cbn in mf_unit;
        do 2 rewrite id_left in mf_unit;
        etrans; [ apply pathsinv0 | apply maponpaths_2; exact mf_unit ];
        etrans; [ rewrite assoc' | apply id_right ];
        apply maponpaths;
        exact (iso_inv_after_iso (pr11 (monad_mor_natural mf) X ,, _))
      ).
  - abstract (
        refine (λ (X Y : x) (p : x ⟦ X, pr1 (Monad_to_Ktriple_data mx) Y ⟧), _);
        unfold Monad_to_Ktriple_data, bind_kt; simpl;
        etrans; [ apply (monad_mor_bind_alt mf) | idtac ];
        do 2 rewrite (inv_monad_mor_natural_pointwise mf);
        do 2 rewrite assoc';
        apply idpath
      ).
Defined.

Definition Monad_to_Ktriple_2cell
  : ∏ (x y : univalent_category)
      (f g : x ⟶ y)
      (α : prebicat_cells bicat_of_cats f g)
      (mx : (monad bicat_of_cats) x) (my : (monad bicat_of_cats) y)
      (mf : mx -->[ f] my)
      (mg : mx -->[ g] my),
    mf ==>[ α] mg
    →
    ∏ X,
    pr1 ((pr2 (monad_mor_natural mf)) ^-1) X
        · id₁ (f (pr1 (monad_endo mx) X))
        · pr1 α ((pr111 (pr1 mx)) X) =
    monad_bind my (pr1 α X · pr1 (monad_unit my) (g X))
               · (pr1 ((pr2 (monad_mor_natural mg)) ^-1) X
                      · id₁ (g (pr1 (monad_endo mx) X))).
Proof.
  intros x y f g α mx my mf mg mα.
  refine (λ X: (x:univalent_category), _).
  rewrite !id_right.
  pose (nat_trans_eq_pointwise (pr11 mα) X) as d.
  pose (maponpaths (λ z, z · pr1 ((pr2 (monad_mor_natural mg)) ^-1) X) d) as p₁.
  cbn in p₁.
  rewrite assoc' in p₁.
  pose (maponpaths (λ z, pr1 α (pr1 (pr11 mx) X) · z)
                   (!(nat_trans_eq_pointwise
                        (vcomp_rinv (monad_mor_natural mg))
                        X))) as p₂.
  pose (!(id_right _) @ p₂ @ p₁) as r.
  refine (maponpaths (λ z, _ · z) r @ _).
  clear d p₁ p₂ r.
  rewrite !assoc.
  apply maponpaths_2.
  pose (maponpaths (λ z, z · # (pr111 my) (pr1 α X))
                   (!(nat_trans_eq_pointwise
                        (vcomp_linv (monad_mor_natural mf))
                        X))) as p.
  pose (!(id_left _) @ p) as r.
  refine (!r @ _).
  clear p r.
  apply cat_monad_map_as_bind.
Qed.

Definition Monad_to_Ktriple_identitor
  : ∏ (x : bicat_of_cats) (xx : (monad bicat_of_cats) x),
    (id_disp (Monad_to_Ktriple_data xx))
      ==>[ psfunctor_id (id_psfunctor bicat_of_cats) x]
      Monad_to_Ktriple_functor (id_disp xx).
Proof.
  intros x mx X; cbn.
  unfold precomp_with.
  do 2 rewrite id_left ; do 3 rewrite id_right.
  rewrite (functor_id (pr11 mx)), id_right.
  refine (!_).
  apply (cat_monad_unit_bind mx).
Qed.

Definition Monad_to_Ktriple_compositor
  : ∏ (x y z : univalent_category)
      (f : x ⟶ y) (g : y ⟶ z)
      (xx : (monad bicat_of_cats) x)
      (yy : (monad bicat_of_cats) y)
      (zz : (monad bicat_of_cats) z)
      (ff : xx -->[ f] yy) (gg : yy -->[ g] zz),
    (Monad_to_Ktriple_functor ff;; Monad_to_Ktriple_functor gg)
      ==>[ id₂ _]
      Monad_to_Ktriple_functor (ff;; gg).
Proof.
  intros x y z f g mx my mz mf mg.
  refine (λ X : pr1 x, _).
  cbn ; unfold precomp_with.
  etrans.
  {
    refine (id_right _ @ _).
    etrans.
    {
      do 2 apply maponpaths.
      apply id_right.
    }
    apply maponpaths_2.
    apply id_right.
  }
  refine (!_).
  etrans.
  {
    etrans.
    {
      apply maponpaths.
      apply id_right.
    }
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply id_left.
      }
      exact (cat_monad_unit_bind mz).
    }
    refine (id_left _ @ _).
    apply maponpaths.
    refine (id_left _ @ _).
    apply maponpaths.
    refine (id_left _ @ _).
    apply id_right.
  }
  etrans.
  {
    etrans.
    {
      apply maponpaths_2.
      exact (functor_id (pr11 mz) (g(f X))).
    }
    apply id_left.
  }
  apply idpath.
Qed. (* 32 seconds on my computer *)


Definition Monad_to_Ktriple
  : disp_psfunctor (monad bicat_of_cats)
                   kleisli_triple_disp_bicat
                   (id_psfunctor bicat_of_cats).
Proof.
  use make_disp_psfunctor.
  - exact disp_2cells_isaprop_kleisli.
  - exact disp_locally_groupoid_kleisli.
  - exact @Monad_to_Ktriple_data.
  - exact @Monad_to_Ktriple_functor.
  - exact Monad_to_Ktriple_2cell.
  - exact Monad_to_Ktriple_identitor.
  - exact Monad_to_Ktriple_compositor.
Defined.

Lemma bind_kt_monad_to_kleisli
      {x : univalent_category}
      (k : kleisli_triple x)
      {a b : x}
      (f : x ⟦ a, k b ⟧)
  : bind_kt (Monad_to_Ktriple_data (unit_mu_kleisli k)) f = bind_kt k f.
Proof.
  unfold bind_kt at 1; simpl.
  unfold monad_bind; simpl.
  rewrite (bind_bind k).
  apply maponpaths.
  etrans; [ idtac | apply id_right ].
  rewrite assoc'.
  apply maponpaths.
  apply (unit_bind k).
Qed.

Definition Monad_biequiv_Ktriple_unit
  : disp_pstrans
      (disp_pseudo_comp
         (id_psfunctor bicat_of_cats) (id_psfunctor bicat_of_cats)
         (monad bicat_of_cats)
         kleisli_triple_disp_bicat
         (monad bicat_of_cats)
         Monad_to_Ktriple
         Ktriple_to_Monad)
      (disp_pseudo_id (monad bicat_of_cats))
      (pstrans_lunitor (id_psfunctor bicat_of_cats)).
Proof.
  use make_disp_pstrans.
  - exact (disp_2cells_isaprop_monad
             bicat_of_cats
             univalent_cat_is_univalent_2).
  - exact (disp_locally_groupoid_monad
             bicat_of_cats
             univalent_cat_is_univalent_2).
  - intros.
    use make_cat_monad_mor.
    + simpl.
      cbn.
      use make_nat_iso.
      * use make_nat_trans.
        ** intro z. apply identity.
        ** abstract
             (intros z t f ; cbn;
              rewrite id_left, id_right;
              unfold monad_bind;
              rewrite (functor_comp (monad_endo xx : _ ⟶ _));
              rewrite assoc';
              etrans;
              [ apply maponpaths; apply (cat_monad_ημ xx)
              | apply id_right ]).
      * intros z. apply identity_is_iso.
    + intros z.
      apply id_right.
    + abstract (
          simpl;
          intros X;
          rewrite id_left;
          apply id_right).
  - abstract (
        intros;
        use make_cat_monad_cell;
        simpl;
        intros X;
        rewrite !(functor_id ((monad_endo yy) : _ ⟶ _));
        rewrite (functor_id f);
        rewrite !id_left;
        rewrite !(functor_id ((monad_endo yy) : _ ⟶ _));
        rewrite !id_right;
        apply pathsinv0;
        apply inv_iso_unique';
        unfold precomp_with;
        simpl;
        exact (iso_after_iso_inv (pr11 (monad_mor_natural ff) X,, _))
      ).
Defined.

Definition Monad_bequiv_Ktriple_counit
  : disp_pstrans
      (disp_pseudo_comp
         (id_psfunctor bicat_of_cats) (id_psfunctor bicat_of_cats)
         kleisli_triple_disp_bicat
         (monad bicat_of_cats)
         kleisli_triple_disp_bicat
         Ktriple_to_Monad Monad_to_Ktriple)
      (disp_pseudo_id kleisli_triple_disp_bicat)
      (pstrans_lunitor (id_psfunctor bicat_of_cats)).
Proof.
  use make_disp_pstrans.
  - exact disp_2cells_isaprop_kleisli.
  - exact disp_locally_groupoid_kleisli.
  - refine (λ (x : univalent_category) (kx : kleisli_triple x), _).
    use make_kleisli_triple_on_functor.
    + exact (λ X, identity_iso (kx X)).
    + abstract (
          refine (λ A : x, _);
          apply pathsinv0;
          apply id_right).
    + abstract (
          refine (λ (A B : pr1 x) (f : pr1 x ⟦ A, pr1 kx B ⟧), _);
          simpl;
          rewrite id_right;
          etrans; [ apply bind_kt_monad_to_kleisli | idtac ];
          etrans;
          [ pose (kleisli_triple_on_functor_bind_kt
                    (kleisli_triple_on_identity_functor
                       kx)
                    _ _ f
                 ) as H;
            simpl in H;
            exact H
          | idtac ];
          apply id_right
        ).
  - abstract (
        refine (λ (x y : univalent_category)
                  (f : pr1 x ⟶ pr1 y)
                  (kx : kleisli_triple x)
                  (ky : kleisli_triple y)
                  (kf : kleisli_triple_on_functor kx ky f)
                  (X : x),
                _);
        simpl;
        apply pathsinv0;
        etrans;
        [ apply maponpaths_2;
          do 2 rewrite id_left;
          apply (bind_unit ky)
        | idtac ];
        etrans; [ apply id_left | idtac];
        etrans; [ apply id_left | idtac];
        apply pathsinv0;
        simpl;
        etrans;
        [ rewrite assoc';
          apply maponpaths;
          rewrite functor_id;
          etrans; [ apply id_left | idtac];
          apply id_left
        | idtac ];
        etrans; [ apply id_right | idtac];
        apply inv_iso_unique';
        exact (iso_after_iso_inv (kleisli_triple_on_functor_iso kf X))
      ).
Defined.

Definition Monad_biequiv_Ktriple_unit_counit
  : is_disp_biequivalence_unit_counit
      (monad bicat_of_cats)
      kleisli_triple_disp_bicat
      (id_is_biequivalence _) Monad_to_Ktriple Ktriple_to_Monad.
Proof.
  split.
  - exact Monad_biequiv_Ktriple_unit.
  - exact Monad_bequiv_Ktriple_counit.
Defined.

Definition Monad_biequiv_Ktriple_unit_inv
  : disp_pstrans
      (disp_pseudo_id (monad bicat_of_cats))
      (disp_pseudo_comp
         (id_psfunctor bicat_of_cats) (id_psfunctor bicat_of_cats)
         (monad bicat_of_cats)
         kleisli_triple_disp_bicat
         (monad bicat_of_cats)
         Monad_to_Ktriple
         Ktriple_to_Monad)
      (pstrans_linvunitor (id_psfunctor bicat_of_cats)).
Proof.
  use make_disp_pstrans.
  - exact (disp_2cells_isaprop_monad
             bicat_of_cats
             univalent_cat_is_univalent_2).
  - exact (disp_locally_groupoid_monad
             bicat_of_cats
             univalent_cat_is_univalent_2).
  - intros.
    use make_cat_monad_mor.
    + simpl.
      cbn.
      use make_nat_iso.
      * use make_nat_trans.
        ** intro z. apply identity.
        ** abstract
             (intros z t f ; cbn ;
              rewrite id_left, id_right ;
              apply cat_monad_map_as_bind).
      * intros z. apply identity_is_iso.
    + intros z.
      apply id_right.
    + abstract
        (simpl ;
         intros X ;
         rewrite !id_left, id_right ;
         rewrite bind_unit ;
         rewrite id_left ;
         cbn ;
         unfold monad_bind ;
         rewrite functor_id ;
         rewrite id_left ;
         apply idpath).
  - abstract
      (intros ;
       use make_cat_monad_cell ;
       simpl ;
       intro z ;
       rewrite !id_left ;
       rewrite !id_right ;
       rewrite (functor_id f) ;
       rewrite id_left ;
       cbn ;
       unfold precomp_with ;
       rewrite id_right ;
       rewrite <- assoc ;
       apply maponpaths ;
       refine (!_) ;
       refine (maponpaths (λ q, _ · q) (cat_monad_unit_bind _) @ _) ;
       apply id_right).
Defined.

Definition Monad_biequiv_Ktriple_counit_inv
  : disp_pstrans
      (disp_pseudo_id kleisli_triple_disp_bicat)
      (disp_pseudo_comp
         (id_psfunctor bicat_of_cats) (id_psfunctor bicat_of_cats)
         kleisli_triple_disp_bicat
         (monad bicat_of_cats)
         kleisli_triple_disp_bicat
         Ktriple_to_Monad Monad_to_Ktriple)
      (pstrans_linvunitor (id_psfunctor bicat_of_cats)).
Proof.
  use make_disp_pstrans.
  - exact disp_2cells_isaprop_kleisli.
  - exact disp_locally_groupoid_kleisli.
  - refine (λ (x : univalent_category) (kx : kleisli_triple x), _).
    use make_kleisli_triple_on_functor.
    + exact (λ X, identity_iso (kx X)).
    + abstract (
          refine (λ A : x, _);
          apply pathsinv0;
          apply id_right).
    + abstract
        (intros A B f ;
         simpl ;
         rewrite id_left, id_right ;
         refine (!_) ;
         etrans ; [ apply bind_kt_monad_to_kleisli | ] ;
         apply maponpaths ;
         apply id_right).
  - abstract
      (intros x y f kx ky kf z ;
       simpl ;
       cbn ;
       unfold precomp_with ;
       rewrite !id_left, !id_right ;
       rewrite functor_id, id_right ;
       refine (!_) ;
       apply inv_iso_unique' ;
       unfold precomp_with ;
       cbn ;
       refine (maponpaths
                 (λ q, _ · (q · _))
                 (cat_monad_unit_bind (unit_mu_kleisli ky))
               @ _) ;
       rewrite id_left ;
       apply iso_after_iso_inv).
Defined.

Definition Monad_disp_biequiv_Ktriple
  : disp_is_biequivalence_data
      (monad bicat_of_cats)
      kleisli_triple_disp_bicat
      (id_is_biequivalence _)
      Monad_biequiv_Ktriple_unit_counit.
Proof.
  simple refine (_ ,, _ ,, ((_ ,, _) ,, (_ ,, _))).
  - exact Monad_biequiv_Ktriple_unit_inv.
  - exact Monad_biequiv_Ktriple_counit_inv.
  - use make_disp_invmodification.
    + exact (disp_2cells_isaprop_monad
               bicat_of_cats
               univalent_cat_is_univalent_2).
    + exact (disp_locally_groupoid_monad
               bicat_of_cats
               univalent_cat_is_univalent_2).
    + abstract
        (intros x xx ;
         use make_cat_monad_cell ;
         intros z ;
         simpl ;
         rewrite !id_left ;
         rewrite (functor_id (pr11 xx)), (functor_id (monad_endo xx)) ;
         exact (!(id_left _))).
  - use make_disp_invmodification.
    + exact (disp_2cells_isaprop_monad
               bicat_of_cats
               univalent_cat_is_univalent_2).
    + exact (disp_locally_groupoid_monad
               bicat_of_cats
               univalent_cat_is_univalent_2).
    + abstract
        (intros x xx ;
         use make_cat_monad_cell ;
         intros z ;
         simpl ;
         rewrite !id_left ;
         refine (!_) ;
         refine (bind_bind
                   (Monad_to_Ktriple_data xx)
                   (unit_kt (Monad_to_Ktriple_data xx) z)
                   (unit_kt (Monad_to_Ktriple_data xx) z)
                 @ _) ;
         apply maponpaths ;
         apply unit_bind).
  - use make_disp_invmodification.
    + exact disp_2cells_isaprop_kleisli.
    + exact disp_locally_groupoid_kleisli.
    + abstract
        (intros x xx z ;
         simpl ;
         rewrite !id_left, id_right ;
         rewrite bind_unit ;
         apply idpath).
  - use make_disp_invmodification.
    + exact disp_2cells_isaprop_kleisli.
    + exact disp_locally_groupoid_kleisli.
    + abstract
        (intros x xx z ;
         simpl ;
         rewrite !id_left, id_right ;
         rewrite bind_unit ;
         apply idpath).
Defined.

Definition Monad_to_Ktriple_psfunctor
  : psfunctor
      (total_bicat (monad bicat_of_cats))
      (total_bicat kleisli_triple_disp_bicat)
  := total_psfunctor
       (monad bicat_of_cats)
       kleisli_triple_disp_bicat
       (id_psfunctor bicat_of_cats)
       Monad_to_Ktriple.

Definition Monad_biequiv_Ktriple
  : is_biequivalence Monad_to_Ktriple_psfunctor
  := total_is_biequivalence
       _
       _
       _
       Monad_disp_biequiv_Ktriple.
