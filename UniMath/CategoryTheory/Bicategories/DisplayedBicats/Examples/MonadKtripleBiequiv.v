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
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.AdjointUnique.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.

Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.

Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.AlgebraMap.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.FullSub.

Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Monads.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.KleisliTriple.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBuilders.

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

Local Definition unit_kleisli_data : ∏ a : x, x ⟦ a, pr1 k a ⟧
  := unit_kt k.

Local Lemma unit_kleisli_natural
  : is_nat_trans (functor_identity_data x)
                 (functor_data_of_kleisli_triple k)
                 unit_kleisli_data.
Proof.
  intros a b f. cbn.
  symmetry.
  apply (unit_bind k).
Qed.

Definition unit_kleisli
  : functor_identity x ⟹ functor_of_kleisli_triple k
  := make_nat_trans (functor_identity x)
                    (functor_of_kleisli_triple k)
                    unit_kleisli_data
                    unit_kleisli_natural.

Local Definition mu_kleisli_data (a : x) : x ⟦ k (k a), k a ⟧
  := bind_kt k (identity (k a)).

Local Lemma mu_kleisli_natural
  : is_nat_trans (functor_composite_data (functor_of_kleisli_triple k)
                                         (functor_of_kleisli_triple k))
                 (functor_of_kleisli_triple k) mu_kleisli_data.
Proof.
  unfold mu_kleisli_data.
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
                    mu_kleisli_data
                    mu_kleisli_natural.

End Monad_of_Kleisli_Data.

Section Monad_of_Kleisli_Data.

Context {x : univalent_category} (k : kleisli_triple x).

Local Definition unit_mu_kleisli_data
  : add_unit_mu bicat_of_cats (ps_id_functor bicat_of_cats x)
  := (functor_of_kleisli_triple k,,
      make_dirprod (unit_kleisli k)
                   (mu_kleisli k)).

Local Lemma unit_mu_kleisli_laws
  : disp_fullsubbicat (lawless_monad bicat_of_cats)
                      (monad_laws bicat_of_cats)
                      (ps_id_functor bicat_of_cats x,, unit_mu_kleisli_data).
Proof.
  cbn.
  repeat apply make_dirprod; cbn;
    (apply nat_trans_eq;
     [ apply x
     | cbn; intro a; unfold unit_kleisli_data, mu_kleisli_data;
       repeat rewrite id_left;
       repeat rewrite (bind_bind k) ]).
  - etrans.
    { apply maponpaths.
      rewrite assoc'.
      rewrite (unit_bind k).
      apply id_right.
    }
    apply (bind_unit k).
  - apply (unit_bind k).
  - apply maponpaths.
    rewrite id_left.
    rewrite assoc'.
    rewrite (unit_bind k).
    symmetry.
    apply id_right.
Qed.

Definition unit_mu_kleisli
  : disp_monad bicat_of_cats (ps_id_functor bicat_of_cats x)
  := (unit_mu_kleisli_data,, unit_mu_kleisli_laws).

End Monad_of_Kleisli_Data.

(* ------------------------------------------------------------------------- *)
(** ** Pseudofunctor Ktriples to Monads.                                     *)
(* ------------------------------------------------------------------------- *)

Lemma disp_2cells_isaprop_monad : disp_2cells_isaprop (disp_monad bicat_of_cats).
Proof.
  cbn.
  intro.
  intros.
  simpl.
  repeat apply isapropdirprod; try apply isapropunit.
  apply isaprop_eq_2cell.
Qed.

Lemma disp_locally_groupoid_monad : disp_locally_groupoid (disp_monad bicat_of_cats).
Proof.
  apply make_disp_locally_groupoid.
  - intros a b f g x aa bb ff gg xx.
    refine ((_ ,, (tt ,, tt)) ,, tt).
    cbn.
    unfold alg_disp_cat_2cell.
    pose (pr11 xx) as xx11.
    cbn in xx11.
    unfold alg_disp_cat_2cell in xx11.
    admit.
  - exact disp_2cells_isaprop_monad.
Admitted.

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

Definition Ktriple_to_Monad_disp_2cell
           {x y : bicat_of_cats}
           {f : bicat_of_cats ⟦ x, y ⟧}
           {kx : kleisli_triple_disp_bicat x}
           {ky : kleisli_triple_disp_bicat y}
           (kf : kx -->[f] ky)
  : unit_mu_kleisli kx -->[ #(ps_id_functor bicat_of_cats) f] unit_mu_kleisli ky.
Proof.
  refine (make_dirprod _ tt).
  use tpair.
  - apply nat_iso_to_invertible_2cell.
    exact (functor_of_kleisli_iso kf).
  - abstract
      (split;
       [ use nat_trans_eq; try apply homset_property;
         intro a; cbn;
         do 2 rewrite id_left;
         unfold unit_kleisli_data;
         refine (maponpaths (λ z, z · _) (pr12 kf a) @ _);
         rewrite assoc';
         rewrite iso_inv_after_iso;
         apply id_right
       | use nat_trans_eq; try apply homset_property;
         intro a; cbn;
         do 2 rewrite id_right;
         rewrite id_left;
         unfold mu_kleisli_data;
         rewrite (pr22 kf);
         rewrite assoc';
         rewrite iso_inv_after_iso;
         rewrite id_right;
         rewrite assoc';
         apply maponpaths;
         rewrite (bind_bind ky);
         apply maponpaths;
         rewrite functor_id;
         rewrite id_left;
         rewrite assoc';
         rewrite (unit_bind ky);
         apply pathsinv0;
         apply id_right ]).
Defined.

Definition Ktriple_to_Monad
  : disp_psfunctor kleisli_triple_disp_bicat
                   (disp_monad bicat_of_cats)
                   (ps_id_functor bicat_of_cats).
Proof.
  use make_disp_psfunctor.
  - exact disp_2cells_isaprop_monad.
  - exact disp_locally_groupoid_monad.
  - exact @unit_mu_kleisli.
  - exact @Ktriple_to_Monad_disp_2cell.
  - abstract
      (cbn; intros x y f g α kx ky kf kg e;
       refine ((_,, (tt,, tt)),, tt);
       use nat_trans_eq; try apply homset_property;
       cbn; intro a;
       symmetry;
       apply iso_inv_on_left;
       rewrite assoc';
       rewrite <- e;
       rewrite assoc;
       rewrite iso_after_iso_inv;
       symmetry;
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
       symmetry;
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
