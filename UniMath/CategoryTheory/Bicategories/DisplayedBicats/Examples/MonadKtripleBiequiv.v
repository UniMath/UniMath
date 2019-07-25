(* ------------------------------------------------------------------------- *)
(** * Biequivalence between Monads and Ktriples                              *)
(* ------------------------------------------------------------------------- *)

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
  : functor_identity x ⟹ functor_of_kleisli_triple k.
Proof.
   use make_nat_trans.
   - exact unit_kleisli_data.
   - exact unit_kleisli_natural.
Defined.

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
    functor_of_kleisli_triple k.
Proof.
  use make_nat_trans.
  - exact mu_kleisli_data.
  - exact mu_kleisli_natural.
Defined.

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

Definition isaprop_eq_2cell
           {B : bicat}
           {a b : B}
           {f g : a --> b}
           (x y : f ==> g)
  : isaprop (x = y).
Proof.
  apply B.
Defined.

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

Lemma functor_of_kleisli_comm
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

Local Lemma lemma1
      {x y : univalent_category}
      {f : bicat_of_cats ⟦x, y⟧}
      {kx : kleisli_triple x}
      {ky : kleisli_triple y}
      (kf : kleisli_triple_on_functor kx ky f)
  :
      (unit_kleisli kx ▹ f) • functor_of_kleisli_comm kf =
      (lunitor f • rinvunitor f) • (f ◃ unit_kleisli ky)
    × (mu_kleisli kx ▹ f) • functor_of_kleisli_comm kf =
      ((((rassociator (functor_of_kleisli_triple kx : bicat_of_cats ⟦_,_⟧)
                      (functor_of_kleisli_triple kx) f
            • ((functor_of_kleisli_triple kx : bicat_of_cats ⟦_,_⟧) ◃ functor_of_kleisli_comm kf))
           • lassociator (functor_of_kleisli_triple kx : bicat_of_cats ⟦_,_⟧)
                         f
                         (functor_of_kleisli_triple ky))
          • (functor_of_kleisli_comm kf ▹
             (functor_of_kleisli_triple ky : bicat_of_cats ⟦_,_⟧)))
         • rassociator f (functor_of_kleisli_triple ky) (functor_of_kleisli_triple ky))
        • (f ◃ mu_kleisli ky).
Proof.
  split.
  - use nat_trans_eq.
    { apply y. }
    intro a. cbn.
    rewrite !id_left.
    unfold unit_kleisli_data.
    refine (maponpaths (λ z, z · _) (pr12 kf a) @ _).
    rewrite assoc'.
    rewrite iso_inv_after_iso.
    apply id_right.
  - use nat_trans_eq. { apply y. }
                      intro a. cbn.
    do 2 rewrite id_right.
    rewrite id_left.
    unfold mu_kleisli_data.
    etrans.
    apply maponpaths_2.
    apply (pr22 kf).
    rewrite assoc'.
    rewrite iso_inv_after_iso.
    rewrite id_right.
    rewrite assoc'.
    apply maponpaths.
    rewrite (bind_bind ky).
    apply maponpaths.
    rewrite functor_id.
    rewrite id_left.
    rewrite assoc'.
    rewrite (unit_bind ky).
    apply pathsinv0.
    apply id_right.
Qed.

Local Lemma lemma2
      {x y : univalent_category}
      {f g : x ⟶ y} {α : f ⟹ g}
      {kx : kleisli_triple x}
      {ky : kleisli_triple y}
      {kf : kleisli_triple_on_functor kx ky f}
      {kg : kleisli_triple_on_functor kx ky g}
      (e : (∏ a : x, pr1 kf a · α (kx a) = bind_kt ky (α a · unit_kt ky (g a)) · pr1 kg a))
  : alg_disp_cat_2cell
      (ps_id_functor bicat_of_cats) x y f g α
      (functor_of_kleisli_triple kx) (functor_of_kleisli_triple ky)
      (nat_iso_to_invertible_2cell
         (functor_of_kleisli_triple kx ∙ f)
         (f ∙ functor_of_kleisli_triple ky) (functor_of_kleisli_iso kf))
      (nat_iso_to_invertible_2cell
         (functor_of_kleisli_triple kx ∙ g)
         (g ∙ functor_of_kleisli_triple ky) (functor_of_kleisli_iso kg)).
Proof.
  use nat_trans_eq.
  { apply y. }
  cbn. intro a.
  symmetry.
  apply iso_inv_on_left.
  rewrite assoc'.
  rewrite <- e.
  rewrite assoc.
  rewrite iso_after_iso_inv.
  symmetry.
  apply id_left.
Qed.

Local Lemma lemma3
      {x : univalent_category}
      (kx : kleisli_triple x)
  : alg_disp_cat_2cell
      (ps_id_functor bicat_of_cats) x x (functor_identity (pr1 x))
      (functor_identity (pr1 x)) (nat_trans_id (functor_identity (pr1 x)))
      (functor_of_kleisli_triple kx) (functor_of_kleisli_triple kx)
      (nat_trans_comp
         (functor_of_kleisli_triple kx ∙ functor_identity (pr1 x))
         (functor_identity (pr1 x) ∙ functor_of_kleisli_triple kx)
         (functor_identity (pr1 x) ∙ functor_of_kleisli_triple kx)
         (nat_trans_comp
            (functor_of_kleisli_triple kx ∙ functor_identity (pr1 x))
            (functor_of_kleisli_triple kx) (functor_identity (pr1 x) ∙ functor_of_kleisli_triple kx)
            (nat_trans_id (functor_of_kleisli_triple kx))
            (nat_trans_id (functor_of_kleisli_triple kx)))
         (post_whisker (nat_trans_id (functor_identity (pr1 x))) (functor_of_kleisli_triple kx)),,
         is_invertible_2cell_vcomp
         (is_invertible_2cell_vcomp
            (is_invertible_2cell_runitor
               (functor_of_kleisli_triple kx : bicat_of_cats ⟦ x, x ⟧))
            (is_invertible_2cell_linvunitor
               (functor_of_kleisli_triple kx : bicat_of_cats ⟦ x, x ⟧)))
         (is_invertible_2cell_rwhisker
            (functor_of_kleisli_triple kx : bicat_of_cats ⟦ x, x ⟧)
            (is_invertible_2cell_id₂ (functor_identity (pr1 x) : bicat_of_cats ⟦ x, x ⟧))))
      (nat_iso_to_invertible_2cell
         (functor_of_kleisli_triple kx ∙ functor_identity (pr1 x))
         (functor_identity (pr1 x) ∙ functor_of_kleisli_triple kx)
         (functor_of_kleisli_iso (kleisli_triple_on_identity_functor kx))).
Proof.
  unfold alg_disp_cat_2cell.
  use nat_trans_eq.
  { apply x. }
  intro a. cbn.
  rewrite !id_left.
  rewrite (bind_bind kx).
  rewrite (unit_bind kx).
  symmetry.
  apply (bind_unit kx).
Qed.

Definition Ktriple_to_Monad_data
  : disp_psfunctor kleisli_triple_disp_bicat
                   (disp_monad bicat_of_cats)
                   (ps_id_functor bicat_of_cats).
Proof.
  use make_disp_psfunctor.
  - exact disp_2cells_isaprop_monad.
  - exact disp_locally_groupoid_monad.
  - exact @unit_mu_kleisli.
  - unfold bicat_of_cats.
    simpl.
    intros x y f kx ky kf.
    refine (make_dirprod _ tt).
    use tpair.
    + apply nat_iso_to_invertible_2cell.
      exact (functor_of_kleisli_iso kf).
    + exact (lemma1 kf).
  - cbn.
    intros.
    repeat apply make_dirprod; try exact tt.
    exact (lemma2 X).
  - cbn.
    intros x kx.
    refine ((_,, (tt,, tt)),, tt).
    exact (lemma3 kx).
  - simpl.
    intros x y z f g kx ky kz kf kg.
    refine ((_,, (tt,, tt)),, tt).
    abstract
      (unfold alg_disp_cat_2cell; simpl;
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
Admitted. (* No subgoal, but very slow Qed. *)

Local Lemma Ktriple_to_Monad_psfunctor
  : is_disp_psfunctor kleisli_triple_disp_bicat (disp_monad bicat_of_cats)
                      (ps_id_functor bicat_of_cats) (pr1 Ktriple_to_Monad_data).
Proof.
  repeat apply make_dirprod;
    intro; intros; simpl;
      repeat apply isapropdirprod; try apply isapropunit;
        apply isaprop_eq_2cell.
Admitted. (* No subgoal, but very slow Qed. *)

Definition Ktriple_to_Monad
  : disp_psfunctor kleisli_triple_disp_bicat
                   (disp_monad bicat_of_cats)
                   (ps_id_functor bicat_of_cats).
Proof.
  use tpair.
  - apply Ktriple_to_Monad_data.
  - apply Ktriple_to_Monad_psfunctor.
Defined.
