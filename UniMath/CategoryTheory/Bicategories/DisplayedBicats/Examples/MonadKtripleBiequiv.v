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
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Modification.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Biequivalence.

Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Monads.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.KleisliTriple.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Unitality.

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

Local Definition unit_kleisli_data : ∏ a : x, x ⟦ a, pr1 k a ⟧
  := unit_kt k.

Local Lemma unit_kleisli_natural
  : is_nat_trans (functor_identity_data x)
                 (functor_data_of_kleisli_triple k)
                 unit_kleisli_data.
Proof.
  intros a b f. cbn.
  refine (!_).
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

Definition unit_mu_kleisli
  : monad bicat_of_cats x.
Proof.
  use make_cat_monad.
  - exact (functor_of_kleisli_triple k).
  - exact (unit_kleisli k).
  - exact (mu_kleisli k).
  - abstract
      (cbn; intros;
       unfold unit_kleisli_data, mu_kleisli_data;
       rewrite (bind_bind k);
       rewrite assoc';
       rewrite (unit_bind k);
       rewrite id_right;
       apply (bind_unit k)).
  - abstract
      (cbn; intros;
       unfold unit_kleisli_data, mu_kleisli_data;
       apply (unit_bind k)).
  - abstract
      (cbn; intros;
       unfold unit_kleisli_data, mu_kleisli_data;
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

Lemma disp_2cells_isaprop_monad : disp_2cells_isaprop (monad bicat_of_cats).
Proof.
  cbn.
  intro.
  intros.
  simpl.
  repeat apply isapropdirprod; try apply isapropunit.
  apply isaprop_eq_2cell.
Qed.

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
      (intros X ; cbn ; unfold unit_kleisli_data;
       rewrite (kleisli_triple_on_functor_unit_kt KF);
       rewrite assoc';
       rewrite iso_inv_after_iso;
       rewrite id_right;
       apply idpath).
  - abstract
      (intros X ; cbn ; unfold mu_kleisli_data;
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
                   (ps_id_functor bicat_of_cats).
Proof.
  use make_disp_psfunctor.
  - exact disp_2cells_isaprop_monad.
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
(*  Kleisly_of_Monad                                                         *)
(* ------------------------------------------------------------------------- *)

Definition disp_2cells_isaprop_kleisli
  : disp_2cells_isaprop kleisli_triple_disp_bicat.
Proof.
Admitted.

Definition disp_locally_groupoid_kleisli
  : disp_locally_groupoid kleisli_triple_disp_bicat.
Proof.
Admitted.

Section Kleisly_of_Monad_data.

Context {x : univalent_category} (m : monad bicat_of_cats x).

End Kleisly_of_Monad_data.

Definition Monad_to_Ktriple_data {x : univalent_category}
           (m : monad bicat_of_cats x)
  : kleisli_triple_disp_bicat (ps_id_functor bicat_of_cats x).
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
  : kleisli_triple_on_functor
      (Monad_to_Ktriple_data mx)
      (Monad_to_Ktriple_data my)
      f.
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

Definition Monad_to_Ktriple
  : disp_psfunctor (monad bicat_of_cats)
                   kleisli_triple_disp_bicat
                   (ps_id_functor bicat_of_cats).
Proof.
  use make_disp_psfunctor.
  - exact disp_2cells_isaprop_kleisli.
  - exact disp_locally_groupoid_kleisli.
  - exact @Monad_to_Ktriple_data.
  - exact @Monad_to_Ktriple_functor.
  - abstract
      (intros x y f g α mx my mf mg mα;
       refine (λ X: (x:univalent_category), _);
       cbn ; unfold precomp_with ; cbn;
       rewrite !id_right;
       pose (nat_trans_eq_pointwise (pr11 mα) X) as d;
       cbn in d;
       pose (maponpaths (λ z, z · pr1 ((pr2 (monad_mor_natural mg)) ^-1) X) d) as p₁;
       cbn in p₁;
       rewrite assoc' in p₁;
       pose (maponpaths (λ z, pr1 α (pr1 (pr11 mx) X) · z)
                        (!(nat_trans_eq_pointwise
                             (vcomp_rinv (monad_mor_natural mg))
                             X))) as p₂;
       cbn in p₂;
       pose (!(id_right _) @ p₂ @ p₁) as r;
       refine (maponpaths (λ z, _ · z) r @ _);
       clear d p₁ p₂ r;
       rewrite !assoc;
       apply maponpaths_2;
       pose (maponpaths (λ z, z · # (pr111 my) (pr1 α X))
                        (!(nat_trans_eq_pointwise
                             (vcomp_lid (monad_mor_natural mf))
                             X))) as p;
       pose (!(id_left _) @ p) as r;
       refine (!r @ _);
       clear p r;
       apply cat_monad_map_as_bind).
  -  abstract (
         intros x mx X; simpl;
         unfold bind_kt, unit_kt; simpl;
         etrans; [apply id_left | apply pathsinv0 ];
         etrans;
         [ apply maponpaths_2;
           rewrite id_left;
          apply (cat_monad_unit_bind mx)
         | idtac];
         etrans; [apply id_left | apply pathsinv0 ];
         apply inv_iso_unique';
         unfold precomp_with;
         simpl;
         do 2 rewrite id_left;
         rewrite id_right;
         apply functor_id
       ).

  (* About 3min on my computer. *)
  - Time abstract (
      intros x y z f g mx my mz mf mg;
      refine (λ X : pr1 x, _); simpl;
      unfold bind_kt, unit_kt; simpl;
      apply pathsinv0;
      etrans;
      [ apply maponpaths_2;
        rewrite id_left;
        apply (cat_monad_unit_bind mz)
      | idtac ];
      etrans; [ apply id_left | idtac ];
      apply pathsinv0;
      apply inv_iso_unique';
      unfold precomp_with;
      etrans;
      [ apply maponpaths_2;
        simpl;
        rewrite id_left;
        do 2 rewrite id_right;
        rewrite (functor_id (monad_endo mz : _ ⟶ _));
        apply id_right
      | idtac ];
      rewrite id_right;
      etrans; [ apply assoc' | idtac ];
      etrans;
      [ apply maponpaths;
        etrans; [ apply assoc | idtac ];
        etrans;
        [ apply maponpaths_2;
          apply (iso_inv_after_iso (pr11 (monad_mor_natural mg) (pr1 f X),, _))
        | idtac ];
        apply id_left
      | idtac ];
      etrans; [ apply pathsinv0, functor_comp | idtac ];
      etrans;
      [ apply maponpaths;
        apply (iso_inv_after_iso (pr11 (monad_mor_natural mf) X,, _))
      | apply functor_id]
    ).
Time Defined.

Definition TODO {A : UU} : A.
Admitted.

Definition Monad_biequiv_Ktriple
  : is_disp_biequivalence_unit_counit
      (monad bicat_of_cats)
      kleisli_triple_disp_bicat
      (id_is_biequivalence _) Monad_to_Ktriple Ktriple_to_Monad.
Proof.
  split.
  - use make_disp_pstrans.
    + exact disp_2cells_isaprop_monad.
    + exact (disp_locally_groupoid_monad
               bicat_of_cats
               univalent_cat_is_univalent_2).
    + intros.
      use make_cat_monad_mor.
      * simpl.
        cbn.
        use make_nat_iso.
        ** use make_nat_trans.
           *** intro z. apply identity.
           *** abstract
                 (intros z t f ; cbn;
                  rewrite id_left, id_right;
                  unfold monad_bind;
                  rewrite (functor_comp (monad_endo xx : _ ⟶ _));
                  rewrite assoc';
                  etrans;
                  [ apply maponpaths; apply (cat_monad_ημ xx)
                  | apply id_right ]).
        ** intros z. apply identity_is_iso.
      * intros z.
        apply id_right.
      * simpl.
        intros X.
        rewrite id_left.
        apply id_right.
    + intros.
      use make_cat_monad_cell.
      cbn.
      intros X.
      rewrite !(functor_id ((monad_endo yy) : _ ⟶ _)), !id_left, !id_right.
      rewrite (functor_id f).
      rewrite !(functor_id ((monad_endo yy) : _ ⟶ _)), !id_left, !id_right.
      apply TODO.
  - use make_disp_pstrans.
    + apply TODO.
    + apply TODO.
    + apply TODO.
    + apply TODO.
Defined.
