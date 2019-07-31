(**
Monads as a bicategory. The construction has 3 layers.
In the first layer: we take algebras on the identity functor.
In the second layer: we add η an μ. This is done by adding 2-cells (as in Add2Cell)
In the third layer: we take the full subcategory and we add the monad laws.
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.AlgebraMap.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Sigma.

Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.

Local Open Scope cat.

(* Proposal for name changes:

- plain_monad    ->  monad_support
- add_unit_mu    ->  monad_data
- lawless_monad  ->  big_monad_data

Redefine, using monad_of_bigmonad, see below.
- monad_obj      ->  bigmonad_obj
- monad_map      ->  bigmonad_map
- monad_unit     ->  bigmonad_unit
- monad_mu       ->  bigmonad_mu

Define
- monad_of_bigmonad
- monad_obj
- monad_map
- monad_unit
- bigmonad_mu
*)

Definition monad_support (C : bicat)
  : bicat
  := bicat_algebra (ps_id_functor C).

Definition monad_support_is_univalent_2_1 {C : bicat}
           (HC_1 : is_univalent_2_1 C)
  : is_univalent_2_1 (monad_support C).
Proof.
  apply bicat_algebra_is_univalent_2_1.
  exact HC_1.
Defined.

Definition monad_support_is_univalent_2_0 {C : bicat}
           (HC : is_univalent_2 C)
  : is_univalent_2_0 (monad_support C).
Proof.
  apply bicat_algebra_is_univalent_2_0.
  exact HC.
Defined.

Definition monad_support_is_univalent_2 {C : bicat}
           (HC : is_univalent_2 C)
  : is_univalent_2 (monad_support C).
Proof.
  split.
  - apply monad_support_is_univalent_2_0; assumption.
  - apply monad_support_is_univalent_2_1.
    exact (pr2 HC).
Defined.

Definition add_unit (C : bicat)
  : disp_bicat (monad_support C).
Proof.
  use add_cell_disp_cat.
  - exact (ps_id_functor _).
  - exact (var _ _).
  - exact (alg_map _).
Defined.

Definition add_mu (C : bicat)
  : disp_bicat (monad_support C).
Proof.
  use add_cell_disp_cat.
  - exact (ps_id_functor _).
  - exact ((alg_map _) · (alg_map _)).
  - exact (alg_map _).
Defined.

Definition monad_data (C : bicat)
  : disp_bicat C
  := sigma_bicat _ _ (disp_dirprod_bicat (add_unit C) (add_mu C)).

Definition lawless_monad (C : bicat) := total_bicat (monad_data C).

Definition lawless_monad_is_univalent_2_1 (C : bicat)
           (HC_1 : is_univalent_2_1 C)
  : is_univalent_2_1 (lawless_monad C).
Proof.
  apply sigma_is_univalent_2_1.
  - exact HC_1.
  - apply disp_alg_bicat_univalent_2_1.
  - apply is_univalent_2_1_dirprod_bicat.
    + apply add_cell_disp_cat_univalent_2_1.
    + apply add_cell_disp_cat_univalent_2_1.
Defined.

Definition lawless_monad_is_univalent_2_0 (C : bicat)
           (HC : is_univalent_2 C)
  : is_univalent_2_0 (lawless_monad C).
Proof.
  pose (HC_1 := pr2 HC).
  apply sigma_is_univalent_2_0.
  - exact HC.
  - split.
    + apply disp_alg_bicat_univalent_2_0.
      apply HC.
    + apply disp_alg_bicat_univalent_2_1.
  - split.
    + apply is_univalent_2_0_dirprod_bicat.
      * apply total_is_univalent_2_1.
        ** exact (pr2 HC).
        ** apply disp_alg_bicat_univalent_2_1.
      * apply add_cell_disp_cat_univalent_2.
        ** exact (pr2 HC).
          ** apply disp_alg_bicat_univalent_2_1.
      * apply add_cell_disp_cat_univalent_2.
        ** exact (pr2 HC).
        ** apply disp_alg_bicat_univalent_2_1.
    + apply is_univalent_2_1_dirprod_bicat.
      * apply add_cell_disp_cat_univalent_2_1.
      * apply add_cell_disp_cat_univalent_2_1.
Defined.

Definition lawless_monad_is_univalent_2 (C : bicat)
           (HC : is_univalent_2 C)
  : is_univalent_2 (lawless_monad C).
Proof.
  split.
  - apply lawless_monad_is_univalent_2_0; assumption.
  - apply lawless_monad_is_univalent_2_1.
    exact (pr2 HC).
Defined.

Section BigProjections.

  Context {C : bicat}.

  Definition bigmonad_obj : lawless_monad C → C
    := λ m, pr1 m.

  Definition bigmonad_map : ∏ (m : lawless_monad C), bigmonad_obj m --> bigmonad_obj m
    := λ m, pr12 m.

  Definition bigmonad_unit : ∏ (m : lawless_monad C), id₁ (bigmonad_obj m) ==> bigmonad_map m
    := λ m, pr122 m.

  Definition bigmonad_mu
    : ∏ (m : lawless_monad C), bigmonad_map m · bigmonad_map m ==> bigmonad_map m
    := λ m, pr222 m.

  Definition bigmonad_laws (m : lawless_monad C) : UU
    := ((linvunitor (bigmonad_map m))
          • (bigmonad_unit m ▹ bigmonad_map m)
          • bigmonad_mu m
        =
        id₂ (bigmonad_map m))
         ×
       ((rinvunitor (bigmonad_map m))
          • (bigmonad_map m ◃ bigmonad_unit m)
          • bigmonad_mu m
        =
        id₂ (bigmonad_map m))
         ×
       ((bigmonad_map m ◃ bigmonad_mu m)
          • bigmonad_mu m
        =
        (lassociator (bigmonad_map m) (bigmonad_map m) (bigmonad_map m))
          • (bigmonad_mu m ▹ bigmonad_map m)
          • bigmonad_mu m).
End BigProjections.

Definition monad (C : bicat) : disp_bicat C
  := sigma_bicat _ _ (disp_fullsubbicat (lawless_monad C) bigmonad_laws).

(** Projections *)

Section Projections.

Context {C : bicat} {x : C} (m : monad C x).

Definition monad_map : x --> x
  := pr11 m.

Definition monad_unit : id₁ x ==> monad_map
  := pr121 m.

Definition monad_mu : monad_map · monad_map ==> monad_map
  := pr221 m.

Definition monad_ημ
  : linvunitor monad_map • (monad_unit ▹ monad_map) • monad_mu = id₂ monad_map
  := pr12 m.

Definition monad_μη
  : rinvunitor monad_map • (monad_map ◃ monad_unit) • monad_mu = id₂ monad_map
  := pr122 m.

Definition monad_μμ
  : (monad_map ◃ monad_mu) • monad_mu
    =
    lassociator monad_map monad_map monad_map • (monad_mu ▹ monad_map) • monad_mu
  := pr222 m.

End Projections.

Section Projections2.

Context {C : bicat} {x y : C} {mx : monad C x} {my : monad C y}
        {f : x --> y}
        (mf : mx -->[f] my).

Definition monad_mor_natural
  : invertible_2cell (monad_map mx · f) (f · monad_map my)
  := pr11 mf.

Definition monad_mor_unit
  : (monad_unit mx ▹ f) • monad_mor_natural
    =
    (lunitor f • rinvunitor f) • (f ◃ monad_unit my)
  := pr121 mf.

Definition monad_mor_mu
  : (monad_mu mx ▹ _) • monad_mor_natural
    =
    ((((rassociator _ _ _ • (_ ◃ monad_mor_natural))
         • lassociator _ _ _) • (monad_mor_natural ▹ _))
       • rassociator _ _ _) • (_ ◃ monad_mu my)
  := pr221 mf.

End Projections2.

Section Projections3.

Context {C : bicat} {x y : C} {mx : monad C x} {my : monad C y}
        {f g : x --> y} {α : f ==> g}
        {mf : mx -->[f] my}
        {mg : mx -->[g] my}
        (αα : mf ==>[α] mg).

Definition monad_cell_natural
  : (monad_map mx ◃ α) • monad_mor_natural mg
    =
    monad_mor_natural mf • (α ▹ monad_map my)
  := pr11 αα.

End Projections3.

(** Builders. *)

Definition make_monad {C : bicat}
           (X : C)
           (f : C⟦X,X⟧)
           (η : id₁ X ==> f)
           (μ : f · f ==> f)
           (ημ : linvunitor f • (η ▹ f) • μ
                 =
                 id₂ f)
           (μη : rinvunitor f • (f ◃ η) • μ
                 =
                 id₂ f)
           (μμ : (f ◃ μ) • μ
                 =
                 lassociator f f f • (μ ▹ f) • μ)
  : monad C X.
Proof.
  use tpair.
  - use tpair.
    + exact f.
    + split.
      * exact η.
      * exact μ.
  - repeat split.
    + exact ημ.
    + exact μη.
    + exact μμ.
Defined.

Definition make_monad_mor
           {C : bicat}
           {x y : C} {mx : monad C x} {my : monad C y}
           {f : x --> y}
           (mf_nat : invertible_2cell (monad_map mx · f) (f · monad_map my))
           (mfη : (monad_unit mx ▹ f) • mf_nat
                     =
                     (lunitor f • rinvunitor f) • (f ◃ monad_unit my))
           (mfμ : (monad_mu mx ▹ _) • mf_nat
                  =
                  ((((rassociator _ _ _ • (_ ◃ mf_nat))
                       • lassociator _ _ _) • (mf_nat ▹ _))
                     • rassociator _ _ _) • (_ ◃ monad_mu my))
  : mx -->[f] my.
Proof.
  refine (_,, tt).
  use tpair.
  - exact mf_nat.
  - apply make_dirprod.
    + exact mfη.
    + exact mfμ.
Defined.

Definition make_monad_cell
           {C : bicat} {x y : C} {mx : monad C x} {my : monad C y}
           {f g : x --> y} {α : f ==> g}
           {mf : mx -->[f] my}
           {mg : mx -->[g] my}
           (α_nat : (monad_map mx ◃ α) • monad_mor_natural mg
                    =
                    monad_mor_natural mf • (α ▹ monad_map my))
  : mf ==>[ α ] mg
  := ((α_nat ,, (tt,,tt)),, tt).

Definition bigmonad (C : bicat) := total_bicat (monad C).

Definition base {C : bicat} (m : bigmonad C) : C := pr1 m.

Coercion bigmonad_to_monad {C : bicat} (m : bigmonad C) : monad C (base m)
  := pr2 m.

Definition make_bigmonad {C : bicat}
           (X : C)
           (f : C⟦X,X⟧)
           (η : id₁ X ==> f)
           (μ : f · f ==> f)
           (ημ : linvunitor f • (η ▹ f) • μ
                 =
                 id₂ f)
           (μη : rinvunitor f • (f ◃ η) • μ
                 =
                 id₂ f)
           (μμ : (f ◃ μ) • μ
                 =
                 lassociator f f f • (μ ▹ f) • μ)
  : bigmonad C.
Proof.
  use tpair.
  - exact X.
  - use make_monad.
    + exact f.
    + exact η.
    + exact μ.
    + exact ημ.
    + exact μη.
    + exact μμ.
Defined.

Definition monad_is_univalent_2_1
           (C : bicat)
  : disp_univalent_2_1 (monad_data C).
Proof.
  use sigma_disp_univalent_2_1_with_props.
  - apply disp_2cells_isaprop_alg.
  - apply disp_2cells_isaprop_prod ; apply disp_2cells_isaprop_add_cell.
  - apply disp_alg_bicat_univalent_2_1.
  - apply is_univalent_2_1_dirprod_bicat ; apply add_cell_disp_cat_univalent_2_1.
Defined.

Definition monad_is_univalent_2_0
           (C : bicat)
           (HC : is_univalent_2 C)
  : disp_univalent_2_0 (monad_data C).
Proof.
  use sigma_disp_univalent_2_0_with_props.
  - exact HC.
  - apply disp_2cells_isaprop_alg.
  - apply disp_2cells_isaprop_prod ; apply disp_2cells_isaprop_add_cell.
  - apply disp_alg_bicat_univalent_2_1.
  - apply is_univalent_2_1_dirprod_bicat ; apply add_cell_disp_cat_univalent_2_1.
  - apply disp_locally_groupoid_alg.
  - apply disp_locally_groupoid_prod ; apply disp_locally_groupoid_add_cell.
  - apply disp_alg_bicat_univalent_2_0.
    exact (pr2 HC).
  - apply is_univalent_2_0_dirprod_bicat.
    + apply total_is_univalent_2_1.
      * exact (pr2 HC).
      * apply disp_alg_bicat_univalent_2_1.
    + apply add_cell_disp_cat_univalent_2.
      * exact (pr2 HC).
      * apply disp_alg_bicat_univalent_2_1.
    + apply add_cell_disp_cat_univalent_2.
      * exact (pr2 HC).
      * apply disp_alg_bicat_univalent_2_1.
Defined.

Definition bigmonad_is_univalent_2_1
           (C : bicat)
           (HC_1 : is_univalent_2_1 C)
  : is_univalent_2_1 (bigmonad C).
Proof.
  apply sigma_is_univalent_2_1.
  - exact HC_1.
  - apply monad_is_univalent_2_1.
  - apply disp_fullsubbicat_univalent_2_1.
Defined.

Definition bigmonad_is_univalent_2_0
           (C : bicat)
           (HC : is_univalent_2 C)
  : is_univalent_2_0 (bigmonad C).
Proof.
  apply sigma_is_univalent_2_0.
  - exact HC.
  - split.
    + apply monad_is_univalent_2_0.
      exact HC.
    + apply monad_is_univalent_2_1.
  - split.
    + apply disp_univalent_2_0_fullsubbicat.
      * exact (lawless_monad_is_univalent_2 C HC).
      * intro ; simpl.
        repeat (apply isapropdirprod) ; apply C.
    + apply disp_fullsubbicat_univalent_2_1.
Defined.

Definition bigmonad_is_univalent_2
           (C : bicat)
           (HC : is_univalent_2 C)
  : is_univalent_2 (bigmonad C).
Proof.
  split.
  - apply bigmonad_is_univalent_2_0; assumption.
  - apply bigmonad_is_univalent_2_1.
    exact (pr2 HC).
Defined.

Definition disp_2cells_isaprop_monad
           (C : bicat)
           (HC : is_univalent_2 C)
  : disp_2cells_isaprop (monad C).
Proof.
  apply disp_2cells_isaprop_sigma.
  - apply disp_2cells_isaprop_sigma.
    + apply disp_2cells_isaprop_alg.
    + apply disp_2cells_isaprop_prod.
      * apply disp_2cells_isaprop_add_cell.
      * apply disp_2cells_isaprop_add_cell.
  - apply disp_2cells_isaprop_fullsubbicat.
Qed.

Definition disp_locally_groupoid_monad
           (C : bicat)
           (HC : is_univalent_2 C)
  : disp_locally_groupoid (monad C).
Proof.
  apply disp_locally_groupoid_sigma.
  - exact HC.
  - apply disp_2cells_isaprop_sigma.
    + apply disp_2cells_isaprop_alg.
    + apply disp_2cells_isaprop_prod.
      * apply disp_2cells_isaprop_add_cell.
      * apply disp_2cells_isaprop_add_cell.
  - apply disp_2cells_isaprop_fullsubbicat.
  - apply disp_locally_groupoid_sigma.
    + exact HC.
    + apply disp_2cells_isaprop_alg.
    + apply disp_2cells_isaprop_prod.
      * apply disp_2cells_isaprop_add_cell.
      * apply disp_2cells_isaprop_add_cell.
    + apply disp_locally_groupoid_alg.
    + apply disp_locally_groupoid_prod.
      * apply disp_locally_groupoid_add_cell.
      * apply disp_locally_groupoid_add_cell.
  - apply disp_locally_groupoid_fullsubbicat.
Qed.

(* ------------------------------------------------------------------------- *)
(* C = bicat_of_cats.                                                        *)
(* ------------------------------------------------------------------------- *)

Definition make_cat_monad
           (C : univalent_category)
           (M : C ⟶ C)
           (η : functor_identity C ⟹ M)
           (μ : M ∙ M ⟹ M)
           (lid : ∏ (X : C), #M (η X) · μ X = id₁ (M X))
           (rid : ∏ (X : C), η (M X) · μ X = id₁ (M X))
           (massoc :  ∏ (X : C), μ (M X) · μ X = #M (μ X) · μ X)
  : monad bicat_of_cats C.
Proof.
  use make_monad.
  - exact M.
  - exact η.
  - exact μ.
  - abstract
      (use nat_trans_eq; try apply homset_property;
       intros X ; cbn;
       rewrite id_left;
       apply lid).
  - abstract
      (use nat_trans_eq; try apply homset_property;
       intros X ; cbn;
       rewrite id_left;
       apply rid).
  - abstract
      (use nat_trans_eq; try apply homset_property;
       intros X ; cbn;
       rewrite id_left;
       apply massoc).
Defined.

Definition cat_monad_ημ {C : univalent_category} (M : monad bicat_of_cats C)
  : ∏ (X : C), #(pr1(monad_map M)) (pr1(monad_unit M) X) · pr1(monad_mu M) X = id₁ _.
Proof.
  intros X.
  pose (nat_trans_eq_pointwise (monad_ημ M) X) as p.
  cbn in p.
  rewrite id_left in p.
  exact p.
Qed.

Definition cat_monad_μη {C : univalent_category} (M : monad bicat_of_cats C)
  : ∏ (X : C), pr1(monad_unit M) (pr1(monad_map M) X) · pr1(monad_mu M) X = id₁ _.
Proof.
  intros X.
  pose (nat_trans_eq_pointwise (monad_μη M) X) as p.
  cbn in p.
  rewrite id_left in p.
  exact p.
Qed.

Definition cat_monad_μμ {C : univalent_category} (M : monad bicat_of_cats C)
  : ∏ (X : C),
    pr1(monad_mu M) (pr1(monad_map M) X) · pr1(monad_mu M) X
    =
    #(pr1(monad_map M)) (pr1(monad_mu M) X) · pr1(monad_mu M) X.
Proof.
  intros X.
  pose (nat_trans_eq_pointwise (monad_μμ M) X) as p.
  cbn in p.
  rewrite id_left in p.
  exact p.
Qed.

(* ------------------------------------------------------------------------- *)
(* Bind and associated fusion laws.                                          *)
(* ------------------------------------------------------------------------- *)

Section Bind.

Context {C : univalent_category}
        (M : monad bicat_of_cats C).

Definition monad_bind
           {A B : C}
           (f : C⟦A, (monad_map M : _ ⟶ _) B⟧)
  : C⟦ (monad_map M : _ ⟶ _) A, (monad_map M : _ ⟶ _) B⟧
  := #(monad_map M : _ ⟶ _) f · pr1 (monad_mu M) B.

Lemma cat_monad_bind_unit
      {A B : C}
      (f : C⟦A, (monad_map M : _ ⟶ _) B⟧)
  : (monad_unit M : _ ⟹ _) A · monad_bind f = f.
Proof.
  unfold monad_bind.
  etrans.
  { rewrite assoc.
    apply maponpaths_2.
    apply (!(nat_trans_ax ((monad_unit M : _ ⟹ _)) A _ f)).
  }
  etrans.
  2: apply id_right.
  rewrite assoc'.
  apply maponpaths.
  apply (cat_monad_μη M).
Qed.

Lemma cat_monad_unit_bind
      {A : C}
  : monad_bind ((monad_unit M : _ ⟹ _) A) = id₁ _.
Proof.
  apply (cat_monad_ημ M).
Qed.

Lemma cat_monad_bind_bind
      {a b c : C}
      (f : C⟦a, (monad_map M : _ ⟶ _) b⟧)
      (g : C⟦b, (monad_map M : _ ⟶ _) c⟧)
  : monad_bind f · monad_bind g = monad_bind (f · monad_bind g).
Proof.
  unfold monad_bind.
  etrans.
  2: {
    rewrite (functor_comp (monad_map M : _ ⟶ _)).
    rewrite assoc'.
    apply maponpaths.
    rewrite (functor_comp (monad_map M : _ ⟶ _)).
    rewrite assoc'.
    apply maponpaths.
    apply (cat_monad_μμ M).
  }
  pose (nat_trans_ax ((monad_mu M : _ ⟹ _)) _ _ g) as Hμ.
  simpl in Hμ.
  rewrite assoc'.
  apply maponpaths.
  etrans.
  { rewrite assoc.
    apply maponpaths_2.
    apply (!Hμ).
  }
  rewrite assoc.
  apply idpath.
Qed.

End Bind.


(* ------------------------------------------------------------------------- *)
(* Monad morphism on C = bicat_of_cats.                                      *)
(* ------------------------------------------------------------------------- *)

Definition make_cat_monad_mor
           {C D : univalent_category}
           {mx : monad bicat_of_cats C} {my : monad bicat_of_cats D}
           {F : C ⟶ D}
           (mf_nat : nat_iso (monad_map mx ∙ F) (F ∙ monad_map my))
           (mfη : ∏ (X : C), #F (pr1 (monad_unit mx) X) · mf_nat X
                             =
                             pr1 (monad_unit my) (F X))
           (mfμ : ∏ (X : C),
                  # F (pr1 (monad_mu mx) X) · mf_nat X
                  =
                  mf_nat (pr1 (monad_map mx) X)
                         · # (pr1 (monad_map my)) (mf_nat X)
                         · pr1 (monad_mu my) (F X))
  : mx -->[ F ] my.
Proof.
  use make_monad_mor.
  - apply nat_iso_to_invertible_2cell.
    exact mf_nat.
  - abstract
      (use nat_trans_eq; try apply homset_property;
       intros X ; cbn;
       do 2 rewrite id_left;
       apply mfη).
  - abstract
      (use nat_trans_eq; try apply homset_property;
       intros X ; cbn;
       rewrite id_left, !id_right;
       apply mfμ).
Defined.

Definition make_cat_monad_cell
           {C D : univalent_category}
           {mx : monad bicat_of_cats C}
           {my : monad bicat_of_cats D}
           {f g : C ⟶ D}
           {α : f ⟹ g}
           {mf : mx -->[f] my}
           {mg : mx -->[g] my}
           (H : ∏ (X : C),
                α (pr1 (monad_map mx) X) · (pr11 (monad_mor_natural mg)) X
                =
                (pr11 (monad_mor_natural mf)) X · # (pr1 (monad_map my)) (pr1 α X))
  : mf ==>[α: prebicat_cells bicat_of_cats _ _] mg.
Proof.
  apply make_monad_cell.
  use nat_trans_eq; try apply homset_property.
  intros X; cbn.
  apply H.
Qed.

Definition monad_mor_nat_iso
           {C₁ C₂ : univalent_category}
           {F : C₁ ⟶ C₂}
           {M₁ : monad bicat_of_cats C₁}
           {M₂ : monad bicat_of_cats C₂}
           (FF : M₁ -->[F] M₂)
  : nat_iso (monad_map M₁ ∙ F) (F ∙ monad_map M₂)
  := invertible_2cell_to_nat_iso _ _ (monad_mor_natural FF).
