(*
  Extensive Categories

  A category with binary coproducts C is extensive if the functor
             e_{a,b} : C/a × C/b → C/(a + b) : (f,g) ↦ (f + g),
  is an equivalence of categories for every a, b : C.

  A binary coproduct preserving functor F : C → D between extensive categories implies that the extensivity structure is preserved, that is:
  the following square commutes up to an invertible natural transformation:

  C/a × C/b     -- e_{a,b}   -->  C/(a + b)
      |                               |
 (F/a)×(F/b)                          |
      |                               |
  D/F(a)×D/F(b) -- e_{Fa,Fb} --> D/(Fa + Fb)

  where the right vertical functor is the composite of
        F/(a+b) : C/(a + b) → D/F(a+b)
  with the codomain functor induced by the isomorphism F(a+b) ≅ Fa + Fb given by the assumption on F:
        D/F(a+b) → D/(Fa + Fb)

  Contents.
  1. Definition of extensive categories [is_extensive]
  2. Proof that the extensivity structure is preserved [bincoproduct_preserving_functor_commutes_with_extensivity]

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLeftAdjoint.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.

(** * 1. Extensive categories *)
Section ExtensivityFunctor.

  Context {C : category} (cp : BinCoproducts C) (a b : C).

  Definition extensivity_functor_ob
    (f : C / a) (g : C / b)
    : C / cp a b.
  Proof.
    exists (cp (cod_dom f) (cod_dom g)).
    use BinCoproductOfArrows.
    + exact (cod_mor f).
    + exact (cod_mor g).
  Defined.

  Definition extensivity_functor_mor_is_mor_of_slice
    {f f' : C / a} {g g' : C / b}
    (i : C / a ⟦f, f'⟧)
    (j : C / b ⟦g, g'⟧)
    : BinCoproductOfArrows C
        (cp (cod_dom f) (cod_dom g)) (cp (cod_dom f') (cod_dom g')) (pr1 i) (pr1 j)
        · BinCoproductOfArrows C (cp (cod_dom f') (cod_dom g')) (cp a b) (cod_mor f') (cod_mor g')
      = BinCoproductOfArrows C (cp (cod_dom f) (cod_dom g)) (cp a b) (cod_mor f) (cod_mor g)
          · identity (cp a b).
  Proof.
    etrans. { apply precompWithBinCoproductArrow. }
    simpl.
    rewrite id_right.
    unfold BinCoproductOfArrows.
    do 2 rewrite assoc.
    use maponpaths_12.
    - etrans. apply maponpaths_2, (pr2 i).
      now rewrite id_right.
    - etrans. apply maponpaths_2, (pr2 j).
      now rewrite id_right.
  Qed.

  Definition extensivity_functor_mor
    {f f' : C / a} {g g' : C / b}
    (i : C / a ⟦f, f'⟧)
    (j : C / b ⟦g, g'⟧)
    : C / cp a b ⟦ extensivity_functor_ob f g, extensivity_functor_ob f' g'⟧.
  Proof.
    use tpair.
    - use BinCoproductOfArrows ; [apply i | apply j].
    - apply extensivity_functor_mor_is_mor_of_slice.
  Defined.

  Definition extensivity_functor_data
    : functor_data (category_binproduct (cod_slice a) (cod_slice b)) (cod_slice (cp a b)).
  Proof.
    use make_functor_data.
    - exact (λ fg, extensivity_functor_ob (pr1 fg) (pr2 fg)).
    - intros [f g] [f' g'] [i j].
      exact (extensivity_functor_mor i j).
  Defined.

  Lemma extensivity_functor_laws
    : is_functor extensivity_functor_data.
  Proof.
    split ; intro ; intros ; (use subtypePath ; [intro ; apply homset_property | ]) ; cbn.
    - apply BinCoproduct_of_identities.
    - etrans.
      2: { apply pathsinv0, (@pr1_transportf (_⟦_,_⟧) (λ _, _⟦_,_⟧)). }
      etrans. {
        apply maponpaths_12 ; apply (@pr1_transportf (_⟦_,_⟧) (λ _, _⟦_,_⟧)).
      }
      do 3 rewrite transportf_const.
      apply pathsinv0.
      etrans. { apply precompWithBinCoproductArrow. }
      now do 2 rewrite assoc.
  Qed.

  Definition extensivity_functor
    : functor (category_binproduct (cod_slice a) (cod_slice b)) (cod_slice (cp a b)).
  Proof.
    use make_functor.
    - exact extensivity_functor_data.
    - apply extensivity_functor_laws.
  Defined.

End ExtensivityFunctor.

Definition is_extensive
  {C : category} (cp : BinCoproducts C)
  : UU
  := ∏ a b : C, adj_equivalence_of_cats (extensivity_functor cp a b).

(** * 2. Extensive functors *)
Section ExtensivitySquare.

  Context {C D : category} (cC : BinCoproducts C) (cD : BinCoproducts D)
    {F : functor C D} (F_pc : preserves_bincoproduct F) (a b : C).

  Definition comp_functor_on_coprod
    : (C / cC a b) ⟶ (D / cD (F a) (F b)).
  Proof.
    use (functor_composite (codomain_functor F _)).
    use comp_functor.
    exact (preserves_bincoproduct_to_z_iso _ F_pc (cC _ _) (cD _ _)).
  Defined.

  Lemma commutation_slices_data_is_welldefined
    (f : C / a) (g : C / b)
    : from_BinCoproduct_to_BinCoproduct D
        (preserves_bincoproduct_to_bincoproduct F F_pc (cC (cod_dom f) (cod_dom g)))
        (cD (F (cod_dom f)) (F (cod_dom g)))
        · BinCoproductOfArrows D (cD (F (pr1 f)) (F (pr1 g))) (cD (F a) (F b)) (# F (pr2 f)) (# F (pr2 g))
      = # F (BinCoproductOfArrows C (cC (cod_dom f) (cod_dom g)) (cC a b) (cod_mor f) (cod_mor g))
          · from_BinCoproduct_to_BinCoproduct D (preserves_bincoproduct_to_bincoproduct F F_pc (cC a b)) (cD (F a) (F b))
          · identity (cD (F a) (F b)).
  Proof.
    simpl.
    rewrite id_right.

    etrans. {
      apply (postcompWithBinCoproductArrow _ (preserves_bincoproduct_to_bincoproduct _ _ _)).
    }
    cbn.
    etrans. { apply maponpaths_2, BinCoproductIn1Commutes. }
    etrans. { apply maponpaths_1, BinCoproductIn2Commutes. }
    unfold from_BinCoproduct_to_BinCoproduct.

    apply pathsinv0.
    use (BinCoproductArrowUnique _ _ _ (preserves_bincoproduct_to_bincoproduct _ _ _)).
    - rewrite assoc.
      cbn.
      rewrite <- functor_comp.
      etrans. {
        apply maponpaths_2, maponpaths.
        apply BinCoproductIn1Commutes.
      }
      rewrite functor_comp.
      rewrite assoc'.
      apply maponpaths.
      apply (BinCoproductIn1Commutes _ _ _ (preserves_bincoproduct_to_bincoproduct _ _ _)).
    - rewrite assoc.
      cbn.
      rewrite <- functor_comp.
      etrans. {
        apply maponpaths_2, maponpaths.
        apply BinCoproductIn2Commutes.
      }
      rewrite functor_comp.
      rewrite assoc'.
      apply maponpaths.
      apply (BinCoproductIn2Commutes _ _ _ (preserves_bincoproduct_to_bincoproduct _ _ _)).
  Qed.

  Definition commutation_slices_data
    : nat_trans_data
        (extensivity_functor cC a b ∙ comp_functor_on_coprod)
        (pair_functor (codomain_functor F a) (codomain_functor F b)
           ∙ extensivity_functor cD (F a) (F b)).
  Proof.
    intros [f g].
    use tpair.
    + apply (z_iso_inv (preserves_bincoproduct_to_z_iso _ F_pc (cC _ _) (cD _ _))).
    + apply commutation_slices_data_is_welldefined.
  Defined.

  Lemma commutation_slices_is_natural
    : is_nat_trans _ _ commutation_slices_data.
  Proof.
    intro ; intros.
    use subtypePath.
    { intro ; apply homset_property. }
    etrans. { apply Codomain.transportf_cod_disp. }
    etrans.
    2: { apply pathsinv0, Codomain.transportf_cod_disp. }
    simpl.
    unfold from_BinCoproduct_to_BinCoproduct.

    apply pathsinv0.
    etrans. {
      apply (postcompWithBinCoproductArrow _ (preserves_bincoproduct_to_bincoproduct _ _ _)).
    }

    etrans. { apply maponpaths_2, BinCoproductIn1Commutes. }
    etrans. { apply maponpaths_1, BinCoproductIn2Commutes. }

    apply pathsinv0.
    use (BinCoproductArrowUnique _ _ _ (preserves_bincoproduct_to_bincoproduct _ _ _)).
    * rewrite assoc.
      etrans. {
        apply maponpaths_2, maponpaths.
        apply (@pr1_transportf (_⟦_,_⟧) (λ _, _⟦_,_⟧)).
      }
      rewrite transportf_const.
      cbn.
      rewrite <- functor_comp.
      etrans. {
        apply maponpaths_2, maponpaths.
        apply BinCoproductIn1Commutes.
      }
      rewrite functor_comp.
      rewrite assoc'.
      apply pathsinv0.
      etrans. {
        apply maponpaths_2.
        apply (@pr1_transportf (_⟦_,_⟧) (λ _, _⟦_,_⟧)).
      }
      rewrite transportf_const.
      cbn.
      apply maponpaths, pathsinv0.
      apply (BinCoproductIn1Commutes _ _ _ (preserves_bincoproduct_to_bincoproduct _ _ _)).
    * rewrite assoc.
      etrans. {
        apply maponpaths_2, maponpaths.
        apply (@pr1_transportf (_⟦_,_⟧) (λ _, _⟦_,_⟧)).
      }
      rewrite transportf_const.
      cbn.
      rewrite <- functor_comp.
      etrans. {
        apply maponpaths_2, maponpaths.
        apply BinCoproductIn2Commutes.
      }
      rewrite functor_comp.
      rewrite assoc'.
      apply pathsinv0.
      etrans. {
        apply maponpaths_2.
        apply (@pr1_transportf (_⟦_,_⟧) (λ _, _⟦_,_⟧)).
      }
      rewrite transportf_const.
      cbn.
      apply maponpaths, pathsinv0.
      apply (BinCoproductIn2Commutes _ _ _ (preserves_bincoproduct_to_bincoproduct _ _ _)).
  Qed.

  Definition commutation_slices
    : nat_trans
        (extensivity_functor cC a b ∙ comp_functor_on_coprod)
        (pair_functor (codomain_functor F a) (codomain_functor F b)
           ∙ extensivity_functor cD (F a) (F b)).
  Proof.
    use make_nat_trans.
    - exact commutation_slices_data.
    - exact commutation_slices_is_natural.
  Defined.

  Lemma bincoproduct_preserving_functor_commutes_with_extensivity
    : is_nat_z_iso commutation_slices.
  Proof.
    intro.
    use make_is_z_iso_in_slice.
    use (is_z_iso_from_BinCoproduct_to_BinCoproduct
           _ (preserves_bincoproduct_to_bincoproduct _ _ _)).
  Defined.

End ExtensivitySquare.
