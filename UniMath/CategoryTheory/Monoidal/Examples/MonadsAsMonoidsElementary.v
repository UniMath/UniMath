(** In this file, we show how any monoid in the monoidal category of endofunctors is a monad  - here w.r.t. the
    elementary definition of that monoidal category

    the bicategorical variant is found in [MonadsAsMonoidsWhiskered]

    we also show the direction from monads to monoids, also showing 
    that the category of monads in C is equivalent to the category of monoids in [C, C]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.BicatOfCatsElementary.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.BicatOfCatsElementary.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.Examples.EndofunctorsMonoidalElementary.

Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

Section FixACategory.

  Context {C : category}.

  Let EndC : monoidal_cat := monendocat_monoidal_cat C.
  Let Monoids : category := category_of_monoids_in_monoidal_cat EndC.
  Let Monads : category := category_Monad C.

Section MonoidToMonad.

Section OnObjects.

  Context (M : Monoids).

  Let x := monoid_carrier _ M.
  Let η := monoid_unit _ M.
  Let μ := monoid_multiplication _ M.

  Definition monoid_to_disp_Monad_data_CAT : disp_Monad_data x := μ ,, η.

  Lemma monoid_to_disp_Monad_laws_CAT : disp_Monad_laws monoid_to_disp_Monad_data_CAT.
  Proof.
    repeat split.
    - intro c.
      set (t := monoid_right_unit_law _ M).
      exact (toforallpaths _ _ _ (base_paths _ _ t) c).
    - intro c.
      set (t := monoid_left_unit_law _ M).
      exact (toforallpaths _ _ _ (base_paths _ _ t) c).
    - intro c.
      set (t := monoid_assoc_law _ M).
      refine (! (toforallpaths _ _ _ (base_paths _ _ t) c) @ _).
      etrans.
      + apply assoc'.
      + apply id_left.
  Qed.

  Definition monoid_to_monad_CAT : Monads
    := _ ,, _ ,, monoid_to_disp_Monad_laws_CAT.

End OnObjects.

  Lemma monoid_to_monad_map_is_monad_mor {M M' : Monoids} (f : M --> M')
    : disp_Monad_Mor_laws (monoid_to_disp_Monad_data_CAT M) (monoid_to_disp_Monad_data_CAT M') (pr1 f).
  Proof.
    induction f as [f [H1 H2]]; split; intro A; cbn in f, H1, H2 |- *.
    {
      etrans.
      use (!maponpaths (λ x, pr1 x A) H1).
      use (maponpaths (λ x, x · _)).
      etrans.
      refine (maponpaths (λ x , pr1 x A) _).
      use vcomp_whisker_CAT.
      easy.
    }
    use (maponpaths (λ x, pr1 x A) H2).
  Qed.

  Definition monoid_to_monad_map 
    (M M' : Monoids)
    (f : M --> M') : monoid_to_monad_CAT M --> monoid_to_monad_CAT M'
    := pr1 f ,, monoid_to_monad_map_is_monad_mor f.


  Definition monoid_to_monad_functor_data 
    : functor_data Monoids Monads
    := make_functor_data monoid_to_monad_CAT monoid_to_monad_map.

  Lemma monoid_to_monad_is_functor
    : is_functor monoid_to_monad_functor_data.
  Proof.
    split.
    - intro M.
      use invmap; [|use path_sigma_hprop|easy].
      use isaprop_disp_Monad_Mor_laws.
    - intros M1 M2 M3 f g.
      use invmap; [|use path_sigma_hprop|easy].
      use isaprop_disp_Monad_Mor_laws.
  Qed.

  Definition monoid_to_monad_functor
    : Monoids ⟶ Monads
    := make_functor monoid_to_monad_functor_data monoid_to_monad_is_functor.

End MonoidToMonad.

Section MonadToMonoid.

Section OnObjects.

  Context (M : Monads).

  Definition monad_to_monoid_CAT_data : monoid_data EndC (functor_from_Monad M)
    := μ M ,, η M.

  Lemma monad_to_monoid_CAT_laws :  monoid_laws EndC monad_to_monoid_CAT_data.
  Proof.
    split3; apply (nat_trans_eq C); intro c; cbn.
    - apply Monad_law2.
    - apply Monad_law1.
    - rewrite id_left. apply pathsinv0, Monad_law3.
  Qed.

  Definition monad_to_monoid_CAT_disp : monoid EndC (functor_from_Monad M)
    := monad_to_monoid_CAT_data,,monad_to_monoid_CAT_laws.

  Definition monad_to_monoid_CAT : Monoids
    := _,,monad_to_monoid_CAT_disp.

End OnObjects.

  Lemma monad_to_monoid_map_is_monoid_mor {M M' : Monads} (f : M --> M')
    : is_monoid_mor _ (monad_to_monoid_CAT_disp M) (monad_to_monoid_CAT_disp M') (pr1 f).
  Proof.
    induction f as [f [H1 H2]]; split.
    - use invmap; [|use path_sigma_hprop|].
      + use isaprop_is_nat_trans; use homset_property.
      + use funextsec; intro A; cbn. 
        etrans; [|use (!H1 A)].
        use (maponpaths (λ x, x · _)).
        use nat_trans_ax.
    - use invmap; [|use path_sigma_hprop|].
      + use isaprop_is_nat_trans; use homset_property.
      + use funextsec; use H2.
  Qed.

  Definition monad_to_monoid_map 
    (M M' : Monad C)
    (f : M --> M') : monad_to_monoid_CAT M --> monad_to_monoid_CAT M'
    := pr1 f ,, monad_to_monoid_map_is_monoid_mor f.

  Definition monad_to_monoid_functor_data 
    : functor_data Monads Monoids
    := make_functor_data monad_to_monoid_CAT monad_to_monoid_map.

  Lemma monad_to_monoid_is_functor
    : is_functor monad_to_monoid_functor_data.
  Proof.
    split.
    - intro M.
      use invmap; [|use path_sigma_hprop|easy].
      use isaprop_is_monoid_mor.
    - intros M1 M2 M3 f g.
      use invmap; [|use path_sigma_hprop|easy].
      use isaprop_is_monoid_mor.
  Qed.

  Definition monad_to_monoid_functor
    : Monads ⟶ Monoids
    := make_functor monad_to_monoid_functor_data monad_to_monoid_is_functor.

End MonadToMonoid.

Lemma monoid_to_monad_to_monoid 
  (M : category_of_monoids_in_monoidal_cat (monendocat_monoidal C))
  : monad_to_monoid_CAT (monoid_to_monad_CAT M) = M.
Proof.
  use (total2_paths2_f (idpath _)).
  use invmap; [|use path_sigma_hprop|easy].
  use isaprop_monoid_laws.
Qed.

Lemma monad_to_monoid_to_monad 
  (M : Monad C)
  : monoid_to_monad_CAT (monad_to_monoid_CAT M) = M.
Proof.
  use (total2_paths2_f (idpath _)).
  use invmap; [|use path_sigma_hprop|easy].
  use isaprop_disp_Monad_laws.
Qed.

Definition nat_id_monoid_to_monad_to_monoid_data
  : nat_trans_data (functor_identity Monads) (monad_to_monoid_functor ∙ monoid_to_monad_functor)
  := λ M,
    transportb 
      (λ x, ∑ f, disp_Monad_Mor_laws (pr12 x) (pr12 x) f) 
      (monad_to_monoid_to_monad M) 
      (nat_trans_id _ ,, monads_category_id_subproof _ (pr22 M)).

Lemma nat_id_monoid_to_monad_to_monoid_data_is_nat
  : is_nat_trans _ _ nat_id_monoid_to_monad_to_monoid_data.
Proof.
  intros M M' f.
  use invmap; [|use path_sigma_hprop|]. 
  2: use invmap; [|use path_sigma_hprop|].
  - use isaprop_disp_Monad_Mor_laws.
  - use isaprop_is_nat_trans; use homset_property.
  - unfold nat_id_monoid_to_monad_to_monoid_data, transportb.
    do 2 rewrite transportf_total2.
    use funextsec; intro A.
    induction (monad_to_monoid_to_monad M'), (monad_to_monoid_to_monad M); cbn.
    now rewrite id_left, id_right.
Qed.

Definition nat_id_monoid_to_monad_to_monoid
  : functor_identity Monads ⟹ monad_to_monoid_functor ∙ monoid_to_monad_functor
  := nat_id_monoid_to_monad_to_monoid_data ,, nat_id_monoid_to_monad_to_monoid_data_is_nat.

Definition nat_monad_to_monoid_to_monad_id_data
  : nat_trans_data (monoid_to_monad_functor ∙ monad_to_monoid_functor) (functor_identity Monoids)
  := (λ M, nat_trans_id _,, id_is_monoid_mor _ _).

Lemma nat_monad_to_monoid_to_monad_id_is_nat
  : is_nat_trans _ _ nat_monad_to_monoid_to_monad_id_data.
Proof.
  intros M M' f.
  use invmap; [|use path_sigma_hprop|]. 
  2: use invmap; [|use path_sigma_hprop|].
  - use isaprop_is_monoid_mor.
  - use isaprop_is_nat_trans; use homset_property.
  - use funextsec; intro A; cbn.
    now rewrite id_left, id_right.
Qed.

Definition nat_monad_to_monoid_to_monad_id
  : monoid_to_monad_functor ∙ monad_to_monoid_functor ⟹ functor_identity Monoids
  := nat_monad_to_monoid_to_monad_id_data ,, nat_monad_to_monoid_to_monad_id_is_nat.

Definition adjunction_monad_monoid 
  : adjunction_data Monads Monoids
  := make_adjunction_data 
        monad_to_monoid_functor 
        monoid_to_monad_functor
        nat_id_monoid_to_monad_to_monoid
        nat_monad_to_monoid_to_monad_id.

Lemma adjunction_monad_monoid_equiv : forms_equivalence adjunction_monad_monoid.
Proof.
  use make_forms_equivalence.
  - intro M; use make_is_z_isomorphism; [|use make_is_inverse_in_precat].
    {
      apply (transportb (λ x, ∑ f, disp_Monad_Mor_laws (pr12 x) (pr12 x) f) (monad_to_monoid_to_monad M)).
      exists (nat_trans_id _).
      exact (monads_category_id_subproof _ (pr22 M)).
    }
    
    all: use invmap; [|use path_sigma_hprop|]; [use isaprop_disp_Monad_Mor_laws|];
      use invmap; [|use path_sigma_hprop|]; [use isaprop_is_nat_trans; use homset_property|];
      use funextsec; intro A; cbn;
      do 2 (unfold nat_id_monoid_to_monad_to_monoid_data, transportb; rewrite transportf_total2; cbn);
      induction monad_to_monoid_to_monad; cbn; use id_left.

  - intro M; use make_is_z_isomorphism; [|use make_is_inverse_in_precat].
    
    {
      eapply (transportb (λ x, ∑ f, is_monoid_mor _ (pr2 x) (pr2 x) f) (monoid_to_monad_to_monoid M)).
      exists (identity _); use id_is_monoid_mor.
    }

    all: use invmap; [|use path_sigma_hprop|]; [use isaprop_is_monoid_mor|];
      use invmap; [|use path_sigma_hprop|]; [use isaprop_is_nat_trans; use homset_property|];
      use funextsec; intro A; cbn;
      unfold transportb; rewrite transportf_total2; cbn;
      induction (monoid_to_monad_to_monoid M);
      now rewrite id_left.
Qed.

Definition monad_equiv_monoid_endcat
  : equivalence_of_cats Monads Monoids
  := make_equivalence_of_cats adjunction_monad_monoid adjunction_monad_monoid_equiv.

End FixACategory.
