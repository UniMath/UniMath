Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorCategory.

Local Open Scope cat.

Local Lemma aux1
  {D : category}
  {X Y : category}
  (f g : Y ⟶ X)
  (H : f = g)
  {Xdata : X^op ⟶ D}
  {Ydata : Y^op ⟶ D}
  (fdata : functor_opp f ∙ Xdata ⟹ Ydata)
  : transportf (λ t, functor_opp t ∙ Xdata ⟹ Ydata) H fdata
    = nat_trans_comp _ _ _ (post_whisker (op_nt (z_iso_mor (idtoiso (C := [_, _]) H))) Xdata) fdata.
Proof.
  (* Induction on H replaces g by f, makes the transport trivial and turns `z_iso_mor (idtoiso H)` into the identity natural transformation *)
  induction H.
  (* The goal is now `fdata = nat_trans_comp _ _ _ (post_whisker (op_nt (nat_trans_id f)) Xdata) fdata *)
  apply (nat_trans_eq_alt _ Ydata).
  (* nat_trans_eq_alt reduces a proof about natural transformations to a pointwise proof about the morphisms at every x *)
  intro x.
  (* The goal is now `fdata x = # (pr1 Xdata) (identity (pr1 f x)) · fdata x` *)
  refine (!id_left _ @ _).
  apply (maponpaths (λ x, x · _)).
  now refine (!functor_id Xdata _ @ _).
Qed.
