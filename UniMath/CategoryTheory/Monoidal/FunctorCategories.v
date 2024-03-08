(** some categories of monoidal functors and their univalence

- the lax monoidal functors
- the symmetric lax monoidal functors
- the symmetric lax monoidal comonads (functors with counit and comultiplication)

author: Ralph Matthes, August 2023

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.

Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.Monads.Comonads.

Local Open Scope cat.

Section LaxMonoidalFunctorCategory.

Context {C D : category} (M : monoidal C) (N : monoidal D).

Definition disp_cat_lax_monoidal_functors : disp_cat [C,D].
Proof.
  use disp_struct.
  - intro F. exact (fmonoidal_lax M N F).
  - intros F G Fm Gm α. exact (is_mon_nat_trans Fm Gm α).
  - intros; apply isaprop_is_mon_nat_trans.
  - intros F Fm. apply is_mon_nat_trans_identity.
  - intros F G H Fm Gm Hm α β Hα Hβ. exact (is_mon_nat_trans_comp Fm Gm Hm α β Hα Hβ).
Defined.

Definition category_lax_monoidal_functors : category
  := total_category disp_cat_lax_monoidal_functors.

Lemma lax_monoidal_functors_Pisset (F : C ⟶ D) : isaset (fmonoidal_lax M N F).
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  { apply isasetdirprod.
    - apply impred; intro x; apply impred; intro y. apply D.
    - apply D.
  }
  intro fmd.
  apply isasetaprop.
  apply isaprop_fmonoidal_laxlaws.
Qed.

Lemma lax_monoidal_functors_Hstandard {F : C ⟶ D}
  (Fm Fm' : fmonoidal_lax M N F) :
  is_mon_nat_trans Fm Fm' (nat_trans_id (pr1 F))
  → is_mon_nat_trans Fm' Fm (nat_trans_id (pr1 F)) → Fm = Fm'.
Proof.
  intros H H'.
  apply fmonoidal_lax_eq.
  apply dirprodeq.
  - destruct H as [H _].
    apply funextsec; intro c.
    apply funextsec; intro c'.
    assert (aux := H c c').
    cbn in aux.
    rewrite id_right in aux.
    rewrite (bifunctor_distributes_over_id) in aux.
    + rewrite id_left in aux.
      exact aux.
    + apply (bifunctor_leftid N).
    + apply (bifunctor_rightid N).
  - destruct H as [_ H].
    red in H. cbn in H.
    rewrite id_right in H.
    exact H.
Qed.

Definition is_univalent_disp_cat_lax_monoidal_functors :
  is_univalent_disp disp_cat_lax_monoidal_functors.
Proof.
  use is_univalent_disp_from_SIP_data.
  - exact lax_monoidal_functors_Pisset.
  - intros F Fm Fm'. apply lax_monoidal_functors_Hstandard.
Defined.

End LaxMonoidalFunctorCategory.

Definition is_univalent_category_lax_monoidal_functors
  {C D : category} (HD : is_univalent D)
  (M : monoidal C) (N : monoidal D)
  : is_univalent (category_lax_monoidal_functors M N).
Proof.
  apply is_univalent_total_category.
  - apply is_univalent_functor_category. apply HD.
  - apply is_univalent_disp_cat_lax_monoidal_functors.
Defined.

Section SymmetricLaxMonoidalFunctorCategory.

  Context {C D : category} {M : monoidal C} {N : monoidal D}
    (HM : symmetric M) (HN : symmetric N).

Definition disp_cat_symmetric_lax_monoidal_functors_aux :
  disp_cat (category_lax_monoidal_functors M N).
Proof.
  use disp_full_sub.
  intro FFm. exact (is_symmetric_monoidal_functor HM HN (pr2 FFm)).
Defined.

Definition is_univalent_disp_cat_symmetric_lax_monoidal_functors_aux :
  is_univalent_disp disp_cat_symmetric_lax_monoidal_functors_aux.
Proof.
  apply disp_full_sub_univalent.
  intro F. apply isaprop_is_symmetric_monoidal_functor.
Defined.

Definition disp_cat_symmetric_lax_monoidal_functors : disp_cat [C,D]
  := sigma_disp_cat disp_cat_symmetric_lax_monoidal_functors_aux.

Definition category_symmetric_lax_monoidal_functors : category
  := total_category disp_cat_symmetric_lax_monoidal_functors.

Definition is_univalent_disp_cat_symmetric_lax_monoidal_functors :
  is_univalent_disp disp_cat_symmetric_lax_monoidal_functors.
Proof.
  apply is_univalent_sigma_disp.
  - apply is_univalent_disp_cat_lax_monoidal_functors.
  - apply is_univalent_disp_cat_symmetric_lax_monoidal_functors_aux.
Defined.

End SymmetricLaxMonoidalFunctorCategory.

Definition is_univalent_category_symmetric_lax_monoidal_functors
  {C D : category} (HD : is_univalent D) {M : monoidal C} {N : monoidal D}
  (HM : symmetric M) (HN : symmetric N) :
  is_univalent (category_symmetric_lax_monoidal_functors HM HN).
Proof.
  apply is_univalent_total_category.
  - apply is_univalent_functor_category. apply HD.
  - apply is_univalent_disp_cat_symmetric_lax_monoidal_functors.
Defined.

Section SymmetricMonoidalComonads.

  Context {C : category} {M : monoidal C} (HM : symmetric M).

Definition symmetric_monoidal_comonads_extra_laws {F : C ⟶ C}
  (Fm : disp_cat_lax_monoidal_functors M M F)
  (δ : F ⟹ F ∙ F) (ε : F ⟹ functor_identity C) : UU :=
  is_mon_nat_trans Fm (comp_fmonoidal_lax Fm Fm) δ ×
  is_mon_nat_trans Fm (identity_fmonoidal_lax M) ε.

Lemma isaprop_symmetric_monoidal_comonads_extra_laws {F : C ⟶ C}
  (Fm : disp_cat_lax_monoidal_functors M M F)
  (δ : F ⟹ F ∙ F) (ε : F ⟹ functor_identity C) :
  isaprop (symmetric_monoidal_comonads_extra_laws Fm δ ε).
Proof.
  apply isapropdirprod; apply isaprop_is_mon_nat_trans.
Qed.

Definition disp_cat_symmetric_monoidal_comonads :
  disp_cat (category_symmetric_lax_monoidal_functors HM HM).
Proof.
  use disp_struct.
  - intros [F [Fm Fs]].
    use total2.
    + exact (comonads_category_disp F).
    + intro H.
      induction H as [[δ ε] _].
      exact (symmetric_monoidal_comonads_extra_laws Fm δ ε).
  - intros F G T T' α.
    exact (disp_Comonad_Mor_laws (pr11 T) (pr11 T') (pr1 α)).
  - intros. apply isaprop_disp_Comonad_Mor_laws.
  - intros F T. apply comonads_category_id_subproof.
    exact (pr21 T).
  - intros F F' F'' T T' T'' α α' Hα Hα'. cbn in *.
    exact (comonads_category_comp_subproof (pr11 T) (pr21 T) (pr11 T') (pr21 T') (pr11 T'') (pr21 T'') _ _ Hα Hα').
Defined.

Definition category_symmetric_monoidal_comonad : category
  := total_category disp_cat_symmetric_monoidal_comonads.

Definition symmetric_monoidal_comonad : UU := ob category_symmetric_monoidal_comonad.

#[reversible=no] Coercion comonad_from_symmetric_monoidal_comonad (T : symmetric_monoidal_comonad)
  : Comonad C
  := pr11 T ,, pr12 T.

Definition lax_monoidal_from_symmetric_monoidal_comonad (T : symmetric_monoidal_comonad) : fmonoidal_lax M M T
  := pr121 T.

Definition symmetric_monoidal_comonad_extra_laws (T : symmetric_monoidal_comonad)
  : symmetric_monoidal_comonads_extra_laws (pr121 T) (δ T) (ε T)
  := pr22 T.

Definition make_symmetric_monoidal_comonad
  {T : Comonad C}
  {Tm : fmonoidal_lax M M (pr1 T)}
  (Ts : is_symmetric_monoidal_functor HM HM Tm)
  (Hδ : is_mon_nat_trans Tm (comp_fmonoidal_lax Tm Tm) (δ T))
  (Hε : is_mon_nat_trans Tm (identity_fmonoidal_lax M) (ε T))
  : symmetric_monoidal_comonad.
Proof.
  use tpair.
  - use tpair.
    + exact (pr1 T).
    + exact (Tm,,Ts).
  - use tpair.
    + exact (pr2 T).
    + exact (Hδ,,Hε).
Defined.

Lemma category_symmetric_monoidal_comonad_disp_eq
  (F : category_symmetric_lax_monoidal_functors HM HM)
  (T T' : disp_cat_symmetric_monoidal_comonads F)
  : pr1 T = pr1 T' -> T = T'.
Proof.
  intro H.
  induction T as [T Textralaws].
  induction T' as [T' T'extralaws].
  apply subtypePath.
  - intro; apply isaprop_symmetric_monoidal_comonads_extra_laws.
  - exact H.
Qed.

Lemma symmetric_monoidal_comonad_category_Pisset
  (smF : ∑ (F : C ⟶ C) (d : fmonoidal_lax M M F),
      is_symmetric_monoidal_functor HM HM d)
  : isaset
    (∑ H : ∑ T : disp_Comonad_data (pr1 smF), disp_Comonad_laws T,
          symmetric_monoidal_comonads_extra_laws (pr12 smF) (pr11 H) (pr21 H)).
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  - apply isofhleveltotal2.
    { apply isasetdirprod; apply [C,C]. }
    intro T.
    apply isasetaprop.
    apply isaprop_disp_Comonad_laws.
  - intro TT.
    apply isasetaprop.
    apply isaprop_symmetric_monoidal_comonads_extra_laws.
Qed.

Lemma symmetric_monoidal_comonad_category_Hstandard
  (smF : ∑ (F : C ⟶ C) (d : fmonoidal_lax M M F), is_symmetric_monoidal_functor HM HM d)
  (TT TT' : ∑ H : ∑ T : disp_Comonad_data (pr1 smF), disp_Comonad_laws T,
        symmetric_monoidal_comonads_extra_laws (pr12 smF) (pr11 H) (pr21 H)) :
  disp_Comonad_Mor_laws (pr11 TT) (pr11 TT') (nat_trans_id (pr11 smF))
  → disp_Comonad_Mor_laws (pr11 TT') (pr11 TT) (nat_trans_id (pr11 smF)) → TT = TT'.
Proof.
  intros H H'.
  apply category_symmetric_monoidal_comonad_disp_eq.
  apply comonads_category_Hstandard; assumption.
Qed.

Definition is_univalent_disp_cat_symmetric_monoidal_comonads :
  is_univalent_disp disp_cat_symmetric_monoidal_comonads.
Proof.
  use is_univalent_disp_from_SIP_data.
  - apply symmetric_monoidal_comonad_category_Pisset.
  - apply symmetric_monoidal_comonad_category_Hstandard.
Defined.

End SymmetricMonoidalComonads.

Definition is_univalent_symmetric_monoidal_comonad {C : category} (HC : is_univalent C)
  {M : monoidal C} (HM : symmetric M)
  : is_univalent (category_symmetric_monoidal_comonad HM).
Proof.
  apply is_univalent_total_category.
  - apply (is_univalent_category_symmetric_lax_monoidal_functors HC).
  - apply is_univalent_disp_cat_symmetric_monoidal_comonads.
Defined.

(**
 Alias for the bundled case
 *)
Definition sym_monoidal_cmd
           (V : sym_monoidal_cat)
  : UU
  := symmetric_monoidal_comonad (pr2 V).

Identity Coercion sym_monoidal_cmd_to_symmetric_monoidal_comonad
  : sym_monoidal_cmd >-> symmetric_monoidal_comonad.
