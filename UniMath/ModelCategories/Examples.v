Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.SplitMonicsAndEpis.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.ModelCategories.MorphismClass.
Require Import UniMath.ModelCategories.NWFS.
Require Import UniMath.ModelCategories.Helpers.
Require Import UniMath.ModelCategories.Generated.LiftingWithClass.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Three.


Local Open Scope cat.

Section Examples.
Context {C : category}.
Context (CC : BinCoproducts C).

Definition cop_ff_cop (f : arrow C) : BinCoproduct _ _ :=
    CC (arrow_dom f) (arrow_cod f).
Opaque cop_ff_cop.

Definition cop_functorial_factorization_data : section_disp_data (three_disp C).
Proof.
  use tpair.
  - intro f.
    exists (BinCoproductObject (cop_ff_cop f)).
    exists (BinCoproductIn1 (cop_ff_cop f)).
    exists (BinCoproductArrow (cop_ff_cop f) f (identity _)).
    abstract (
      exact (BinCoproductIn1Commutes _ _ _ (cop_ff_cop f) _ _ _)
    ).
  - intros f g γ.
    use tpair.
    * (* arrow dom f ∐ cod f --> dom g ∐ cod g
         simply given by γ: f --> g *)
      use BinCoproductOfArrows.
      + exact (arrow_mor00 γ).
      + exact (arrow_mor11 γ).
    * abstract (
        split; [apply BinCoproductIn1Commutes|];
        use BinCoproductArrowsEq; [
          etrans; [apply assoc|];
          etrans; [apply cancel_postcomposition;
                  apply BinCoproductIn1Commutes|];
          apply pathsinv0;
          etrans; [apply assoc|];
          etrans; [apply cancel_postcomposition;
                  apply BinCoproductIn1Commutes|];
          etrans; [apply assoc'|];
          etrans; [apply cancel_precomposition;
                  apply BinCoproductIn1Commutes|];
          exact (arrow_mor_comm γ)
        |
          etrans; [apply assoc|];
          etrans; [apply cancel_postcomposition;
                  apply BinCoproductIn2Commutes|];
          etrans; [apply id_left|];
          apply pathsinv0;
          etrans; [apply assoc|];
          etrans; [apply cancel_postcomposition;
                  apply BinCoproductIn2Commutes|];
          etrans; [apply assoc'|];
          etrans; [apply cancel_precomposition;
                  apply BinCoproductIn2Commutes|];
          apply id_right
        ]
      ).
Defined.

Definition cop_functorial_factorization_axioms :
    section_disp_axioms cop_functorial_factorization_data.
Proof.
  split; intros; apply pathsinv0;
    (apply subtypePath; [intro; apply isapropdirprod; apply homset_property|]).
  - use BinCoproduct_endo_is_identity.
    * etrans. apply BinCoproductIn1Commutes.
      apply id_left.
    * etrans. apply BinCoproductIn2Commutes.
      apply id_left.
  - use BinCoproductArrowUnique.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn1Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn1Commutes.
      apply assoc.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn2Commutes.
      apply assoc.
Qed.

Definition cop_functorial_factorization : functorial_factorization C :=
    (_,, cop_functorial_factorization_axioms).

Definition cop_ff_comul_data :
    nat_trans_data
        (fact_L cop_functorial_factorization)
        (functor_composite (fact_L cop_functorial_factorization) (fact_L cop_functorial_factorization)).
Proof.
  intro f.
  use mors_to_arrow_mor.
  - exact (identity _).
  - use BinCoproductArrow.
    * use BinCoproductIn1.
    * use (compose (BinCoproductIn2 (cop_ff_cop f))).
      use BinCoproductIn2.
  - abstract (
      etrans; [apply id_left|];
      apply pathsinv0;
      apply BinCoproductIn1Commutes
    ).
Defined.

Lemma cop_ff_comul_ax :
    is_nat_trans _ _ cop_ff_comul_data.
Proof.
  intros f g γ.
  use arrow_mor_eq.
  - etrans. apply id_right.
    apply pathsinv0.
    apply id_left.
  - use BinCoproductArrowsEq.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn1Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn1Commutes.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn1Commutes.
      etrans. apply BinCoproductIn1Commutes.
      reflexivity.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn2Commutes.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      apply assoc'.
Qed.

Definition cop_ff_comul :
    nat_trans _ _ :=
  (_,, cop_ff_comul_ax).

Lemma cop_ff_comul_monad_laws :
    disp_Comonad_laws (L_monad_data cop_functorial_factorization cop_ff_comul).
Proof.
  repeat split; intro f; use arrow_mor_eq.
  - apply id_left.
  - use BinCoproductArrowsEq.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn1Commutes.
      etrans. apply BinCoproductIn1Commutes.
      apply pathsinv0.
      apply id_right.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn2Commutes.
      reflexivity.
  - apply id_left.
  - use BinCoproductArrowsEq.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn1Commutes.
      etrans. apply BinCoproductIn1Commutes.
      etrans. apply id_left.
      apply pathsinv0.
      apply id_right.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply id_left.
      apply pathsinv0.
      apply id_right.
  - reflexivity.
  - use BinCoproductArrowsEq.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn1Commutes.
      etrans. apply BinCoproductIn1Commutes.
      etrans. apply id_left.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
            apply BinCoproductIn1Commutes.
      etrans. apply BinCoproductIn1Commutes.
      reflexivity.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn2Commutes.
      apply assoc.
Qed.

Definition cop_lnwfs_over : lnwfs_over cop_functorial_factorization.
Proof.
  exists cop_ff_comul.
  exact cop_ff_comul_monad_laws.
Defined.

Definition cop_ff_mul_data :
    nat_trans_data
        (functor_composite (fact_R cop_functorial_factorization) (fact_R cop_functorial_factorization))
        (fact_R cop_functorial_factorization).
Proof.
  intro f.
  use mors_to_arrow_mor.
  - use BinCoproductArrow.
    * use BinCoproductArrow.
      + use BinCoproductIn1.
      + use BinCoproductIn2.
    * use BinCoproductIn2.
  - exact (identity _).
  - abstract (
      use BinCoproductArrowsEq; [
        etrans; [apply assoc|];
        etrans; [apply cancel_postcomposition;
                apply BinCoproductIn1Commutes|];
        apply pathsinv0;
        etrans; [apply assoc|];
        etrans; [apply id_right|];
        etrans; [apply BinCoproductIn1Commutes|];
        use BinCoproductArrowsEq; [
            etrans; [apply BinCoproductIn1Commutes|];
            apply pathsinv0;
            etrans; [apply assoc|];
            etrans; [apply cancel_postcomposition;
                      apply BinCoproductIn1Commutes|];
            etrans; [apply BinCoproductIn1Commutes|];
            reflexivity
        |
            etrans; [apply BinCoproductIn2Commutes|];
            apply pathsinv0;
            etrans; [apply assoc|];
            etrans; [apply cancel_postcomposition;
                      apply (BinCoproductIn2Commutes _ _ _ (cop_ff_cop f))|];
            apply BinCoproductIn2Commutes
        ]
      |
        etrans; [apply assoc|];
        etrans; [apply cancel_postcomposition;
                apply BinCoproductIn2Commutes|];
        etrans; [apply BinCoproductIn2Commutes|];
        apply pathsinv0;
        etrans; [apply assoc|];
        etrans; [apply cancel_postcomposition;
                apply BinCoproductIn2Commutes|];
        apply id_left
      ]
    ).
Defined.

Lemma cop_ff_mul_ax :
    is_nat_trans _ _ cop_ff_mul_data.
Proof.
  intros f g γ.
  use arrow_mor_eq.
  - use BinCoproductArrowsEq.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn1Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn1Commutes.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn1Commutes.
      use BinCoproductArrowsEq.
        + etrans. apply assoc.
          etrans. apply cancel_postcomposition.
                  apply BinCoproductIn1Commutes.
          etrans. apply BinCoproductIn1Commutes.
          apply pathsinv0.
          etrans. apply assoc.
          etrans. apply cancel_postcomposition.
                  apply BinCoproductIn1Commutes.
          etrans. apply assoc'.
          etrans. apply cancel_precomposition.
                  apply BinCoproductIn1Commutes.
          reflexivity.
        + etrans. apply assoc.
          etrans. apply cancel_postcomposition.
                  apply (BinCoproductIn2Commutes _ _ _ (cop_ff_cop f)).
          etrans. apply BinCoproductIn2Commutes.
          apply pathsinv0.
          etrans. apply assoc.
          etrans. apply cancel_postcomposition.
                  apply (BinCoproductIn2Commutes _ _ _ (cop_ff_cop f)).
          etrans. apply assoc'.
          etrans. apply cancel_precomposition.
                  apply BinCoproductIn2Commutes.
          reflexivity.
      * etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply BinCoproductIn2Commutes.
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply BinCoproductIn2Commutes.
        apply pathsinv0.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply BinCoproductIn2Commutes.
        etrans. apply BinCoproductIn2Commutes.
        reflexivity.
  - etrans. apply id_right.
    apply pathsinv0.
    apply id_left.
Qed.

Definition cop_ff_mul :
    nat_trans _ _ :=
  (_,, cop_ff_mul_ax).

Lemma cop_ff_mul_monad_laws :
    disp_Monad_laws (R_monad_data cop_functorial_factorization cop_ff_mul).
Proof.
  repeat split; intro f; use arrow_mor_eq.
  - use BinCoproductArrowsEq.
    * etrans. apply cancel_precomposition.
              apply BinCoproductIn1Commutes.
      etrans. apply BinCoproductIn1Commutes.
      apply pathsinv0.
      apply id_right.
    * etrans. apply cancel_precomposition.
              apply BinCoproductIn1Commutes.
      etrans. apply BinCoproductIn2Commutes.
      apply pathsinv0.
      apply id_right.
  - apply id_left.
  - use BinCoproductArrowsEq.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn1Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn1Commutes.
      etrans. apply BinCoproductIn1Commutes.
      apply pathsinv0.
      apply id_right.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply assoc'.
      etrans. apply id_left.
      etrans. apply BinCoproductIn2Commutes.
      apply pathsinv0.
      apply id_right.
  - apply id_left.
  - use BinCoproductArrowsEq.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn1Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn1Commutes.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn1Commutes.
      use BinCoproductArrowsEq.
      + etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply BinCoproductIn1Commutes.
        etrans. apply BinCoproductIn1Commutes.
        apply pathsinv0.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply BinCoproductIn1Commutes.
        use BinCoproductArrowsEq.
        -- etrans. apply assoc.
           etrans. apply cancel_postcomposition.
                   apply BinCoproductIn1Commutes.
           etrans. apply BinCoproductIn1Commutes.
           apply pathsinv0.
           etrans. apply BinCoproductIn1Commutes.
           reflexivity.
        -- etrans. apply assoc.
           etrans. apply cancel_postcomposition.
                   apply (BinCoproductIn2Commutes _ _ _ (cop_ff_cop f)).
           etrans. apply (BinCoproductIn2Commutes _ _ _ (cop_ff_cop f)).
           apply pathsinv0.
           etrans. apply BinCoproductIn2Commutes.
           reflexivity.
      + etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply (BinCoproductIn2Commutes _ _ _ (cop_ff_cop (fact_R cop_functorial_factorization f))).
        etrans. apply (BinCoproductIn2Commutes _ _ _ (cop_ff_cop (fact_R cop_functorial_factorization f))).
        apply pathsinv0.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply (BinCoproductIn2Commutes _ _ _ (cop_ff_cop (fact_R cop_functorial_factorization f))).
        etrans. apply (BinCoproductIn2Commutes _ _ _ (cop_ff_cop f)).
        reflexivity.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply id_left.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply BinCoproductIn2Commutes.
      etrans. apply BinCoproductIn2Commutes.
      reflexivity.
  - reflexivity.
Qed.

Definition cop_rnwfs_over : rnwfs_over cop_functorial_factorization.
Proof.
  exists cop_ff_mul.
  exact cop_ff_mul_monad_laws.
Defined.

Definition cop_nwfs_over : nwfs_over cop_functorial_factorization.
Proof.
  split.
  - exact cop_lnwfs_over.
  - exact cop_rnwfs_over.
Defined.

Definition cop_nwfs : nwfs C :=
    (_,, cop_nwfs_over).

Lemma cop_nwfs_r_map_is_split_epi
    (g : arrow C) :
  nwfs_R_maps cop_nwfs g
  -> is_split_epi g.
Proof.
  intro Rg.
  destruct Rg as [αg αgax].
  use tpair.
  - exact (BinCoproductIn2 _ · (arrow_mor00 αg)).
  - etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            exact (arrow_mor_comm αg).
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (BinCoproductIn2Commutes).
    exact (arrow_mor11_eq (pr1 αgax)).
Qed.

Lemma cop_nwfs_split_epi_is_r_map
    (g : arrow C) :
  is_split_epi g
  -> nwfs_R_maps cop_nwfs g.
Proof.
  intro Hg.
  destruct Hg as [g' rel].
  use tpair.
  - use mors_to_arrow_mor.
    * use BinCoproductArrow.
      + exact (identity _).
      + exact g'.
    * exact (identity _).
    * abstract (
        use BinCoproductArrowsEq; [
          etrans; [apply assoc|];
          etrans; [apply cancel_postcomposition;
                    apply BinCoproductIn1Commutes|];
          etrans; [apply id_left|];
          apply pathsinv0;
          etrans; [apply assoc|];
          etrans; [apply cancel_postcomposition;
                    apply BinCoproductIn1Commutes|];
          apply id_right
        | etrans; [apply assoc|];
          etrans; [apply cancel_postcomposition;
                    apply BinCoproductIn2Commutes|];
          etrans; [exact (rel)|];
          apply pathsinv0;
          etrans; [apply assoc|];
          etrans; [apply id_right|];
          etrans; [apply BinCoproductIn2Commutes|];
          reflexivity
        ]
      ).
  - split; use arrow_mor_eq.
    * etrans. apply BinCoproductIn1Commutes.
      reflexivity.
    * apply id_left.
    * use BinCoproductArrowsEq.
      + etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply BinCoproductIn1Commutes.
        apply pathsinv0.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply BinCoproductIn1Commutes.
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply BinCoproductIn1Commutes.
        etrans. apply id_right.
        use BinCoproductArrowsEq.
        --  etrans. apply BinCoproductIn1Commutes.
            apply pathsinv0.
            etrans. apply assoc.
            etrans. apply cancel_postcomposition.
                    apply BinCoproductIn1Commutes.
            etrans. apply BinCoproductIn1Commutes.
            reflexivity.
        --  etrans. apply BinCoproductIn2Commutes.
            apply pathsinv0.
            etrans. apply assoc.
            etrans. apply cancel_postcomposition.
                    apply (BinCoproductIn2Commutes _ _ _ (cop_ff_cop g)).
            etrans. apply BinCoproductIn2Commutes.
            reflexivity.
      + etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply BinCoproductIn2Commutes.
        etrans. apply BinCoproductIn2Commutes.
        apply pathsinv0.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply BinCoproductIn2Commutes.
        etrans. apply assoc'.
        etrans. apply id_left.
        etrans. apply BinCoproductIn2Commutes.
        reflexivity.
    * reflexivity.
Qed.

Lemma cop_nwfs_r_map_iff_split_epi
    (g : arrow C) :
  nwfs_R_maps cop_nwfs g <-> is_split_epi g.
Proof.
  split.
  - apply cop_nwfs_r_map_is_split_epi.
  - apply cop_nwfs_split_epi_is_r_map.
Qed.

Transparent cop_ff_cop.
End Examples.
