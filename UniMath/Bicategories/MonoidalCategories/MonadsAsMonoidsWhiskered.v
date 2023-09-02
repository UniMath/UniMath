(** In this file, we show that the monoids in the monoidal category of endofunctors correspond to the monads.

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.Bicategories.MonoidalCategories.EndofunctorsWhiskeredMonoidal.
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

Section FixTheContext.

  Context {C : category}.

  Let ENDO : category := cat_of_endofunctors C.
  Let M_ENDO : monoidal ENDO := monoidal_of_endofunctors C.
  Let MON : category := category_of_monoids_in_monoidal_cat M_ENDO.

  Section MonoidToMonadOb.

  Context (M : MON).

  Let x : ENDO := monoid_carrier _ M.
  Let η : ENDO ⟦ monoidal_unit M_ENDO, x ⟧ := monoid_unit _ M.
  Let μ : ENDO ⟦ x ⊗_{M_ENDO} x, x⟧ := monoid_multiplication _ M.

  Definition monoid_to_disp_Monad_data : disp_Monad_data x := μ,, η.

  Lemma monoid_to_disp_Monad_laws : disp_Monad_laws monoid_to_disp_Monad_data.
  Proof.
    repeat split.
    - intro c.
      set (t := monoid_right_unit_law _ M).
      exact (eqtohomot (base_paths _ _ t) c).
    - intro c.
      set (t := monoid_left_unit_law _ M).
      exact (eqtohomot (base_paths _ _ t) c).
    - intro c.
      set (t := monoid_assoc_law _ M).
      refine (! (eqtohomot (base_paths _ _ t) c) @ _).
      etrans.
      1: apply assoc'.
      apply id_left.
  Qed.

  Definition monoid_to_monad : Monad C
    := _ ,, _ ,, monoid_to_disp_Monad_laws.

End MonoidToMonadOb.

Section MonadToMonoidOb.

  Context (M : Monad C).

  Let x : ENDO := M : functor _ _.
  Let η : ENDO ⟦ monoidal_unit M_ENDO, x ⟧ := η M.
  Let μ : ENDO ⟦ x ⊗_{M_ENDO} x, x⟧ := μ M.

  Definition monad_to_monoid_data : monoid_data M_ENDO x := μ ,, η.

  Lemma monad_to_monoid_laws : monoid_laws M_ENDO monad_to_monoid_data.
  Proof.
    repeat split; apply (nat_trans_eq C); intro c; cbn.
    - apply Monad_law2.
    - apply Monad_law1.
    - rewrite id_left. apply pathsinv0, Monad_law3.
  Qed.

  Definition monad_to_monoid : MON := x ,, monad_to_monoid_data ,, monad_to_monoid_laws.

End MonadToMonoidOb.

  Definition monoid_equiv_monoid : MON ≃ Monad C.
  Proof.
    use weq_iso.
    - apply monoid_to_monad.
    - apply monad_to_monoid.
    - abstract (intro M;
                use total2_paths_f;
                [apply idpath |
                  use total2_paths_f;
                  [apply idpath |
                    apply isaprop_monoid_laws]]).
    - abstract (intro M;
                use total2_paths_f;
                [apply idpath |
                  use total2_paths_f;
                  [apply idpath | apply isaprop_disp_Monad_laws]]).
  Defined.

Section MonoidToMonadMor.

  Context (M N : MON) (f : M --> N).

  Lemma monoid_to_monad_mor_laws : Monad_Mor_laws (pr1 f : monoid_to_monad M ⟹ monoid_to_monad N).
  Proof.
    split.
    - intro c.
      set (t := pr12 f).
      apply pathsinv0.
      etrans.
      2: { exact (eqtohomot (base_paths _ _ t) c). }
      rewrite (bifunctor_equalwhiskers M_ENDO).
      apply idpath.
    - intro c.
      set (t := pr22 f).
      exact (eqtohomot (base_paths _ _ t) c).
  Qed.

  Definition monoid_to_monad_mor : category_Monad C ⟦monoid_to_monad M, monoid_to_monad N⟧
    := pr1 f ,, monoid_to_monad_mor_laws.

End MonoidToMonadMor.

Section MonadToMonoidMor.

  Context (M N : Monad C) (f : category_Monad C ⟦M, N⟧).

  Lemma monad_to_monoid_mor_laws : pr2 (monad_to_monoid M) -->[ pr1 f] pr2 (monad_to_monoid N).
  Proof.
    split.
    - red.
      rewrite (bifunctor_equalwhiskers M_ENDO).
      apply (nat_trans_eq C); intro c.
      apply pathsinv0, Monad_Mor_μ.
    - apply (nat_trans_eq C); intro c.
      apply Monad_Mor_η.
  Qed.

  Definition monad_to_monoid_mor : monad_to_monoid M --> monad_to_monoid N
    := pr1 f ,, monad_to_monoid_mor_laws.

End MonadToMonoidMor.

End FixTheContext.
