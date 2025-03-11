Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.

Local Open Scope cat.

Section IdempotentsSplitInSet.

  Context {A : SET} {f : SET⟦A, A⟧} (p : f · f = f).

  (* Let I : UU := ∑ b : pr1 A, ∃ a : pr1 A, f a = b.*)
  Let I : UU := ∑ b : pr1 A, f b = b.
  Let J : SET.
  Proof.
    exists I.
    apply isaset_total2.
    - apply A.
    - intro.
      apply isasetaprop.
      apply A.
  Defined.

  Let pr : SET⟦A, J⟧.

  Proof.
    intro a.
    exists (f a).
    exact ((toforallpaths _ _ _ p) a).
  Defined.

  Let inc : SET⟦J, A⟧ := pr1.

  Lemma image_fact_gives_retraction
    : is_retraction inc pr.
  Proof.
    apply funextsec.
    intro i.
    use subtypePath. {
      intro ; apply A.
    }
    exact (pr2 i).
  Defined.

  Definition splitting_in_set : is_split_idempotent f.
  Proof.
    exists J.
    simple refine ((inc ,, pr ,, _) ,, _).
    - exact image_fact_gives_retraction.
    - apply funextsec ; intro ; apply idpath.
  Defined.

End IdempotentsSplitInSet.

Proposition idempotents_split_in_set
  : idempotents_split SET.
Proof.
  intro ; intro.
  apply hinhpr.
  apply splitting_in_set.
  apply f.
Defined.
