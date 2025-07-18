(** ** Equivalence between being a final coalgebra in UU and in HSET

    Authors : Antoine Fisse (@AextraT), Ralph Matthes (@rmatthes), 2025

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Induction.FunctorCoalgebras_legacy.
Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.SetBasedPolynomialFunctors.
Require Import UniMath.Induction.M.Core.

Require Import UniMath.CategoryTheory.Categories.Type.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require UniMath.CategoryTheory.FunctorCoalgebras.

Local Open Scope cat.

Section M.
  Context {A : ob HSET} (B : pr1hSet A → ob HSET).

  Local Definition F : type_precat ⟶ type_precat := polynomial_functor (pr1hSet A) (fun a => pr1hSet (B a)).

  Local Definition F' : functor HSET HSET := polynomial_functor_HSET A B.

  Definition FromCoalgInHSET (C' : FunctorCoalgebras.CoAlg_category F') : coalgebra F.
  Proof.
    use tpair.
    - exact (pr1hSet (FunctorCoalgebras.coalg_carrier F' C')).
    - exact (FunctorCoalgebras.coalg_map F' C').
  Defined.

  Definition ToCoalgInHSET (C : coalgebra F) : isaset (coalgebra_ob F C) -> FunctorCoalgebras.CoAlg_category F'.
  Proof.
    intro Hyp.
    use tpair.
    - exact (coalgebra_ob F C ,, Hyp).
    - exact (coalgebra_mor F C).
  Defined.

  Section ToFinalInHSET.

  Context (C0 : coalgebra F).

  Local Definition c0 : type_precat := coalgebra_ob F C0.

  Context (c0_isaset : isaset c0).

  Definition C0' : FunctorCoalgebras.coalgebra_ob F'.
  Proof.
    exact (ToCoalgInHSET C0 c0_isaset).
  Defined.

  Context (C0_is_final : is_final C0).

  Lemma C0'_is_final : isTerminal (FunctorCoalgebras.CoAlg_category F') C0'.
  Proof.
    intro C'.
    destruct (C0_is_final (FromCoalgInHSET C')) as [[φ p2] isunique].
    cbn in φ.
    use tpair.
    - use tpair.
      + exact φ.
      + change (pr2 C' -->[φ] pr2 C0').
        exact p2.
    - intro ψ.
      apply isunique.
  Defined.

  End ToFinalInHSET.

  Section IngredientsOfAnAdjunction.

  Local Definition out_set_trunc (C : coalgebra F) : coalgebra_ob F C → pr1hSet (F' (settrunc (coalgebra_ob F C))).
  Proof.
    intro x.
    destruct C as [c s_c].
    cbn -[settrunc].
    unfold polynomial_functor_obj.
    use tpair.
    - exact (pr1(s_c(x))).
    - intro b.
      exact (settruncin c (pr2(s_c(x))(b))).
  Defined.

  Definition coalg_set_trunc (C : coalgebra F) : FunctorCoalgebras.CoAlg_category F'.
  Proof.
    exists (settrunc (coalgebra_ob F C)).
    exact (settrunc_rec _ (out_set_trunc C)).
  Defined.

  Lemma is_coalgebra_homo_comp_with_settruncin (C : coalgebra F) (C0' : FunctorCoalgebras.coalgebra_ob F') (f : FunctorCoalgebras.CoAlg_category F' ⟦coalg_set_trunc C, C0'⟧)
    : is_coalgebra_homo F (X:=C) (Y:=FromCoalgInHSET C0') (λ x, pr1 f (settruncin ((coalgebra_ob F C)) x)).
  Proof.
    destruct f as [φ p1].
    set (s0' := FunctorCoalgebras.coalg_map F' C0').
    destruct C as [c s_c].
    cbn in c.
    cbn in s_c.
    unfold polynomial_functor_obj in s_c.
    set (c' := settrunc c).
    set (C' := coalg_set_trunc (c,, s_c) : FunctorCoalgebras.coalgebra_ob F').
    set (s_c' := FunctorCoalgebras.coalg_map _ C' : c' → pr1hSet (F' c')).
    cbn -[settrunc] in φ.
    set (ψ := λ x, φ(settruncin c x) : pr1 (FunctorCoalgebras.coalg_carrier F' C0')).
    change (is_coalgebra_homo F (X:=(c,,s_c)) (Y:=FromCoalgInHSET C0') ψ).
    unfold is_coalgebra_homo.
    apply funextfun.
    intro x.
    cbn in x.
    symmetry.
    assert (p21 : (s0'(ψ(x)) = s0'(φ(settruncin c x)))).
    { unfold ψ. apply idpath. }
    assert (p22 : s0'(ψ(x)) = (#F φ)(s_c'(settruncin c x))).
    {
      etrans.
      - apply p21.
      - set (f1 := λ y : c', s0'(φ(y))).
        set (f2 := λ y : c', (#F φ)(s_c'(y))).
        set (x' := settruncin c x : c').
        assert (p221 : f1 = f2).
        { cbn -[settrunc] in p1. unfold f1, f2. cbn -[settrunc]. unfold s0'. symmetry. apply p1. }
        assert (p222 : f1 x' = f2 x').
        { apply (toforallpaths _ f1 f2 p221). }
        apply p222.
    }
    assert (p23 : s0'(ψ(x)) = (#F ψ)(s_c(x))).
    {
      etrans.
      - apply p22.
      - apply idpath.
    }
    apply p23.
  Qed.

  Lemma is_homo_of_coalgebras_settrunc_rec (C : coalgebra F) (C0' : FunctorCoalgebras.coalgebra_ob F') (f' : coalgebra_homo F _ (FromCoalgInHSET C0'))
    : pr2 (coalg_set_trunc C) -->[settrunc_rec _ (pr1 f')] pr2 (FromCoalgInHSET C0').
  Proof.
    destruct f' as [ψ' p'].
    cbn in ψ'.
    set (φ' := settrunc_rec _ ψ').
    destruct C as [c s_c].
    set (s0' := FunctorCoalgebras.coalg_map F' C0').
    set (C' := coalg_set_trunc (c,, s_c) : FunctorCoalgebras.coalgebra_ob F').
    set (s_c' := FunctorCoalgebras.coalg_map _ C').
    assert (p11' : (s0' ∘ φ' ∘ (settruncin c))%functions = ((#F φ') ∘ s_c' ∘ (settruncin c))%functions).
    {
      unfold is_coalgebra_homo in p'.
      cbn in p'.
      symmetry.
      apply p'.
    }
    apply settrunc_rec_unique.
    intro x.
    apply pathsinv0.
    apply (toforallpaths _ _ _ p11').
  Qed.

  End IngredientsOfAnAdjunction.

  Section FromFinalInHSET.

    Context (C0' : FunctorCoalgebras.coalgebra_ob F').
    Context (C0'_is_final : isTerminal (FunctorCoalgebras.CoAlg_category F') C0').

    Definition C0 : coalgebra F := FromCoalgInHSET C0'.

  Lemma C0_is_final : is_final C0.
  Proof.
    set (s0' := FunctorCoalgebras.coalg_map F' C0').
    intros [c s_c].
    cbn in c.
    cbn in s_c.
    unfold polynomial_functor_obj in s_c.
    set (c' := settrunc c).
    set (C' := coalg_set_trunc (c,, s_c) : FunctorCoalgebras.coalgebra_ob F').
    set (s_c' := FunctorCoalgebras.coalg_map _ C' : c' → pr1hSet (F' c')).
    destruct (C0'_is_final C') as [f isunique].
    use tpair.
    - use tpair.
      2: { apply (is_coalgebra_homo_comp_with_settruncin _ _ f). }
    - intro f'.
      set (φ' := settrunc_rec _ (pr1 f')).
      set (p1' := is_homo_of_coalgebras_settrunc_rec _ _ f').
      assert (p41 : (φ',, p1') = f).
      {
        apply (isunique (φ',, p1')).
      }
      assert (p411 := maponpaths (λ x, pr1 x) p41 : (φ' = pr1 f)).
      clear p41.
      use total2_paths_f.
      + apply funextfun.
        intro x.
        etrans.
        * assert (p421 : pr1 f' x = φ' (settruncin c x)).
          {
            apply idpath.
          }
          apply p421.
        * apply (toforallpaths _ φ' (pr1 f) p411).
      + (* show_id_type.
           unfold is_coalgebra_homo in TYPE. *)
        set (is_set := isaset_forall_hSet c (λ _, F' (pr1 C0'))).
        apply is_set.
  Defined.

  End FromFinalInHSET.
End M.
