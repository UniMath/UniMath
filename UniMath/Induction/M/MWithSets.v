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
Require UniMath.Induction.FunctorCoalgebras_legacy_alt_UU.

Require Import UniMath.CategoryTheory.Categories.Type.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require UniMath.CategoryTheory.FunctorCoalgebras.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

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

    Let c0 : type_precat := coalgebra_ob F C0.

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

    Lemma C0_is_final_unicity
      {c : UU}
      {s_c : c -> F c}
      (C' := (coalg_set_trunc (c,, s_c) : FunctorCoalgebras.coalgebra_ob F')
    : FunctorCoalgebras.coalgebra_ob F')
      {f : FunctorCoalgebras.CoAlg_category F' ⟦ C', C0' ⟧}
      (isunique : ∏ t : FunctorCoalgebras.CoAlg_category F' ⟦ C', C0' ⟧, t = f)
      (f' : coalgebra_homo F (c,, s_c) C0)
      : f' =
          (λ x : coalgebra_ob F (c,, s_c), (pr1 f (settruncin (coalgebra_ob F (c,, s_c)) x)) : coalgebra_ob F C0),,
            is_coalgebra_homo_comp_with_settruncin (c,, s_c) C0' f.
    Proof.
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
    Qed.

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
        apply C0_is_final_unicity.
        apply isunique.
    Defined.

  End FromFinalInHSET.

  Section FunctorAdjunctions_UU_HSET.

    (** If the definition of a coalgebra is tweaked, we can show an adjunction between the
       two functors going from UU coalgebras to HSET coalgebras and vice versa.
       This result shall not be used for other purposes but rather gives an intuition for
       the results above.
     *)

    Local Definition cat1 := UniMath.Induction.FunctorCoalgebras_legacy_alt_UU.CoAlg_precategory F.
    Local Definition cat2 := CoAlg_precategory F'.

    (* HSET -> UU coalgebras functor*)

    Definition functor_coalgebra_HSET_to_UU_obj (C : FunctorCoalgebras.coalgebra_ob F') : (coalgebra F).
    Proof.
      exact (pr1 (pr1 C),, pr2 C).
    Defined.

    Definition functor_coalgebra_HSET_to_UU_data : functor_data cat2 cat1.
    Proof.
      use make_functor_data.
      - exact functor_coalgebra_HSET_to_UU_obj.
      - intros a b f.
        exists (pr1 f).
        intro x.
        exact (hinhpr (toforallpaths _ _ _ (pr2 f) x)).
    Defined.

    Lemma functor_coalgebra_HSET_to_UU_is_functor : is_functor functor_coalgebra_HSET_to_UU_data.
    Proof.
      split.
      - unfold functor_idax.
        intro.
        use total2_paths_f.
        + apply idpath.
        + use funextsec. intro.
          apply isapropishinh.
      - unfold functor_compax.
        intros.
        use total2_paths_f.
        + apply idpath.
        + use funextsec. intro.
          apply isapropishinh.
    Defined.

    Definition functor_coalgebra_HSET_to_UU : functor cat2 cat1 := _,, functor_coalgebra_HSET_to_UU_is_functor.

    (* UU -> HSET coalgebras functor *)

    Definition functor_coalgebra_UU_to_HSET_obj (C : coalgebra F) : FunctorCoalgebras.coalgebra_ob F'.
    Proof.
      exact (coalg_set_trunc C).
    Defined.

    Lemma is_morph_UU_to_HSET {a b : coalgebra F} {f : type_precat ⟦ pr1 a, pr1 b ⟧} (x : pr1 a) (p : ((pr2 a) · #F f) x = (f · (pr2 b)) x ) :
      tpair (λ a, pr1hSet (B a) -> settrunc (pr1 b)) (pr1 (((pr2 a) · #F f) x)) (λ y, settruncin _ (pr2 (((pr2 a) · #F f) x) y)) = tpair (λ a, pr1hSet (B a) -> settrunc (pr1 b)) (pr1 ((f · (pr2 b)) x)) (λ y, settruncin _ (pr2 ((f · (pr2 b)) x) y)).
    Proof.
      induction p.
      apply idpath.
    Defined.

    Definition functor_coalgebra_UU_to_HSET_data : functor_data cat1 cat2.
    Proof.
      use make_functor_data.
      - exact functor_coalgebra_UU_to_HSET_obj.
      - intros a b f.
        cbn.
        cbn -[settrunc].
        set (f0 := settrunc_rec _ (λ x, settruncin _ (pr1 f x)) :  SET ⟦ pr1 (functor_coalgebra_UU_to_HSET_obj a), pr1 (functor_coalgebra_UU_to_HSET_obj b) ⟧).
        assert (p1 : ∏ x : pr1 a, ∥ (pr2 (functor_coalgebra_UU_to_HSET_obj a) · # F' f0) (settruncin _ x) = (f0 · pr2 (functor_coalgebra_UU_to_HSET_obj b)) (settruncin _ x) ∥ ).
        {
          intro x.
          cbn -[F'].
          set (goal := ∥ # F' f0 (out_set_trunc a x) = out_set_trunc b (pr1 f x) ∥).
          set (p11 := UniMath.Induction.FunctorCoalgebras_legacy_alt_UU.coalgebra_homo_commutes F f x goal).
          apply p11.
          cbn -[F F'].
          intro p12.
          set (p13 := is_morph_UU_to_HSET x p12).
          exact (hinhpr p13).
        }
        assert (p2 : ∏ x : pr1 (settrunc (coalgebra_ob F a)), ∥ ((pr2 (functor_coalgebra_UU_to_HSET_obj a)) · #F' f0) x = (f0 · (pr2 (functor_coalgebra_UU_to_HSET_obj b))) x ∥).
        {
          use setquotunivprop'.
          - intro. apply propproperty.
          - apply p1.
        }
        assert (p3 : is_coalgebra_homo F' f0).
        {
          use funextfun.
          intro x.
          simple refine (factor_through_squash _  _ (p2 x)).
          - apply setproperty.
          - trivial.
        }
        exact (f0,, p3).
    Defined.

    Lemma functor_coalgebra_UU_to_HSET_is_functor : is_functor functor_coalgebra_UU_to_HSET_data.
    Proof.
      split.
      - intro.
        use total2_paths_f.
        + cbn -[settrunc].
          assert (p : ∏ x : pr1 a, settrunc_rec (FunctorCoalgebras_legacy_alt_UU.coalgebra_ob F a) (λ x : FunctorCoalgebras_legacy_alt_UU.coalgebra_ob F a, settruncin (FunctorCoalgebras_legacy_alt_UU.coalgebra_ob F a) x) (settruncin _ x) = (λ x : settrunc (coalgebra_ob F a), x) (settruncin _ x)).
          { intro x.
            apply idpath.
          }
          apply (settrunc_rec_unique _ _ _ p).
        + apply isaset_forall_hSet.
      - unfold functor_compax.
        intros.
        use total2_paths_f.
        + assert (p : ∏ x : pr1 a, pr1 (# functor_coalgebra_UU_to_HSET_data (f · g)) (settruncin _ x)=
                                     pr1 (# functor_coalgebra_UU_to_HSET_data f · # functor_coalgebra_UU_to_HSET_data g) (settruncin _ x)).
          { intro x. apply idpath. }
          apply (settrunc_rec_unique _ _ _ p).
        + apply isaset_forall_hSet.
    Defined.

    Definition functor_coalgebra_UU_to_HSET : functor cat1 cat2 := _,, functor_coalgebra_UU_to_HSET_is_functor.

    (* Adjunction *)

    Definition adj_unit_coalg_data : nat_trans_data (pr1 (functor_identity cat1)) (pr1 (functor_coalgebra_UU_to_HSET ∙ functor_coalgebra_HSET_to_UU)).
    Proof.
      unfold nat_trans_data.
      intro X.
      cbn.
      unfold FunctorCoalgebras_legacy_alt_UU.coalgebra_homo.
      cbn -[F F' settrunc].
      set (f := (settruncin (pr1 X)) : type_precat ⟦ FunctorCoalgebras_legacy_alt_UU.coalgebra_ob F X, FunctorCoalgebras_legacy_alt_UU.coalgebra_ob F ((functor_coalgebra_UU_to_HSET ∙ functor_coalgebra_HSET_to_UU) X) ⟧).
      assert (p : ∏ x : FunctorCoalgebras_legacy_alt_UU.coalgebra_ob F X, ∥ (FunctorCoalgebras_legacy_alt_UU.is_coalgebra_homo F f x) ∥).
      {
        intro x.
        exact (hinhpr (idpath ((#F f ∘ (pr2 X)) x))).
      }
      exact (f,, p).
    Defined.

    Lemma adj_unit_coalg_is_nat_trans : is_nat_trans _ _ adj_unit_coalg_data.
    Proof.
      unfold is_nat_trans.
      intros.
      cbn -[F F' functor_coalgebra_UU_to_HSET functor_coalgebra_HSET_to_UU].
      use total2_paths_f.
      - apply idpath.
      - use funextsec. intro. apply isapropishinh.
    Defined.

    Definition adj_unit_coalg : nat_trans _ _ := _,, adj_unit_coalg_is_nat_trans.

    Definition adj_counit_coalg_data : nat_trans_data (pr1 (functor_coalgebra_HSET_to_UU ∙ functor_coalgebra_UU_to_HSET)) (pr1 (functor_identity cat2)).
    Proof.
      unfold nat_trans_data.
      intro X.
      cbn.
      cbn -[F F' settrunc].
      set (f := settrunc_rec _ (λ x : pr11 X, x) : SET ⟦ pr1 ((functor_coalgebra_HSET_to_UU ∙ functor_coalgebra_UU_to_HSET) X), pr1 X ⟧).
      assert (p1 :  ∏ x : pr1 (settrunc (pr11 X)), ∥ ((pr2 ((functor_coalgebra_HSET_to_UU ∙ functor_coalgebra_UU_to_HSET) X)) · #F' f) x = (f · pr2 X) x ∥).
      {
        use setquotunivprop'.
        - intro. apply propproperty.
        - intro. exact (hinhpr (idpath (((pr2 X) ∘ f) (settruncin _ x)))).
      }
      assert (p2 : is_coalgebra_homo F' f).
      {
        use funextfun.
        intro x.
        simple refine (factor_through_squash _  _ (p1 x)).
        - apply setproperty.
        - trivial.
      }
      exact (f,, p2).
    Defined.

    Lemma adj_counit_coalg_is_nat_trans : is_nat_trans _ _ adj_counit_coalg_data.
    Proof.
      unfold is_nat_trans.
      intros.
      cbn  -[F F' functor_coalgebra_UU_to_HSET functor_coalgebra_HSET_to_UU].
      use total2_paths_f.
      - cbn -[F F' settrunc].
        use settrunc_rec_unique.
        intro. apply idpath.
      - apply isaset_forall_hSet.
    Defined.

    Definition adj_counit_coalg : nat_trans _ _ := _,, adj_counit_coalg_is_nat_trans.

    Lemma adj_coalg : are_adjoints functor_coalgebra_UU_to_HSET functor_coalgebra_HSET_to_UU.
    Proof.
      assert (p : form_adjunction _ _ adj_unit_coalg adj_counit_coalg).
      {
        use make_form_adjunction.
        - intro.
          use total2_paths_f.
          + cbn -[F F' settrunc].
            use settrunc_rec_unique.
            intro. apply idpath.
          + apply isaset_forall_hSet.
        - intro.
          use total2_paths_f.
          + apply idpath.
          + use funextsec. intro. apply isapropishinh.
      }
      exact ((adj_unit_coalg,, adj_counit_coalg),, p).
    Defined.

  End FunctorAdjunctions_UU_HSET.
End M.
