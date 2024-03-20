(***********************************************************************************************

 Subobject classifieres in slice categories

 If `C` is a category with a subobject classifier `Ω`, then the slice categories `C/x` have a
 subobject classifier for every object `x`. This subobject classifier is given by `x × Ω --> x`.

 To understand why `x × Ω --> x` is a subobject classifier, we need to realize a couple of
 things. The first is that morphisms `y₁ --> y₂` in `C/x` are monomorphisms if and only if the
 underlying morphism from `y₁` to `y₂` is a monomorphism. This allows us to use the universal
 property of `Ω` to say something about the universal property of `x × Ω`. The second thing is a
 difficulty that arises from the fact that the terminal object of `C/x` is given by `x --> x`,
 and that it does not use the terminal object in `C`. As such, if we have a monomorphism
 `y₁ --> y₂` in the slice category, then we get the following pullback square in `C`:

<<
   y₁ ---> 𝟙
   |       |
   |       |
   V       V
   y₂ ---> Ω
>>

 whereas we would like to have a pullback square like this

<<
   y₁ -----> x
   |         |
   |         |
   V         V
   y₂ ---> x × Ω
>>

 where each of the objects in this diagram lives in the slice category. Proving that we have
 the desired pullback squares, is a matter of doing it.

 Contents
 1. The universal property
 2. The subobject classifier

 ***********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodMorphisms.

Local Open Scope cat.

Section SubobjectClassifier.
  Context {C : category}
          (T : Terminal C)
          (P : BinProducts C)
          (Ω : subobject_classifier T)
          (x : C).

  (** * 1. The universal property *)
  Section UMP.
    Context {zg₁ zg₂ : C/x}
            (mp : Monic _ zg₁ zg₂).

    Let z₁ : C := cod_dom zg₁.
    Let g₁ : z₁ --> x := cod_mor zg₁.

    Let z₂ : C := cod_dom zg₂.
    Let g₂ : z₂ --> x := cod_mor zg₂.

    Let m_mor : z₁ --> z₂ := dom_mor mp.

    Local Lemma monic_mor_of_slice
      : isMonic m_mor.
    Proof.
      use from_is_monic_cod_fib.
      exact (pr2 mp).
    Qed.

    Let m : Monic _ z₁ z₂ := make_Monic _ _ monic_mor_of_slice.

    Definition cod_fib_subobject_classifier_mor_map
      : z₂ --> P x Ω.
    Proof.
      use BinProductArrow.
      - exact g₂.
      - exact (characteristic_morphism Ω m).
    Defined.

    Definition cod_fib_subobject_classifier_mor
      : zg₂ --> pr_cod_fib P x Ω.
    Proof.
      use make_cod_fib_mor.
      - exact cod_fib_subobject_classifier_mor_map.
      - abstract
          (apply BinProductPr1Commutes).
    Defined.

    Proposition cod_fib_subobject_classifier_comm
      : mp · cod_fib_subobject_classifier_mor
        =
        TerminalArrow (codomain_fib_terminal x) zg₁
        · mor_to_pr_cod_fib P (cod_fib_id x) (const_true x Ω).
    Proof.
      use eq_mor_cod_fib.
      rewrite !comp_in_cod_fib.
      cbn.
      rewrite id_right.
      unfold cod_fib_subobject_classifier_mor_map.
      use BinProductArrowsEq.
      - rewrite !assoc'.
        rewrite !BinProductPr1Commutes.
        rewrite id_right.
        exact (mor_eq mp).
      - rewrite !assoc'.
        rewrite !BinProductPr2Commutes.
        refine (subobject_classifier_square_commutes Ω m @ _).
        unfold const_true.
        rewrite !assoc.
        apply maponpaths_2.
        apply TerminalArrowEq.
    Qed.

    Proposition cod_fib_subobject_classifier_comm_dom
      : m · cod_fib_subobject_classifier_mor_map
        =
        g₁ · identity _ · dom_mor (mor_to_pr_cod_fib P (cod_fib_id x) (const_true x Ω)).
    Proof.
      exact (!(comp_in_cod_fib _ _)
             @ maponpaths dom_mor cod_fib_subobject_classifier_comm
             @ comp_in_cod_fib _ _).
    Qed.

    Section PBUMP.
      Context {w : C}
              (h : w --> z₂)
              (k : w --> x)
              (p : h · cod_fib_subobject_classifier_mor_map
                   =
                   k · BinProductArrow C (P x Ω) (identity x) (const_true x Ω)).

      Let PB : Pullback (characteristic_morphism Ω m) Ω
        := subobject_classifier_pullback Ω m.

      Proposition cod_fib_subobject_classifier_pb_unique
        : isaprop
            (∑ hk,
             (hk · m = h)
             ×
             (hk · (cod_mor zg₁ · identity x) = k)).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use (MorphismsIntoPullbackEqual (isPullback_Pullback PB)).
        - exact (pr12 φ₁ @ !(pr12 φ₂)).
        - apply TerminalArrowEq.
      Qed.

      Definition cod_fib_subobject_classifier_pb_map
        : w --> z₁.
      Proof.
        use (PullbackArrow PB).
        - exact h.
        - apply TerminalArrow.
        - abstract
            (pose (maponpaths (λ z, z · BinProductPr2 _ _) p) as q ;
             cbn in q ;
             unfold cod_fib_subobject_classifier_mor_map, const_true in q ;
             rewrite !assoc' in q ;
             rewrite !BinProductPr2Commutes in q ;
             refine (q @ _) ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             apply TerminalArrowEq).
      Defined.

      Proposition cod_fib_subobject_classifier_pb_pr1
        : cod_fib_subobject_classifier_pb_map · m = h.
      Proof.
        apply (PullbackArrow_PullbackPr1 PB).
      Qed.

      Proposition cod_fib_subobject_classifier_pb_pr2
        : cod_fib_subobject_classifier_pb_map · (g₁ · identity x) = k.
      Proof.
        rewrite id_right.
        pose (maponpaths (λ z, z · BinProductPr1 _ _) p) as q.
        cbn in q.
        unfold cod_fib_subobject_classifier_mor_map, const_true in q.
        rewrite !assoc' in q.
        rewrite !BinProductPr1Commutes in q.
        rewrite id_right in q.
        refine (_ @ q).
        etrans.
        {
          apply maponpaths.
          exact (!(mor_eq mp)).
        }
        rewrite !assoc.
        apply maponpaths_2.
        apply (PullbackArrow_PullbackPr1 PB).
      Qed.
    End PBUMP.

    Proposition cod_fib_subobject_classifier_pb
      : isPullback cod_fib_subobject_classifier_comm.
    Proof.
      use to_is_pullback_slice.
      - exact cod_fib_subobject_classifier_comm_dom.
      - intros w h k p.
        use iscontraprop1.
        + apply cod_fib_subobject_classifier_pb_unique.
        + simple refine (_ ,, _ ,, _).
          * exact (cod_fib_subobject_classifier_pb_map h k p).
          * apply cod_fib_subobject_classifier_pb_pr1.
          * apply cod_fib_subobject_classifier_pb_pr2.
    Defined.

    Proposition cod_fib_subobject_classifier_unique_eq
                (χ : zg₂ --> pr_cod_fib P x Ω)
                (p : mp · χ
                     =
                     TerminalArrow (codomain_fib_terminal x) zg₁
                     · mor_to_pr_cod_fib P (codomain_fib_terminal x) (const_true x Ω))
                (H : isPullback p)
      : m · (dom_mor χ · BinProductPr2 C (P x Ω)) = const_true z₁ Ω.
    Proof.
      pose (maponpaths dom_mor p) as q.
      rewrite !comp_in_cod_fib in q.
      rewrite !assoc.
      refine (maponpaths (λ z, z · _) q @ _).
      cbn.
      rewrite id_right.
      rewrite !assoc'.
      rewrite BinProductPr2Commutes.
      unfold const_true.
      rewrite !assoc.
      apply maponpaths_2.
      apply TerminalArrowEq.
    Qed.

    Section SubPBUMP.
      Context {χ : zg₂ --> pr_cod_fib P x Ω}
              {p : mp · χ
                   =
                   TerminalArrow (codomain_fib_terminal x) zg₁
                   · mor_to_pr_cod_fib P (codomain_fib_terminal x) (const_true x Ω)}
              (H : isPullback p)
              {w : C}
              (h : w --> z₂)
              (k : w --> T)
              (r : h · (dom_mor χ · BinProductPr2 C (P x Ω)) = k · Ω).

      Local Lemma cod_fib_subobject_classifier_unique_pb_eq
        : dom_mor mp
          · dom_mor χ
          =
          dom_mor (TerminalArrow (codomain_fib_terminal x) zg₁)
          · dom_mor (mor_to_pr_cod_fib P (codomain_fib_terminal x) (const_true x Ω)).
      Proof.
        rewrite <- !comp_in_cod_fib.
        rewrite p.
        apply idpath.
      Qed.

      Let q := cod_fib_subobject_classifier_unique_pb_eq.
      Let PB := make_Pullback _ (from_is_pullback_slice _ _ _ _ q _ H).

      Local Lemma cod_fib_subobject_classifier_unique_pb_map_eq
        : h · dom_mor χ
          =
          h · g₂ · BinProductArrow C (P x Ω) (identity x) (const_true x Ω).
      Proof.
        use BinProductArrowsEq.
        - rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            exact (mor_eq χ).
          }
          rewrite BinProductPr1Commutes.
          rewrite id_right.
          apply idpath.
        - rewrite !assoc'.
          rewrite BinProductPr2Commutes.
          refine (r @ _).
          unfold const_true.
          rewrite !assoc.
          apply maponpaths_2.
          apply TerminalArrowEq.
      Qed.

      Definition cod_fib_subobject_classifier_unique_pb_map
        : w --> z₁.
      Proof.
        use (PullbackArrow PB _ h (h · g₂)).
        exact cod_fib_subobject_classifier_unique_pb_map_eq.
      Defined.

      Proposition cod_fib_subobject_classifier_unique_pb_pr1
        : cod_fib_subobject_classifier_unique_pb_map · m = h.
      Proof.
        apply (PullbackArrow_PullbackPr1 PB).
      Qed.

      Proposition cod_fib_subobject_classifier_unique_pb_unique
        : isaprop (∑ hk, hk · m = h × hk · TerminalArrow T z₁ = k).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use (MorphismsIntoPullbackEqual (isPullback_Pullback PB)).
        - exact (pr12 φ₁ @ !(pr12 φ₂)).
        - cbn.
          rewrite id_right.
          rewrite <- !(mor_eq mp).
          rewrite !assoc.
          apply maponpaths_2.
          exact (pr12 φ₁ @ !(pr12 φ₂)).
      Qed.
    End SubPBUMP.

    Definition cod_fib_subobject_classifier_unique_pb
               (χ : zg₂ --> pr_cod_fib P x Ω)
               (p : mp · χ
                    =
                    TerminalArrow (codomain_fib_terminal x) zg₁
                    · mor_to_pr_cod_fib P (codomain_fib_terminal x) (const_true x Ω))
               (H : isPullback p)
      : isPullback (cod_fib_subobject_classifier_unique_eq χ p H).
    Proof.
      intros w h k r.
      use iscontraprop1.
      - exact (cod_fib_subobject_classifier_unique_pb_unique H h k).
      - simple refine (_ ,, _ ,, _).
        + exact (cod_fib_subobject_classifier_unique_pb_map H h k r).
        + apply cod_fib_subobject_classifier_unique_pb_pr1.
        + abstract
            (apply TerminalArrowEq).
    Defined.

    Proposition cod_fib_subobject_classifier_unique
      : isaprop
          (∑ (χ : zg₂ --> pr_cod_fib P x Ω)
             (H : mp · χ
                  =
                  TerminalArrow (codomain_fib_terminal x) zg₁
                  · mor_to_pr_cod_fib P (codomain_fib_terminal x) (const_true x Ω)),
            isPullback H).
    Proof.
      use invproofirrelevance.
      intros χ₁ χ₂.
      use subtypePath.
      {
        intro.
        apply isaproptotal2.
        {
          intro.
          apply isaprop_isPullback.
        }
        intros.
        apply homset_property.
      }
      use eq_mor_cod_fib.
      use BinProductArrowsEq.
      - exact (mor_eq (pr1 χ₁) @ !(mor_eq (pr1 χ₂))).
      - use (subobject_classifier_map_eq Ω m).
        + exact (cod_fib_subobject_classifier_unique_eq (pr1 χ₁) (pr12 χ₁) (pr22 χ₁)).
        + exact (cod_fib_subobject_classifier_unique_eq (pr1 χ₂) (pr12 χ₂) (pr22 χ₂)).
        + apply cod_fib_subobject_classifier_unique_pb.
        + apply cod_fib_subobject_classifier_unique_pb.
    Qed.
  End UMP.

  (** * 2. The subobject classifier *)
  Definition cod_fib_subobject_classifier
    : subobject_classifier (codomain_fib_terminal x).
  Proof.
    use make_subobject_classifier.
    - exact (pr_cod_fib P x Ω).
    - use mor_to_pr_cod_fib.
      exact (const_true x Ω).
    - intros zg₁ zg₂ mp.
      use iscontraprop1.
      + apply cod_fib_subobject_classifier_unique.
      + simple refine (_ ,, _ ,, _).
        * exact (cod_fib_subobject_classifier_mor mp).
        * exact (cod_fib_subobject_classifier_comm mp).
        * exact (cod_fib_subobject_classifier_pb mp).
  Defined.
End SubobjectClassifier.
