(** A direct definition of finite ordered coproducts by using coproducts *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.initial.

Local Open Scope cat.
Local Open Scope stn.

(** Definition of finite ordered coproducts. *)
Section def_FinOrdCoproducts.

  Variable C : category.

  Definition FinOrdCoproducts : UU :=
    ∏ (n : nat) (a : stn n -> C), Coproduct (stn n) C a.
  Definition hasFinOrdCoproducts : UU :=
    ∏ (n : nat) (a : stn n -> C), ∥ Coproduct (stn n) C a ∥.

End def_FinOrdCoproducts.


(** Construction of FinOrdCoproducts from Initial and BinCoproducts. *)
Section FinOrdCoproduct_criteria.

  Variable C : category.

  (** Case n = 0 of the theorem. *)
  Lemma InitialToCoproduct (I : Initial C):
    ∏ (a : stn 0 -> C), Coproduct (stn 0) C a.
  Proof.
    intros a.
    use (make_Coproduct _ _ _ I
                            (λ i : stn 0, fromempty (weqstn0toempty i))).
    intros c g.
    use unique_exists.
    - apply (InitialArrow I c).
    - intros i. apply (fromempty (weqstn0toempty i)).
    - intro; apply impred_isaprop.
      intro; apply homset_property.
    - intros. apply InitialArrowUnique.
  Defined.

  (** Case n = 1 of the theorem. *)
  Lemma ObjectToCoproduct:
    ∏ (a : stn 1 -> C), Coproduct (stn 1) C a.
  Proof.
    intros a.
    set (stn1ob := invweq(weqstn1tounit) tt).
    use (make_Coproduct _ _ _ (a stn1ob)).
    intros i. exact (idtoiso (! (maponpaths a (isconnectedstn1 stn1ob i)))).

    (* isCoproductcocone *)
    use (make_isCoproduct _ _ C).
    intros c g.
    use (unique_exists (g stn1ob)).

    (* Commutativity. *)
    intros i. rewrite <- (isconnectedstn1 stn1ob i). apply id_left.

    (* Equality of equalities of morphisms. *)
    intros y. apply impred_isaprop. intros t. apply C.

    (* Uniqueness. *)
    intros y X. rewrite <- (X stn1ob). apply pathsinv0. apply id_left.
  Defined.

  Local Definition coproducts_stn_unit {n : nat}
    (Ncoprods : Coproducts (⟦ n ⟧) C)
    (BinCoprods : BinCoproducts C)
    : Coproducts (⟦ n ⟧ ⨿ unit) C.
  Proof.
    intro t.
    set (N := Ncoprods (t ∘ inl)%functions).
    set (E := t (inr tt)).
    set (B := BinCoprods (CoproductObject _ _ N) E).
    use make_Coproduct.
    - exact(BinCoproductObject B).
    - apply coprod_rect.
      + exact(λ k : ⟦ n ⟧, CoproductIn _ C N k · BinCoproductIn1 B).
      + exact(unit_rect _ (BinCoproductIn2 B)).
    - intros Q q.
      use unique_exists.
      + apply BinCoproductArrow.
        * apply CoproductArrow.
          exact(q ∘ inl)%functions.
        * exact(q (inr tt)).
      + use coprod_rect.
        * intros k.
          etrans. { apply assoc'. }
          etrans.
          {
            apply maponpaths.
            apply BinCoproductIn1Commutes.
          }
          use CoproductInCommutes.
        * apply unit_rect.
          apply BinCoproductIn2Commutes.
      + abstract(intros; apply impred_isaprop; intro; apply homset_property).
      + intros f fcommutes.
        apply BinCoproductArrowUnique.
        * apply CoproductArrowUnique; intro k.
          etrans. { apply assoc. }
          exact(fcommutes (inl k)).
        * exact(fcommutes (inr tt)).
  Defined.

  Local Definition coproducts_stn_Sn
    (n : nat)
    (stncoprods : Coproducts (⟦ n ⟧ ⨿ unit) C)
    : Coproducts (⟦ S n ⟧) C.
  Proof.
    set(w := (weqdnicoprod n lastelement)).
    set(q := invmap (univalence _ _) w).
    exact(transportf (fun X : UU => Coproducts X C) q stncoprods).
  Defined.

  (** Finite ordered coproducts from initial and binary coproducts. *)
  Theorem FinOrdCoproducts_from_Initial_and_BinCoproducts :
    Initial C -> BinCoproducts C -> FinOrdCoproducts C.
  Proof.
    intros I BinCoprods n.
    induction n as [|n IHn].

    - exact(InitialToCoproduct I). (* Case n = 0 *)
    - apply coproducts_stn_Sn.
      exact(coproducts_stn_unit IHn BinCoprods).
  Defined.

End FinOrdCoproduct_criteria.
