(** A direct definition of finite ordered products by using products *)

Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Local Open Scope cat.
Local Open Scope stn.

(** Definition of finite ordered products. *)
Section def_FinOrdProducts.

  Variable C : category.

  Definition FinOrdProducts : UU :=
    ∏ (n : nat) (a : stn n -> C), Product (stn n) C a.
  Definition hasFinOrdProducts : UU :=
    ∏ (n : nat) (a : stn n -> C), ∥ Product (stn n) C a ∥.

End def_FinOrdProducts.


(** Construction of FinOrdProducts from Terminal and BinProducts. *)
Section FinOrdProduct_criteria.

  Variable C : category.

  (** Case n = 0 of the theorem. *)
  Lemma TerminalToProduct (T : Terminal C):
    ∏ (a : stn 0 -> C), Product (stn 0) C a.
  Proof.
    intros a.
    use make_Product.
    - exact T.
    - exact(λ (x : ⟦ 0 ⟧), fromempty (weqstn0toempty x)).
    - intros c g.
      use unique_exists.
      + apply TerminalArrow.
      + exact(λ (x : ⟦ 0 ⟧), fromempty (weqstn0toempty x)).
      + intro; apply impred_isaprop.
        intro; apply homset_property.
      + intros; apply TerminalArrowEq.
  Defined.

  Local Definition products_stn_unit (n : nat) :
    Products (⟦ n ⟧) C -> BinProducts C -> Products (⟦ n ⟧ ⨿ unit) C.
  Proof.
    intros NProds BinProds.
    intro t.
    set (N := NProds (t ∘ inl)%functions).
    set (E := t (inr tt)).
    set (B := BinProds (ProductObject _ _ N) E).
    use make_Product.
    - exact(BinProductObject _ B).
    - apply coprod_rect.
      + intro k.
        exact(BinProductPr1 _ B · (ProductPr _ _ N k)).
      + apply unit_rect.
        exact(BinProductPr2 _ B).
    - intros Q q.
      use unique_exists.
      + apply BinProductArrow.
        * apply ProductArrow.
          exact(q ∘ inl)%functions.
        * exact(q (inr tt)).
      + use coprod_rect.
        * intros k.
          etrans. { apply assoc. }
          etrans. { apply maponpaths_2. apply BinProductPr1Commutes. }
          use ProductPrCommutes.
        * apply unit_rect.
          apply BinProductPr2Commutes.
      + abstract(intros; apply impred_isaprop; intro; apply homset_property).
      + intros f fcommutes.
        apply BinProductArrowUnique.
        * apply ProductArrowUnique; intro k.
          etrans. { apply assoc'. }
          exact(fcommutes (inl k)).
        * exact(fcommutes (inr tt)).
  Defined.

  Local Definition products_stn_Sn
    (n : nat)
    (stnprods : Products (⟦ n ⟧ ⨿ unit) C)
    : Products (⟦ S n ⟧) C.
  Proof.
    pose(w := (weqdnicoprod n lastelement)).
    pose(q := invmap (univalence _ _) w).
    exact(transportf (fun X : UU => Products X C) q stnprods).
  Defined.

  (** Finite ordered products from terminal and binary products *)
  Theorem FinOrdProducts_from_Terminal_and_BinProducts :
    Terminal C -> BinProducts C -> FinOrdProducts C.
  Proof.
    intros T BinProds n.
    induction n as [|n IHn].
    - (* Case n = 0 *)
      exact(TerminalToProduct T).
    - (* Case (S n) assuming n. *)
      apply products_stn_Sn.
      now apply products_stn_unit.
  Defined.

End FinOrdProduct_criteria.
