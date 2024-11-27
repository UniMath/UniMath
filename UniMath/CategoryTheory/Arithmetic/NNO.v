(**

Definition natural number objects (NNO's)

This is related to the initial algebra definition in FunctorAlgebras.v

Written by: Anders Mörtberg, 2018

*)
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.

Local Open Scope cat.

Section nno.

Context {C : category} (TC : Terminal C).

Local Notation "1" := TC.

Definition isNNO (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧) : hProp.
Proof.
use tpair.
- exact (∏ (a : C) (q : C ⟦ 1, a ⟧) (f : C ⟦ a, a ⟧),
         ∃! u : C ⟦ n, a ⟧, (z · u = q) × (s · u = u · f)).
- abstract (repeat (apply impred_isaprop; intros); apply isapropiscontr).
Defined.

Definition NNO : UU :=
  ∑ (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧), isNNO n z s.

Definition NNObject (n : NNO) : C := pr1 n.
Coercion NNObject : NNO >-> ob.

Definition zeroNNO (n : NNO) : C ⟦1,n⟧ := pr1 (pr2 n).
Definition sucNNO (n : NNO) : C ⟦n,n⟧ := pr1 (pr2 (pr2 n)).

Lemma isNNO_NNO (n : NNO) : isNNO n (zeroNNO n) (sucNNO n).
Proof.
exact (pr2 (pr2 (pr2 n))).
Qed.

Section UniversalMappingProperty.
  Context (N : NNO)
          {x : C}
          (z : 1 --> x)
          (s : x --> x).

  Definition NNO_mor
    : N --> x
    := pr11 (isNNO_NNO N x z s).

  Proposition NNO_mor_Z
    : zeroNNO N · NNO_mor = z.
  Proof.
    exact (pr121 (isNNO_NNO N x z s)).
  Qed.

  Proposition NNO_mor_S
    : sucNNO N · NNO_mor = NNO_mor · s.
  Proof.
    exact (pr221 (isNNO_NNO N x z s)).
  Qed.

  Proposition NNO_mor_unique
              {f g : N --> x}
              (fz : zeroNNO N · f = z)
              (gz : zeroNNO N · g = z)
              (fs : sucNNO N · f = f · s)
              (gs : sucNNO N · g = g · s)
    : f = g.
  Proof.
    exact (base_paths
             _ _
             (proofirrelevance
                _
                (isapropifcontr (isNNO_NNO N x z s))
                (f ,, fz ,, fs)
                (g ,, gz ,, gs))).
  Qed.
End UniversalMappingProperty.

Definition make_NNO (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧)
 (h : isNNO n z s) : NNO := (n,,z,,s,,h).

Definition hasNNO : hProp := ∥ NNO ∥.

End nno.

Section UniqueUpToIso.
  Context {C : category}
          {TC : Terminal C}.

  Definition mor_between_NNO
             (N₁ N₂ : NNO TC)
    : N₁ --> N₂.
  Proof.
    use NNO_mor.
    - exact (zeroNNO TC N₂).
    - exact (sucNNO TC N₂).
  Defined.

  Proposition mor_between_NNO_inv
              (N₁ N₂ : NNO TC)
    : mor_between_NNO N₁ N₂ · mor_between_NNO N₂ N₁
      =
      identity _.
  Proof.
    unfold mor_between_NNO.
    use NNO_mor_unique.
    - exact (zeroNNO TC N₁).
    - exact (sucNNO TC N₁).
    - rewrite !assoc.
      rewrite !NNO_mor_Z.
      apply idpath.
    - apply id_right.
    - rewrite !assoc.
      rewrite NNO_mor_S.
      rewrite !assoc'.
      rewrite NNO_mor_S.
      apply idpath.
    - rewrite id_left, id_right.
      apply idpath.
  Qed.

  Definition iso_between_NNO
             (N₁ N₂ : NNO TC)
    : z_iso N₁ N₂.
  Proof.
    use make_z_iso.
    - apply mor_between_NNO.
    - apply mor_between_NNO.
    - abstract
        (split ; apply mor_between_NNO_inv).
  Defined.
End UniqueUpToIso.
