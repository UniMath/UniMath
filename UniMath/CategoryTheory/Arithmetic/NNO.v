(**

Definition natural number objects (NNO's)

This is related to the initial algebra definition in FunctorAlgebras.v

Written by: Anders Mörtberg, 2018

*)
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.

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

  Proposition NNO_mor_unique'
              {f : N --> x}
              (fz : zeroNNO N · f = z)
              (fs : sucNNO N · f = f · s)
    : f = NNO_mor.
  Proof.
    apply NNO_mor_unique.
    - exact fz.
    - apply NNO_mor_Z.
    - exact fs.
    - exact NNO_mor_S.
  Qed.

End UniversalMappingProperty.

Definition make_NNO (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧)
 (h : isNNO n z s) : NNO := (n,,z,,s,,h).

Definition hasNNO : hProp := ∥ NNO ∥.

End nno.

Section IndependenceOfTerminal.
  (* A change of base *)

  Context {C : category} (T₀ T₁ : Terminal C).

  Section TransportNNO_along_terminal_UVP.

    Context (N : NNO T₀)
      {a : C} (q : C⟦T₁, a⟧) (f : C⟦a, a⟧).

    Let u := NNO_mor _ N (TerminalArrow T₁ _ · q) f.

    Lemma NNO_mor_Z_after_terminal_change
      : TerminalArrow T₀ T₁ · zeroNNO T₀ N · NNO_mor T₀ N (TerminalArrow T₁ T₀ · q) f = q.
    Proof.
      refine (assoc' _ _ _ @ _).
      etrans. { apply maponpaths, NNO_mor_Z. }
      refine (assoc _ _ _ @ _).
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply proofirrelevance, isapropifcontr, T₁.
    Qed.

    Let uvp : UU
        := ∑ u : C ⟦ N, a ⟧, TerminalArrow T₀ T₁ · zeroNNO T₀ N · u = q × sucNNO T₀ N · u = u · f.

    Definition NNO_mor_after_terminal_change
      : uvp.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact (NNO_mor _ N (TerminalArrow T₁ _ · q) f).
      - apply NNO_mor_Z_after_terminal_change.
      - apply NNO_mor_S.
    Defined.

    Lemma NNO_mor_after_terminal_change_uniqueness (ϕ : uvp)
      : ϕ = NNO_mor_after_terminal_change.
    Proof.
      use subtypePath.
      { intro ; apply isapropdirprod ; apply homset_property. }
      use (NNO_mor_unique' _ N).
      - etrans.
        2: { apply maponpaths, (pr12 ϕ). }
        rewrite ! assoc.
        apply maponpaths_2.
        refine (! id_left _ @ _).
        apply maponpaths_2.
        apply proofirrelevance, isapropifcontr, T₀.
      - exact (pr22 ϕ).
    Qed.

  End TransportNNO_along_terminal_UVP.

  Definition NNO_transport_along_terminal
    : NNO T₀ → NNO T₁.
  Proof.
    intro N.
    apply (make_NNO _ N (TerminalArrow T₀ _ · zeroNNO _ N) (sucNNO _ N)).
    intros a q f.
    use make_iscontr.
    - apply NNO_mor_after_terminal_change.
    - apply NNO_mor_after_terminal_change_uniqueness.
  Defined.

End IndependenceOfTerminal.

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

Section ToBeMoved.

  Lemma identity_preserves_chosen_terminal
    {C : category} (T : Terminal C)
    : preserves_chosen_terminal T (functor_identity C).
  Proof.
    apply T.
  Qed.

  Lemma composition_preserves_chosen_terminal
    {C₀ C₁ C₂ : category}
    {F : functor C₀ C₁} {G : functor C₁ C₂}
    {T₀ : Terminal C₀} {T₁ : Terminal C₁}
    (F_pT : preserves_chosen_terminal T₀ F)
    (G_pT : preserves_chosen_terminal T₁ G)
    : preserves_chosen_terminal T₀ (functor_composite F G).
  Proof.
    set (t₁ := preserves_terminal_if_preserves_chosen _ _ F_pT).
    set (t₂ := preserves_terminal_if_preserves_chosen _ _ G_pT).
    apply (t₂ _ (t₁ _ (pr2 T₀))).
  Qed.

  Definition preserves_chosen_terminal_iso
    {C₀ C₁ : category}
    {F : functor C₀ C₁}
    {T₀ : Terminal C₀}
    (T₁ : Terminal C₁)
    (F_pT : preserves_chosen_terminal T₀ F)
    : z_iso T₁ (F T₀).
  Proof.
    use (z_iso_inv (preserves_terminal_to_z_iso _ _ T₀ T₁)).
    exact (preserves_terminal_if_preserves_chosen T₀ _ F_pT).
  Defined.

End ToBeMoved.

Section HomomorphismNNO.

  Definition preserves_NNO
    {C₀ C₁ : category}
    {F : functor C₀ C₁}
    (F_pT : preserves_terminal F) : UU
    := ∏ (T₀ : Terminal C₀) (N₀ : NNO T₀),
      isNNO
        (preserves_terminal_to_terminal _ F_pT T₀)
        (F N₀)
        (#F (zeroNNO _ N₀))
        (#F (sucNNO _ N₀)).

  Lemma isaprop_preserves_NNO
    {C₀ C₁ : category}
    {F : functor C₀ C₁}
    (F_pT : preserves_terminal F)
    : isaprop (preserves_NNO F_pT).
  Proof.
    do 2 (apply impred_isaprop ; intro).
    apply isNNO.
  Qed.

  Lemma identity_preserves_NNO
    (C : category)
    : preserves_NNO (identity_preserves_terminal C).
  Proof.
    intro ; intro ; apply isNNO_NNO.
  Defined.

  Lemma composition_preserves_NNO
    {C₀ C₁ C₂ : category}
    {F : functor C₀ C₁} {G : functor C₁ C₂}
    {F_pT : preserves_terminal F}
    {G_pT : preserves_terminal G}
    (F_pN : preserves_NNO F_pT)
    (G_pN : preserves_NNO G_pT)
    : preserves_NNO (composition_preserves_terminal F_pT G_pT).
  Proof.
    intros T₀ N₀.
    set (N₁ := make_NNO _ _ _ _ (F_pN _ N₀)).
    set (N₂ := make_NNO _ _ _ _ (G_pN _ N₁)).
    exact (isNNO_NNO _ N₂).
  Defined.

  Definition preserves_chosen_NNO
    {C₀ C₁ : category}
    {F : functor C₀ C₁}
    {T₀ : Terminal C₀}
    {T₁ : Terminal C₁}
    (F_pT : preserves_chosen_terminal T₀ F)
    (N₀ : NNO T₀)
    (N₁ : NNO T₁)
    : UU
    := is_z_isomorphism
         (NNO_mor _ N₁
            (preserves_chosen_terminal_iso T₁ F_pT · #F (zeroNNO _ N₀))
            (#F (sucNNO _ N₀))
         ).

  Lemma isaprop_preserves_chosen_NNO
    {C₀ C₁ : category}
    {F : functor C₀ C₁}
    {T₀ : Terminal C₀}
    {T₁ : Terminal C₁}
    (F_pT : preserves_chosen_terminal T₀ F)
    (N₀ : NNO T₀)
    (N₁ : NNO T₁)
    : isaprop (preserves_chosen_NNO F_pT N₀ N₁).
  Proof.
    apply isaprop_is_z_isomorphism.
  Qed.

  Lemma identity_preserves_chosen_NNO
    {C : category} {T : Terminal C} (N : NNO T)
    : preserves_chosen_NNO (identity_preserves_chosen_terminal T) N N.
  Proof.
    use (transportf _ _ (pr2 (iso_between_NNO N N))).
    simpl ; unfold mor_between_NNO.
    apply maponpaths_2.
    refine (! id_left _ @ _).
    apply maponpaths_2.
    use proofirrelevance.
    use isapropifcontr.
    apply T.
  Qed.

  Lemma composition_preserves_chosen_NNO
    {C₀ C₁ C₂ : category}
    {F : functor C₀ C₁} {G : functor C₁ C₂}
    {T₀ : Terminal C₀} {T₁ : Terminal C₁} {T₂ : Terminal C₂}
    {F_pT : preserves_chosen_terminal T₀ F}
    {G_pT : preserves_chosen_terminal T₁ G}
    {N₀ : NNO T₀} {N₁ : NNO T₁} {N₂ : NNO T₂}
    (F_pN : preserves_chosen_NNO F_pT N₀ N₁)
    (G_pN : preserves_chosen_NNO G_pT N₁ N₂)
    : preserves_chosen_NNO (composition_preserves_chosen_terminal F_pT G_pT) N₀ N₂.
  Proof.
    use is_z_isomorphism_path.
    - refine (NNO_mor _ N₂ _ _ · #G (NNO_mor _ N₁ _ _)).
      + exact (preserves_chosen_terminal_iso T₂ G_pT · #G (zeroNNO T₁ N₁)).
      + exact (#G (sucNNO T₁ N₁)).
      + exact (preserves_chosen_terminal_iso T₁ F_pT · # F (zeroNNO T₀ N₀)).
      + exact (# F (sucNNO T₀ N₀)).
    - use NNO_mor_unique'.
      + refine (assoc _ _ _ @ _).
        etrans. {
          apply maponpaths_2.
          apply NNO_mor_Z.
        }
        refine (assoc' _ _ _ @ _).
        etrans. {
          apply maponpaths.
          apply pathsinv0.
          apply (functor_comp G).
        }
        etrans. {
          apply maponpaths.
          apply maponpaths_1.
          apply NNO_mor_Z.
        }
        etrans. {
          apply maponpaths.
          apply (functor_comp G).
        }
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        use proofirrelevance.
        apply isapropifcontr.
        apply (composition_preserves_chosen_terminal F_pT G_pT _).
      + cbn.
        rewrite assoc.
        rewrite NNO_mor_S.
        rewrite assoc'.
        rewrite <- (functor_comp G).
        rewrite NNO_mor_S.
        rewrite ! assoc'.
        apply maponpaths.
        now rewrite functor_comp.
    - use is_z_isomorphism_comp.
      + exact G_pN.
      + apply (functor_on_is_z_isomorphism G).
        exact F_pN.
  Qed.

End HomomorphismNNO.
