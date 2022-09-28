(*******************************************************************

 Kleisli objects in bicategories

 Contents
 1. Kleisli objects via universal mapping properties
 2. It is a proposition
 3. Bicategories with Kleisli objects

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.TransportLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.

Local Open Scope cat.

Section KleisliObject.
  Context {B : bicat}
          (m : mnd (op1_bicat B)).

  Let z : B := ob_of_mnd m.
  Let h : z --> z := endo_of_mnd m.
  Let η : id₁ _ ==> h := unit_of_mnd m.
  Let μ : h · h ==> h := mult_of_mnd m.

  (**
   1. Kleisli objects via universal mapping properties
   *)
  Definition kleisli_cocone
    : UU
    := ∑ (x : B)
         (f : z --> x)
         (γ : h · f ==> f),
       (η ▹ f • γ = lunitor _)
       ×
       (rassociator _ _ _ • (_ ◃ γ) • γ = (μ ▹ f) • γ).

  Definition make_kleisli_cocone
             {x : B}
             (f : z --> x)
             (γ : h · f ==> f)
             (fη : η ▹ f • γ = lunitor _)
             (fμ : rassociator _ _ _ • (_ ◃ γ) • γ = (μ ▹ f) • γ)
    : kleisli_cocone
    := x ,, f ,, γ ,, fη ,, fμ.

  Coercion kleisli_cocone_ob (q : kleisli_cocone) : B := pr1 q.

  Section Projections.
    Context (q : kleisli_cocone).

    Definition mor_of_kleisli_cocone
      : z --> q
      := pr12 q.

    Definition cell_of_kleisli_cocone
      : h · mor_of_kleisli_cocone
        ==>
        mor_of_kleisli_cocone
      := pr122 q.

    Definition kleisli_cocone_unit
      : (η ▹ _) • cell_of_kleisli_cocone = lunitor _
      := pr1 (pr222 q).

    Definition kleisli_cocone_mult
      : rassociator _ _ _
        • (_ ◃ cell_of_kleisli_cocone)
        • cell_of_kleisli_cocone
        =
        (μ ▹ _) • cell_of_kleisli_cocone
      := pr2 (pr222 q).
  End Projections.

  Definition kleisli_cocone_mor
             (q₁ q₂ : kleisli_cocone)
    : UU
    := ∑ (f : q₁ --> q₂)
         (α : mor_of_kleisli_cocone q₁ · f ==> mor_of_kleisli_cocone q₂),
       ((_ ◃ α) • cell_of_kleisli_cocone q₂
        =
        lassociator _ _ _
        • (cell_of_kleisli_cocone q₁ ▹ _)
        • α)
       ×
       is_invertible_2cell α.

  Definition make_kleisli_cocone_mor
             {q₁ q₂ : kleisli_cocone}
             (f : q₁ --> q₂)
             (α : mor_of_kleisli_cocone q₁ · f ==> mor_of_kleisli_cocone q₂)
             (p : (_ ◃ α) • cell_of_kleisli_cocone q₂
                  =
                  lassociator _ _ _
                  • (cell_of_kleisli_cocone q₁ ▹ _)
                  • α)
             (Hα : is_invertible_2cell α)
    : kleisli_cocone_mor q₁ q₂
    := f ,, α ,, p ,, Hα.

  Coercion mor_of_kleisli_cocone_mor
           {q₁ q₂ : kleisli_cocone}
           (f : kleisli_cocone_mor q₁ q₂)
    : q₁ --> q₂
    := pr1 f.

  Definition cell_of_kleisli_cocone_mor
             {q₁ q₂ : kleisli_cocone}
             (f : kleisli_cocone_mor q₁ q₂)
    : mor_of_kleisli_cocone q₁ · f ==> mor_of_kleisli_cocone q₂
    := pr12 f.

  Definition kleisli_cocone_mor_endo
             {q₁ q₂ : kleisli_cocone}
             (f : kleisli_cocone_mor q₁ q₂)
    : (_ ◃ cell_of_kleisli_cocone_mor f) • cell_of_kleisli_cocone q₂
      =
      lassociator _ _ _
      • (cell_of_kleisli_cocone q₁ ▹ _)
      • cell_of_kleisli_cocone_mor f
    := pr122 f.

  Definition cell_of_kleisli_cocone_mor_is_invertible
             {q₁ q₂ : kleisli_cocone}
             (f : kleisli_cocone_mor q₁ q₂)
    : is_invertible_2cell (cell_of_kleisli_cocone_mor f)
    := pr222 f.

  Definition inv2cell_of_kleisli_cocone_mor
             {q₁ q₂ : kleisli_cocone}
             (f : kleisli_cocone_mor q₁ q₂)
    : invertible_2cell
        (mor_of_kleisli_cocone q₁ · f)
        (mor_of_kleisli_cocone q₂).
  Proof.
    use make_invertible_2cell.
    - exact (cell_of_kleisli_cocone_mor f).
    - exact (cell_of_kleisli_cocone_mor_is_invertible f).
  Defined.

  Definition path_kleisli_cocone_mor
             (HB : is_univalent_2_1 B)
             {q₁ q₂ : kleisli_cocone}
             {f₁ f₂ : kleisli_cocone_mor q₁ q₂}
             (α : invertible_2cell f₁ f₂)
             (p : (mor_of_kleisli_cocone q₁ ◃ α) • cell_of_kleisli_cocone_mor f₂
                  =
                  cell_of_kleisli_cocone_mor f₁)
    : f₁ = f₂.
  Proof.
    use total2_paths_f.
    - exact (isotoid_2_1 HB α).
    - use subtypePath.
      {
        intro.
        apply isapropdirprod ; [ apply cellset_property | apply isaprop_is_invertible_2cell ].
      }
      rewrite pr1_transportf.
      rewrite transport_two_cell_FlFr.
      rewrite maponpaths_for_constant_function.
      cbn.
      rewrite id2_right.
      use vcomp_move_R_pM ; [ is_iso | ].
      cbn.
      rewrite <- idtoiso_2_1_lwhisker.
      rewrite idtoiso_2_1_isotoid_2_1.
      exact (!p).
  Qed.

  Definition has_kleisli_ump_1
             (k : kleisli_cocone)
    : UU
    := ∏ (q : kleisli_cocone), kleisli_cocone_mor k q.

  Definition has_kleisli_ump_2
             (k : kleisli_cocone)
    : UU
    := ∏ (x : B)
         (g₁ g₂ : k --> x)
         (α : mor_of_kleisli_cocone k · g₁ ==> mor_of_kleisli_cocone k · g₂)
         (p : lassociator _ _ _
              • (cell_of_kleisli_cocone k ▹ _)
              • α
              =
              (_ ◃ α)
              • lassociator _ _ _
              • (cell_of_kleisli_cocone k ▹ _)),
       ∃! (β : g₁ ==> g₂), _ ◃ β = α.

  Definition has_kleisli_ump
             (k : kleisli_cocone)
    : UU
    := has_kleisli_ump_1 k × has_kleisli_ump_2 k.

  Section Projections.
    Context {k : kleisli_cocone}
            (Hk : has_kleisli_ump k).

    Definition kleisli_ump_mor
               {a : B}
               {g : z --> a}
               (γ : h · g ==> g)
               (p₁ : (η ▹ g) • γ = lunitor g)
               (p₂ : (rassociator h h g • (h ◃ γ)) • γ = (μ ▹ g) • γ)
      : k --> a
      := pr1 Hk (make_kleisli_cocone g γ p₁ p₂).

    Definition kleisli_ump_mor_cell
               {a : B}
               {g : z --> a}
               (γ : h · g ==> g)
               (p₁ : (η ▹ g) • γ = lunitor g)
               (p₂ : (rassociator h h g • (h ◃ γ)) • γ = (μ ▹ g) • γ)
      : mor_of_kleisli_cocone k · kleisli_ump_mor γ p₁ p₂ ==> g
      := cell_of_kleisli_cocone_mor (pr1 Hk (make_kleisli_cocone g γ p₁ p₂)).

    Definition kleisli_ump_mor_cell_endo
               {a : B}
               {g : z --> a}
               (γ : h · g ==> g)
               (p₁ : (η ▹ g) • γ = lunitor g)
               (p₂ : (rassociator h h g • (h ◃ γ)) • γ = (μ ▹ g) • γ)
      : (h ◃ kleisli_ump_mor_cell γ p₁ p₂) • γ
        =
        lassociator _ _ _
        • (cell_of_kleisli_cocone k ▹ _)
        • kleisli_ump_mor_cell γ p₁ p₂
      := kleisli_cocone_mor_endo (pr1 Hk (make_kleisli_cocone g γ p₁ p₂)).

    Definition kleisli_ump_mor_cell_is_invertible
               {a : B}
               {g : z --> a}
               (γ : h · g ==> g)
               (p₁ : (η ▹ g) • γ = lunitor g)
               (p₂ : (rassociator h h g • (h ◃ γ)) • γ = (μ ▹ g) • γ)
      : is_invertible_2cell (kleisli_ump_mor_cell γ p₁ p₂)
      := cell_of_kleisli_cocone_mor_is_invertible
           (pr1 Hk (make_kleisli_cocone g γ p₁ p₂)).

    Definition kleisli_ump_mor_inv2cell
               {a : B}
               {g : z --> a}
               (γ : h · g ==> g)
               (p₁ : (η ▹ g) • γ = lunitor g)
               (p₂ : (rassociator h h g • (h ◃ γ)) • γ = (μ ▹ g) • γ)
      : invertible_2cell
          (mor_of_kleisli_cocone k · kleisli_ump_mor γ p₁ p₂) g.
    Proof.
      use make_invertible_2cell.
      - exact (kleisli_ump_mor_cell γ p₁ p₂).
      - exact (kleisli_ump_mor_cell_is_invertible γ p₁ p₂).
    Defined.

    Definition kleisli_ump_cell
               {x : B}
               {g₁ g₂ : k --> x}
               (α : mor_of_kleisli_cocone k · g₁ ==> mor_of_kleisli_cocone k · g₂)
               (p : lassociator _ _ _
                    • (cell_of_kleisli_cocone k ▹ _)
                    • α
                    =
                    (_ ◃ α)
                    • lassociator _ _ _
                    • (cell_of_kleisli_cocone k ▹ _))
      : g₁ ==> g₂
      := pr11 (pr2 Hk x g₁ g₂ α p).

    Definition kleisli_ump_cell_eq
               {x : B}
               {g₁ g₂ : k --> x}
               (α : mor_of_kleisli_cocone k · g₁ ==> mor_of_kleisli_cocone k · g₂)
               (p : lassociator _ _ _
                    • (cell_of_kleisli_cocone k ▹ _)
                    • α
                    =
                    (_ ◃ α)
                    • lassociator _ _ _
                    • (cell_of_kleisli_cocone k ▹ _))
      : _ ◃ kleisli_ump_cell α p = α
      := pr21 (pr2 Hk x g₁ g₂ α p).

    Definition kleisli_ump_eq
               {x : B}
               {g₁ g₂ : k --> x}
               (α : mor_of_kleisli_cocone k · g₁ ==> mor_of_kleisli_cocone k · g₂)
               (p : lassociator _ _ _
                    • (cell_of_kleisli_cocone k ▹ _)
                    • α
                    =
                    (_ ◃ α)
                    • lassociator _ _ _
                    • (cell_of_kleisli_cocone k ▹ _))
               {β₁ β₂ : g₁ ==> g₂}
               (q₁ : _ ◃ β₁ = α)
               (q₂ : _ ◃ β₂ = α)
      : β₁ = β₂.
    Proof.
      exact (maponpaths
               pr1
               (proofirrelevance
                  _
                  (isapropifcontr (pr2 Hk x g₁ g₂ α p))
                  (β₁ ,, q₁)
                  (β₂ ,, q₂))).
    Qed.

    Section Invertible.
      Context {x : B}
              {g₁ g₂ : k --> x}
              (α : invertible_2cell
                     (mor_of_kleisli_cocone k · g₁)
                     (mor_of_kleisli_cocone k · g₂))
              (p : lassociator _ _ _
                   • (cell_of_kleisli_cocone k ▹ _)
                   • α
                   =
                   (_ ◃ α)
                   • lassociator _ _ _
                   • (cell_of_kleisli_cocone k ▹ _)).

      Definition kleisi_ump_cell_inv
        : g₂ ==> g₁.
      Proof.
        refine (kleisli_ump_cell (α^-1) _).
        abstract
          (use vcomp_move_R_Mp ; [ is_iso | ] ;
           rewrite !vassocl ;
           use vcomp_move_L_pM ; [ is_iso | ] ;
           cbn ;
           rewrite !vassocr ;
           exact (!p)).
      Defined.

      Definition kleisi_ump_cell_inv_left
        : kleisli_ump_cell α p • kleisi_ump_cell_inv = id₂ _.
      Proof.
        use kleisli_ump_eq.
        - exact (id2 _).
        - rewrite id2_right.
          rewrite lwhisker_id2, id2_left.
          apply idpath.
        - rewrite <- !lwhisker_vcomp.
          unfold kleisi_ump_cell_inv.
          rewrite !kleisli_ump_cell_eq.
          apply vcomp_rinv.
        - apply lwhisker_id2.
      Qed.

      Definition kleisi_ump_cell_inv_right
        : kleisi_ump_cell_inv • kleisli_ump_cell α p = id₂ _.
      Proof.
        use kleisli_ump_eq.
        - exact (id2 _).
        - rewrite id2_right.
          rewrite lwhisker_id2, id2_left.
          apply idpath.
        - rewrite <- !lwhisker_vcomp.
          unfold kleisi_ump_cell_inv.
          rewrite !kleisli_ump_cell_eq.
          apply vcomp_linv.
        - apply lwhisker_id2.
      Qed.

      Definition kleisi_ump_cell_is_invertible
        : is_invertible_2cell (kleisli_ump_cell α p).
      Proof.
        use make_is_invertible_2cell.
        - exact kleisi_ump_cell_inv.
        - exact kleisi_ump_cell_inv_left.
        - exact kleisi_ump_cell_inv_right.
      Defined.
    End Invertible.

    Definition kleisli_ump_inv2cell
               {x : B}
               {g₁ g₂ : k --> x}
               (α : invertible_2cell
                      (mor_of_kleisli_cocone k · g₁)
                      (mor_of_kleisli_cocone k · g₂))
               (p : lassociator _ _ _
                    • (cell_of_kleisli_cocone k ▹ _)
                    • α
                    =
                    (_ ◃ α)
                    • lassociator _ _ _
                    • (cell_of_kleisli_cocone k ▹ _))
      : invertible_2cell g₁ g₂.
    Proof.
      use make_invertible_2cell.
      - exact (kleisli_ump_cell α p).
      - exact (kleisi_ump_cell_is_invertible α p).
    Defined.
  End Projections.

  (**
   2. It is a proposition
   *)
  Definition isaprop_has_kleisli_ump
             (HB : is_univalent_2_1 B)
             (k : kleisli_cocone)
    : isaprop (has_kleisli_ump k).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      repeat (use impred ; intro).
      apply isapropiscontr.
    }
    use funextsec ; intro.
    use (path_kleisli_cocone_mor HB).
    - use (kleisli_ump_inv2cell φ₁).
      + exact (comp_of_invertible_2cell
                 (inv2cell_of_kleisli_cocone_mor (pr1 φ₁ x))
                 (inv_of_invertible_2cell
                    (inv2cell_of_kleisli_cocone_mor (pr1 φ₂ x)))).
      + abstract
          (cbn ;
           rewrite <- !lwhisker_vcomp ;
           rewrite !vassocr ;
           rewrite <- (kleisli_cocone_mor_endo (pr1 φ₁ x)) ;
           rewrite !vassocl ;
           apply maponpaths ;
           use vcomp_move_L_pM ; [ is_iso | ] ; cbn ;
           rewrite !vassocr ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           exact (kleisli_cocone_mor_endo (pr1 φ₂ x))).
    - cbn.
      rewrite kleisli_ump_cell_eq.
      rewrite !vassocl.
      rewrite vcomp_linv.
      apply id2_right.
  Qed.
End KleisliObject.

(**
 3. Bicategories with Kleisli objects
 *)
Definition has_kleisli
           (B : bicat)
  : UU
  := ∏ (m : mnd (op1_bicat B)),
     ∑ (k : kleisli_cocone m),
     has_kleisli_ump m k.
