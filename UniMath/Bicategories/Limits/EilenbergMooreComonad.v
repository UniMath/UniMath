(*************************************************************************

 Eilenberg-Moore objects of comonads

 In this file, we define the notion of Eilenberg-Moore object for
 comonads.
 The main purpose of this notion, is that Eilenberg-Moore objects for
 comonads in `B` give rise to Eilenberg-Moore objects in `op2_bicat B`.

 Contents
 1. Eilenberg-Moore objects of comonads via universal mapping properties
 2. Being an Eilenberg-Moore object for a comonad is a proposition
 3. Bicategories with Eilenberg-Moore objects for comonads

 *************************************************************************)
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
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.

Local Open Scope cat.

Section EilenbergMooreComonad.
  Context {B : bicat}
          (m : mnd (op2_bicat B)).

  Let z : B := ob_of_mnd m.
  Let h : z --> z := endo_of_mnd m.
  Let ε : h ==> id₁ _ := unit_of_mnd m.
  Let ν : h ==> h · h := mult_of_mnd m.

  (**
   1. Eilenberg-Moore objects of comonads via universal mapping properties
   *)
  Definition em_comnd_cone
    : UU
    := ∑ (x : B)
         (f : x --> z)
         (γ : f ==> f · h),
      (γ • (f ◃ ε) = rinvunitor _)
      ×
      (γ • (γ ▹ _) • rassociator _ _ _ = γ • (f ◃ ν)).

  Definition make_em_comnd_cone
             {x : B}
             (f : x --> z)
             (γ : f ==> f · h)
             (fε : γ • (f ◃ ε) = rinvunitor _)
             (fν : γ • (γ ▹ _) • rassociator _ _ _ = γ • (f ◃ ν))
    : em_comnd_cone
    := x ,, f ,, γ ,, fε ,, fν.

  Coercion em_comnd_cone_ob (q : em_comnd_cone) : B := pr1 q.

  Section Projections.
    Context (q : em_comnd_cone).

    Definition mor_of_em_comnd_cone
      : q --> z
      := pr12 q.

    Definition cell_of_em_comnd_cone
      : mor_of_em_comnd_cone
        ==>
        mor_of_em_comnd_cone · h
      := pr122 q.

    Definition em_comnd_cone_counit
      : cell_of_em_comnd_cone • (_ ◃ ε) = rinvunitor _
      := pr1 (pr222 q).

    Definition em_comnd_cone_comult
      : (cell_of_em_comnd_cone
         • (cell_of_em_comnd_cone ▹ _))
         • rassociator _ _ _
        =
        cell_of_em_comnd_cone
        • (_ ◃ ν)
      := pr2 (pr222 q).
  End Projections.

  Definition em_comnd_cone_mor
             (q₁ q₂ : em_comnd_cone)
    : UU
    := ∑ (f : q₁ --> q₂)
         (α : mor_of_em_comnd_cone q₁ ==> f · mor_of_em_comnd_cone q₂),
       (cell_of_em_comnd_cone q₁ • (α ▹ _)
        =
        α • (_ ◃ cell_of_em_comnd_cone q₂) • lassociator _ _ _)
       ×
       is_invertible_2cell α.

  Definition make_em_comnd_cone_mor
             {q₁ q₂ : em_comnd_cone}
             (f : q₁ --> q₂)
             (α : mor_of_em_comnd_cone q₁ ==> f · mor_of_em_comnd_cone q₂)
             (p : cell_of_em_comnd_cone q₁ • (α ▹ _)
                  =
                  α • (_ ◃ cell_of_em_comnd_cone q₂) • lassociator _ _ _)
             (Hα : is_invertible_2cell α)
    : em_comnd_cone_mor q₁ q₂
    := f ,, α ,, p ,, Hα.

  Coercion mor_of_em_comnd_cone_mor
           {q₁ q₂ : em_comnd_cone}
           (f : em_comnd_cone_mor q₁ q₂)
    : q₁ --> q₂
    := pr1 f.

  Definition cell_of_em_comnd_cone_mor
             {q₁ q₂ : em_comnd_cone}
             (f : em_comnd_cone_mor q₁ q₂)
    : mor_of_em_comnd_cone q₁ ==> f · mor_of_em_comnd_cone q₂
    := pr12 f.

  Definition em_comnd_cone_mor_endo
             {q₁ q₂ : em_comnd_cone}
             (f : em_comnd_cone_mor q₁ q₂)
    : cell_of_em_comnd_cone q₁
      • (cell_of_em_comnd_cone_mor f ▹ _)
      =
      cell_of_em_comnd_cone_mor f
      • (_ ◃ cell_of_em_comnd_cone q₂)
      • lassociator _ _ _
    := pr122 f.

  Definition cell_of_em_comnd_cone_mor_is_invertible
             {q₁ q₂ : em_comnd_cone}
             (f : em_comnd_cone_mor q₁ q₂)
    : is_invertible_2cell (cell_of_em_comnd_cone_mor f)
    := pr222 f.

  Definition inv2cell_of_em_comnd_cone_mor
             {q₁ q₂ : em_comnd_cone}
             (f : em_comnd_cone_mor q₁ q₂)
    : invertible_2cell
        (mor_of_em_comnd_cone q₁)
        (f · mor_of_em_comnd_cone q₂).
  Proof.
    use make_invertible_2cell.
    - exact (cell_of_em_comnd_cone_mor f).
    - exact (cell_of_em_comnd_cone_mor_is_invertible f).
  Defined.

  Definition path_em_comnd_cone_mor
             (HB : is_univalent_2_1 B)
             {q₁ q₂ : em_comnd_cone}
             {f₁ f₂ : em_comnd_cone_mor q₁ q₂}
             (α : invertible_2cell f₁ f₂)
             (p : cell_of_em_comnd_cone_mor f₁ • (α ▹ mor_of_em_comnd_cone q₂)
                  =
                  cell_of_em_comnd_cone_mor f₂)
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
      rewrite id2_left.
      rewrite <- idtoiso_2_1_rwhisker.
      rewrite idtoiso_2_1_isotoid_2_1.
      exact p.
  Qed.

  Definition has_em_comnd_ump_1
             (e : em_comnd_cone)
    : UU
    := ∏ (q : em_comnd_cone), em_comnd_cone_mor q e.

  Definition has_em_comnd_ump_2
             (e : em_comnd_cone)
    : UU
    := ∏ (x : B)
         (g₁ g₂ : x --> e)
         (α : g₁ · mor_of_em_comnd_cone e ==> g₂ · mor_of_em_comnd_cone e)
         (p : α
              • (_ ◃ cell_of_em_comnd_cone e)
              • lassociator _ _ _
              =
              (_ ◃ cell_of_em_comnd_cone e)
              • lassociator _ _ _
              • (α ▹ _)),
       ∃! (β : g₁ ==> g₂), β ▹ _ = α.

  Definition has_em_comnd_ump
             (e : em_comnd_cone)
    : UU
    := has_em_comnd_ump_1 e × has_em_comnd_ump_2 e.

  Section Projections.
    Context {e : em_comnd_cone}
            (He : has_em_comnd_ump e).

    Definition em_comnd_ump_mor
               {a : B}
               (g : a --> z)
               (γ : g ==> g · h)
               (p₁ : γ • (g ◃ ε) = rinvunitor g)
               (p₂ : (γ • (γ ▹ h)) • rassociator g h h = γ • (g ◃ ν))
      : a --> e
      := pr1 He (make_em_comnd_cone g γ p₁ p₂).

    Definition em_comnd_ump_mor_cell
               {a : B}
               (g : a --> z)
               (γ : g ==> g · h)
               (p₁ : γ • (g ◃ ε) = rinvunitor g)
               (p₂ : (γ • (γ ▹ h)) • rassociator g h h = γ • (g ◃ ν))
      : g ==> em_comnd_ump_mor g γ p₁ p₂ · mor_of_em_comnd_cone e
      := cell_of_em_comnd_cone_mor (pr1 He (make_em_comnd_cone g γ p₁ p₂)).

    Definition em_comnd_ump_mor_cell_endo
               {a : B}
               (g : a --> z)
               (γ : g ==> g · h)
               (p₁ : γ • (g ◃ ε) = rinvunitor g)
               (p₂ : (γ • (γ ▹ h)) • rassociator g h h = γ • (g ◃ ν))
      : γ
        • (em_comnd_ump_mor_cell g γ p₁ p₂ ▹ h)
        =
        em_comnd_ump_mor_cell g γ p₁ p₂
        • (em_comnd_ump_mor g γ p₁ p₂ ◃ cell_of_em_comnd_cone e)
        • lassociator _ _ _
      := em_comnd_cone_mor_endo (pr1 He (make_em_comnd_cone g γ p₁ p₂)).

    Definition em_comnd_ump_mor_cell_is_invertible
               {a : B}
               (g : a --> z)
               (γ : g ==> g · h)
               (p₁ : γ • (g ◃ ε) = rinvunitor g)
               (p₂ : (γ • (γ ▹ h)) • rassociator g h h = γ • (g ◃ ν))
      : is_invertible_2cell (em_comnd_ump_mor_cell g γ p₁ p₂)
      := cell_of_em_comnd_cone_mor_is_invertible
           (pr1 He (make_em_comnd_cone g γ p₁ p₂)).

    Definition em_comnd_ump_mor_inv2cell
               {a : B}
               (g : a --> z)
               (γ : g ==> g · h)
               (p₁ : γ • (g ◃ ε) = rinvunitor g)
               (p₂ : (γ • (γ ▹ h)) • rassociator g h h = γ • (g ◃ ν))
      : invertible_2cell
          g
          (em_comnd_ump_mor g γ p₁ p₂ · mor_of_em_comnd_cone e).
    Proof.
      use make_invertible_2cell.
      - exact (em_comnd_ump_mor_cell g γ p₁ p₂).
      - exact (em_comnd_ump_mor_cell_is_invertible g γ p₁ p₂).
    Defined.

    Definition em_comnd_ump_cell
               {x : B}
               {g₁ g₂ : x --> e}
               (α : g₁ · mor_of_em_comnd_cone e ==> g₂ · mor_of_em_comnd_cone e)
               (p : α
                    • (g₂ ◃ cell_of_em_comnd_cone e)
                    • lassociator _ _ _
                    =
                    (g₁ ◃ cell_of_em_comnd_cone e)
                    • lassociator _ _ _
                    • (α ▹ h))
      : g₁ ==> g₂
      := pr11 (pr2 He x g₁ g₂ α p).

    Definition em_comnd_ump_cell_eq
               {x : B}
               {g₁ g₂ : x --> e}
               (α : g₁ · mor_of_em_comnd_cone e ==> g₂ · mor_of_em_comnd_cone e)
               (p : α
                    • (g₂ ◃ cell_of_em_comnd_cone e)
                    • lassociator _ _ _
                    =
                    (g₁ ◃ cell_of_em_comnd_cone e)
                    • lassociator _ _ _
                    • (α ▹ h))
      : em_comnd_ump_cell α p ▹ _ = α
      := pr21 (pr2 He x g₁ g₂ α p).

    Definition em_comnd_ump_eq
               {x : B}
               {g₁ g₂ : x --> e}
               (α : g₁ · mor_of_em_comnd_cone e ==> g₂ · mor_of_em_comnd_cone e)
               (p : α
                    • (g₂ ◃ cell_of_em_comnd_cone e)
                    • lassociator _ _ _
                    =
                    (g₁ ◃ cell_of_em_comnd_cone e)
                    • lassociator _ _ _
                    • (α ▹ h))
               {β₁ β₂ : g₁ ==> g₂}
               (q₁ : β₁ ▹ _ = α)
               (q₂ : β₂ ▹ _ = α)
      : β₁ = β₂.
    Proof.
      exact (maponpaths
               pr1
               (proofirrelevance
                  _
                  (isapropifcontr (pr2 He x g₁ g₂ α p))
                  (β₁ ,, q₁)
                  (β₂ ,, q₂))).
    Qed.

    Section Invertible.
      Context {x : B}
              {g₁ g₂ : x --> e}
              (α : invertible_2cell
                     (g₁ · mor_of_em_comnd_cone e)
                     (g₂ · mor_of_em_comnd_cone e))
              (p : α
                   • (g₂ ◃ cell_of_em_comnd_cone e)
                   • lassociator _ _ _
                   =
                   (g₁ ◃ cell_of_em_comnd_cone e)
                   • lassociator _ _ _
                   • (α ▹ h)).

      Definition em_comnd_ump_cell_inv
        : g₂ ==> g₁.
      Proof.
        refine (em_comnd_ump_cell (α^-1) _).
        abstract
          (use vcomp_move_L_Mp ; [ is_iso | ] ;
           rewrite !vassocl ;
           use vcomp_move_R_pM ; [ is_iso | ] ;
           cbn ;
           rewrite !vassocr ;
           exact (!p)).
      Defined.

      Definition em_comnd_ump_cell_inv_left
        : em_comnd_ump_cell α p • em_comnd_ump_cell_inv = id₂ _.
      Proof.
        use em_comnd_ump_eq.
        - exact (id2 _).
        - rewrite id2_left.
          rewrite id2_rwhisker, id2_right.
          apply idpath.
        - rewrite <- !rwhisker_vcomp.
          unfold em_comnd_ump_cell_inv.
          rewrite !em_comnd_ump_cell_eq.
          apply vcomp_rinv.
        - apply id2_rwhisker.
      Qed.

      Definition em_comnd_ump_cell_inv_right
        : em_comnd_ump_cell_inv • em_comnd_ump_cell α p = id₂ _.
      Proof.
        use em_comnd_ump_eq.
        - exact (id2 _).
        - rewrite id2_left.
          rewrite id2_rwhisker, id2_right.
          apply idpath.
        - rewrite <- !rwhisker_vcomp.
          unfold em_comnd_ump_cell_inv.
          rewrite !em_comnd_ump_cell_eq.
          apply vcomp_linv.
        - apply id2_rwhisker.
      Qed.

      Definition em_comnd_ump_cell_is_invertible
        : is_invertible_2cell (em_comnd_ump_cell α p).
      Proof.
        use make_is_invertible_2cell.
        - exact em_comnd_ump_cell_inv.
        - exact em_comnd_ump_cell_inv_left.
        - exact em_comnd_ump_cell_inv_right.
      Defined.
    End Invertible.

    Definition em_comnd_ump_inv2cell
               {x : B}
               {g₁ g₂ : x --> e}
               (α : invertible_2cell
                      (g₁ · mor_of_em_comnd_cone e)
                      (g₂ · mor_of_em_comnd_cone e))
               (p : α
                    • (g₂ ◃ cell_of_em_comnd_cone e)
                    • lassociator _ _ _
                   =
                   (g₁ ◃ cell_of_em_comnd_cone e)
                   • lassociator _ _ _
                   • (α ▹ h))
      : invertible_2cell g₁ g₂.
    Proof.
      use make_invertible_2cell.
      - exact (em_comnd_ump_cell α p).
      - exact (em_comnd_ump_cell_is_invertible α p).
    Defined.
  End Projections.

  (**
   2. Being an Eilenberg-Moore object for a comonad is a proposition
   *)
  Definition isaprop_has_em_comnd_ump
             (HB : is_univalent_2_1 B)
             (e : em_comnd_cone)
    : isaprop (has_em_comnd_ump e).
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
    use (path_em_comnd_cone_mor HB).
    - use (em_comnd_ump_inv2cell φ₁).
      + exact (comp_of_invertible_2cell
                 (inv_of_invertible_2cell (inv2cell_of_em_comnd_cone_mor (pr1 φ₁ x)))
                 (inv2cell_of_em_comnd_cone_mor (pr1 φ₂ x))).
      + abstract
          (cbn ;
           rewrite <- !rwhisker_vcomp ;
           rewrite !vassocl ;
           rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
           rewrite <- (em_comnd_cone_mor_endo (pr1 φ₂ x)) ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
           rewrite !vassocr ;
           use vcomp_move_L_Mp ; [ is_iso | ] ; cbn ;
           exact (em_comnd_cone_mor_endo (pr1 φ₁ x))).
    - cbn.
      rewrite em_comnd_ump_cell_eq.
      rewrite !vassocr.
      rewrite vcomp_rinv.
      apply id2_left.
  Qed.
End EilenbergMooreComonad.

(**
 3. Bicategories with Eilenberg-Moore objects for comonads
 *)
Definition has_em_comnd
           (B : bicat)
  : UU
  := ∏ (m : mnd (op2_bicat B)),
     ∑ (e : em_comnd_cone m),
     has_em_comnd_ump m e.
