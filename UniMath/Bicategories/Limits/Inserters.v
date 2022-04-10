(****************************************************************************

 Inserters in bicategories

 Contents
 1. Cones
 2. The universal mapping property
 3. The universal property gives an equivalence of categories
 4. Bicategories with inserters
 5. Inserters are faithful
 6. Inserters are conservative

 ****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.

Local Open Scope cat.

Section Inserters.
  Context {B : bicat}
          {b₁ b₂ : B}
          {f g : b₁ --> b₂}.

  (**
   1. Cones
   *)
  Definition inserter_cone
    : UU
    := ∑ (i : B)
         (m : i --> b₁),
       m · f ==> m · g.

  Definition make_inserter_cone
             (i : B)
             (m : i --> b₁)
             (α : m · f ==> m · g)
    : inserter_cone
    := i ,, m ,, α.

  Coercion inserter_cone_ob
           (cone : inserter_cone)
    : B
    := pr1 cone.

  Definition inserter_cone_pr1
             (cone : inserter_cone)
    : cone --> b₁
    := pr12 cone.

  Definition inserter_cone_cell
             (cone : inserter_cone)
    : inserter_cone_pr1 cone · f ==> inserter_cone_pr1 cone · g
    := pr22 cone.

  Definition inserter_1cell
             (cone₁ cone₂ : inserter_cone)
    : UU
    := ∑ (k : cone₁ --> cone₂)
         (α : invertible_2cell
                (k · inserter_cone_pr1 cone₂)
                (inserter_cone_pr1 cone₁)),
       (k ◃ inserter_cone_cell cone₂)
       • lassociator _ _ _
       • (α ▹ g)
       =
       lassociator _ _ _
       • (α ▹ f)
       • inserter_cone_cell cone₁.

  Definition make_inserter_1cell
             {cone₁ cone₂ : inserter_cone}
             (k : cone₁ --> cone₂)
             (α : invertible_2cell
                    (k · inserter_cone_pr1 cone₂)
                    (inserter_cone_pr1 cone₁))
             (p : (k ◃ inserter_cone_cell cone₂)
                  • lassociator _ _ _
                  • (α ▹ g)
                  =
                  lassociator _ _ _
                  • (α ▹ f)
                  • inserter_cone_cell cone₁)
    : inserter_1cell cone₁ cone₂
    := k ,, α ,, p.

  Coercion inserter_1cell_mor
           {cone₁ cone₂ : inserter_cone}
           (u : inserter_1cell cone₁ cone₂)
    : cone₁ --> cone₂
    := pr1 u.

  Definition inserter_1cell_pr1
             {cone₁ cone₂ : inserter_cone}
             (u : inserter_1cell cone₁ cone₂)
    : invertible_2cell
        (u · inserter_cone_pr1 cone₂)
        (inserter_cone_pr1 cone₁)
    := pr12 u.

  Definition inserter_1cell_cell
             {cone₁ cone₂ : inserter_cone}
             (u : inserter_1cell cone₁ cone₂)
    : (_ ◃ inserter_cone_cell cone₂)
       • lassociator _ _ _
       • (inserter_1cell_pr1 u ▹ g)
       =
       lassociator _ _ _
       • (inserter_1cell_pr1 u ▹ f)
       • inserter_cone_cell cone₁
    := pr22 u.

  (**
   2. The universal mapping property
   *)
  Section UniversalMappingProperty.
    Context (cone : inserter_cone).

    Definition has_inserter_ump_1
      : UU
      := ∏ (other_cone : inserter_cone),
         inserter_1cell other_cone cone.

    Definition has_inserter_ump_2
      : UU
      := ∏ (x : B)
           (u₁ u₂ : x --> cone)
           (α : u₁ · inserter_cone_pr1 cone
                ==>
                u₂ · inserter_cone_pr1 cone)
           (p : rassociator _ _ _
                • (u₁ ◃ inserter_cone_cell cone)
                • lassociator _ _ _
                • (α ▹ g)
                =
                (α ▹ f)
                • rassociator _ _ _
                • (u₂ ◃ inserter_cone_cell cone)
                • lassociator _ _ _),
         ∑ (ζ : u₁ ==> u₂),
         ζ ▹ inserter_cone_pr1 cone = α.

    Definition has_inserter_ump_eq
      : UU
      := ∏ (x : B)
           (u₁ u₂ : x --> cone)
           (α : u₁ · inserter_cone_pr1 cone
                ==>
                u₂ · inserter_cone_pr1 cone)
           (p : rassociator _ _ _
                • (u₁ ◃ inserter_cone_cell cone)
                • lassociator _ _ _
                • (α ▹ g)
                =
                (α ▹ f)
                • rassociator _ _ _
                • (u₂ ◃ inserter_cone_cell cone)
                • lassociator _ _ _)
           (φ₁ φ₂ : u₁ ==> u₂)
           (q₁ : φ₁ ▹ inserter_cone_pr1 cone = α)
           (q₂ : φ₂ ▹ inserter_cone_pr1 cone = α),
         φ₁ = φ₂.

    Definition has_inserter_ump
      : UU
      := has_inserter_ump_1 × has_inserter_ump_2 × has_inserter_ump_eq.
  End UniversalMappingProperty.

  Section Projections.
    Context {cone : inserter_cone}
            (H : has_inserter_ump cone).

    Definition inserter_ump_mor
               {i : B}
               (m : i --> b₁)
               (α : m · f ==> m · g)
      : i --> cone
      := pr1 H (make_inserter_cone i m α).

    Definition inserter_ump_mor_pr1
               {i : B}
               (m : i --> b₁)
               (α : m · f ==> m · g)
      : invertible_2cell
          (inserter_ump_mor m α · inserter_cone_pr1 cone)
          m
      := inserter_1cell_pr1 (pr1 H (make_inserter_cone i m α)).

    Definition inserter_ump_mor_cell
               {i : B}
               (m : i --> b₁)
               (α : m · f ==> m · g)
      : (_ ◃ inserter_cone_cell cone)
        • lassociator _ _ _
        • (inserter_ump_mor_pr1 m α ▹ g)
        =
        lassociator _ _ _
        • (inserter_ump_mor_pr1 m α ▹ f)
        • α
      := inserter_1cell_cell (pr1 H (make_inserter_cone i m α)).

    Definition inserter_ump_cell
               {x : B}
               {u₁ u₂ : x --> cone}
               (α : u₁ · inserter_cone_pr1 cone
                    ==>
                    u₂ · inserter_cone_pr1 cone)
               (p : rassociator _ _ _
                    • (u₁ ◃ inserter_cone_cell cone)
                    • lassociator _ _ _
                    • (α ▹ g)
                    =
                    (α ▹ f)
                    • rassociator _ _ _
                    • (u₂ ◃ inserter_cone_cell cone)
                    • lassociator _ _ _)
      : u₁ ==> u₂
      := pr1 (pr12 H x u₁ u₂ α p).

    Definition inserter_ump_cell_pr1
               {x : B}
               {u₁ u₂ : x --> cone}
               (α : u₁ · inserter_cone_pr1 cone
                    ==>
                    u₂ · inserter_cone_pr1 cone)
               (p : rassociator _ _ _
                    • (u₁ ◃ inserter_cone_cell cone)
                    • lassociator _ _ _
                    • (α ▹ g)
                    =
                    (α ▹ f)
                    • rassociator _ _ _
                    • (u₂ ◃ inserter_cone_cell cone)
                    • lassociator _ _ _)
      : inserter_ump_cell α p ▹ inserter_cone_pr1 cone = α
      := pr2 (pr12 H x u₁ u₂ α p).

    Definition inserter_ump_eq
               {x : B}
               {u₁ u₂ : x --> cone}
               (α : u₁ · inserter_cone_pr1 cone
                    ==>
                    u₂ · inserter_cone_pr1 cone)
               (p : rassociator _ _ _
                    • (u₁ ◃ inserter_cone_cell cone)
                    • lassociator _ _ _
                    • (α ▹ g)
                    =
                    (α ▹ f)
                    • rassociator _ _ _
                    • (u₂ ◃ inserter_cone_cell cone)
                    • lassociator _ _ _)
               (φ₁ φ₂ : u₁ ==> u₂)
               (q₁ : φ₁ ▹ inserter_cone_pr1 cone = α)
               (q₂ : φ₂ ▹ inserter_cone_pr1 cone = α)
      : φ₁ = φ₂
      := pr22 H x u₁ u₂ α p φ₁ φ₂ q₁ q₂.

    Definition inserter_ump_eq_alt
               {x : B}
               {u₁ u₂ : x --> cone}
               (φ₁ φ₂ : u₁ ==> u₂)
               (p : rassociator _ _ _
                    • (u₁ ◃ inserter_cone_cell cone)
                    • lassociator _ _ _
                    • (φ₁ ▹ inserter_cone_pr1 cone ▹ g)
                    =
                    (φ₁ ▹ inserter_cone_pr1 cone ▹ f)
                    • rassociator _ _ _
                    • (u₂ ◃ inserter_cone_cell cone)
                    • lassociator _ _ _)
               (q : φ₁ ▹ inserter_cone_pr1 cone
                    =
                    φ₂ ▹ inserter_cone_pr1 cone)
      : φ₁ = φ₂.
    Proof.
      use inserter_ump_eq.
      - exact (φ₁ ▹ inserter_cone_pr1 cone).
      - exact p.
      - apply idpath.
      - exact (!q).
    Qed.
  End Projections.

  (**
   3. The universal property gives an equivalence of categories
   *)
  Definition inserter_cone_functor_data
             (cone : inserter_cone)
             (x : B)
    : functor_data
        (hom x cone)
        (dialgebra (post_comp x f) (post_comp x g)).
  Proof.
    use make_functor_data.
    - exact (λ h, h · inserter_cone_pr1 cone
                  ,,
                  rassociator _ _ _ • (h ◃ inserter_cone_cell cone) • lassociator _ _ _).
    - refine (λ x y g, g ▹ _ ,, _) ; cbn.
      abstract
        (rewrite !vassocr ;
         rewrite rwhisker_rwhisker_alt ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite !vassocr ;
         rewrite vcomp_whisker ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite rwhisker_rwhisker ;
         apply idpath).
  Defined.

  Definition inserter_cone_functor_is_functor
             (cone : inserter_cone)
             (x : B)
    : is_functor (inserter_cone_functor_data cone x).
  Proof.
    split.
    - intro h.
      use eq_dialgebra ; cbn.
      rewrite id2_rwhisker.
      apply idpath.
    - intros z₁ z₂ z₃ h₁ h₂.
      use eq_dialgebra ; cbn.
      rewrite rwhisker_vcomp.
      apply idpath.
  Qed.

  Definition inserter_cone_functor
             (cone : inserter_cone)
             (x : B)
    : hom x cone ⟶ dialgebra (post_comp x f) (post_comp x g).
  Proof.
    use make_functor.
    - exact (inserter_cone_functor_data cone x).
    - exact (inserter_cone_functor_is_functor cone x).
  Defined.

  Definition is_universal_inserter_cone
             (cone : inserter_cone)
    : UU
    := ∏ (x : B),
       adj_equivalence_of_cats (inserter_cone_functor cone x).


  Section MakeUniversalInserterCone.
    Context (HB_2_1 : is_univalent_2_1 B)
            (cone : inserter_cone)
            (H : has_inserter_ump cone)
            (x : B).

    Definition make_is_universal_inserter_cone_full
      : full (inserter_cone_functor cone x).
    Proof.
      intros u₁ u₂ α.
      pose (p := pr2 α).
      cbn in p.
      rewrite !vassocr in p.
      apply hinhpr.
      simple refine (_ ,, _).
      - use (inserter_ump_cell H).
        + exact (pr1 α).
        + exact p.
      - use eq_dialgebra ; cbn in *.
        apply inserter_ump_cell_pr1.
    Defined.

    Definition make_is_universal_inserter_cone_faithful
      : faithful (inserter_cone_functor cone x).
    Proof.
      intros u₁ u₂ α.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use (inserter_ump_eq_alt H).
      - pose (pr2 α) as p.
        cbn in p.
        rewrite !vassocr in p.
        refine (_ @ p @ _).
        + do 2 apply maponpaths.
          exact (maponpaths pr1 (pr2 φ₁)).
        + do 3 apply maponpaths_2.
          apply maponpaths.
          exact (!(maponpaths pr1 (pr2 φ₁))).
      - exact (maponpaths pr1 (pr2 φ₁) @ !(maponpaths pr1 (pr2 φ₂))).
    Qed.

    Definition make_is_universal_inserter_cone_essentially_surjective
      : essentially_surjective (inserter_cone_functor cone x).
    Proof.
      intros h.
      use hinhpr.
      simple refine (_ ,, _).
      - exact (inserter_ump_mor H (pr1 h) (pr2 h)).
      - use iso_dialgebra.
        + simple refine (_ ,, _) ; cbn.
          * apply inserter_ump_mor_pr1.
          * abstract
              (cbn ;
               rewrite !vassocl ;
               use vcomp_move_R_pM ; [ is_iso | ] ;
               cbn ;
               rewrite !vassocr ;
               apply inserter_ump_mor_cell).
        + use is_inv2cell_to_is_iso.
          apply property_from_invertible_2cell.
    Defined.
  End MakeUniversalInserterCone.

  Definition make_is_universal_inserter_cone
             (HB_2_1 : is_univalent_2_1 B)
             (cone : inserter_cone)
             (H : has_inserter_ump cone)
    : is_universal_inserter_cone cone.
  Proof.
    intro x.
    use rad_equivalence_of_cats.
    - apply is_univ_hom.
      exact HB_2_1.
    - use full_and_faithful_implies_fully_faithful.
      split.
      + apply make_is_universal_inserter_cone_full.
        apply H.
      + apply make_is_universal_inserter_cone_faithful.
        apply H.
    - apply make_is_universal_inserter_cone_essentially_surjective.
      apply H.
  Defined.
End Inserters.

Arguments inserter_cone {_ _ _} _ _.

(**
 4. Bicategories with inserters
 *)
Definition has_inserters
           (B : bicat)
  : UU
  := ∏ (b₁ b₂ : B)
       (f g : b₁ --> b₂),
     ∑ (i : B)
       (m : i --> b₁)
       (α : m · f ==> m · g),
     has_inserter_ump (make_inserter_cone i m α).

(**
 5. Inserters are faithful
 *)
Definition inserter_faithful
           {B : bicat}
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           {i : B}
           (m : i --> b₁)
           (α : m · f ==> m · g)
           (H : has_inserter_ump (make_inserter_cone i m α))
  : faithful_1cell m.
Proof.
  intros x g₁ g₂ β₁ β₂ p.
  use (inserter_ump_eq_alt H) ; cbn.
  - abstract
      (rewrite rwhisker_rwhisker_alt ;
       rewrite !vassocl ;
       apply maponpaths ;
       rewrite rwhisker_rwhisker ;
       rewrite !vassocr ;
       apply maponpaths_2 ;
       refine (!_) ;
       apply vcomp_whisker).
  - exact p.
Defined.

(**
 6. Inserters are conservative
 *)
Section InserterConservative.
  Context {B : bicat}
          {b₁ b₂ : B}
          {f g : b₁ --> b₂}
          {i : B}
          (m : i --> b₁)
          (α : m · f ==> m · g)
          (H : has_inserter_ump (make_inserter_cone i m α))
          {x : B}
          {g₁ g₂ : x --> i}
          (β : g₁ ==> g₂)
          (Hβ : is_invertible_2cell (β ▹ m)).

  Definition inserter_conservative_inv
    : g₂ ==> g₁.
  Proof.
    use (inserter_ump_cell H).
    - exact (Hβ^-1).
    - abstract
        (cbn ;
         use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
         rewrite !vassocl ;
         rewrite rwhisker_rwhisker ;
         use vcomp_move_L_pM ; [ is_iso | ] ; cbn ;
         rewrite !vassocr ;
         apply maponpaths_2 ;
         rewrite rwhisker_rwhisker_alt ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite vcomp_whisker ;
         apply idpath).
  Defined.

  Definition inserter_conservative_rinv
    : β • inserter_conservative_inv = id₂ _.
  Proof.
    use (inserter_ump_eq_alt H) ; cbn.
    - rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_whisker.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      unfold inserter_conservative_inv.
      rewrite (inserter_ump_cell_pr1 H).
      rewrite id2_rwhisker.
      apply vcomp_rinv.
  Qed.

  Definition inserter_conservative_linv
    : inserter_conservative_inv • β = id₂ _.
  Proof.
    use (inserter_ump_eq_alt H) ; cbn.
    - rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_whisker.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      unfold inserter_conservative_inv.
      rewrite (inserter_ump_cell_pr1 H).
      rewrite id2_rwhisker.
      apply vcomp_linv.
  Qed.
End InserterConservative.

Definition inserter_conservative
           {B : bicat}
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           {i : B}
           (m : i --> b₁)
           (α : m · f ==> m · g)
           (H : has_inserter_ump (make_inserter_cone i m α))
  : conservative_1cell m.
Proof.
  intros x g₁ g₂ β Hβ.
  use make_is_invertible_2cell.
  - exact (inserter_conservative_inv m α H β Hβ).
  - exact (inserter_conservative_rinv m α H β Hβ).
  - exact (inserter_conservative_linv m α H β Hβ).
Defined.

Definition inserter_discrete
           {B : bicat}
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           {i : B}
           (m : i --> b₁)
           (α : m · f ==> m · g)
           (H : has_inserter_ump (make_inserter_cone i m α))
  : discrete_1cell m.
Proof.
  split.
  - exact (inserter_faithful m α H).
  - exact (inserter_conservative m α H).
Defined.
