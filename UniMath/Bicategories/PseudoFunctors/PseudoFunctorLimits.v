(***************************************************************************
 Properties of the bicat of pseudofunctors

 In this file, we study some properties of the bicategory of pseudofunctors.
 We look at the following properties:
 1. Being locally groupoidal
 2. Terminal objects
 3. Initial objects
 ***************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Faithful.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Constant.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.Colimits.Final.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Products.
Import Products.Notations.

Local Open Scope cat.

(** 1. Locally groupoidal *)
Section FixALocallyGrpd.
  Context (B₁ : bicat)
          {B₂ : bicat}
          (HB₂ : locally_groupoid B₂).

  Definition locally_groupoid_psfunctor_bicat
    : locally_groupoid (psfunctor_bicat B₁ B₂).
  Proof.
    intros F G α β m.
    use make_is_invertible_modification.
    intro x.
    apply HB₂.
  Defined.
End FixALocallyGrpd.

(** 2. Final objects *)
Section FixAFinal.
  Context (B₁ : bicat)
          {B₂ : bicat}
          {HB₂_2_1 : is_univalent_2_1 B₂}
          (f : BiFinal HB₂_2_1).

  Definition final_psfunctor
    : psfunctor_bicat B₁ B₂
    := constant _ (pr1 f).

  Definition final_psfunctor_1cell_data
             (F : psfunctor B₁ B₂)
    : pstrans_data F final_psfunctor.
  Proof.
    use make_pstrans_data.
    - exact (λ x, bifinal_1cell _ (pr2 f) (F x)).
    - intros x y g.
      apply (bifinal_2cell _ (pr2 f)).
  Defined.

  Definition final_psfunctor_1cell_is_pstrans
             (F : psfunctor B₁ B₂)
    : is_pstrans (final_psfunctor_1cell_data F).
  Proof.
    repeat split ; intros ; apply (bifinal_eq _ (pr2 f)).
  Qed.

  Definition final_psfunctor_1cell
             (F : psfunctor B₁ B₂)
    : pstrans F final_psfunctor.
  Proof.
    use make_pstrans.
    - exact (final_psfunctor_1cell_data F).
    - exact (final_psfunctor_1cell_is_pstrans F).
  Defined.

  Definition final_psfunctor_2cell_data
             {F : psfunctor B₁ B₂}
             (α β : pstrans F final_psfunctor)
    : invertible_modification_data α β
    := λ x, bifinal_2cell _ (pr2 f) (α x) (β x).

  Definition final_psfunctor_2cell_is_modification
             {F : psfunctor B₁ B₂}
             (α β : pstrans F final_psfunctor)
    : is_modification (final_psfunctor_2cell_data α β).
  Proof.
    intros x y g.
    apply (bifinal_eq _ (pr2 f)).
  Qed.

  Definition final_psfunctor_2cell
             {F : psfunctor B₁ B₂}
             (α β : pstrans F final_psfunctor)
    : invertible_modification α β.
  Proof.
    use make_invertible_modification.
    - exact (final_psfunctor_2cell_data α β).
    - exact (final_psfunctor_2cell_is_modification α β).
  Defined.

  Definition final_psfunctor_eq
             {F : psfunctor B₁ B₂}
             {α β : pstrans F final_psfunctor}
             (m₁ m₂ : modification α β)
    : m₁ = m₂.
  Proof.
    use modification_eq.
    intro.
    apply (bifinal_eq _ (pr2 f)).
  Qed.

  Definition psfunctor_bifinal
    : BiFinal (psfunctor_bicat_is_univalent_2_1 B₁ B₂ HB₂_2_1).
  Proof.
    simple refine (_ ,, _).
    - exact final_psfunctor.
    - use is_bifinal'_to_is_bifinal.
      use make_is_bifinal'.
      + exact final_psfunctor_1cell.
      + exact @final_psfunctor_2cell.
      + exact @final_psfunctor_eq.
  Defined.
End FixAFinal.

(** 3. Initial objects *)
Section FixAnInitial.
  Context (B₁ : bicat)
          {B₂ : bicat}
          {HB₂_2_1 : is_univalent_2_1 B₂}
          (i : BiInitial HB₂_2_1).

  Definition initial_psfunctor
    : psfunctor_bicat B₁ B₂
    := constant _ (pr1 i).

  Definition initial_psfunctor_1cell_data
             (F : psfunctor B₁ B₂)
    : pstrans_data initial_psfunctor F.
  Proof.
    use make_pstrans_data.
    - exact (λ x, biinitial_1cell _ (pr2 i) (F x)).
    - intros x y g.
      apply (biinitial_2cell _ (pr2 i)).
  Defined.

  Definition initial_psfunctor_1cell_is_pstrans
             (F : psfunctor B₁ B₂)
    : is_pstrans (initial_psfunctor_1cell_data F).
  Proof.
    repeat split ; intros ; apply (biinitial_eq _ (pr2 i)).
  Qed.

  Definition initial_psfunctor_1cell
             (F : psfunctor B₁ B₂)
    : pstrans initial_psfunctor F.
  Proof.
    use make_pstrans.
    - exact (initial_psfunctor_1cell_data F).
    - exact (initial_psfunctor_1cell_is_pstrans F).
  Defined.

  Definition initial_psfunctor_2cell_data
             {F : psfunctor B₁ B₂}
             (α β : pstrans initial_psfunctor F)
    : invertible_modification_data α β
    := λ x, biinitial_2cell _ (pr2 i) (α x) (β x).

  Definition initial_psfunctor_2cell_is_modification
             {F : psfunctor B₁ B₂}
             (α β : pstrans initial_psfunctor F)
    : is_modification (initial_psfunctor_2cell_data α β).
  Proof.
    intros x y g.
    apply (biinitial_eq _ (pr2 i)).
  Qed.

  Definition initial_psfunctor_2cell
             {F : psfunctor B₁ B₂}
             (α β : pstrans initial_psfunctor F)
    : invertible_modification α β.
  Proof.
    use make_invertible_modification.
    - exact (initial_psfunctor_2cell_data α β).
    - exact (initial_psfunctor_2cell_is_modification α β).
  Defined.

  Definition initial_psfunctor_eq
             {F : psfunctor B₁ B₂}
             {α β : pstrans initial_psfunctor F}
             (m₁ m₂ : modification α β)
    : m₁ = m₂.
  Proof.
    use modification_eq.
    intro.
    apply (biinitial_eq _ (pr2 i)).
  Qed.

  Definition psfunctor_biinitial
    : BiInitial (psfunctor_bicat_is_univalent_2_1 B₁ B₂ HB₂_2_1).
  Proof.
    simple refine (_ ,, _).
    - exact initial_psfunctor.
    - use is_biinitial'_to_is_biinitial.
      use make_is_biinitial'.
      + exact initial_psfunctor_1cell.
      + exact @initial_psfunctor_2cell.
      + exact @initial_psfunctor_eq.
  Defined.
End FixAnInitial.

Definition TODO {A : UU} : A.
Admitted.

(*
Section FixProducts.
  Context (B₁ : bicat)
          {B₂ : bicat}
          (prod_B₂ : has_binprod B₂).

  Notation "b₁ ⊗ b₂" := (binprod prod_B₂ b₁ b₂).
  Notation "'π₁'" := (binprod_pr1 prod_B₂ _ _).
  Notation "'π₂'" := (binprod_pr2 prod_B₂ _ _).
  Notation "⟨ f , g ⟩" := (pair_1cell prod_B₂ f g).
  Notation "⟨⟨ α , β ⟩⟩" := (pair_2cell prod_B₂ α β).

  Section BinprodPSFunctor.
    Context (F G : psfunctor B₁ B₂).

    Definition binprod_psfunctor_data
      : psfunctor_data B₁ B₂.
    Proof.
      use make_psfunctor_data.
      - exact (λ z, F z ⊗ G z).
      - exact (λ x y f, ⟨ π₁ · #F f , π₂ · #G f ⟩).
      - exact (λ x y f g α, ⟨⟨ π₁ ◃ ##F α , π₂ ◃ ##G α ⟩⟩).
      - intro b ; cbn.
        refine (_
                  • ⟨⟨ rinvunitor _ , rinvunitor _ ⟩⟩
                  • ⟨⟨ π₁ ◃ psfunctor_id F b , π₂ ◃ psfunctor_id G b ⟩⟩).
        apply TODO.
      - intros b₁ b₂ b₃ f g.
        refine (_
                  • ⟨⟨ rassociator _ _ _ , rassociator _ _ _ ⟩⟩
                  • ⟨⟨ π₁ ◃ psfunctor_comp F f g , π₂ ◃ psfunctor_comp G f g ⟩⟩).
        apply TODO.
    Defined.

    Definition binprod_psfunctor_laws
      : psfunctor_laws binprod_psfunctor_data.
    Proof.
      repeat split.
      - intros b₁ b₂ f ; cbn.
        rewrite !psfunctor_id2, !lwhisker_id2.
        apply TODO.
      - intros b₁ b₂ f g h α β ; cbn.
        rewrite !psfunctor_vcomp.
        rewrite <- !lwhisker_vcomp.
        apply TODO.
      - intros b₁ b₂ f ; cbn.
        apply TODO.
      - intros b₁ b₂ f ; cbn.
        apply TODO.
      - intros b₁ b₂ b₃ b₄ f g h ; cbn.
        apply TODO.
      - intros b₁ b₂ b₃ f g₁ g₂ α ; cbn.
        apply TODO.
      - intros b₁ b₂ b₃ f g₁ g₂ α ; cbn.
        apply TODO.
    Qed.

    Definition binprod_psfunctor_invertible_2cells
      : invertible_cells binprod_psfunctor_data.
    Proof.
      split ; cbn.
      - intros b.
        is_iso.
        + apply TODO.
        + apply TODO.
        + apply TODO.
      - intros b₁ b₂ b₃ f g.
        is_iso.
        + apply TODO.
        + apply TODO.
        + apply TODO.
    Defined.

    Definition binprod_psfunctor
      : psfunctor B₁ B₂.
    Proof.
      use make_psfunctor.
      - exact binprod_psfunctor_data.
      - exact binprod_psfunctor_laws.
      - exact binprod_psfunctor_invertible_2cells.
    Defined.

    Definition binprod_psfunctor_pr1_data
      : pstrans_data binprod_psfunctor F.
    Proof.
      use make_pstrans_data.
      - exact (λ x, π₁).
      - cbn.
        simple refine (λ x y f, _).
        use inv_of_invertible_2cell.
        apply pair_1cell_pr1.
    Defined.

    Definition binprod_psfunctor_pr1_is_pstrans
      : is_pstrans binprod_psfunctor_pr1_data.
    Proof.
      repeat split.
      - intros b₁ b₂ f g α ; cbn.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
        rewrite pair_2cell_pr1.
        apply idpath.
      - intros b ; cbn.
        apply TODO.
      - intros b₁ b₂ b₃ f g ; cbn.
        apply TODO.
    Qed.

    Definition binprod_psfunctor_pr1
      : pstrans binprod_psfunctor F.
    Proof.
      use make_pstrans.
      - exact binprod_psfunctor_pr1_data.
      - exact binprod_psfunctor_pr1_is_pstrans.
    Defined.

    Definition binprod_psfunctor_pr2_data
      : pstrans_data binprod_psfunctor G.
    Proof.
      use make_pstrans_data.
      - exact (λ x, π₂).
      - cbn.
        simple refine (λ x y f, _).
        use inv_of_invertible_2cell.
        apply pair_1cell_pr2.
    Defined.

    Definition binprod_psfunctor_pr2_is_pstrans
      : is_pstrans binprod_psfunctor_pr2_data.
    Proof.
      repeat split.
      - intros b₁ b₂ f g α ; cbn.
        use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
        rewrite !vassocr.
        use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
        rewrite pair_2cell_pr2.
        apply idpath.
      - intros b ; cbn.
        apply TODO.
      - intros b₁ b₂ b₃ f g ; cbn.
        apply TODO.
    Qed.

    Definition binprod_psfunctor_pr2
      : pstrans binprod_psfunctor G.
    Proof.
      use make_pstrans.
      - exact binprod_psfunctor_pr2_data.
      - exact binprod_psfunctor_pr2_is_pstrans.
    Defined.

    Definition psfunctor_binprod_cone
      : binprod_cone F G.
    Proof.
      use make_binprod_cone.
      - exact binprod_psfunctor.
      - exact binprod_psfunctor_pr1.
      - exact binprod_psfunctor_pr2.
    Defined.

    Definition psfunctor_binprod_ump
      : has_binprod_ump psfunctor_binprod_cone.
    Proof.
      use make_binprod_ump.
      - intro q.
        use make_binprod_1cell.
        + use make_pstrans.
          * use make_pstrans_data.
            ** cbn.
               intros x.
               exact ⟨ (binprod_cone_pr1 q : pstrans _ _) x
                       ,
                       (binprod_cone_pr2 q : pstrans _ _) x ⟩.
            ** cbn.
               apply TODO.
          * apply TODO.
        + apply TODO.
        + apply TODO.
      - intros q H₁ H₂ α β.
      - apply TODO.
      - apply TODO.
      - apply TODO.
    Defined.
  End BinprodPSFunctor.

  Definition psfunctor_has_binprod
    : has_binprod (psfunctor_bicat B₁ B₂).
  Proof.
    intros F G.
    simple refine (_ ,, _).
    - exact (psfunctor_binprod_cone F G).
    - exact (psfunctor_binprod_ump F G).
  Defined.
End FixProducts.

*)


(*
Section FixProducts.
  Context (B₁ : bicat)
          {B₂ : bicat}
          (prod_B₂ : has_binprod B₂).

  Let pB₂ (x y : B₂) : B₂
    := pr1 (prod_B₂ x y).

  Notation "x ⊗ y" := (pB₂ x y).

  Let π₁ {x y : B₂} : x ⊗ y --> x
    := binprod_cone_pr1 (pr1 (prod_B₂ x y)).
  Let π₂ {x y : B₂} : x ⊗ y --> y
    := binprod_cone_pr2 (pr1 (prod_B₂ x y)).

  Notation "⟨ f , g ⟩" := (binprod_ump_1_1cell _ (pr2 (prod_B₂ _ _)) _ f g).

  (*
  Let prod_cell
      {x y z : B₂}
      {f₁ f₂ : x --> y}
      {g₁ g₂ : x --> z}
      (α : f₁ ==> f₂)
      (β : g₁ ==> g₂)
    : ⟨ f₁ , g₁ ⟩ ==> ⟨ f₂ , g₂ ⟩.
  Proof.
    pose (pr122 (prod_B₂ y z) (make_binprod_cone x f₁ g₁)).
    unfold binprod_ump_2 in b.
    cbn in b.
    assert (binprod_1cell (make_binprod_cone x f₁ g₁) (pr1 (prod_B₂ y z))).
    {
      use make_binprod_1cell.
      - refine ⟨ f₂ , g₂ ⟩.
      - cbn.
    use (binprod_ump_2_cell
           _
           (pr2 (prod_B₂ y z))).
    - exact f₂.
    - exact g₂.
    - admit.
    - admit.
    - apply binprod_ump_1_1cell_pr1.
    - apply binprod_ump_1_1cell_pr2.
    -
      cbn.
   *)

  Definition binprod_psfunctor_data
             (F G : psfunctor B₁ B₂)
    : psfunctor_data B₁ B₂.
  Proof.
    use make_psfunctor_data.
    - exact (λ z, F z ⊗ G z).
    - exact (λ x y f, ⟨ π₁ · #F f , π₂ · #G f ⟩).
    - refine (λ x y f g α, _).
      use (binprod_ump_2_cell _ (pr2 (prod_B₂ _ _))).
      + exact (π₁ · #F g).
      + exact (π₂ · #G g).
      + admit.
      + admit.
      + apply binprod_ump_1_1cell_pr1.
      + apply binprod_ump_1_1cell_pr2.
    - intro x ; cbn.
      cbn.


  Definition binprod_psfunctor
             (F G : psfunctor B₁ B₂)
    : psfunctor B₁ B₂.
  Proof.
    use make_psfunctor.

  Definition psfunctor_has_binprod
    : has_binprod (psfunctor_bicat B₁ B₂).
  Proof.
    intros F₁ F₂.
    simple refine (_ ,, _).
    - use make_binprod_cone.
 *)
