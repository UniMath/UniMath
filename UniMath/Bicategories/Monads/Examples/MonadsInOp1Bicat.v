(*************************************************************************

 Monads in the opposite bicategory

 If we look at monads in the opposite bicategory, then the only thing
 that changes, is the 1-cells and the 2-cells. Instead of being the usual
 monad functors, the 2-cell goes in the other direction.

 Contents
 1. Monad opfunctor
 2. Monad optransformation
 3. Monads in the opposite bicat
 4. Monad morphisms in the opposite bicat
 5. Monad cells in the opposite bicat
 6. Constructors for monad opfunctors

 *************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.

Local Open Scope cat.

(**
 1. Monad opfunctor
 *)
Section MonadOpMor.
  Context {B : bicat}
          {m₁ m₂ : mnd B}.

  Definition mnd_opmor_data
    : UU
    := ∑ (f : ob_of_mnd m₁ --> ob_of_mnd m₂),
       endo_of_mnd m₁ · f ==> f · endo_of_mnd m₂.

  Definition make_mnd_opmor_data
             (f : ob_of_mnd m₁ --> ob_of_mnd m₂)
             (α : endo_of_mnd m₁ · f ==> f · endo_of_mnd m₂)
    : mnd_opmor_data
    := f ,, α.

  Coercion mor_of_mnd_opmor_data
           (f : mnd_opmor_data)
    : ob_of_mnd m₁ --> ob_of_mnd m₂
    := pr1 f.

  Definition mnd_opmor_endo
             (f : mnd_opmor_data)
    : endo_of_mnd m₁ · f ==> f · endo_of_mnd m₂
    := pr2 f.

  Section MonadOpmorLaws.
    Context (f : mnd_opmor_data).

    Definition mnd_opmor_unit_law
      : UU
      := rinvunitor _ • (f ◃ unit_of_mnd m₂)
         =
         linvunitor _ • (unit_of_mnd m₁ ▹ _) • mnd_opmor_endo f.

    Definition mnd_opmor_mu_law
      : UU
      := rassociator _ _ _
         • (_ ◃ mnd_opmor_endo f)
         • lassociator _ _ _
         • (mnd_opmor_endo f ▹ _)
         • rassociator _ _ _
         • (_ ◃ mult_of_mnd m₂)
         =
         (mult_of_mnd m₁ ▹ _)
         • mnd_opmor_endo f.
  End MonadOpmorLaws.

  Definition mnd_opmor_laws
             (f : mnd_opmor_data)
    : UU
    := mnd_opmor_unit_law f × mnd_opmor_mu_law f.

  Definition mnd_opmor
    : UU
    := ∑ (f : mnd_opmor_data), mnd_opmor_laws f.

  Definition make_mnd_opmor
             (f : mnd_opmor_data)
             (Hf : mnd_opmor_laws f)
    : mnd_opmor
    := f ,, Hf.

  Coercion mnd_opmor_to_mnd_opmor_data
           (f : mnd_opmor)
    : mnd_opmor_data
    := pr1 f.

  Section LawProjections.
    Context (f : mnd_opmor).

    Definition mnd_opmor_unit
      : rinvunitor _ • (f ◃ unit_of_mnd m₂)
        =
        linvunitor _ • (unit_of_mnd m₁ ▹ _) • mnd_opmor_endo f
      := pr12 f.

    Definition mnd_opmor_mu
      : rassociator _ _ _
        • (_ ◃ mnd_opmor_endo f)
        • lassociator _ _ _
        • (mnd_opmor_endo f ▹ _)
        • rassociator _ _ _
        • (_ ◃ mult_of_mnd m₂)
        =
        (mult_of_mnd m₁ ▹ _)
        • mnd_opmor_endo f
      := pr22 f.
  End LawProjections.
End MonadOpMor.

Arguments mnd_opmor_data {_} _ _.
Arguments mnd_opmor {_} _ _.

(**
 2. Monad optransformation
 *)
Definition is_mnd_opcell
           {B : bicat}
           {m₁ m₂ : mnd B}
           {f₁ f₂ : mnd_opmor m₁ m₂}
           (α : f₁ ==> f₂)
  : UU
  := mnd_opmor_endo f₁ • (α ▹ endo_of_mnd m₂)
     =
     (endo_of_mnd m₁ ◃ α) • mnd_opmor_endo f₂.

Definition mnd_opcell
           {B : bicat}
           {m₁ m₂ : mnd B}
           (f₁ f₂ : mnd_opmor m₁ m₂)
  : UU
  := ∑ (α : f₁ ==> f₂), is_mnd_opcell α.

Coercion mnd_opcell_to_cell
         {B : bicat}
         {m₁ m₂ : mnd B}
         {f₁ f₂ : mnd_opmor m₁ m₂}
         (α : mnd_opcell f₁ f₂)
  : f₁ ==> f₂
  := pr1 α.

Definition make_mnd_opcell
           {B : bicat}
           {m₁ m₂ : mnd B}
           {f₁ f₂ : mnd_opmor m₁ m₂}
           (α : f₁ ==> f₂)
           (Hα : is_mnd_opcell α)
  : mnd_opcell f₁ f₂
  := α ,, Hα.

(**
 3. Monads in the opposite bicat
 *)
Section MonadsInOpBicat.
  Context {B : bicat}.

  Definition mnd_op1_to_mnd_data
             (m : mnd (op1_bicat B))
    : mnd_data B.
  Proof.
    use make_mnd_data.
    - exact (ob_of_mnd m).
    - exact (endo_of_mnd m).
    - exact (unit_of_mnd m).
    - exact (mult_of_mnd m).
  Defined.

  Definition mnd_op1_to_is_mnd
             (m : mnd (op1_bicat B))
    : is_mnd B (mnd_op1_to_mnd_data m).
  Proof.
    refine (_ ,, _ ,, _).
    - exact (mnd_unit_right m).
    - exact (mnd_unit_left m).
    - exact (!(mnd_mult_assoc' m)).
  Qed.

  Definition mnd_op1_to_mnd
             (m : mnd (op1_bicat B))
    : mnd B.
  Proof.
    use make_mnd.
    - exact (mnd_op1_to_mnd_data m).
    - exact (mnd_op1_to_is_mnd m).
  Defined.
End MonadsInOpBicat.

Section MonadsInOpBicat.
  Context {B : bicat}.

  Definition op1_mnd_to_mnd_data
             (m : op1_bicat (mnd (op1_bicat B)))
    : mnd_data B.
  Proof.
    use make_mnd_data.
    - exact (ob_of_mnd m).
    - exact (endo_of_mnd m).
    - exact (unit_of_mnd m).
    - exact (mult_of_mnd m).
  Defined.

  Definition op1_mnd_to_mnd_is_mnd
             (m : op1_bicat (mnd (op1_bicat B)))
    : is_mnd B (op1_mnd_to_mnd_data m).
  Proof.
    refine (_ ,, _ ,, _).
    - exact (mnd_unit_right m).
    - exact (mnd_unit_left m).
    - exact (!(mnd_mult_assoc' m)).
  Qed.

  Definition op1_mnd_to_mnd
             (m : op1_bicat (mnd (op1_bicat B)))
    : mnd B.
  Proof.
    use make_mnd.
    - exact (op1_mnd_to_mnd_data m).
    - exact (op1_mnd_to_mnd_is_mnd m).
  Defined.

  Definition mnd_to_op1_mnd
             (m : mnd B)
    : op1_bicat (mnd (op1_bicat B)).
  Proof.
    use make_mnd.
    - use make_mnd_data.
      + exact (ob_of_mnd m).
      + exact (endo_of_mnd m).
      + exact (unit_of_mnd m).
      + exact (mult_of_mnd m).
    - refine (_ ,, _ ,, _).
      + exact (mnd_unit_right m).
      + exact (mnd_unit_left m).
      + exact (!(mnd_mult_assoc' m)).
  Defined.

  Definition op1_mnd_weq_mnd_inv₁
             (m : op1_bicat (mnd (op1_bicat B)))
    : mnd_to_op1_mnd (op1_mnd_to_mnd m) = m.
  Proof.
    refine (maponpaths (λ z, _ ,, z) _).
    use subtypePath.
    {
      intro ; apply isaprop_is_mnd.
    }
    apply idpath.
  Qed.

  Definition op1_mnd_weq_mnd_inv₂
             (m : mnd B)
    : op1_mnd_to_mnd (mnd_to_op1_mnd m) = m.
  Proof.
    refine (maponpaths (λ z, _ ,, z) _).
    use subtypePath.
    {
      intro ; apply isaprop_is_mnd.
    }
    apply idpath.
  Qed.
End MonadsInOpBicat.

Definition op1_mnd_weq_mnd
           (B : bicat)
  : op1_bicat (mnd (op1_bicat B)) ≃ mnd B.
Proof.
  use make_weq.
  - exact op1_mnd_to_mnd.
  - use isweq_iso.
    + exact mnd_to_op1_mnd.
    + exact op1_mnd_weq_mnd_inv₁.
    + exact op1_mnd_weq_mnd_inv₂.
Defined.

(**
 4. Monad morphisms in the opposite bicat
 *)
Section MonadMorInOpBicat.
  Context {B : bicat}
          {m₁ m₂ : op1_bicat (mnd (op1_bicat B))}.

  Definition op1_mnd_mor_to_mnd_opmor
             (f : m₁ --> m₂)
    : mnd_opmor (op1_mnd_to_mnd m₁) (op1_mnd_to_mnd m₂).
  Proof.
    use make_mnd_opmor.
    - use make_mnd_opmor_data.
      + exact (mor_of_mnd_mor f).
      + exact (mnd_mor_endo f).
    - split.
      + exact (mnd_mor_unit f).
      + exact (mnd_mor_mu f).
  Defined.

  Definition mnd_opmor_to_op1_mnd_mor_data
             (f : mnd_opmor (op1_mnd_to_mnd m₁) (op1_mnd_to_mnd m₂))
    : mnd_mor_data m₂ m₁.
  Proof.
    use make_mnd_mor_data.
    - exact f.
    - exact (mnd_opmor_endo f).
  Defined.

  Definition mnd_opmor_to_op1_mnd_mor_is_mnd
             (f : mnd_opmor (op1_mnd_to_mnd m₁) (op1_mnd_to_mnd m₂))
    : mnd_mor_laws (mnd_opmor_to_op1_mnd_mor_data f).
  Proof.
    use make_mnd_mor_laws.
    - exact (mnd_opmor_unit f).
    - exact (mnd_opmor_mu f).
  Qed.

  Definition mnd_opmor_to_op1_mnd_mor
             (f : mnd_opmor (op1_mnd_to_mnd m₁) (op1_mnd_to_mnd m₂))
    : m₁ --> m₂.
  Proof.
    use make_mnd_mor.
    - exact (mnd_opmor_to_op1_mnd_mor_data f).
    - exact (mnd_opmor_to_op1_mnd_mor_is_mnd f).
  Defined.

  Definition op1_mnd_mor_weq_mnd_opmor_inv₁
             (f : m₁ --> m₂)
    : mnd_opmor_to_op1_mnd_mor (op1_mnd_mor_to_mnd_opmor f) = f.
  Proof.
    refine (maponpaths (λ z, _ ,, z) _).
    use subtypePath.
    {
      intro.
      apply isapropunit.
    }
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply cellset_property.
    }
    apply idpath.
  Qed.

  Definition op1_mnd_mor_weq_mnd_opmor_inv₂
             (f : mnd_opmor (op1_mnd_to_mnd m₁) (op1_mnd_to_mnd m₂))
    : op1_mnd_mor_to_mnd_opmor (mnd_opmor_to_op1_mnd_mor f) = f.
  Proof.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply cellset_property.
    }
    apply idpath.
  Qed.
End MonadMorInOpBicat.

Definition op1_mnd_mor_weq_mnd_opmor
           {B : bicat}
           (m₁ m₂ : op1_bicat (mnd (op1_bicat B)))
  : m₁ --> m₂ ≃ mnd_opmor (op1_mnd_to_mnd m₁) (op1_mnd_to_mnd m₂).
Proof.
  use make_weq.
  - exact op1_mnd_mor_to_mnd_opmor.
  - use isweq_iso.
    + exact mnd_opmor_to_op1_mnd_mor.
    + exact op1_mnd_mor_weq_mnd_opmor_inv₁.
    + exact op1_mnd_mor_weq_mnd_opmor_inv₂.
Defined.

(**
 5. Monad cells in the opposite bicat
 *)
Section MonadCellInOpBicat.
  Context {B : bicat}
          {m₁ m₂ : op1_bicat (mnd (op1_bicat B))}
          {f₁ f₂ : m₁ --> m₂}.

  Definition op1_mnd_cell_to_mnd_opcell
             (α : f₁ ==> f₂)
    : mnd_opcell (op1_mnd_mor_to_mnd_opmor f₁) (op1_mnd_mor_to_mnd_opmor f₂).
  Proof.
    use make_mnd_opcell.
    - exact (pr1 α).
    - exact (mnd_cell_endo α).
  Defined.

  Definition mnd_opcell_to_op1_mnd_cell
             (α : mnd_opcell
                    (op1_mnd_mor_to_mnd_opmor f₁)
                    (op1_mnd_mor_to_mnd_opmor f₂))
    : f₁ ==> f₂.
  Proof.
    use make_mnd_cell.
    - unfold mnd_cell_data.
      exact α.
    - exact (pr2 α).
  Defined.
End MonadCellInOpBicat.

Definition op1_mnd_cell_weq_mnd_opcell
           {B : bicat}
           {m₁ m₂ : op1_bicat (mnd (op1_bicat B))}
           (f₁ f₂ : m₁ --> m₂)
  : f₁ ==> f₂
    ≃
    mnd_opcell (op1_mnd_mor_to_mnd_opmor f₁) (op1_mnd_mor_to_mnd_opmor f₂).
Proof.
  use make_weq.
  - exact op1_mnd_cell_to_mnd_opcell.
  - use isweq_iso.
    + exact mnd_opcell_to_op1_mnd_cell.
    + abstract
        (intro α ;
         use eq_mnd_cell ;
         apply idpath).
    + abstract
        (intro α ;
         use subtypePath ; [ intro ; apply cellset_property | ] ;
         apply idpath).
Defined.

(**
 6. Constructors for monad opfunctors
 *)
Definition mnd_mor_to_mor_opmor_data
           {B : bicat}
           {m₁ m₂ : mnd B}
           (f : mnd_to_op1_mnd m₁ --> mnd_to_op1_mnd m₂)
  : mnd_opmor_data m₁ m₂.
Proof.
  use make_mnd_opmor_data.
  - exact (mor_of_mnd_mor f).
  - exact (mnd_mor_endo f).
Defined.

Definition mnd_mor_to_mor_opmor_laws
           {B : bicat}
           {m₁ m₂ : mnd B}
           (f : mnd_to_op1_mnd m₁ --> mnd_to_op1_mnd m₂)
  : mnd_opmor_laws (mnd_mor_to_mor_opmor_data f).
Proof.
  split.
  - exact (mnd_mor_unit f).
  - exact (mnd_mor_mu f).
Qed.

Definition mnd_mor_to_mor_opmor
           {B : bicat}
           {m₁ m₂ : mnd B}
           (f : mnd_to_op1_mnd m₁ --> mnd_to_op1_mnd m₂)
  : mnd_opmor m₁ m₂.
Proof.
  use make_mnd_opmor.
  - exact (mnd_mor_to_mor_opmor_data f).
  - exact (mnd_mor_to_mor_opmor_laws f).
Defined.

Definition mor_opmor_to_mnd_mor_data
           {B : bicat}
           {m₁ m₂ : mnd B}
           (f : mnd_opmor m₁ m₂)
  : mnd_mor_data (mnd_to_op1_mnd m₂) (mnd_to_op1_mnd m₁).
Proof.
  use make_mnd_mor_data.
  - exact f.
  - exact (mnd_opmor_endo f).
Defined.

Definition mor_opmor_to_mnd_mor_laws
           {B : bicat}
           {m₁ m₂ : mnd B}
           (f : mnd_opmor m₁ m₂)
  : mnd_mor_laws (mor_opmor_to_mnd_mor_data f).
Proof.
  use make_mnd_mor_laws.
  - exact (mnd_opmor_unit f).
  - exact (mnd_opmor_mu f).
Qed.

Definition mor_opmor_to_mnd_mor
           {B : bicat}
           {m₁ m₂ : mnd B}
           (f : mnd_opmor m₁ m₂)
  : mnd_to_op1_mnd m₁ --> mnd_to_op1_mnd m₂.
Proof.
  use make_mnd_mor.
  - exact (mor_opmor_to_mnd_mor_data f).
  - exact (mor_opmor_to_mnd_mor_laws f).
Defined.

Definition mnd_id_opmor
           {B : bicat}
           (m : mnd B)
  : mnd_opmor m m
  := mnd_mor_to_mor_opmor (id₁ _).

Definition mnd_opmor_comp
           {B : bicat}
           {m₁ m₂ m₃ : mnd B}
           (f₁ : mnd_opmor m₁ m₂)
           (f₂ : mnd_opmor m₂ m₃)
  : mnd_opmor m₁ m₃
  := mnd_mor_to_mor_opmor (mor_opmor_to_mnd_mor f₁ · mor_opmor_to_mnd_mor f₂).
