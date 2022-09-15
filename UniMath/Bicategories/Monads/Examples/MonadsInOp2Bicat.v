(*************************************************************************

 Monads in `op2 B`

 Comnads can be defined as monads internal to a bicategory. More
 specifically, comonads in `B` are the same as moands in `op2 B`.

 Contents
 1. Comonads
 2. Comonad morphisms
 3. Comonad cells
 4. Monads in `op2 B`
 5. Monad morphisms in `op2 B`
 6. Monad cells in `op2 B`

 *************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.

Local Open Scope cat.

(**
 1. Comonads
 *)
Section Comonads.
  Context {B : bicat}.

  Definition comnd_data
    : UU
    := ∑ (x : B)
         (f : x --> x),
       f ==> id₁ _ × f ==> f · f.

  Definition make_comnd_data
             (x : B)
             (f : x --> x)
             (ex : f ==> id₁ _)
             (dup : f ==> f · f)
    : comnd_data
    := x ,, f ,, ex ,, dup.

  Section Projections.
    Context (C : comnd_data).

    Definition ob_of_comnd
      : B
      := pr1 C.

    Definition endo_of_comnd
      : ob_of_comnd --> ob_of_comnd
      := pr12 C.

    Definition counit_of_comnd
      : endo_of_comnd ==> id₁ _
      := pr122 C.

    Definition comult_of_comnd
      : endo_of_comnd ==> endo_of_comnd · endo_of_comnd
      := pr222 C.
  End Projections.

  Section ComonadLaws.
    Context (C : comnd_data).

    Definition comnd_counit_left_law
      : UU
      := comult_of_comnd C • (counit_of_comnd C ▹ _) • lunitor _
         =
         id₂ _.

    Definition comnd_counit_right_law
      : UU
      := comult_of_comnd C • (_ ◃ counit_of_comnd C) • runitor _
         =
         id₂ _.

    Definition comnd_comult_assoc_law
      : UU
      := comult_of_comnd C
         • (_ ◃ comult_of_comnd C)
         • lassociator _ _ _
         =
         comult_of_comnd C • (comult_of_comnd C ▹ _).
  End ComonadLaws.

  Definition comnd_laws
             (C : comnd_data)
    : UU
    := comnd_counit_left_law C
       ×
       comnd_counit_right_law C
       ×
       comnd_comult_assoc_law C.

  Definition isaprop_comnd_laws
             (C : comnd_data)
    : isaprop (comnd_laws C).
  Proof.
    repeat (use isapropdirprod) ; apply cellset_property.
  Qed.

  Definition comnd
    : UU
    := ∑ (C : comnd_data), comnd_laws C.

  Coercion comnd_to_comnd_data (C : comnd) : comnd_data := pr1 C.

  Section LawsProjections.
    Context (C : comnd).

    Definition comnd_counit_left
      : comult_of_comnd C • (counit_of_comnd C ▹ _) • lunitor _
        =
        id₂ _
      := pr12 C.

    Definition comnd_counit_right
      : comult_of_comnd C • (_ ◃ counit_of_comnd C) • runitor _
        =
        id₂ _
      := pr122 C.

    Definition comnd_comult_assoc
      : comult_of_comnd C
        • (_ ◃ comult_of_comnd C)
        • lassociator _ _ _
        =
        comult_of_comnd C • (comult_of_comnd C ▹ _)
      := pr222 C.
  End LawsProjections.

  Definition make_comnd
             (C : comnd_data)
             (HC : comnd_laws C)
    : comnd
    := C ,, HC.
End Comonads.

Arguments comnd_data : clear implicits.
Arguments comnd : clear implicits.

(**
 2. Comonad morphisms
 *)
Section ComonadMorphism.
  Context {B : bicat}
          {C₁ C₂ : comnd B}.

  Definition comnd_mor_data
    : UU
    := ∑ (f : ob_of_comnd C₁ --> ob_of_comnd C₂),
       endo_of_comnd C₁ · f ==> f · endo_of_comnd C₂.

  Definition make_comnd_mor_data
             (f : ob_of_comnd C₁ --> ob_of_comnd C₂)
             (fe : endo_of_comnd C₁ · f ==> f · endo_of_comnd C₂)
    : comnd_mor_data
    := f ,,  fe.

  Coercion mor_of_comnd_mor
           (f : comnd_mor_data)
    : ob_of_comnd C₁ --> ob_of_comnd C₂
    := pr1 f.

  Definition comnd_mor_endo
             (f : comnd_mor_data)
    : endo_of_comnd C₁ · f ==> f · endo_of_comnd C₂
    := pr2 f.

  Section ComonadMorphismLaws.
    Context (f : comnd_mor_data).

    Definition comnd_mor_counit_law
      : UU
      := (counit_of_comnd C₁ ▹ _) • lunitor _
         =
         comnd_mor_endo f • (_ ◃ counit_of_comnd C₂) • runitor _.

    Definition comnd_mor_comult_law
      : UU
      := (comult_of_comnd C₁ ▹ _)
         • rassociator _ _ _
         • (_ ◃ comnd_mor_endo f)
         • lassociator _ _ _
         • (comnd_mor_endo f ▹ _)
         • rassociator _ _ _
         =
         comnd_mor_endo f
         • (_ ◃ comult_of_comnd C₂).
  End ComonadMorphismLaws.

  Definition comnd_mor_laws
             (f : comnd_mor_data)
    : UU
    := comnd_mor_counit_law f × comnd_mor_comult_law f.

  Definition comnd_mor
    : UU
    := ∑ (f : comnd_mor_data), comnd_mor_laws f.

  Coercion comnd_mor_to_comnd_mor_data
           (f : comnd_mor)
    : comnd_mor_data
    := pr1 f.

  Definition make_comnd_mor
             (f : comnd_mor_data)
             (Hf : comnd_mor_laws f)
    : comnd_mor
    := f ,, Hf.

  Section LawProjections.
    Context (f : comnd_mor).

    Definition comnd_mor_counit
      : (counit_of_comnd C₁ ▹ _) • lunitor _
         =
         comnd_mor_endo f • (_ ◃ counit_of_comnd C₂) • runitor _
      := pr12 f.

    Definition comnd_mor_comult
      : (comult_of_comnd C₁ ▹ _)
        • rassociator _ _ _
        • (_ ◃ comnd_mor_endo f)
        • lassociator _ _ _
        • (comnd_mor_endo f ▹ _)
        • rassociator _ _ _
        =
        comnd_mor_endo f
        • (_ ◃ comult_of_comnd C₂)
      := pr22 f.
  End LawProjections.
End ComonadMorphism.

Arguments comnd_mor_data {_} _ _.
Arguments comnd_mor {_} _ _.

(**
 3. Comonad cells
 *)
Definition is_comnd_cell
           {B : bicat}
           {C₁ C₂ : comnd B}
           {f₁ f₂ : comnd_mor C₁ C₂}
           (α : f₂ ==> f₁)
  : UU
  := (_ ◃ α) • comnd_mor_endo f₁
     =
     comnd_mor_endo f₂ • (α ▹ _).

Definition comnd_cell
           {B : bicat}
           {C₁ C₂ : comnd B}
           (f₁ f₂ : comnd_mor C₁ C₂)
  : UU
  := ∑ (α : f₂ ==> f₁), is_comnd_cell α.

Coercion comnd_cell_to_cell
         {B : bicat}
         {C₁ C₂ : comnd B}
         {f₁ f₂ : comnd_mor C₁ C₂}
         (α : comnd_cell f₁ f₂)
  : f₂ ==> f₁
  := pr1 α.

Definition make_comnd_cell
           {B : bicat}
           {C₁ C₂ : comnd B}
           {f₁ f₂ : comnd_mor C₁ C₂}
           (α : f₂ ==> f₁)
           (Hα : is_comnd_cell α)
  : comnd_cell f₁ f₂
  := α ,, Hα.

(**
 4. Monads in `op2 B`
 *)
Section MonadsInOp2Bicat.
  Context {B : bicat}.

  Definition op2_mnd_to_comnd
             (m : mnd (op2_bicat B))
    : comnd B.
  Proof.
    use make_comnd.
    - use make_comnd_data.
      + exact (ob_of_mnd m).
      + exact (endo_of_mnd m).
      + exact (unit_of_mnd m).
      + exact (mult_of_mnd m).
    - repeat split.
      + abstract
          (unfold comnd_counit_left_law ;
           rewrite !vassocl ;
           exact (mnd_unit_left m)).
      + abstract
          (unfold comnd_counit_right_law ;
           rewrite !vassocl ;
           exact (mnd_unit_right m)).
      + abstract
          (unfold comnd_comult_assoc_law ;
           rewrite !vassocl ;
           exact (mnd_mult_assoc m)).
  Defined.

  Definition comnd_to_op2_mnd
             (C : comnd B)
    : mnd (op2_bicat B).
  Proof.
    use make_mnd.
    - use make_mnd_data.
      + exact (ob_of_comnd C).
      + exact (endo_of_comnd C).
      + exact (counit_of_comnd C).
      + exact (comult_of_comnd C).
    - repeat split.
      + abstract
          (cbn ;
           rewrite !vassocr ;
           exact (comnd_counit_left C)).
      + abstract
          (cbn ;
           rewrite !vassocr ;
           exact (comnd_counit_right C)).
      + abstract
          (cbn ;
           rewrite !vassocr ;
           exact (comnd_comult_assoc C)).
  Defined.

  Definition op2_mnd_weq_comnd_inv₁
             (m : mnd (op2_bicat B))
    : comnd_to_op2_mnd (op2_mnd_to_comnd m) = m.
  Proof.
    refine (maponpaths (λ z, ob_of_mnd m ,, z) _).
    use subtypePath.
    {
      intro.
      apply isaprop_is_mnd.
    }
    apply idpath.
  Qed.

  Definition op2_mnd_weq_comnd_inv₂
             (C : comnd B)
    : op2_mnd_to_comnd (comnd_to_op2_mnd C) = C.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_comnd_laws.
    }
    apply idpath.
  Qed.
End MonadsInOp2Bicat.

Definition op2_mnd_weq_comnd
           (B : bicat)
  : mnd (op2_bicat B) ≃ comnd B.
Proof.
  use make_weq.
  - exact op2_mnd_to_comnd.
  - use gradth.
    + exact comnd_to_op2_mnd.
    + exact op2_mnd_weq_comnd_inv₁.
    + exact op2_mnd_weq_comnd_inv₂.
Defined.

(**
 5. Monad morphisms in `op2 B`
 *)
Section MonadMorInOp2Bicat.
  Context {B : bicat}
          {m₁ m₂ : mnd (op2_bicat B)}.

  Definition op2_mnd_mor_to_comnd_mor
             (f : m₁ --> m₂)
    : comnd_mor (op2_mnd_to_comnd m₁) (op2_mnd_to_comnd m₂).
  Proof.
    use make_comnd_mor.
    - use make_comnd_mor_data.
      + exact (mor_of_mnd_mor f).
      + exact (mnd_mor_endo f).
    - split.
      + abstract
          (unfold comnd_mor_counit_law ;
           cbn ;
           rewrite !vassocl ;
           exact (mnd_mor_unit f)).
      + abstract
          (unfold comnd_mor_comult_law ;
           cbn ;
           rewrite !vassocl ;
           exact (mnd_mor_mu f)).
  Defined.

  Definition comnd_mor_to_op2_mnd_mor
             (f : comnd_mor (op2_mnd_to_comnd m₁) (op2_mnd_to_comnd m₂))
    : m₁ --> m₂.
  Proof.
    use make_mnd_mor.
    - use make_mnd_mor_data.
      + exact f.
      + exact (comnd_mor_endo f).
    - split.
      + abstract
          (cbn ;
           rewrite !vassocr ;
           exact (comnd_mor_counit f)).
      + abstract
          (cbn ;
           rewrite !vassocr ;
           exact (comnd_mor_comult f)).
  Defined.

  Definition op2_mnd_mor_weq_comnd_mor_inv₁
             (f : m₁ --> m₂)
    : comnd_mor_to_op2_mnd_mor (op2_mnd_mor_to_comnd_mor f) = f.
  Proof.
    refine (maponpaths (λ z, _ ,, z) _).
    use subtypePath.
    {
      intro ; apply isapropunit.
    }
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply cellset_property.
    }
    apply idpath.
  Qed.

  Definition op2_mnd_mor_weq_comnd_mor_inv₂
             (f : comnd_mor (op2_mnd_to_comnd m₁) (op2_mnd_to_comnd m₂))
    : op2_mnd_mor_to_comnd_mor (comnd_mor_to_op2_mnd_mor f) = f.
  Proof.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply cellset_property.
    }
    apply idpath.
  Qed.
End MonadMorInOp2Bicat.

Definition op2_mnd_mor_weq_comnd_mor
           {B : bicat}
           (m₁ m₂ : mnd (op2_bicat B))
  : m₁ --> m₂ ≃ comnd_mor (op2_mnd_to_comnd m₁) (op2_mnd_to_comnd m₂).
Proof.
  use make_weq.
  - exact op2_mnd_mor_to_comnd_mor.
  - use gradth.
    + exact comnd_mor_to_op2_mnd_mor.
    + exact op2_mnd_mor_weq_comnd_mor_inv₁.
    + exact op2_mnd_mor_weq_comnd_mor_inv₂.
Defined.

(**
 6. Monad cells in `op2 B`
 *)
Section MonadMorInOp2Bicat.
  Context {B : bicat}
          {m₁ m₂ : mnd (op2_bicat B)}
          {f₁ f₂ : m₁ --> m₂}.

  Definition op2_mnd_cell_to_comnd_cell
             (α : f₁ ==> f₂)
    : comnd_cell (op2_mnd_mor_to_comnd_mor f₁) (op2_mnd_mor_to_comnd_mor f₂).
  Proof.
    use make_comnd_cell.
    - exact (cell_of_mnd_cell α).
    - exact (mnd_cell_endo α).
  Defined.

  Definition comnd_cell_to_op2_mnd_cell
             (α : comnd_cell (op2_mnd_mor_to_comnd_mor f₁) (op2_mnd_mor_to_comnd_mor f₂))
    : f₁ ==> f₂.
  Proof.
    use make_mnd_cell.
    - exact (pr1 α).
    - exact (pr2 α).
  Defined.
End MonadMorInOp2Bicat.

Definition op2_mnd_cell_weq_comnd_cell
           {B : bicat}
           {m₁ m₂ : mnd (op2_bicat B)}
           (f₁ f₂ : m₁ --> m₂)
  : f₁ ==> f₂ ≃ comnd_cell (op2_mnd_mor_to_comnd_mor f₁) (op2_mnd_mor_to_comnd_mor f₂).
Proof.
  use make_weq.
  - exact op2_mnd_cell_to_comnd_cell.
  - use gradth.
    + exact comnd_cell_to_op2_mnd_cell.
    + abstract
        (intro ;
         use eq_mnd_cell ;
         apply idpath).
    + abstract
        (intro ;
         use subtypePath ; [ intro ; apply cellset_property | ] ;
         apply idpath).
Defined.
