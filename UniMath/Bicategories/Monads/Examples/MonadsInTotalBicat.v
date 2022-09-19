(*********************************************************************

 Monads in total bicategories

 We show how to construct monads in total bicategories.

 Many interesting examples of bicategories can be constructed as
 total bicategories, such as monoidal categories, categories with an
 action, and categories with certain (co)limits. By showing how to
 construct monads, monad morphisms and monad cells in total
 bicategories, we are also able to construct those in the previously
 mentioned bicategories.

 Note: the formalization is currently restricted to the case in which
 all displayed 2-cells are equal. This is because this restriction
 makes all involved definitions simpler, because the laws do not
 have to be mentioned.

 Contents
 1. Monads
 2. Monad morphisms
 3. Monad cells
 4. Projections of monad in total bicategory

 *********************************************************************)
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
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EndoMap.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.

Local Open Scope cat.

Section MonadInTotalBicat.
  Context {B : bicat}
          {D : disp_bicat B}
          (HD : disp_2cells_isaprop D).

  Let E : bicat := total_bicat D.

  (**
   1. Monads
   *)
  Definition disp_mnd
             (m : mnd B)
    : UU
    := ∑ (Hob : D (ob_of_mnd m))
         (Hendo : Hob -->[ endo_of_mnd m ] Hob),
       (id_disp Hob ==>[ unit_of_mnd m ] Hendo)
       ×
       (Hendo ;; Hendo ==>[ mult_of_mnd m ] Hendo).

  Definition ob_of_disp_mnd {m : mnd B} (d : disp_mnd m) : D (ob_of_mnd m)
    := pr1 d.

  Section Projections.
    Context {m : mnd B}
            (dm : disp_mnd m).

    Definition endo_of_disp_mnd
      : ob_of_disp_mnd dm -->[ endo_of_mnd m ] ob_of_disp_mnd dm
      := pr12 dm.

    Definition unit_of_disp_mnd
      : id_disp _ ==>[ unit_of_mnd m ] endo_of_disp_mnd
      := pr122 dm.

    Definition mult_of_disp_mnd
      : endo_of_disp_mnd ;; endo_of_disp_mnd ==>[ mult_of_mnd m ] endo_of_disp_mnd
      := pr222 dm.
  End Projections.

  Definition make_disp_mnd
             {m : mnd B}
             (Hob : D (ob_of_mnd m))
             (Hendo : Hob -->[ endo_of_mnd m ] Hob)
             (Hunit : id_disp Hob ==>[ unit_of_mnd m ] Hendo)
             (Hmult : Hendo ;; Hendo ==>[ mult_of_mnd m ] Hendo)
    : disp_mnd m
    := Hob ,, Hendo ,, Hunit ,, Hmult.

  Section MakeMonad.
    Context {m : mnd B}
            (dm : disp_mnd m).

    Definition make_mnd_data_total_bicat
      : mnd_data E.
    Proof.
      use make_mnd_data.
      - exact (ob_of_mnd m ,, ob_of_disp_mnd dm).
      - exact (endo_of_mnd m ,, endo_of_disp_mnd dm).
      - exact (unit_of_mnd m ,, unit_of_disp_mnd dm).
      - exact (mult_of_mnd m ,, mult_of_disp_mnd dm).
    Defined.

    Definition make_is_mnd_total_bicat
      : is_mnd E make_mnd_data_total_bicat.
    Proof.
      repeat split ; (use subtypePath ; [ intro ; apply HD | ]) ; cbn.
      - exact (mnd_unit_left m).
      - exact (mnd_unit_right m).
      - exact (mnd_mult_assoc m).
    Qed.

    Definition make_mnd_total_bicat
      : mnd E.
    Proof.
      use make_mnd.
      - exact make_mnd_data_total_bicat.
      - exact make_is_mnd_total_bicat.
    Defined.
  End MakeMonad.

  (**
   2. Monad morphisms
   *)
  Definition disp_mnd_mor
             {m₁ m₂ : mnd B}
             (f : m₁ --> m₂)
             (dm₁ : disp_mnd m₁)
             (dm₂ : disp_mnd m₂)
    : UU
    := ∑ (ff : ob_of_disp_mnd dm₁ -->[ mor_of_mnd_mor f] ob_of_disp_mnd dm₂),
       ff ;; endo_of_disp_mnd dm₂ ==>[ mnd_mor_endo f] endo_of_disp_mnd dm₁ ;; ff.

  Section Projections.
    Context {m₁ m₂ : mnd B}
            {f : m₁ --> m₂}
            {dm₁ : disp_mnd m₁}
            {dm₂ : disp_mnd m₂}
            (ff : disp_mnd_mor f dm₁ dm₂).

    Definition mor_of_disp_mnd_mor
      : ob_of_disp_mnd dm₁ -->[ mor_of_mnd_mor f] ob_of_disp_mnd dm₂
      := pr1 ff.

    Definition disp_mnd_mor_endo
      : mor_of_disp_mnd_mor ;; endo_of_disp_mnd dm₂
        ==>[ mnd_mor_endo f ]
        endo_of_disp_mnd dm₁ ;; mor_of_disp_mnd_mor
      := pr2 ff.
  End Projections.

  Definition make_disp_mnd_mor
             {m₁ m₂ : mnd B}
             {f : m₁ --> m₂}
             {dm₁ : disp_mnd m₁}
             {dm₂ : disp_mnd m₂}
             (ff : ob_of_disp_mnd dm₁ -->[ mor_of_mnd_mor f] ob_of_disp_mnd dm₂)
             (Hff : ff ;; endo_of_disp_mnd dm₂
                    ==>[ mnd_mor_endo f]
                    endo_of_disp_mnd dm₁ ;; ff)
    : disp_mnd_mor f dm₁ dm₂
    := ff ,, Hff.

  Section MakeMonadMor.
    Context {m₁ m₂ : mnd B}
            {f : m₁ --> m₂}
            {dm₁ : disp_mnd m₁}
            {dm₂ : disp_mnd m₂}
            (ff : disp_mnd_mor f dm₁ dm₂).

    Definition make_mnd_mor_data_total_bicat
      : mnd_mor_data
          (make_mnd_total_bicat dm₁)
          (make_mnd_total_bicat dm₂).
    Proof.
      use make_mnd_mor_data.
      - exact (mor_of_mnd_mor f ,, mor_of_disp_mnd_mor ff).
      - exact (mnd_mor_endo f ,, disp_mnd_mor_endo ff).
    Defined.

    Definition make_mnd_mor_laws_total_bicat
      : mnd_mor_laws make_mnd_mor_data_total_bicat.
    Proof.
      repeat split ; (use subtypePath ; [ intro ; apply HD | ]) ; cbn.
      - exact (mnd_mor_unit f).
      - exact (mnd_mor_mu f).
    Qed.

    Definition make_mnd_mor_total_bicat
      : make_mnd_total_bicat dm₁ --> make_mnd_total_bicat dm₂.
    Proof.
      use make_mnd_mor.
      - exact make_mnd_mor_data_total_bicat.
      - exact make_mnd_mor_laws_total_bicat.
    Defined.
  End MakeMonadMor.

  (**
   3. Monad cells
   *)
  Definition disp_mnd_cell
             {m₁ m₂ : mnd B}
             {f g : m₁ --> m₂}
             (α : f ==> g)
             {dm₁ : disp_mnd m₁}
             {dm₂ : disp_mnd m₂}
             (ff : disp_mnd_mor f dm₁ dm₂)
             (gg : disp_mnd_mor g dm₁ dm₂)
    : UU
    := mor_of_disp_mnd_mor ff ==>[ cell_of_mnd_cell α] mor_of_disp_mnd_mor gg.

  Section MakeMonadCell.
    Context {m₁ m₂ : mnd B}
            {f g : m₁ --> m₂}
            {α : f ==> g}
            {dm₁ : disp_mnd m₁}
            {dm₂ : disp_mnd m₂}
            {ff : disp_mnd_mor f dm₁ dm₂}
            {gg : disp_mnd_mor g dm₁ dm₂}
            (αα : disp_mnd_cell α ff gg).

    Definition make_mnd_cell_data_total_bicat
      : mnd_cell_data
          (make_mnd_mor_total_bicat ff)
          (make_mnd_mor_total_bicat gg)
      := cell_of_mnd_cell α ,, αα.

    Definition make_is_mnd_cell_total_bicat
      : is_mnd_cell make_mnd_cell_data_total_bicat.
    Proof.
      use subtypePath ; [ intro ; apply HD | ].
      exact (mnd_cell_endo α).
    Qed.

    Definition make_mnd_cell_total_bicat
      : make_mnd_mor_total_bicat ff
        ==>
        make_mnd_mor_total_bicat gg.
    Proof.
      use make_mnd_cell.
      - exact make_mnd_cell_data_total_bicat.
      - exact make_is_mnd_cell_total_bicat.
    Defined.
  End MakeMonadCell.

  (**
   4. Projections of monad in total bicategory
   *)
  Definition pr1_of_mnd_total_bicat_data
             (m : mnd E)
    : mnd_data B.
  Proof.
    use make_mnd_data.
    - exact (pr1 (ob_of_mnd m)).
    - exact (pr1 (endo_of_mnd m)).
    - exact (pr1 (unit_of_mnd m)).
    - exact (pr1 (mult_of_mnd m)).
  Defined.

  Definition pr1_of_mnd_total_bicat_is_mnd
             (m : mnd E)
    : is_mnd B (pr1_of_mnd_total_bicat_data m).
  Proof.
    repeat split.
    - exact (maponpaths pr1 (mnd_unit_left m)).
    - exact (maponpaths pr1 (mnd_unit_right m)).
    - exact (maponpaths pr1 (mnd_mult_assoc m)).
  Qed.

  Definition pr1_of_mnd_total_bicat
             (m : mnd E)
    : mnd B.
  Proof.
    use make_mnd.
    - exact (pr1_of_mnd_total_bicat_data m).
    - exact (pr1_of_mnd_total_bicat_is_mnd m).
  Defined.

  Definition disp_mnd_of_mnd_total_bicat
             (m : mnd E)
    : disp_mnd (pr1_of_mnd_total_bicat m).
  Proof.
    use make_disp_mnd.
    - exact (pr2 (ob_of_mnd m)).
    - exact (pr2 (endo_of_mnd m)).
    - exact (pr2 (unit_of_mnd m)).
    - exact (pr2 (mult_of_mnd m)).
  Defined.
End MonadInTotalBicat.
