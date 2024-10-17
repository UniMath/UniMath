Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.GrothendieckToposes.GrothendieckTopologies.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sheaves.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Presheaf.

Local Open Scope cat.

Section TerminalSheaf.

  Context {D : category}.
  Context (GT : Grothendieck_topology D).

  Definition terminal_is_sheaf
    : is_sheaf GT (Terminal_PreShv).
  Proof.
    intros X S f.
    use unique_exists.
    - apply (TerminalArrow Terminal_PreShv).
    - abstract apply (TerminalArrowEq (T := Terminal_PreShv)).
    - abstract (
        intro;
        apply isaset_nat_trans;
        apply homset_property
      ).
    - abstract (
        intros x y;
        apply (TerminalArrowUnique Terminal_PreShv)
      ).
  Defined.

  Definition terminal_sheaf_sheaf
    : sheaf_cat GT
    := _ ,, terminal_is_sheaf.

  Definition terminal_sheaf_is_terminal
    : isTerminal (sheaf_cat GT) terminal_sheaf_sheaf.
  Proof.
    intros Y.
    use unique_exists.
    - apply TerminalArrow.
    - exact tt.
    - abstract (
        intro f;
        apply isapropunit
      ).
    - abstract (
        intros f t;
        apply TerminalArrowUnique
      ).
  Defined.

  Definition terminal_sheaf
    : Terminal (sheaf_cat GT)
    := make_Terminal terminal_sheaf_sheaf terminal_sheaf_is_terminal.

End TerminalSheaf.
