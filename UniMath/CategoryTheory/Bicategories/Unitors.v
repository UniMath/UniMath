(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    April 2018

 We formalize the proof showing that in a bicategory,
 left and right unitor coincide on the identity.
 We follow Joyal and Ross'
 Braided Tensor Categories, Proposition 1.1

 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.OpMorBicat.
Require Import UniMath.CategoryTheory.Bicategories.OpCellBicat.

Open Scope cat.

Section unitors.

Context {C : bicat}.

(** The triangle with "?" in the proof of the Proposition *)

Lemma runitor_rwhisker_rwhisker {a b c d: C} (f : C⟦a, b⟧)
      (g : C⟦b, c⟧) (h : C⟦c, d⟧)
  : (rassociator f g (identity c) ▹ h) • ((f ◃ runitor g) ▹ h) =
    runitor (f · g) ▹ h.
Proof.
  (** rewrite with uppler left triangle *)
  apply pathsinv0.
  etrans.
  { apply pathsinv0. apply lunitor_lwhisker. }

  (** attach rassociator on both sides *)
  use (inv_2cell_right_cancellable (rassociator _ _ _ )).
  { apply is_invertible_2cell_rassociator. }

  (** rewrite upper right square *)
  etrans.
  { apply vassocl. }
  etrans.
  { apply maponpaths.
    apply pathsinv0, lwhisker_lwhisker_rassociator.
  }

  (** rewrite lower middle square *)
  apply pathsinv0.
  etrans. { apply vassocl. }
  etrans.
  { apply maponpaths.
    apply pathsinv0, rwhisker_lwhisker_rassociator.
  }

  (** rewrite lower right triangle *)
  etrans.
  { do 3 apply maponpaths.
    apply pathsinv0.
    apply lunitor_lwhisker.
  }

  (** distribute the whiskering *)
  etrans.
  { do 2 apply maponpaths.
    apply pathsinv0, lwhisker_vcomp.
  }

  (** remove trailing lunitor *)
  etrans. { apply vassocr. }
  etrans. { apply vassocr. }

  apply pathsinv0.
  etrans. { apply vassocr. }
  apply maponpaths_2.

  (** turn the rassociators into lassociators *)
  use cell_id_if_inv_cell_id.
  - use is_invertible_2cell_composite.
    + apply is_invertible_2cell_rassociator.
    + apply is_invertible_2cell_rassociator.
  - use is_invertible_2cell_composite.
    + use is_invertible_2cell_composite.
      * apply is_invertible_2cell_rwhisker.
        apply is_invertible_2cell_rassociator.
      * apply is_invertible_2cell_rassociator.
    + apply is_invertible_2cell_lwhisker.
      apply is_invertible_2cell_rassociator.
  - cbn.
    apply pathsinv0.
    etrans. apply vassocr.
    apply lassociator_lassociator.
Qed.

Lemma rwhisker_id_inj {a b : C} (f g : C⟦a, b⟧)
      (x y : f  ==> g)
  : x ▹ identity b = y ▹ identity b → x = y.
Proof.
  intro H.
  use inv_2cell_left_cancellable.
  - apply (f · identity _ ).
  - apply runitor.
  - apply is_invertible_2cell_runitor.
  - etrans. apply pathsinv0, vcomp_runitor.
    etrans. 2: apply vcomp_runitor.
    apply maponpaths_2. apply H.
Qed.

Lemma lwhisker_id_inj {a b : C} (f g : C⟦a, b⟧)
      (x y : f  ==> g)
  : identity a ◃ x = identity a ◃ y → x = y.
Proof.
  intro H.
  use inv_2cell_left_cancellable.
  - apply (identity _ · f).
  - apply lunitor.
  - apply is_invertible_2cell_lunitor.
  - etrans. apply pathsinv0, vcomp_lunitor.
    etrans. 2: apply vcomp_lunitor.
    apply maponpaths_2. apply H.
Qed.

(** The first triangle in the Proposition *)
(** a · (1 ⊗ r) = r *)
Lemma runitor_triangle {a b c: C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : rassociator f g (identity c) • (f ◃ runitor g) = runitor (f · g).
Proof.
  apply rwhisker_id_inj.
  etrans. 2: apply runitor_rwhisker_rwhisker.
  apply pathsinv0, rwhisker_vcomp.
Qed.

(** The square in the Proposition *)

(** r = r ⊗ 1 *)
Lemma runitor_is_runitor_rwhisker (a : C)
  : runitor (identity a · identity a) = runitor (identity a) ▹ (identity a).
Proof.
  use (inv_2cell_right_cancellable (runitor _ )).
  - apply is_invertible_2cell_runitor.
  - apply pathsinv0. apply vcomp_runitor .
Qed.

(** l = 1 ⊗ l *)
Lemma lunitor_is_lunitor_lwhisker (a : C)
  : lunitor (identity a · identity a) = identity a ◃ lunitor (identity a).
Proof.
  use (inv_2cell_right_cancellable (lunitor _ )).
  - apply is_invertible_2cell_lunitor.
  - apply pathsinv0. apply vcomp_lunitor .
Qed.

(**  1 ⊗ r = 1 ⊗ l *)
Lemma lwhisker_runitor_lunitor (a : C)
  : identity a  ◃ runitor (identity a) = identity a ◃ lunitor (identity a).
Proof.
  use (inv_2cell_left_cancellable (rassociator _ _ _ )).
  - apply is_invertible_2cell_rassociator.
  - rewrite runitor_triangle.
    rewrite lunitor_lwhisker.
    apply runitor_is_runitor_rwhisker.
Qed.

Lemma runitor_lunitor_identity (a : C)
  : runitor (identity a) = lunitor (identity a).
Proof.
  apply (inv_2cell_left_cancellable (lunitor _ )).
  { apply is_invertible_2cell_lunitor. }
  etrans. { apply pathsinv0. apply vcomp_lunitor. }
  etrans. { apply maponpaths_2. apply lwhisker_runitor_lunitor. }
  apply maponpaths_2. apply (!lunitor_is_lunitor_lwhisker _).
Qed.

Lemma lunitor_runitor_identity (a : C)
  : lunitor (identity a) = runitor (identity a).
Proof.
  apply (! runitor_lunitor_identity _ ).
Qed.

End unitors.

(* ----------------------------------------------------------------------------------- *)
(** ** Examples of laws derived by reversing morphisms or cells.                       *)
(* ----------------------------------------------------------------------------------- *)

Definition rinvunitor_triangle (C : bicat) (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧)
  : (f ◃ rinvunitor g) • lassociator f g (identity c) = rinvunitor (f · g)
  := runitor_triangle (C := op2_bicat C) f g.

Definition lunitor_triangle (C : bicat) (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧)
  : lassociator (identity a) f g • (lunitor f ▹ g) = lunitor (f · g)
  := runitor_triangle (C := op1_bicat C) g f.
