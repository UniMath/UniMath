(* ******************************************************************************* *)
(** * Displayed bicategories
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
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicat.

Open Scope cat.
Open Scope mor_disp_scope.

(** To be moved to Bicat *)
Section auxiliary.

Context {C : prebicat}.

Lemma inv_2cell_right_cancellable {a b : C} {f g : C⟦a, b⟧}
      (x : f ==> g) (H : is_invertible_2cell x)
      {e : C⟦a, b⟧} (y z : e ==> f)
  : y • x = z • x -> y = z.
Proof.
  intro R.
  set (xiso := x,, H : invertible_2cell f g).
  etrans.
  { etrans. { apply (! id2_right _ ). }
            apply maponpaths. apply (! invertible_2cell_after_inv_cell xiso). }
  etrans. apply vassocr.
  apply pathsinv0.
  etrans.
  { etrans. { apply (! id2_right _ ). }
            apply maponpaths. apply (! invertible_2cell_after_inv_cell xiso). }
  etrans. apply vassocr.

  apply pathsinv0.
  apply maponpaths_2.
  apply R.
Qed.

Lemma inv_2cell_left_cancellable {a b : C} {f g : C⟦a, b⟧}
      (x : f ==> g) (H : is_invertible_2cell x)
      {h : C⟦a, b⟧} (y z : g ==> h)
  : x • y = x • z -> y = z.
Proof.
  intro R.
  set (xiso := x,, H : invertible_2cell f g).
  etrans.
  { etrans. { apply (! id2_left _ ). }
            apply maponpaths_2. apply (! inv_cell_after_invertible_2cell xiso). }
  etrans. apply (!vassocr _ _ _ ).
  apply pathsinv0.
  etrans.
  { etrans. { apply (! id2_left _ ). }
            apply maponpaths_2. apply (! inv_cell_after_invertible_2cell xiso). }
  etrans. apply (!vassocr _ _ _ ).
  apply pathsinv0.
  apply maponpaths.
  apply R.
Qed.


Lemma rassociator_runitor_lunitor {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : rassociator _ _ _ • (f ◃ lunitor g) = (runitor f ▹ g).
Proof.
  use inv_cell_to_cell_post.
  - apply is_invertible_2cell_rassociator.
  - apply pathsinv0, runitor_rwhisker.
Qed.

End auxiliary.

Section unitors.

Context {C : prebicat}.


(** The first triangle in the Proposition *)
(** a · (1 ⊗ r) = r *)
Lemma runitor_triangle {a b c: C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : rassociator f g (identity c) • (f ◃ runitor g) = runitor (f · g).
Proof.
  admit.
Admitted.

(** The second triangle in the Proposition *)

Lemma lunitor_triangle {a b c: C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : rassociator (identity a) f g • lunitor (f · g) = lunitor f ▹ g .
Proof.
  admit.
Admitted.

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
  : lunitor (identity _ · identity _ ) = identity a ◃ lunitor _ .
Proof.
  use (inv_2cell_right_cancellable (lunitor _ )).
  - apply is_invertible_2cell_lunitor.
  - apply pathsinv0. apply vcomp_lunitor .
Qed.

(**  1 ⊗ r = 1 ⊗ l *)
Lemma lwhisker_runitor_lunitor (a : C)
  : (identity a ) ◃ runitor _ = (identity _ ) ◃ lunitor _ .
Proof.
  use (inv_2cell_left_cancellable (rassociator _ _ _ )).
  - apply is_invertible_2cell_rassociator.
  - rewrite runitor_triangle.
    rewrite rassociator_runitor_lunitor.
    apply runitor_is_runitor_rwhisker.
Qed.

Lemma runitor_lunitor (a : C)
  : runitor (identity a) = lunitor _ .
Proof.
  apply (inv_2cell_left_cancellable (lunitor _ )).
  { apply is_invertible_2cell_lunitor. }
  etrans. { apply pathsinv0. apply vcomp_lunitor. }
  etrans. { apply maponpaths_2. apply lwhisker_runitor_lunitor. }
  apply maponpaths_2. apply (!lunitor_is_lunitor_lwhisker _).
Qed.

End unitors.