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

(* rwhisker_lwhisker
(∏ (a b c d : C) (f : C⟦a, b⟧) (g h : C⟦b, c⟧) (i : c --> d) (x : g ==> h),
       (f ◃ (x ▹ i)) • lassociator _ _ _ = lassociator _ _ _ • ((f ◃ x) ▹ i))
 *)

Lemma rwhisker_lwhisker_rassociator
      (a b c d : C) (f : C⟦a, b⟧) (g h : C⟦b, c⟧) (i : c --> d) (x : g ==> h)
  : rassociator _ _ _ • (f ◃ (x ▹ i)) = ((f ◃ x) ▹ i) • rassociator _ _ _ .
Proof.
  admit.
Admitted.




End auxiliary.

Section unitors.

Context {C : prebicat}.


(** The triangle with "?" in the proof of the Proposition *)
(** Notes:




*)
Lemma runitor_rwhisker_rwhisker {a b c d: C} (f : C⟦a, b⟧)
      (g : C⟦b, c⟧) (h : C⟦c, d⟧)
  : (rassociator f g (identity _ ) ▹ h) • ((f ◃ runitor _ ) ▹ h) =
    runitor _  ▹ h.
Proof.
  admit.
Admitted.

Lemma rwhisker_id_inj {a b : C} (f g : C⟦a, b⟧)
      (x y : f  ==> g)
  : x ▹ identity _ = y ▹ identity _ → x = y.
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
  : identity _ ◃ x = identity _ ◃ y → x = y.
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
    rewrite lunitor_lwhisker.
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