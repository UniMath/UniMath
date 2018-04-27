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
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicat.

Open Scope cat.
Open Scope mor_disp_scope.

(** To be moved to Bicat *)
Section auxiliary.

Context {C : prebicat}.


Lemma cell_id_if_inv_cell_id {a b : C} {f g : C ⟦a, b⟧} (x y : f ==> g)
      (hx : is_invertible_2cell x) (hy : is_invertible_2cell y)
  : inv_invertible_2cell (x,,hx) = inv_invertible_2cell (y,,hy) → x = y.
Proof.
  intro H.
  set (P:= (inv_invertible_2cell (inv_invertible_2cell (x,,hx)))).
  intermediate_path (pr1 P).
  { apply idpath. }
  unfold P.
  rewrite H.
  apply idpath.
Qed.

(* rwhisker_lwhisker
(∏ (a b c d : C) (f : C⟦a, b⟧) (g h : C⟦b, c⟧) (i : c --> d) (x : g ==> h),
       (f ◃ (x ▹ i)) • lassociator _ _ _ = lassociator _ _ _ • ((f ◃ x) ▹ i))
 *)

Lemma rwhisker_lwhisker_rassociator
      (a b c d : C) (f : C⟦a, b⟧) (g h : C⟦b, c⟧) (i : c --> d) (x : g ==> h)
  : rassociator _ _ _ • (f ◃ (x ▹ i)) = ((f ◃ x) ▹ i) • rassociator _ _ _ .
Proof.
  use (inv_2cell_left_cancellable (lassociator f g i)).
  { apply  is_invertible_2cell_lassociator. }
  etrans. etrans. apply vassocr. apply maponpaths_2. apply lassociator_rassociator.
  etrans. apply id2_left.

  use (inv_2cell_right_cancellable (lassociator f h i)).
  { apply  is_invertible_2cell_lassociator. }
  apply pathsinv0.
  etrans. apply vassocl.
  etrans. apply maponpaths. apply vassocl.
  etrans. do 2 apply maponpaths. apply  rassociator_lassociator.
  etrans. apply maponpaths. apply id2_right.
  apply pathsinv0, rwhisker_lwhisker.
Qed.


(** 8 lwhisker_lwhisker
(∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h i : c --> d) (x : h ==> i),
 f ◃ (g ◃ x) • lassociator _ _ _ = lassociator _ _ _ • (f · g ◃ x))
*)

(** 8 lwhisker_lwhisker *)
Lemma lwhisker_lwhisker_rassociator (a b c d : C) (f : C⟦a, b⟧)
      (g : C⟦b, c⟧) (h i : c --> d) (x : h ==> i)
  : rassociator f g h  • (f ◃ (g ◃ x)) = (f · g ◃ x) • rassociator _ _ _ .
Proof.
  use (inv_2cell_left_cancellable (lassociator f g h)).
  { apply  is_invertible_2cell_lassociator. }
  etrans. etrans. apply vassocr. apply maponpaths_2. apply lassociator_rassociator.
  etrans. apply id2_left.

  use (inv_2cell_right_cancellable (lassociator f g i)).
  { apply  is_invertible_2cell_lassociator. }
  apply pathsinv0.
  etrans. apply vassocl.
  etrans. apply maponpaths. apply vassocl.
  etrans. do 2 apply maponpaths. apply  rassociator_lassociator.
  etrans. apply maponpaths. apply id2_right.
  apply pathsinv0, lwhisker_lwhisker.
Qed.


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
  (** rewrite with uppler left triangle *)
  apply pathsinv0.
  etrans. apply pathsinv0. apply lunitor_lwhisker.

  (** attach rassociator on both sides *)
  use (inv_2cell_right_cancellable (rassociator _ _ _ )).
  { apply is_invertible_2cell_rassociator. }

  (** rewrite upper right square *)

  etrans. apply vassocl.
  etrans. apply maponpaths.
  apply pathsinv0, lwhisker_lwhisker_rassociator.

  (** rewrite lower middle square *)
  apply pathsinv0.
  etrans. apply vassocl.
  etrans. apply maponpaths. apply pathsinv0, rwhisker_lwhisker_rassociator.

  (** rewrite lower right triangle *)
  etrans.
  do 3 apply maponpaths. apply pathsinv0. apply lunitor_lwhisker.

  (** distribute the whiskering *)
  etrans. apply maponpaths. apply maponpaths. apply pathsinv0, lwhisker_vcomp.

  (** remove trailing lunitor *)

  Search ( _ • _ • _ ).

  etrans. apply vassocr.
  etrans. apply vassocr.

  apply pathsinv0.
  etrans. apply vassocr.
  apply maponpaths_2.

  (** turn the rassociators into lassociators *)

  use cell_id_if_inv_cell_id.
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