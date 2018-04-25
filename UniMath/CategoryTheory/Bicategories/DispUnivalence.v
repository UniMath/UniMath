(* =================================================================================== *)
(* Internal adjunciton in displayed bicategories.                                      *)
(* =================================================================================== *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.Univalence.

Open Scope cat.
Open Scope mor_disp_scope.

Section Displayed_Internal_Adjunction.

Notation "f' ==>[ x ] g'" := (disp_2cells x f' g') (at level 60).
Notation "f' <==[ x ] g'" := (disp_2cells x g' f') (at level 60, only parsing).
Notation "rr •• ss" := (vcomp2_disp rr ss) (at level 60).
Notation "ff ◃◃ rr" := (lwhisker_disp ff rr) (at level 60).
Notation "rr ▹▹ gg" := (rwhisker_disp gg rr) (at level 60).

Context {C : prebicat} {D : disp_prebicat C}.

Definition disp_internal_adjunction_over {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
           (j : internal_adjunction_over f g)
           {aa : D a} {bb : D b}
           (ff : aa -->[f] bb) (gg : bb -->[g] aa)
  : UU
  := let (η,ε) := j in
       (id_disp aa ==>[η] ff ;; gg)
     × (gg ;; ff ==>[ε] id_disp bb).

Definition disp_internal_adjunction_data {a b : C} (j : internal_adjunction_data a b)
           (aa : D a) (bb : D b)
           (f := internal_left_adjoint j)
           (g := internal_right_adjoint j)
  : UU
  := ∑ (ff : aa -->[f] bb) (gg : bb -->[g] aa), disp_internal_adjunction_over j ff gg.

Definition disp_internal_left_adjoint {a b : C} {j : internal_adjunction_data a b}
           {aa : D a} {bb : D b}
           (jj : disp_internal_adjunction_data j aa bb)
  : aa -->[internal_left_adjoint j] bb
  := pr1 jj.

Definition disp_internal_right_adjoint {a b : C} {j : internal_adjunction_data a b}
           {aa : D a} {bb : D b}
           (jj : disp_internal_adjunction_data j aa bb)
  : bb -->[internal_right_adjoint j] aa
  := pr1 (pr2 jj).

Coercion disp_internal_adjunction_over_from_data
         {a b : C} {j : internal_adjunction_data a b}
         {aa : D a} {bb : D b}
         (jj : disp_internal_adjunction_data j aa bb)
  : disp_internal_adjunction_over
      j (disp_internal_left_adjoint jj) (disp_internal_right_adjoint jj)
  := pr2 (pr2 jj).

Definition disp_internal_unit
           {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
           {j : internal_adjunction_over f g}
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb} {gg : bb -->[g] aa}
           (jj : disp_internal_adjunction_over j ff gg)
  : id_disp aa ==>[internal_unit j] (ff ;; gg)
  := pr1 jj.

Definition disp_internal_counit
           {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
           {j : internal_adjunction_over f g}
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb} {gg : bb -->[g] aa}
           (jj : disp_internal_adjunction_over j ff gg)
  : (gg ;; ff) ==>[internal_counit j] id_disp bb
  := pr2 jj.

Definition is_disp_internal_adjunction {a b : C}
           {j : internal_adjunction a b}
           (f := internal_left_adjoint j)
           (g := internal_right_adjoint j)
           {aa : D a} {bb : D b}
           (jj : disp_internal_adjunction_data j aa bb)
           (ff := disp_internal_left_adjoint jj)
           (gg := disp_internal_right_adjoint jj)
           (ηη := disp_internal_unit jj)
           (εε := disp_internal_counit jj)
  : UU
  :=   ( linvunitor_disp ff •• (ηη ▹▹ ff) •• rassociator_disp _ _ _ ••
         (ff ◃◃ εε) •• runitor_disp ff =
         transportb (λ x, _ ==>[x] _) (internal_triangle1 j) (id2_disp ff) )
     × ( rinvunitor_disp gg •• (gg ◃◃ ηη) •• lassociator_disp _ _ _ ••
         (εε ▹▹ gg) •• lunitor_disp gg =
         transportb (λ x, _ ==>[x] _) (internal_triangle2 j) (id2_disp gg) ).

Definition disp_internal_adjunction {a b : C}
           (j : internal_adjunction a b)
  : UU
  := ∑ (aa : D a) (bb : D b) (jj : disp_internal_adjunction_data j aa bb),
     is_disp_internal_adjunction jj.

Definition form_disp_internal_equivalence {a b : C}
           {j : internal_equivalence a b}
           {aa: D a} {bb : D b}
           (f := internal_left_adjoint j)
           (g := internal_right_adjoint j)
           {ff : aa -->[f] bb}
           {gg : bb -->[g] aa}
           (η := internal_unit_iso j)
           (ε := internal_counit_iso j)
           (ηη : id_disp aa ==>[η] (ff ;; gg))
           (εε : (gg ;; ff) ==>[ε] id_disp bb)
  : UU
  := is_disp_invertible_2cell ηη × is_disp_invertible_2cell εε.

(*
Definition is_disp_internal_equivalence_over {a b : C}
           {j : internal_equivalence a b}
           {aa: D a} {bb : D b}
           {ff : aa -->[f] bb}
           {gg : bb -->[g] aa}
           (jj : disp_internal_adjunction_over j ff gg)
           (ηη := disp_internal_unit jj)
           (εε := disp_internal_counit jj)
  : UU
  := is_disp_invertible_2cell ηη × is_disp_invertible_2cell εε.
 *)

(* ========================================================================= *)
(* HIC SUNT LEONES !!                                                        *)
(* ========================================================================= *)


(*
  Definition is_internal_equivalence {a b : C} (j : internal_adjunction_data a b)
    : UU
    := is_internal_equivalence_over j.

  Definition internal_equivalence (a b : C)
    : UU
    := ∑ (j : internal_adjunction_data a b), is_internal_equivalence j.

  Coercion internal_adjunction_data_from_internal_equivalence {a b : C}
           (j : internal_equivalence a b)
    : internal_adjunction_data a b
    := pr1 j.

  Coercion is_internal_equivalence_from_internal_equivalence {a b : C}
           (j : internal_equivalence a b)
    : is_internal_equivalence j
    := pr2 j.

  Definition is_internal_left_adjoint_internal_equivalence {a b : C} (f : C⟦a,b⟧)
    : UU
    := ∑ (g : C⟦b,a⟧) (j : internal_adjunction_over f g),
         is_internal_equivalence_over j
       × is_internal_adjunction j.

  Definition internal_adjoint_internal_equivalence (a b : C) : UU
    := ∑ (f : C⟦a,b⟧), is_internal_left_adjoint_internal_equivalence f.

*)


  Definition is_internal_equivalence_over {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
             (j : internal_adjunction_over f g)
             (η := internal_unit j)
             (ε := internal_counit j)
    : UU
    := is_invertible_2cell η × is_invertible_2cell ε.

  Definition is_internal_equivalence {a b : C} (j : internal_adjunction_data a b)
    : UU
    := is_internal_equivalence_over j.

  Definition is_internal_left_adjoint_internal_equivalence {a b : C} (f : C⟦a,b⟧)
    : UU
    := ∑ (g : C⟦b,a⟧) (j : internal_adjunction_over f g),
         is_internal_equivalence_over j
       × is_internal_adjunction j.







Definition disp_is_internal_equivalence {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
           {j : internal_adjunction_data f g}
           {aa : D a} {bb : D b}
           {ff : aa -->[internal_left_adjoint j] bb}
           {gg : bb -->[internal_right_adjoint j] aa}
           (jj : disp_internal_adjunction_over j ff gg)
  : UU
  := let (ηη,εε) := jj in
       is_disp_invertible_2cell ηη
     × is_disp_invertible_2cell εε.


(*
  Definition is_equivalence {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
             (adj : internal_adjunction_data f g)
    : UU
    := let (η,ε) := adj in
         is_invertible_2cell η
       × is_invertible_2cell ε.

  Definition is_internal_adjoint_equivalence {a b : C} (f : C⟦a,b⟧)
    : UU
    := ∑ (g : C⟦b,a⟧) (adj : internal_adjunction_data f g),
         is_equivalence adj
       × is_internal_adjunction adj.

  Definition internal_adjoint_equivalence (a b : C) : UU
    := ∑ (f : C⟦a,b⟧), is_internal_adjoint_equivalence f.

  Definition is_internal_adjunction_identity (a : C)
    : is_internal_adjunction (linvunitor (identity a),, lunitor (identity a)).
  Proof.
    split.
    - etrans.
      { apply maponpaths_2.
        etrans; [apply (!vassocr _ _ _) | ].
        etrans.
        { apply maponpaths.
          etrans; [apply lunitor_lwhisker | ].
          apply maponpaths, pathsinv0, lunitor_runitor_identity.
        }
        etrans; [apply (!vassocr _ _ _) | ].
        etrans.
        { apply maponpaths.
          etrans; [apply rwhisker_vcomp | ].
          etrans; [apply maponpaths, linvunitor_lunitor | ].
          apply id2_rwhisker.
        }
        apply id2_right.
      }
      etrans; [apply maponpaths, pathsinv0, lunitor_runitor_identity | ].
      apply linvunitor_lunitor.
    - etrans.
      { apply maponpaths_2.
        etrans; [apply (!vassocr _ _ _) | ].
        etrans.
        { apply maponpaths.
          etrans.
          { apply maponpaths.
            apply maponpaths.
            apply lunitor_runitor_identity.
          }
          apply runitor_rwhisker.
        }
        etrans; [apply (!vassocr _ _ _) | ].
        apply maponpaths.
        etrans; [ apply lwhisker_vcomp | ].
        apply maponpaths.
        apply linvunitor_lunitor.
      }
      etrans; [apply (!vassocr _ _ _) | ].
      etrans.
      { apply maponpaths.
        etrans; [apply maponpaths_2, lwhisker_id2 | ].
        apply id2_left.
      }
      etrans; [apply maponpaths, lunitor_runitor_identity | ].
      apply rinvunitor_runitor.
  Qed.

  Definition is_internal_adjoint_equivalence_identity (a : C)
    : is_internal_adjoint_equivalence (identity a).
  Proof.
    exists (identity a).
    exists (linvunitor (identity a),, lunitor (identity a)).
    split.
    { split.
      + apply is_invertible_2cell_linvunitor.
      + apply is_invertible_2cell_lunitor.
    }
    apply is_internal_adjunction_identity.
  Defined.

  Definition internal_adjoint_equivalence_identity (a : C)
    : internal_adjoint_equivalence a a.
  Proof.
    exists (identity a).
    eapply is_internal_adjoint_equivalence_identity.
  Defined.

  Definition idtoiso_2_0 (a b : C)
    : a = b -> internal_adjoint_equivalence a b.
  Proof.
    induction 1.
    apply internal_adjoint_equivalence_identity.
  Defined.

  Definition idtoiso_2_1 {a b : C} (f g : C⟦a,b⟧)
    : f = g -> invertible_2cell f g.
  Proof.
    induction 1. apply id2_invertible_2cell.
  Defined.

End Internal_Adjunction.

Definition is_univalent_2_1 (C : prebicat) : UU
  := ∏ (a b : C) (f g : C⟦a,b⟧), isweq (idtoiso_2_1 f g).

Definition is_univalent_2_0 (C : prebicat) : UU
    := ∏ (a b : C), isweq (idtoiso_2_0 a b).

Definition is_univalent_2 (C : bicat) : UU
  := is_univalent_2_0 C × is_univalent_2_1 C.
*)

End Displayed_Internal_Adjunction.
