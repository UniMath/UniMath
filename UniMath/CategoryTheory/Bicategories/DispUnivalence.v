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

Definition disp_internal_adjunction_data {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
           (j : internal_adjunction_data f g)
           {aa : D a} {bb : D b}
           (ff : aa -->[f] bb) (gg : bb -->[g] aa)
  : UU
  := let (η,ε) := j in
       (id_disp aa ==>[η] ff ;; gg)
     × (gg ;; ff ==>[ε] id_disp bb).

Definition is_disp_internal_adjunction {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
           {j : internal_adjunction_data f g}
           (H : is_internal_adjunction j)
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb} {gg : bb -->[g] aa}
           {jj : disp_internal_adjunction_data j ff gg}
  : UU
  := let (H1,H2) := H in
     let (ηη,εε) := jj in
       ( linvunitor_disp ff •• (ηη ▹▹ ff) •• rassociator_disp _ _ _ ••
         (ff ◃◃ εε) •• runitor_disp ff =
         transportb (λ x, _ ==>[x] _) H1 (id2_disp ff) )
     × ( rinvunitor_disp gg •• (gg ◃◃ ηη) •• lassociator_disp _ _ _ ••
         (εε ▹▹ gg) •• lunitor_disp gg =
         transportb (λ x, _ ==>[x] _) H2 (id2_disp gg) ).

Definition disp_internal_adjunction {a b : C}
           (j : internal_adjunction a b)
  : UU
  := ∑ (aa : D a) (bb : D b)
       (ff : aa -->[internal_left_adjoint j] bb) (gg : bb -->[internal_right_adjoint j] aa)
       (jj : disp_internal_adjunction_data j ff gg),
     is_disp_internal_adjunction jj.

(*
Definition disp_internal_adjunction :=
  ∑ (f : C⟦a,b⟧) (g : C⟦b,a⟧) (adj : internal_adjunction_data f g),
  is_internal_adjunction adj.

Definition disp_form_equivalence {f : C⟦a,b⟧} {g : C⟦b,a⟧}
           (adj : internal_adjunction_data f g)
  : UU
  := let (η,ε) := adj in
       is_invertible_2cell η
     × is_invertible_2cell ε.

Definition is_disp_internal_adjoint_equivalence (f : C⟦a,b⟧)
  : UU
  := ∑ (g : C⟦b,a⟧) (adj : internal_adjunction_data f g),
       form_equivalence adj
     × is_internal_adjunction adj.
*)

End Displayed_Internal_Adjunction.
