(* =================================================================================== *)
(* Internal adjunciton in bicategories.                                                *)
(* =================================================================================== *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.

Open Scope cat.

Section Internal_Adjunction.

  Context {C:prebicat}.

  Definition internal_adjunction_over {a b : C} (f : C⟦a,b⟧) (g : C⟦b,a⟧)
    : UU
    :=   (identity a ==> f · g)
       × (g · f ==> identity b).

  Definition internal_adjunction_data (a b : C)
    : UU
    := ∑ (f : C⟦a,b⟧) (g : C⟦b,a⟧), internal_adjunction_over f g.

  Definition internal_left_adjoint {a b : C} (j : internal_adjunction_data a b)
    : C⟦a,b⟧
    := pr1 j.

  Definition internal_right_adjoint {a b : C} (j : internal_adjunction_data a b)
    : C⟦b,a⟧
    := pr1 (pr2 j).

  Coercion interna_adjunction_over_from_data {a b : C} (j : internal_adjunction_data a b)
    : internal_adjunction_over (internal_left_adjoint j) (internal_right_adjoint j)
    := pr2 (pr2 j).

  Coercion interna_adjunction_data_from_over {a b : C}
           {f : C⟦a, b⟧} {g : C⟦b, a⟧} (H : internal_adjunction_over f g)
    : internal_adjunction_data a b
    := (f ,, g ,, H).

  Definition internal_unit {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
             (adj : internal_adjunction_over f g)
    : identity a ==> f · g
    := pr1 adj.

  Definition internal_counit {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
             (adj : internal_adjunction_over f g)
    : g · f ==> identity b
    := pr2 adj.

  Definition is_internal_adjunction {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
             (adj : internal_adjunction_over f g)
    : UU
    := let (η,ε) := adj in
         ( linvunitor f • (η ▹ f) • rassociator _ _ _ • (f ◃ ε) • runitor f = id2 f )
       × ( rinvunitor g • (g ◃ η) • lassociator _ _ _ • (ε ▹ g) • lunitor g = id2 g ).

  Definition internal_triangle1 {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
             {adj : internal_adjunction_over f g}
             (H : is_internal_adjunction adj)
    : linvunitor f • (internal_unit adj ▹ f) • rassociator _ _ _ • (f ◃ internal_counit adj) • runitor f = id2 f
    := pr1 H.

  Definition internal_triangle2 {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
             {adj : internal_adjunction_over f g}
             (H : is_internal_adjunction adj)
    : rinvunitor g • (g ◃ internal_unit adj) • lassociator _ _ _ • (internal_counit adj ▹ g) • lunitor g = id2 g
    := pr2 H.

  Definition internal_adjunction (a b : C) :=
    ∑ (j : internal_adjunction_data a b), is_internal_adjunction j.

  Coercion internal_adjunction_data_from_internal_adjunction {a b : C}
           (j : internal_adjunction a b)
    : internal_adjunction_data a b
    := pr1 j.

  Coercion is_internal_adjunction_from_internal_adjunction {a b : C}
           (j : internal_adjunction a b)
    : is_internal_adjunction j
    := pr2 j.

  Definition is_internal_equivalence_over {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
             (j : internal_adjunction_over f g)
             (η := internal_unit j)
             (ε := internal_counit j)
    : UU
    := is_invertible_2cell η × is_invertible_2cell ε.

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

  Definition internal_unit_iso {a b : C} (j : internal_equivalence a b)
    : invertible_2cell (identity a) (internal_left_adjoint j · internal_right_adjoint j)
    := internal_unit j,, pr1 (pr2 j).

  Definition internal_counit_iso {a b : C} (j : internal_equivalence a b)
    : invertible_2cell (internal_right_adjoint j · internal_left_adjoint j) (identity b)
    := internal_counit j,, pr2 (pr2 j).

  Definition is_internal_left_adjoint_internal_equivalence {a b : C} (f : C⟦a,b⟧)
    : UU
    := ∑ (g : C⟦b,a⟧) (j : internal_adjunction_over f g),
         is_internal_equivalence_over j
       × is_internal_adjunction j.

  Coercion is_internal_equivalence_over_from_is_foo {a b : C} {f : C⟦a,b⟧}
           (H : is_internal_left_adjoint_internal_equivalence f)
    : is_internal_equivalence_over _
    := pr1 (pr2 (pr2 H)).

  Coercion is_internal_adjunction_over_from_is_foo {a b : C} {f : C⟦a,b⟧}
           (H : is_internal_left_adjoint_internal_equivalence f)
    : is_internal_adjunction _
    := pr2 (pr2 (pr2 H)).

  Coercion internal_adjunction_over_from_is_foo {a b : C} {f : C⟦a,b⟧}
           (H : is_internal_left_adjoint_internal_equivalence f)
    : internal_adjunction_over _ _
    := pr1 (pr2 H).


  Definition internal_adjoint_equivalence (a b : C) : UU
    := ∑ j : internal_adjunction_data a b,
             is_internal_equivalence j
           × is_internal_adjunction j.

  Coercion internal_adjunction_data_from_internal_adjoint_equivalence
           {a b : C}
           (f : internal_adjoint_equivalence a b)
    : internal_adjunction_data a b
    := pr1 f.

  Coercion internal_equivalence_from_internal_adjoint_equivalence
           {a b : C}
           (f : internal_adjoint_equivalence a b)
    : internal_equivalence a b := pr1 f ,, pr1 (pr2 f).

  Coercion internal_adjunction_from_internal_adjoint_equivalence
           {a b : C}
           (f : internal_adjoint_equivalence a b)
    : internal_adjunction a b := pr1 f ,, pr2 (pr2 f).

  Definition internal_adjunction_data_identity (a : C)
    : internal_adjunction_data a a.
  Proof.
    exists (identity a).
    exists (identity a).
    exact (linvunitor (identity a),, lunitor (identity a)).
  Defined.

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

  Definition is_internal_left_adjoint_internal_equivalence_identity (a : C)
    : is_internal_left_adjoint_internal_equivalence (identity a).
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

  Lemma is_internal_equivalence_identity (a : C)
    : is_internal_equivalence (internal_adjunction_data_identity a).
  Proof.
    split.
    + apply is_invertible_2cell_linvunitor.
    + apply is_invertible_2cell_lunitor.
  Defined.

  Definition internal_adjunction_identity (a : C)
    : internal_adjunction a a.
  Proof.
    exists (internal_adjunction_data_identity a).
    apply is_internal_adjunction_identity.
  Defined.

  Definition internal_adjoint_equivalence_identity (a : C)
    : internal_adjoint_equivalence a a.
  Proof.
    exists (internal_adjunction_data_identity a).
    split.
    - apply is_internal_equivalence_identity.
    - apply is_internal_adjunction_identity.
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



(*
Definition internal_adjoint_equivalence (a b : C) : UU
  := ∑ (f : C⟦a,b⟧), is_internal_left_adjoint_internal_equivalence f.

Coercion left_adjoint_from_internal_adjoint_equivalent
         {a b : C} (f : internal_adjoint_equivalence a b)
    : C⟦a, b⟧
  := pr1 f.

Coercion is_from_internal_adjoint_equivalence {a b : C}
         (f : internal_adjoint_equivalence a b)
  : is_internal_left_adjoint_internal_equivalence f
  := pr2 f.
*)