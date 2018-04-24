(* =================================================================================== *)
(* Internal adjunciton in bicategories.                                                *)
(* =================================================================================== *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat.

Open Scope cat.

Section Internal_Adjunction.

  Context {C:prebicat}.

  Section Core.

    Context {a b : C}.

    Definition internal_adjunction_data (f : C⟦a,b⟧) (g : C⟦b,a⟧)
      : UU
      :=   (identity a ==> f · g)
         × (g · f ==> identity b).

    Definition is_internal_adjunction {f : C⟦a,b⟧} {g : C⟦b,a⟧}
               (adj : internal_adjunction_data f g)
      : UU
      := let (η,ε) := adj in
           ( linvunitor f • (η ▹ f) • rassociator _ _ _ • (f ◃ ε) • runitor f = id2 f )
         × ( rinvunitor g • (g ◃ η) • lassociator _ _ _ • (ε ▹ g) • lunitor g = id2 g ).

    Definition internal_adjunction :=
      ∑ (f : C⟦a,b⟧) (g : C⟦b,a⟧) (adj : internal_adjunction_data f g),
      is_internal_adjunction adj.

    Definition form_equivalence {f : C⟦a,b⟧} {g : C⟦b,a⟧}
               (adj : internal_adjunction_data f g)
      : UU
      := let (η,ε) := adj in
           is_invertible_2cell η
         × is_invertible_2cell ε.

    Definition is_internal_adjoint_equivalence (f : C⟦a,b⟧)
      : UU
      := ∑ (g : C⟦b,a⟧) (adj : internal_adjunction_data f g),
           form_equivalence adj
         × is_internal_adjunction adj.

  End Core.

  Definition internal_adjoint_equivalence (a b : C) : UU
    := ∑ (f : C⟦a,b⟧), is_internal_adjoint_equivalence f.

  Axiom lunitor_runitor_identity :
    ∏ a : C, lunitor (identity a) = runitor (identity a).

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

  Definition identity_internal_adjoint_equivalence (a : C)
    : internal_adjoint_equivalence a a.
  Proof.
    exists (identity a).
    eapply is_internal_adjoint_equivalence_identity.
  Defined.

End Internal_Adjunction.
