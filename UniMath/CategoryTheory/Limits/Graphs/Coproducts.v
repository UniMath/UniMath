(** ****************************************************************

 Coproducts from colimits

 We show that coproducts can be constructed from colimits.

 Contents
 1. The graph
 2. The construction

 ******************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.coproducts.

Local Open Scope cat.

Section CoproductGraph.
  Context (I : UU).

  (** * 1. The graph *)
  Definition type_graph : graph := I ,, λ _ _, empty.

  Definition coproduct_diagram {C : category} (f : I → C) : diagram type_graph C.
  Proof.
    refine (f ,, _).
    intros u v F.
    induction F.
  Defined.

  (** * 2. The construction *)
  Section CoproductsFromColims.
    Context {C : category}
            (HC : Colims_of_shape type_graph C).

    Section CoproductsFromColim.
      Context (f : I → C).

      Let D : diagram type_graph C := coproduct_diagram f.
      Let L : ColimCocone D := HC D.

      Let x : C := colim L.
      Let fs : ∏ (i : I), f i --> x := λ i, colimIn L i.

      Proposition isCoproduct_from_colims_unique
                  {y : C}
                  (gs : ∏ (i : I), f i --> y)
        : isaprop (∑ g, ∏ (i : I), fs i · g = gs i).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          use impred ; intro.
          apply homset_property.
        }
        use colimArrowUnique' ; cbn.
        intro i.
        exact (pr2 φ₁ i @ !(pr2 φ₂ i)).
      Qed.

      Definition isCoproduct_from_colims
        : isCoproduct I C f x fs.
      Proof.
        intros y gs.
        use iscontraprop1.
        - apply isCoproduct_from_colims_unique.
        - simple refine (_ ,, _).
          + use colimArrow.
            use make_cocone.
            * exact gs.
            * intros u v F.
              induction F.
          + intro i.
            exact (colimArrowCommutes L _ _ i).
      Defined.
    End CoproductsFromColim.

    Theorem Coproducts_from_Colims
      : Coproducts I C.
    Proof.
      intros f.
      exact (make_Coproduct _ _ _ _ _ (isCoproduct_from_colims f)).
    Defined.
  End CoproductsFromColims.
End CoproductGraph.
