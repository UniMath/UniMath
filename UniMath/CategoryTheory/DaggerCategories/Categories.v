Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.

Local Open Scope cat.

Section DaggerCategories.

  Definition dagger_structure (C : category) : UU
    := ∏ x y : C, C⟦x,y⟧ → C⟦y,x⟧.

  Identity Coercion dagger_structure_to_family_of_morphisms
    : dagger_structure >-> Funclass.

  Lemma isaset_dagger_structure (C : category)
    : isaset (dagger_structure C).
  Proof.
    do 2 (apply impred_isaset ; intro).
    apply funspace_isaset.
    apply homset_property.
  Qed.

  Definition dagger_law_id {C : category} (dag : dagger_structure C)
    : UU
    := ∏ x : C, dag x x (identity x) = identity x.

  Definition dagger_law_comp {C : category} (dag : dagger_structure C)
    : UU
    := ∏ (x y z : C) (f: C⟦x,y⟧) (g : C⟦y,z⟧), dag x z (f · g) = dag y z g · dag x y f.

  Definition dagger_law_idemp {C : category} (dag : dagger_structure C)
    : UU
    := ∏ (x y : C) (f : C⟦x,y⟧), dag y x (dag x y f) = f.

  Definition dagger_laws {C : category} (dag : dagger_structure C)
    : UU := dagger_law_id dag × dagger_law_comp dag × dagger_law_idemp dag.

  Lemma isaprop_dagger_laws {C : category} (dag : dagger_structure C)
    : isaprop (dagger_laws dag).
  Proof.
    repeat (apply isapropdirprod)
    ; repeat (apply impred_isaprop ; intro)
    ; apply homset_property.
  Qed.

  Definition dagger (C : category)
    : UU
    := ∑ d : dagger_structure C, dagger_laws d.

  Definition dagger_to_struct {C : category} (dag : dagger C)
    : dagger_structure C := pr1 dag.
  Coercion dagger_to_struct : dagger >-> dagger_structure.

  Definition dagger_to_laws {C : category} (dag : dagger C)
    : dagger_laws dag := pr2 dag.

  Definition dagger_to_law_id
             {C : category} (dag : dagger C)
    : dagger_law_id dag := pr1 (dagger_to_laws dag).

  Definition dagger_to_law_comp
             {C : category} (dag : dagger C)
    : dagger_law_comp dag := pr12 (dagger_to_laws dag).

  Definition dagger_to_law_idemp
             {C : category} (dag : dagger C)
    : dagger_law_idemp dag := pr22 (dagger_to_laws dag).

  Lemma isaset_dagger (C : category)
    : isaset (dagger C).
  Proof.
    apply isaset_total2.
    - apply isaset_dagger_structure.
    - intro ; apply isasetaprop ; apply isaprop_dagger_laws.
  Qed.

  Lemma dagger_equality
        {C : category} (dag1 dag2 : dagger C)
    : dagger_to_struct dag1 = dagger_to_struct dag2
      -> dag1 = dag2.
  Proof.
    intro p.
    apply (total2_paths_f p).
    apply isaprop_dagger_laws.
  Qed.

  Definition dagger_injective
             {C : category} (dag : dagger C)
             {x y : C}
             (f g : C⟦x,y⟧)
    : dag _ _ f = dag _ _ g -> f = g.
  Proof.
    intro p.
    refine (_ @ maponpaths (dag y x) p @ _).
    - apply pathsinv0, dagger_to_law_idemp.
    - apply dagger_to_law_idemp.
  Qed.

  Definition make_dagger_laws
             {C : category} {d : dagger_structure C}
             (lid : dagger_law_id d)
             (lcomp : dagger_law_comp d)
             (lidemp : dagger_law_idemp d)
    : dagger_laws d
    := lid ,, lcomp ,, lidemp.

End DaggerCategories.
