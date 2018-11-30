(* ******************************************************************************* *)
(** * Internal adjunctions and adjoint equivalences
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws.

Local Open Scope bicategory_scope.
Local Open Scope cat.


Section Internal_Adjunction.
  Context {C : bicat}.

  (** ** Definitions of internal adjunctions *)

  (** *** Data & laws for left adjoints *)
  Definition left_adjoint_data {a b : C} (f : C⟦a,b⟧) : UU
    := ∑ (g : C⟦b,a⟧), (identity a ==> f · g)
                    × (g · f ==> identity b).

  Definition left_adjoint_right_adjoint {a b : C} {f : C⟦a,b⟧}
           (αd : left_adjoint_data f) : C⟦b,a⟧ := pr1 αd.

  Definition left_adjoint_unit {a b : C} {f : C⟦a,b⟧}
           (αd : left_adjoint_data f) :
    identity a ==> f · left_adjoint_right_adjoint αd
    := pr12 αd.

  Definition left_adjoint_counit {a b : C} {f : C⟦a,b⟧}
           (αd : left_adjoint_data f) :
    left_adjoint_right_adjoint αd · f ==> identity b
    := pr22 αd.

  Definition left_adjoint_axioms {a b : C} {f : C⟦a,b⟧}
             (αd : left_adjoint_data f) : UU
    := let g := left_adjoint_right_adjoint αd in
       let η := left_adjoint_unit αd in
       let ε := left_adjoint_counit αd in
         ( linvunitor f • (η ▹ f) • rassociator _ _ _ • (f ◃ ε) • runitor f = id2 f )
       × ( rinvunitor g • (g ◃ η) • lassociator _ _ _ • (ε ▹ g) • lunitor g = id2 g ).

  Definition left_adjoint {a b : C} (f : C⟦a,b⟧) : UU
    := ∑ (αd : left_adjoint_data f), left_adjoint_axioms αd.

  Coercion data_of_left_adjoint
           {a b : C}
           {f : C⟦a,b⟧}
           (α : left_adjoint f)
    : left_adjoint_data f
    := pr1 α.

  Coercion axioms_of_left_adjoint
           {a b : C}
           {f : C⟦a,b⟧}
           (α : left_adjoint f)
    : left_adjoint_axioms α
    := pr2 α.

  (** *** Laws for equivalences *)
  Definition left_equivalence_axioms
           {a b : C}
           {f : C⟦a,b⟧}
           (αd : left_adjoint_data f)
    : UU
    :=   is_invertible_2cell (left_adjoint_unit αd)
       × is_invertible_2cell (left_adjoint_counit αd).

  Definition left_equivalence
           {a b : C}
           (f : C⟦a,b⟧) : UU
    := ∑ (αd : left_adjoint_data f),
       left_equivalence_axioms αd.

  Coercion data_of_left_equivalence
           {a b : C}
           {f : C⟦a,b⟧}
           (αe : left_equivalence f)
    : left_adjoint_data f := pr1 αe.

  Coercion axioms_of_left_equivalence
           {a b : C}
           {f : C⟦a,b⟧}
           (αe : left_equivalence f)
    : left_equivalence_axioms αe := pr2 αe.

  Definition left_adjoint_equivalence
           {a b : C}
           (f : C⟦a,b⟧) : UU
    := ∑ (αd : left_adjoint_data f),
            left_adjoint_axioms αd
         ×  left_equivalence_axioms αd.

  (* the coercion to the axioms will be induced *)
  Coercion left_adjoint_of_left_adjoint_equivalence
           {a b : C}
           {f : C⟦a,b⟧}
           (αe : left_adjoint_equivalence f)
    : left_adjoint f := (pr1 αe,, pr12 αe).

  Coercion left_equivalence_of_left_adjoint_equivalence
           {a b : C}
           {f : C⟦a,b⟧}
           (αe : left_adjoint_equivalence f)
    : left_equivalence f := (pr1 αe,, pr22 αe).

  Definition left_equivalence_unit_iso
             {a b : C}
             {f : a --> b}
             (αe : left_equivalence f)
    : invertible_2cell (identity a) (f · left_adjoint_right_adjoint αe).
  Proof.
    refine (left_adjoint_unit αe,, _).
    apply αe.
  Defined.

  Definition left_equivalence_counit_iso
             {a b : C}
             {f : a --> b}
             (αe : left_equivalence f)
    : invertible_2cell (left_adjoint_right_adjoint αe · f) (identity b).
  Proof.
    refine (left_adjoint_counit αe,, _).
    apply αe.
  Defined.

  (** *** Packaged *)
  Definition adjunction (a b : C) : UU
    := ∑ f : C⟦a,b⟧, left_adjoint f.

  Coercion arrow_of_adjunction {a b : C}
           (f : adjunction a b)
    : a --> b
    := pr1 f.

  Coercion left_adjoint_of_adjunction {a b : C}
           (f : adjunction a b)
    : left_adjoint f
    := pr2 f.

  Definition adjoint_equivalence (a b : C) : UU
    := ∑ f : C⟦a,b⟧, left_adjoint_equivalence f.

  Coercion adjunction_of_adjoint_equivalence {a b : C}
           (f : adjoint_equivalence a b)
    : adjunction a b
    := (pr1 f,,left_adjoint_of_left_adjoint_equivalence (pr2 f)).

  Coercion left_adjoint_equivalence_of_adjoint_equivalence {a b : C}
           (f : adjoint_equivalence a b)
    : left_adjoint_equivalence f
    := pr2 f.

  Definition internal_right_adjoint {a b : C}
             (f : adjunction a b) : C⟦b,a⟧ :=
    left_adjoint_right_adjoint f.


  Definition internal_triangle1
             {a b : C} {f : C⟦a,b⟧}
             {adj : left_adjoint_data f}
             (L : left_adjoint_axioms adj)
    : linvunitor f • (left_adjoint_unit adj ▹ f) • rassociator _ _ _ • (f ◃ left_adjoint_counit adj) • runitor f = id2 f
    := pr1 L.

  Definition internal_triangle2
             {a b : C} {f : C⟦a,b⟧}
             {adj : left_adjoint_data f}
             (L : left_adjoint_axioms adj)
             (g := left_adjoint_right_adjoint adj)
    : rinvunitor g • (g ◃ left_adjoint_unit adj) • lassociator _ _ _ • (left_adjoint_counit adj ▹ g) • lunitor g = id2 g
    := pr2 L.

  Definition build_adjoint_equivalence
             {X Y : C}
             (f : C⟦X,Y⟧)
             (g : C⟦Y,X⟧)
             (η : identity X ==> g ∘ f)
             (ε : f ∘ g ==> identity Y)
             (triangle1 :  linvunitor f • (η ▹ f) • rassociator _ _ _ • (f ◃ ε) • runitor f = id2 f)
             (triangle2 : rinvunitor g • (g ◃ η) • lassociator _ _ _ • (ε ▹ g) • lunitor g = id2 g)
             (η_iso : is_invertible_2cell η)
             (ε_iso : is_invertible_2cell ε)
    : adjoint_equivalence X Y.
  Proof.
    refine (f ,, _).
    use tpair.
    - refine (g,, (η,, ε)).
    - cbn. repeat split; assumption.
  Defined.

End Internal_Adjunction.
