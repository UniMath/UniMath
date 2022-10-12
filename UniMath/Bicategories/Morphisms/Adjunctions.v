(* ******************************************************************************* *)
(** * Internal adjunctions and adjoint equivalences
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Section Internal_Adjunction.
  Context {B : bicat}.

  (** ** Definitions of internal adjunctions *)

  (** *** Data & laws for left adjoints *)
  Definition left_adjoint_data
             {a b : B}
             (f : a --> b)
    : UU
    := ∑ (g : b --> a),
       identity a ==> f · g
       ×
       g · f ==> identity b.

  Definition left_adjoint_right_adjoint
             {a b : B}
             {f : a --> b}
             (αd : left_adjoint_data f)
    : b --> a
    := pr1 αd.

  Definition left_adjoint_unit
             {a b : B}
             {f : a --> b}
             (αd : left_adjoint_data f)
    : identity a ==> f · left_adjoint_right_adjoint αd
    := pr12 αd.

  Definition left_adjoint_counit
             {a b : B}
             {f : a --> b}
             (αd : left_adjoint_data f)
    : left_adjoint_right_adjoint αd · f ==> identity b
    := pr22 αd.

  Definition left_adjoint_axioms
             {a b : B}
             {f : a --> b}
             (αd : left_adjoint_data f)
    : UU
    := let g := left_adjoint_right_adjoint αd in
       let η := left_adjoint_unit αd in
       let ε := left_adjoint_counit αd in
       linvunitor f • (η ▹ f) • rassociator _ _ _ • (f ◃ ε) • runitor f = id2 f
       ×
       rinvunitor g • (g ◃ η) • lassociator _ _ _ • (ε ▹ g) • lunitor g = id2 g.

  Definition left_adjoint
             {a b : B}
             (f : a --> b)
    : UU
    := ∑ (αd : left_adjoint_data f), left_adjoint_axioms αd.

  Coercion data_of_left_adjoint
           {a b : B}
           {f : a --> b}
           (α : left_adjoint f)
    : left_adjoint_data f
    := pr1 α.

  Coercion axioms_of_left_adjoint
           {a b : B}
           {f : a --> b}
           (α : left_adjoint f)
    : left_adjoint_axioms α
    := pr2 α.

  (** Data and laws for right adjoints *)
  Definition internal_right_adj_data
             {a b : B}
             (g : b --> a)
    : UU
    := ∑ (f : a --> b),
       identity a ==> f · g
       ×
       g · f ==> identity b.

  Definition internal_right_adj_left_adjoint
             {a b : B}
             {g : b --> a}
             (αd : internal_right_adj_data g)
    : a --> b
    := pr1 αd.

  Definition internal_right_adj_unit
             {a b : B}
             {g : b --> a}
             (αd : internal_right_adj_data g)
    : identity a ==> internal_right_adj_left_adjoint αd · g
    := pr12 αd.

  Definition internal_right_adj_counit
             {a b : B}
             {g : b --> a}
             (αd : internal_right_adj_data g)
    : g · internal_right_adj_left_adjoint αd ==> identity b
    := pr22 αd.

  Definition internal_right_adj_axioms
             {a b : B}
             {g : b --> a}
             (αd : internal_right_adj_data g)
    : UU
    := let f := internal_right_adj_left_adjoint αd in
       let η := internal_right_adj_unit αd in
       let ε := internal_right_adj_counit αd in
       linvunitor f • (η ▹ f) • rassociator _ _ _ • (f ◃ ε) • runitor f = id2 f
       ×
       rinvunitor g • (g ◃ η) • lassociator _ _ _ • (ε ▹ g) • lunitor g = id2 g.

  Definition internal_right_adj
             {a b : B}
             (g : b --> a)
    : UU
    := ∑ (αd : internal_right_adj_data g), internal_right_adj_axioms αd.

  Coercion data_of_internal_right_adj
           {a b : B}
           {g : b --> a}
           (α : internal_right_adj g)
    : internal_right_adj_data g
    := pr1 α.

  Coercion axioms_of_internal_right_adj
           {a b : B}
           {g : b --> a}
           (α : internal_right_adj g)
    : internal_right_adj_axioms α
    := pr2 α.

  (** *** Laws for equivalences *)
  Definition left_equivalence_axioms
             {a b : B}
             {f : a --> b}
             (αd : left_adjoint_data f)
    : UU
    := is_invertible_2cell (left_adjoint_unit αd)
       ×
       is_invertible_2cell (left_adjoint_counit αd).

  Definition left_equivalence
             {a b : B}
             (f : a --> b)
    :UU
    := ∑ (αd : left_adjoint_data f),
       left_equivalence_axioms αd.

  Coercion data_of_left_equivalence
           {a b : B}
           {f : a --> b}
           (αe : left_equivalence f)
    : left_adjoint_data f
    := pr1 αe.

  Coercion axioms_of_left_equivalence
           {a b : B}
           {f : a --> b}
           (αe : left_equivalence f)
    : left_equivalence_axioms αe
    := pr2 αe.

  Definition left_adjoint_equivalence
             {a b : B}
             (f : a --> b)
    : UU
    := ∑ (αd : left_adjoint_data f),
       left_adjoint_axioms αd
       ×
       left_equivalence_axioms αd.

  (* the coercion to the axioms will be induced *)
  Coercion left_adjoint_of_left_adjoint_equivalence
           {a b : B}
           {f : a --> b}
           (αe : left_adjoint_equivalence f)
    : left_adjoint f
    := (pr1 αe,, pr12 αe).

  Coercion left_equivalence_of_left_adjoint_equivalence
           {a b : B}
           {f : a --> b}
           (αe : left_adjoint_equivalence f)
    : left_equivalence f
    := (pr1 αe,, pr22 αe).

  Definition left_equivalence_unit_iso
             {a b : B}
             {f : a --> b}
             (αe : left_equivalence f)
    : invertible_2cell (identity a) (f · left_adjoint_right_adjoint αe).
  Proof.
    refine (left_adjoint_unit αe,, _).
    apply αe.
  Defined.

  Definition left_equivalence_counit_iso
             {a b : B}
             {f : a --> b}
             (αe : left_equivalence f)
    : invertible_2cell (left_adjoint_right_adjoint αe · f) (identity b).
  Proof.
    refine (left_adjoint_counit αe,, _).
    apply αe.
  Defined.

  (** *** Packaged *)
  Definition adjunction (a b : B) : UU
    := ∑ (f : a --> b), left_adjoint f.

  Coercion arrow_of_adjunction
           {a b : B}
           (f : adjunction a b)
    : a --> b
    := pr1 f.

  Coercion left_adjoint_of_adjunction
           {a b : B}
           (f : adjunction a b)
    : left_adjoint f
    := pr2 f.

  Definition adjoint_equivalence
             (a b : B)
    : UU
    := ∑ (f : a --> b), left_adjoint_equivalence f.

  Coercion adjunction_of_adjoint_equivalence
           {a b : B}
           (f : adjoint_equivalence a b)
    : adjunction a b
    := (pr1 f,,left_adjoint_of_left_adjoint_equivalence (pr2 f)).

  Coercion left_adjoint_equivalence_of_adjoint_equivalence
           {a b : B}
           (f : adjoint_equivalence a b)
    : left_adjoint_equivalence f
    := pr2 f.

  Definition internal_right_adjoint
             {a b : B}
             (f : adjunction a b)
    : b --> a
    := left_adjoint_right_adjoint f.

  Definition internal_triangle1
             {a b : B}
             {f : a --> b}
             {adj : left_adjoint_data f}
             (L : left_adjoint_axioms adj)
    : linvunitor f
      • (left_adjoint_unit adj ▹ f)
      • rassociator _ _ _
      • (f ◃ left_adjoint_counit adj)
      • runitor f
      =
      id2 f
    := pr1 L.

  Definition internal_triangle2
             {a b : B}
             {f : a --> b}
             {adj : left_adjoint_data f}
             (L : left_adjoint_axioms adj)
             (g := left_adjoint_right_adjoint adj)
    : rinvunitor g
      • (g ◃ left_adjoint_unit adj)
      • lassociator _ _ _
      • (left_adjoint_counit adj ▹ g)
      • lunitor g
      =
      id2 g
    := pr2 L.

  Definition make_adjoint_equivalence
             {a b : B}
             (f : a --> b)
             (g : b --> a)
             (η : identity _ ==> g ∘ f)
             (ε : f ∘ g ==> identity _)
             (triangle1 : linvunitor f
                          • (η ▹ f)
                          • rassociator _ _ _
                          • (f ◃ ε)
                          • runitor f
                          =
                          id2 f)
             (triangle2 : rinvunitor g
                          • (g ◃ η)
                          • lassociator _ _ _
                          • (ε ▹ g)
                          • lunitor g
                          =
                          id2 g)
             (η_iso : is_invertible_2cell η)
             (ε_iso : is_invertible_2cell ε)
    : adjoint_equivalence a b
    := f ,, ((g ,, (η ,, ε)) ,, ((triangle1 ,, triangle2) ,, (η_iso ,, ε_iso))).
End Internal_Adjunction.
