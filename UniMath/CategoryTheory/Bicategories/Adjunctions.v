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

  (* Definition internal_adjunction_over {a b : C} (f : C⟦a,b⟧) (g : C⟦b,a⟧) *)
  (*   : UU *)
  (*   :=  *)

  (* Definition internal_adjunction_data (a b : C) *)
  (*   : UU *)
  (*   := ∑ (f : C⟦a,b⟧) (g : C⟦b,a⟧), internal_adjunction_over f g. *)

  (* Definition internal_left_adjoint {a b : C} (j : internal_adjunction_data a b) *)
  (*   : C⟦a,b⟧ *)
  (*   := pr1 j. *)

  (* Definition internal_right_adjoint {a b : C} (j : internal_adjunction_data a b) *)
  (*   : C⟦b,a⟧ *)
  (*   := pr1 (pr2 j). *)

  (* Coercion internal_adjunction_over_from_data {a b : C} (j : internal_adjunction_data a b) *)
  (*   : internal_adjunction_over (internal_left_adjoint j) (internal_right_adjoint j) *)
  (*   := pr2 (pr2 j). *)

  (* Coercion internal_adjunction_data_from_over {a b : C} *)
  (*          {f : C⟦a, b⟧} {g : C⟦b, a⟧} (H : internal_adjunction_over f g) *)
  (*   : internal_adjunction_data a b *)
  (*   := (f ,, g ,, H). *)

  (* Definition internal_unit {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧} *)
  (*            (adj : internal_adjunction_over f g) *)
  (*   : identity a ==> f · g *)
  (*   := pr1 adj. *)

  (* Definition internal_counit {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧} *)
  (*            (adj : internal_adjunction_over f g) *)
  (*   : g · f ==> identity b *)
  (*   := pr2 adj. *)

  (* Definition is_internal_adjunction {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧} *)
  (*            (adj : internal_adjunction_over f g) *)
  (*   : UU *)
  (*   := let (η,ε) := adj in *)
  (*        ( linvunitor f • (η ▹ f) • rassociator _ _ _ • (f ◃ ε) • runitor f = id2 f ) *)
  (*      × ( rinvunitor g • (g ◃ η) • lassociator _ _ _ • (ε ▹ g) • lunitor g = id2 g ). *)

  (* Definition internal_adjunction (a b : C) := *)
  (*   ∑ (j : internal_adjunction_data a b), is_internal_adjunction j. *)

  (* Coercion internal_adjunction_data_from_internal_adjunction {a b : C} *)
  (*          (j : internal_adjunction a b) *)
  (*   : internal_adjunction_data a b *)
  (*   := pr1 j. *)

  (* Coercion is_internal_adjunction_from_internal_adjunction {a b : C} *)
  (*          (j : internal_adjunction a b) *)
  (*   : is_internal_adjunction j *)
  (*   := pr2 j. *)

  (* (** Left adjoints *) *)
  (* Definition internal_left_adjoint_data {a b : C} (f : C⟦a,b⟧) : UU *)
  (*   := ∑ (g : C⟦b,a⟧), internal_adjunction_over f g. *)

  (* Coercion internal_adjunction_over_from_left_adjoint *)
  (*     {a b : C} {f : C⟦a,b⟧} *)
  (*     (f_d : internal_left_adjoint_data f) : *)
  (*     internal_adjunction_over f (pr1 f_d) *)
  (*   := pr2 f_d. *)

  (* Definition is_internal_left_adjoint {a b : C} (f : C⟦a,b⟧) *)
  (*   : UU *)
  (*   := ∑ (f_d : internal_left_adjoint_data f), *)
  (*         is_internal_adjunction f_d. *)

  (* Coercion internal_adjunction_from_left_adjoint *)
  (*     {a b : C} {f : C⟦a,b⟧} *)
  (*     (L : is_internal_left_adjoint f) *)
  (*   : internal_adjunction a b. *)
  (* Proof. *)
  (*   refine (internal_adjunction_data_from_over _,, _). *)
  (*   apply L. *)
  (* Defined. *)

  (* Coercion is_internal_left_adjoint_internal_left_adjoint_data *)
  (*          {a b : C} {f : C⟦a,b⟧} *)
  (*          (j : is_internal_left_adjoint f) *)
  (*   : internal_left_adjoint_data f := pr1 j. *)

  (* (** Internal adjoint equivalences *) *)
  (* Definition is_internal_equivalence_over {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧} *)
  (*            (j : internal_adjunction_over f g) *)
  (*            (η := internal_unit j) *)
  (*            (ε := internal_counit j) *)
  (*   : UU *)
  (*   := is_invertible_2cell η × is_invertible_2cell ε. *)

  (* Definition is_internal_equivalence {a b : C} (j : internal_adjunction_data a b) *)
  (*   : UU *)
  (*   := is_internal_equivalence_over j. *)

  (* Definition internal_equivalence (a b : C) *)
  (*   : UU *)
  (*   := ∑ (j : internal_adjunction_data a b), is_internal_equivalence j. *)

  (* Definition build_equiv *)
  (*            {X Y : C} *)
  (*            (f : C⟦X,Y⟧) *)
  (*            (g : C⟦Y,X⟧) *)
  (*            (η : identity X ==> g ∘ f) *)
  (*            (ε : f ∘ g ==> identity Y) *)
  (*            (η_iso : is_invertible_2cell η) *)
  (*            (ε_iso : is_invertible_2cell ε) *)
  (*   : adjoint_equivalence X Y. *)
  (* Proof. *)
  (*   refine (f ,, _). *)
  (*   use tpair. *)
  (*   - refine (g,, (η,, ε)). *)
  (*   - cbn. *)
  (*     split. *)
  (*     + exact η_iso. *)
  (* Defined. *)

  (* Coercion internal_adjunction_data_from_internal_equivalence {a b : C} *)
  (*          (j : internal_equivalence a b) *)
  (*   : internal_adjunction_data a b *)
  (*   := pr1 j. *)

  (* Coercion is_internal_equivalence_from_internal_equivalence {a b : C} *)
  (*          (j : internal_equivalence a b) *)
  (*   : is_internal_equivalence j *)
  (*   := pr2 j. *)

  (* Definition internal_unit_iso {a b : C} (j : internal_equivalence a b) *)
  (*   : invertible_2cell (identity a) (internal_left_adjoint j · internal_right_adjoint j) *)
  (*   := internal_unit j,, pr1 (pr2 j). *)

  (* Definition internal_counit_iso {a b : C} (j : internal_equivalence a b) *)
  (*   : invertible_2cell (internal_right_adjoint j · internal_left_adjoint j) (identity b) *)
  (*   := internal_counit j,, pr2 (pr2 j). *)

  (* Definition is_internal_left_adjoint_internal_equivalence {a b : C} (f : C⟦a,b⟧) *)
  (*   : UU *)
  (*   := ∑ (g : C⟦b,a⟧) (j : internal_adjunction_over f g), *)
  (*        is_internal_equivalence_over j *)
  (*      × is_internal_adjunction j. *)

  (* Coercion is_internal_equivalence_over_from_is_foo {a b : C} {f : C⟦a,b⟧} *)
  (*          (H : is_internal_left_adjoint_internal_equivalence f) *)
  (*   : is_internal_equivalence_over _ *)
  (*   := pr1 (pr2 (pr2 H)). *)

  (* Coercion is_internal_adjunction_over_from_is_foo {a b : C} {f : C⟦a,b⟧} *)
  (*          (H : is_internal_left_adjoint_internal_equivalence f) *)
  (*   : is_internal_adjunction _ *)
  (*   := pr2 (pr2 (pr2 H)). *)

  (* Coercion internal_adjunction_over_from_is_foo {a b : C} {f : C⟦a,b⟧} *)
  (*          (H : is_internal_left_adjoint_internal_equivalence f) *)
  (*   : internal_adjunction_over _ _ *)
  (*   := pr1 (pr2 H). *)

  (* Definition internal_adjoint_equivalence (a b : C) : UU *)
  (*   := ∑ f : C⟦a,b⟧, is_internal_left_adjoint_internal_equivalence f. *)

  (* Coercion internal_adjunction_data_from_internal_adjoint_equivalence *)
  (*            {a b : C} *)
  (*            (f : internal_adjoint_equivalence a b) *)
  (*   : internal_adjunction_data a b *)
  (*   := pr2 f. *)

  (* Coercion internal_equivalence_from_internal_adjoint_equivalence *)
  (*          {a b : C} *)
  (*          (f : internal_adjoint_equivalence a b) *)
  (*   : internal_equivalence a b. *)
  (* Proof. *)
  (*   use tpair. *)
  (*   - apply internal_adjunction_data_from_internal_adjoint_equivalence. *)
  (*     apply f. *)
  (*   - split. *)
  (*     * apply (pr2 (pr2 (pr2 f))). *)
  (*     * apply (pr2 (pr2 (pr2 f))). *)
  (* Defined. *)

  (* Coercion internal_adjunction_from_internal_adjoint_equivalence *)
  (*          {a b : C} *)
  (*          (f : internal_adjoint_equivalence a b) *)
  (*   : internal_adjunction a b. *)
  (* Proof. *)
  (*   use tpair. *)
  (*   - apply internal_adjunction_data_from_internal_adjoint_equivalence. *)
  (*     apply f. *)
  (*   - cbn. *)
  (*     exact (pr2 (pr2 (pr2 (pr2 f)))). *)
  (* Defined. *)

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
