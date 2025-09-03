(**

 Codes for types in the empty context (for categories)

 Our goal is to express that some universe in a category is closed under type formers,
 and in this file we consider the following: unit types, empty types, natural numbers,
 and subobject classifiers. Specifically, we define the following:
 - when a universe contains codes for these types
 - when a functor preserves those codes
 We also develop the main infrastructure necessary to construct univalent displayed
 bicategories representing that the universe is closed under the aforementioned type
 formers.

 There are several ideas in the development. The first important observation is that
 the aforementioned types (unit, empty, natural numbers, subobject classifier) are
 essentially determined by a type in the empty context. From the point of view of
 type theory, we can see it as follows: we have a type `𝟙` (unit type) in the empty
 context, and the unit type in any other context is obtained by weakening. For this
 reason, it suffices to add a code for the desired type only in the empty context
 meaning that we do not need to add coherence conditions.

 To express that a universe contains some type, we use another idea. Specifically,
 we say that there is a code (i.e., morphism `𝟙 --> u` from the terminal object to
 the universe type) whose associated type is isomorphic to the given type. This
 means that we assume that the category has enough structure (e.g., we assume that
 the category has an initial objects to express that the universe has codes for
 the empty type).

 Finally, we give a uniform treatment of all these type formers. Specifically, we
 give a general definition that says when a universe contains a code for a given
 type. Note that this treatment is only for a fixed type in the empty context,
 because for other type formers (like ∏-types) one would need coherence conditions.

 Contents
 1. Codes for a type
 2. Examples for codes
 2.1. The terminal object
 2.2. The initial object
 2.3. Parameterized natural numbers object
 2.4. Subobject classifier
 3. Preservation by functors
 4. Examples for preservation
 4.1. Preservation of the code for the terminal object
 4.2. Preservation of the code for the initial object
 4.3. Preservation of the code for the parameterized natural numbers object
 4.4. Preservation of the code for the subobject classifier
 5. Preservation by identity and composition
 6. Instantiation to the examples
 6.1. Preservation of the code for the terminal object
 6.2. Preservation of the code for the initial object
 6.3. Preservation of the code for the parameterized natural numbers object
 6.4. Preservation of the code for the subobject classifier
 7. Univalence condition
 7.1. Univalence condition for the terminal object
 7.2. Univalence condition for the initial object
 7.3. Univalence condition for the parameterized natural numbers object
 7.4. Univalence condition for the subobject classifier

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.

Local Open Scope cat.

Section TypesInCatUniv.
  Context {C : univ_cat_with_finlim_universe}.

  Let el : cat_stable_el_map_coherent C := univ_cat_cat_stable_el_map C.

  Local Notation "𝟙" := (terminal_univ_cat_with_finlim C).

  (** * 1. Codes for a type *)
  Definition type_in_cat_univ
             (A : C)
    : UU
    := ∑ (a : 𝟙 --> univ_cat_universe C),
       z_iso (cat_el_map_el el a) A.

  Proposition isaset_type_in_cat_univ
              (A : C)
    : isaset (type_in_cat_univ A).
  Proof.
    use isaset_total2.
    - apply homset_property.
    - intro.
      apply isaset_z_iso.
  Qed.

  Definition make_type_in_cat_univ
             {A : C}
             (a : 𝟙 --> univ_cat_universe C)
             (f : z_iso (cat_el_map_el el a) A)
    : type_in_cat_univ A
    := a ,, f.

  Definition type_in_cat_univ_code
             {A : C}
             (a : type_in_cat_univ A)
    : 𝟙 --> univ_cat_universe C
    := pr1 a.

  Definition type_in_cat_univ_z_iso
             {A : C}
             (a : type_in_cat_univ A)
    : z_iso (cat_el_map_el el (type_in_cat_univ_code a)) A
    := pr2 a.

  Proposition type_in_cat_univ_eq
              {A : C}
              {a₁ a₂ : type_in_cat_univ A}
              (p : type_in_cat_univ_code a₁ = type_in_cat_univ_code a₂)
              (q : cat_el_map_el_eq el p · type_in_cat_univ_z_iso a₂
                   =
                   type_in_cat_univ_z_iso a₁)
    : a₁ = a₂.
  Proof.
    induction a₁ as [ a₁ f₁ ].
    induction a₂ as [ a₂ f₂ ].
    cbn in *.
    induction p.
    apply maponpaths.
    use z_iso_eq.
    refine (!q @ _) ; cbn.
    apply id_left.
  Qed.

  (** * 2. Examples for codes *)

  (** ** 2.1. The terminal object *)
  Definition terminal_in_cat_univ
    : UU
    := type_in_cat_univ 𝟙.

  Proposition terminal_in_cat_univ_eq
              {c₁ c₂ : terminal_in_cat_univ}
              (p : type_in_cat_univ_code c₁ = type_in_cat_univ_code c₂)
    : c₁ = c₂.
  Proof.
    use type_in_cat_univ_eq.
    - exact p.
    - apply TerminalArrowEq.
  Qed.

  (** ** 2.2. The initial object *)
  Definition initial_in_cat_univ
             (I : Initial C)
    : UU
    := type_in_cat_univ I.

  Proposition initial_in_cat_univ_eq
              {I : Initial C}
              {c₁ c₂ : initial_in_cat_univ I}
              (p : type_in_cat_univ_code c₁ = type_in_cat_univ_code c₂)
    : c₁ = c₂.
  Proof.
    use type_in_cat_univ_eq.
    - exact p.
    - refine (maponpaths
                pr1
                (z_iso_eq_inv
                   (z_iso_comp (cat_el_map_el_eq el p) (type_in_cat_univ_z_iso c₂))
                   (type_in_cat_univ_z_iso c₁)
                   _)).
      apply InitialArrowEq.
  Qed.

  (** ** 2.3. Parameterized natural numbers object *)
  Definition pnno_in_cat_univ
             (N : parameterized_NNO 𝟙 (binproducts_univ_cat_with_finlim C))
    : UU
    := type_in_cat_univ N.

  (** ** 2.4. Subobject classifier*)
  Definition subobject_classifier_in_cat_univ
             (Ω : subobject_classifier 𝟙)
    : UU
    := type_in_cat_univ Ω.
End TypesInCatUniv.

Arguments type_in_cat_univ_code {C A} a.
Arguments type_in_cat_univ_z_iso {C A} a.
Arguments terminal_in_cat_univ C : clear implicits.

Section FunctorPreservesTypes.
  Context {C₁ C₂ : univ_cat_with_finlim_universe}
          (F : functor_finlim_universe C₁ C₂).

  Let el₁ : cat_stable_el_map_coherent C₁ := univ_cat_cat_stable_el_map C₁.
  Let el₂ : cat_stable_el_map_coherent C₂ := univ_cat_cat_stable_el_map C₂.

  Let Fel : functor_preserves_el
              (univ_cat_cat_stable_el_map C₁)
              (univ_cat_cat_stable_el_map C₂)
              F
    := functor_finlim_universe_preserves_el F.

  (** * 3. Preservation by functors *)
  Definition functor_preserves_type_in_cat_univ_code
             {A₁ : C₁}
             {A₂ : C₂}
             (FA : z_iso (F A₁) A₂)
             (a₁ : type_in_cat_univ A₁)
             (a₂ : type_in_cat_univ A₂)
    : UU
    := #F(type_in_cat_univ_code a₁) · functor_on_universe F
       =
       TerminalArrow _ _ · type_in_cat_univ_code a₂.

  Definition functor_preserves_type_in_cat_univ_code_z_iso
             {A₁ : C₁}
             {A₂ : C₂}
             {FA : z_iso (F A₁) A₂}
             {a₁ : type_in_cat_univ A₁}
             {a₂ : type_in_cat_univ A₂}
             (Fc : functor_preserves_type_in_cat_univ_code FA a₁ a₂)
    : UU
    := #F(type_in_cat_univ_z_iso a₁) · FA
       =
       functor_el_map_iso Fel (type_in_cat_univ_code a₁)
       · (cat_el_map_el_eq el₂ Fc)
       · cat_el_map_pb_mor _ _ _
       · type_in_cat_univ_z_iso a₂.

  Definition functor_preserves_type_in_cat_univ
             {A₁ : C₁}
             {A₂ : C₂}
             (FA : z_iso (F A₁) A₂)
             (a₁ : type_in_cat_univ A₁)
             (a₂ : type_in_cat_univ A₂)
    : UU
    := ∑ (p : functor_preserves_type_in_cat_univ_code FA a₁ a₂),
       functor_preserves_type_in_cat_univ_code_z_iso p.

  Proposition isaprop_functor_preserves_type_in_cat_univ
              {A₁ : C₁}
              {A₂ : C₂}
              (FA : z_iso (F A₁) A₂)
              (a₁ : type_in_cat_univ A₁)
              (a₂ : type_in_cat_univ A₂)
    : isaprop (functor_preserves_type_in_cat_univ FA a₁ a₂).
  Proof.
    use isaproptotal2.
    - intro.
      apply homset_property.
    - intros.
      apply homset_property.
  Qed.

  Definition functor_preserves_type_in_cat_univ_z_iso_eq
             {A₁ : C₁}
             {A₂ : C₂}
             {FA FA' : z_iso (F A₁) A₂}
             (p : FA = FA')
             {a₁ : type_in_cat_univ A₁}
             {a₂ : type_in_cat_univ A₂}
             (HF : functor_preserves_type_in_cat_univ FA a₁ a₂)
    : functor_preserves_type_in_cat_univ FA' a₁ a₂.
  Proof.
    induction p.
    exact HF.
  Qed.

  Definition make_functor_preserves_type_in_cat_univ
             {A₁ : C₁}
             {A₂ : C₂}
             {FA : z_iso (F A₁) A₂}
             {a₁ : type_in_cat_univ A₁}
             {a₂ : type_in_cat_univ A₂}
             (p : functor_preserves_type_in_cat_univ_code FA a₁ a₂)
             (q : functor_preserves_type_in_cat_univ_code_z_iso p)
    : functor_preserves_type_in_cat_univ FA a₁ a₂
    := p ,, q.

  Proposition functor_preserves_type_in_cat_univ_code_eq
              {A₁ : C₁}
              {A₂ : C₂}
              {FA : z_iso (F A₁) A₂}
              {a₁ : type_in_cat_univ A₁}
              {a₂ : type_in_cat_univ A₂}
              (Fc : functor_preserves_type_in_cat_univ FA a₁ a₂)
    : #F(type_in_cat_univ_code a₁) · functor_on_universe F
      =
      TerminalArrow _ _ · type_in_cat_univ_code a₂.
  Proof.
    exact (pr1 Fc).
  Defined.

  Proposition functor_preserves_type_in_cat_univ_code_z_iso_eq
              {A₁ : C₁}
              {A₂ : C₂}
              {FA : z_iso (F A₁) A₂}
              {a₁ : type_in_cat_univ A₁}
              {a₂ : type_in_cat_univ A₂}
              (Fc : functor_preserves_type_in_cat_univ FA a₁ a₂)
    : #F(type_in_cat_univ_z_iso a₁) · FA
      =
      functor_el_map_iso Fel (type_in_cat_univ_code a₁)
      · (cat_el_map_el_eq el₂ (functor_preserves_type_in_cat_univ_code_eq Fc))
      · cat_el_map_pb_mor _ _ _
      · type_in_cat_univ_z_iso a₂.
  Proof.
    exact (pr2 Fc).
  Defined.
End FunctorPreservesTypes.

Arguments functor_preserves_type_in_cat_univ_code {C₁ C₂} F {A₁ A₂} FA a₁ a₂ /.
Arguments functor_preserves_type_in_cat_univ_code_z_iso /.

(** * 4. Examples for preservation *)

(** ** 4.1. Preservation of the code for the terminal object *)
Definition functor_preserves_terminal_in_cat_univ
           {C₁ C₂ : univ_cat_with_finlim_universe}
           (c₁ : terminal_in_cat_univ C₁)
           (c₂ : terminal_in_cat_univ C₂)
           (F : functor_finlim_universe C₁ C₂)
  : UU
  := functor_preserves_type_in_cat_univ
       F
       (preserves_terminal_to_z_iso
          F (functor_finlim_preserves_terminal F)
          _ _)
       c₁
       c₂.

Proposition make_functor_preserves_terminal_in_cat_univ
            {C₁ C₂ : univ_cat_with_finlim_universe}
            {c₁ : terminal_in_cat_univ C₁}
            {c₂ : terminal_in_cat_univ C₂}
            {F : functor_finlim_universe C₁ C₂}
            (p : #F(type_in_cat_univ_code c₁) · functor_on_universe F
                 =
                 TerminalArrow _ _ · type_in_cat_univ_code c₂)
  : functor_preserves_terminal_in_cat_univ c₁ c₂ F.
Proof.
  use make_functor_preserves_type_in_cat_univ.
  - exact p.
  - apply TerminalArrowEq.
Qed.

(** ** 4.2. Preservation of the code for the initial object *)
Definition functor_preserves_initial_in_cat_univ
           {C₁ C₂ : univ_cat_with_finlim_universe}
           {I₁ : Initial C₁}
           {I₂ : Initial C₂}
           (c₁ : initial_in_cat_univ I₁)
           (c₂ : initial_in_cat_univ I₂)
           (F : functor_finlim_universe C₁ C₂)
           (FI : preserves_initial F)
  : UU
  := functor_preserves_type_in_cat_univ
       F
       (preserves_initial_to_z_iso
          F FI
          _ _)
       c₁
       c₂.

Proposition make_functor_preserves_initial_in_cat_univ
            {C₁ C₂ : univ_cat_with_finlim_universe}
            {I₁ : Initial C₁}
            {I₂ : Initial C₂}
            {c₁ : initial_in_cat_univ I₁}
            {c₂ : initial_in_cat_univ I₂}
            {F : functor_finlim_universe C₁ C₂}
            {FI : preserves_initial F}
            (p : #F(type_in_cat_univ_code c₁) · functor_on_universe F
                 =
                 TerminalArrow _ _ · type_in_cat_univ_code c₂)
  : functor_preserves_initial_in_cat_univ c₁ c₂ F FI.
Proof.
  use make_functor_preserves_type_in_cat_univ.
  - exact p.
  - simpl.
    use (cancel_z_iso' (z_iso_inv (functor_on_z_iso F (type_in_cat_univ_z_iso c₁)))).
    apply (InitialArrowEq (O := preserves_initial_to_initial _ FI I₁)).
Qed.

Proposition functor_preserves_initial_in_cat_univ_eq
            {C₁ C₂ : univ_cat_with_finlim_universe}
            {I₁ : Initial C₁}
            {I₂ : Initial C₂}
            (c₁ : initial_in_cat_univ I₁)
            (c₂ : initial_in_cat_univ I₂)
            {F F' : functor_finlim_universe C₁ C₂}
            (p : F = F')
            (FI : preserves_initial F)
            (FI' : preserves_initial F')
            (HF : functor_preserves_initial_in_cat_univ c₁ c₂ F FI)
  : functor_preserves_initial_in_cat_univ c₁ c₂ F' FI'.
Proof.
  induction p.
  assert (FI = FI') as ->.
  {
    apply isaprop_preserves_initial.
  }
  exact HF.
Qed.

(** ** 4.3. Preservation of the code for the parameterized natural numbers object *)
Definition functor_preserves_pnno_in_cat_univ
           {C₁ C₂ : univ_cat_with_finlim_universe}
           {N₁ : parameterized_NNO
                   (terminal_univ_cat_with_finlim C₁)
                   (binproducts_univ_cat_with_finlim C₁)}
           {N₂ : parameterized_NNO
                   (terminal_univ_cat_with_finlim C₂)
                   (binproducts_univ_cat_with_finlim C₂)}
           (c₁ : pnno_in_cat_univ N₁)
           (c₂ : pnno_in_cat_univ N₂)
           (F : functor_finlim_universe C₁ C₂)
           (HF : preserves_parameterized_NNO
                   N₁ N₂
                   F
                   (functor_finlim_preserves_terminal F))
  : UU
  := functor_preserves_type_in_cat_univ
       F
       (preserves_parameterized_NNO_z_iso HF)
       c₁
       c₂.

Proposition make_functor_preserves_pnno_in_cat_univ
            {C₁ C₂ : univ_cat_with_finlim_universe}
            {N₁ : parameterized_NNO
                    (terminal_univ_cat_with_finlim C₁)
                    (binproducts_univ_cat_with_finlim C₁)}
            {N₂ : parameterized_NNO
                    (terminal_univ_cat_with_finlim C₂)
                    (binproducts_univ_cat_with_finlim C₂)}
            {c₁ : pnno_in_cat_univ N₁}
            {c₂ : pnno_in_cat_univ N₂}
            {F : functor_finlim_universe C₁ C₂}
            {HF : preserves_parameterized_NNO
                    N₁ N₂
                    F
                    (functor_finlim_preserves_terminal F)}
            (p : #F(type_in_cat_univ_code c₁) · functor_on_universe F
                 =
                 TerminalArrow _ _ · type_in_cat_univ_code c₂)
            (q : #F (type_in_cat_univ_z_iso c₁)
                 =
                 functor_el_map_iso
                   (functor_finlim_universe_preserves_el F)
                   (type_in_cat_univ_code c₁)
                 · cat_el_map_el_eq (univ_cat_cat_stable_el_map C₂) p
                 · cat_el_map_pb_mor
                     (univ_cat_cat_stable_el_map C₂)
                     (TerminalArrow _ _)
                     (type_in_cat_univ_code c₂)
                 · type_in_cat_univ_z_iso c₂
                 · preserves_parameterized_NNO_mor
                     N₁ N₂
                     F
                     (functor_finlim_preserves_terminal F))
  : functor_preserves_pnno_in_cat_univ c₁ c₂ F HF.
Proof.
  use make_functor_preserves_type_in_cat_univ.
  - exact p.
  - simpl.
    refine (!_).
    use z_iso_inv_on_left.
    exact q.
Qed.

Proposition functor_preserves_pnno_in_cat_univ_eq
            {C₁ C₂ : univ_cat_with_finlim_universe}
            {N₁ : parameterized_NNO
                    (terminal_univ_cat_with_finlim C₁)
                    (binproducts_univ_cat_with_finlim C₁)}
            {N₂ : parameterized_NNO
                    (terminal_univ_cat_with_finlim C₂)
                    (binproducts_univ_cat_with_finlim C₂)}
            {c₁ : pnno_in_cat_univ N₁}
            {c₂ : pnno_in_cat_univ N₂}
            {F F' : functor_finlim_universe C₁ C₂}
            (p : F = F')
            (HF : preserves_parameterized_NNO
                    N₁ N₂
                    F
                    (functor_finlim_preserves_terminal F))
            (HF' : preserves_parameterized_NNO
                     N₁ N₂
                     F'
                     (functor_finlim_preserves_terminal F'))
            (HFF : functor_preserves_pnno_in_cat_univ c₁ c₂ F HF)
  : functor_preserves_pnno_in_cat_univ c₁ c₂ F' HF'.
Proof.
  induction p.
  assert (HF = HF') as ->.
  {
    apply isaprop_preserves_parameterized_NNO.
  }
  exact HFF.
Qed.

(** ** 4.4. Preservation of the code for the subobject classifier *)
Definition functor_preserves_subobject_classifier_in_cat_univ
           {C₁ C₂ : univ_cat_with_finlim_universe}
           {Ω₁ : subobject_classifier (terminal_univ_cat_with_finlim C₁)}
           {Ω₂ : subobject_classifier (terminal_univ_cat_with_finlim C₂)}
           (c₁ : subobject_classifier_in_cat_univ Ω₁)
           (c₂ : subobject_classifier_in_cat_univ Ω₂)
           (F : functor_finlim_universe C₁ C₂)
           (HF : preserves_subobject_classifier
                   F
                   (terminal_univ_cat_with_finlim C₁)
                   (terminal_univ_cat_with_finlim C₂)
                   (functor_finlim_preserves_terminal F))
  : UU
  := functor_preserves_type_in_cat_univ
       F
       (preserves_subobject_classifier_z_iso HF Ω₁ Ω₂)
       c₁
       c₂.

Proposition make_functor_preserves_subobject_classifier_in_cat_univ
            {C₁ C₂ : univ_cat_with_finlim_universe}
            {Ω₁ : subobject_classifier (terminal_univ_cat_with_finlim C₁)}
            {Ω₂ : subobject_classifier (terminal_univ_cat_with_finlim C₂)}
            {c₁ : subobject_classifier_in_cat_univ Ω₁}
            {c₂ : subobject_classifier_in_cat_univ Ω₂}
            {F : functor_finlim_universe C₁ C₂}
            {HF : preserves_subobject_classifier
                    F
                    (terminal_univ_cat_with_finlim C₁)
                    (terminal_univ_cat_with_finlim C₂)
                    (functor_finlim_preserves_terminal F)}
            (p : #F(type_in_cat_univ_code c₁) · functor_on_universe F
                 =
                 TerminalArrow _ _ · type_in_cat_univ_code c₂)
            (q : functor_el_map_iso
                   (functor_finlim_universe_preserves_el F)
                   (type_in_cat_univ_code c₁)
                 · cat_el_map_el_eq (univ_cat_cat_stable_el_map C₂) p
                 · cat_el_map_pb_mor
                     (univ_cat_cat_stable_el_map C₂)
                     (TerminalArrow _ _)
                     (type_in_cat_univ_code c₂)
                 · type_in_cat_univ_z_iso c₂
                 =
                 #F (type_in_cat_univ_z_iso c₁)
                 · mor_subobject_classifier (preserves_subobject_classifier_on_ob HF Ω₁) Ω₂)
  : functor_preserves_subobject_classifier_in_cat_univ c₁ c₂ F HF.
Proof.
  use make_functor_preserves_type_in_cat_univ.
  - exact p.
  - simpl.
    refine (!_).
    exact q.
Qed.

Proposition functor_preserves_subobject_classifier_in_cat_univ_eq
            {C₁ C₂ : univ_cat_with_finlim_universe}
            {Ω₁ : subobject_classifier (terminal_univ_cat_with_finlim C₁)}
            {Ω₂ : subobject_classifier (terminal_univ_cat_with_finlim C₂)}
            {c₁ : subobject_classifier_in_cat_univ Ω₁}
            {c₂ : subobject_classifier_in_cat_univ Ω₂}
            {F F' : functor_finlim_universe C₁ C₂}
            (p : F = F')
            (HF : preserves_subobject_classifier
                    F
                    (terminal_univ_cat_with_finlim C₁)
                    (terminal_univ_cat_with_finlim C₂)
                    (functor_finlim_preserves_terminal F))
            (HF' : preserves_subobject_classifier
                     F'
                     (terminal_univ_cat_with_finlim C₁)
                     (terminal_univ_cat_with_finlim C₂)
                     (functor_finlim_preserves_terminal F'))
            (HFF : functor_preserves_subobject_classifier_in_cat_univ c₁ c₂ F HF)
  : functor_preserves_subobject_classifier_in_cat_univ c₁ c₂ F' HF'.
Proof.
  induction p.
  assert (HF = HF') as ->.
  {
    apply isaprop_preserves_subobject_classifier.
  }
  exact HFF.
Qed.

(** * 5. Preservation by identity and composition *)
Proposition identity_preserves_type_in_cat_univ_code_eq
            {C : univ_cat_with_finlim_universe}
            {A : C}
            (a : type_in_cat_univ A)
  : functor_preserves_type_in_cat_univ_code
      (identity _)
      (identity_z_iso A)
      a
      a.
Proof.
  cbn.
  rewrite id_right.
  refine (!(id_left _) @ _).
  apply maponpaths_2.
  apply TerminalArrowEq.
Qed.

Proposition identity_preserves_type_in_cat_univ_z_iso_eq
            {C : univ_cat_with_finlim_universe}
            {A : C}
            (a : type_in_cat_univ A)
  : functor_preserves_type_in_cat_univ_code_z_iso
      (identity _)
      (identity_preserves_type_in_cat_univ_code_eq a).
Proof.
  cbn.
  refine (id_right _ @ _).
  refine (!(id_left _) @ _).
  apply maponpaths_2.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    use cat_el_map_pb_mor_id'.
    apply TerminalArrowEq.
  }
  rewrite !(cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
  apply (cat_el_map_el_eq_id (univ_cat_cat_stable_el_map C)).
Qed.

Proposition identity_preserves_type_in_cat_univ
            {C : univ_cat_with_finlim_universe}
            {A : C}
            (a : type_in_cat_univ A)
  : functor_preserves_type_in_cat_univ
      (identity _)
      (identity_z_iso A)
      a
      a.
Proof.
  use make_functor_preserves_type_in_cat_univ.
  - exact (identity_preserves_type_in_cat_univ_code_eq a).
  - exact (identity_preserves_type_in_cat_univ_z_iso_eq a).
Qed.

Section CompPreservation.
  Context {C₁ C₂ C₃ : univ_cat_with_finlim_universe}
          (F : functor_finlim_universe C₁ C₂)
          (G : functor_finlim_universe C₂ C₃)
          {A₁ : C₁}
          {A₂ : C₂}
          {A₃ : C₃}
          {a₁ : type_in_cat_univ A₁}
          {a₂ : type_in_cat_univ A₂}
          {a₃ : type_in_cat_univ A₃}
          {FA : z_iso (F A₁) A₂}
          {GA : z_iso (G A₂) A₃}
          (FcA : functor_preserves_type_in_cat_univ F FA a₁ a₂)
          (GcA : functor_preserves_type_in_cat_univ G GA a₂ a₃).

  Proposition comp_functor_preserves_type_in_cat_univ_code_eq
    : functor_preserves_type_in_cat_univ_code
        (F · G)
        (z_iso_comp (functor_on_z_iso G FA) GA)
        a₁
        a₃.
  Proof.
    cbn.
    rewrite !assoc.
    rewrite <- functor_comp.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply (functor_preserves_type_in_cat_univ_code_eq _ FcA).
    }
    rewrite functor_comp.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply (functor_preserves_type_in_cat_univ_code_eq _ GcA).
    }
    rewrite !assoc.
    apply maponpaths_2.
    apply TerminalArrowEq.
  Qed.

  Proposition comp_functor_preserves_type_in_cat_univ_z_iso_eq
    : functor_preserves_type_in_cat_univ_code_z_iso
        (F · G)
        comp_functor_preserves_type_in_cat_univ_code_eq.
  Proof.
    cbn.
    refine (assoc _ _ _ @ _).
    rewrite <- functor_comp.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply FcA.
    }
    rewrite functor_comp.
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply GcA.
    }
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    rewrite !functor_comp.
    do 2 refine (assoc' _ _ _ @ _).
    do 2 refine (_ @ assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      apply (functor_preserves_el_path (functor_finlim_universe_preserves_el G)).
    }
    refine (assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply (functor_el_map_iso_eq_alt (functor_finlim_universe_preserves_el G)).
    }
    do 4 refine (assoc' _ _ _ @ _).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      do 2 apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (!_).
      use cat_el_map_pb_mor_eq.
      etrans.
      {
        apply maponpaths.
        apply GcA.
      }
      rewrite !assoc.
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      use cat_el_map_pb_mor_comp'.
    }
    do 3 refine (assoc _ _ _ @ _).
    refine (_ @ assoc' _ _ _).
    etrans.
    {
      do 3 apply maponpaths_2.
      apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
    }
    etrans.
    {
      apply maponpaths_2.
      apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
    }
    etrans.
    {
      apply maponpaths.
      use cat_el_map_pb_mor_subst_eq.
      - apply TerminalArrow.
      - apply TerminalArrowEq.
    }
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
    }
    refine (!_).
    simpl.
    etrans.
    {
      apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
    }
    apply (cat_el_map_el_eq_eq (univ_cat_cat_stable_el_map C₃)).
  Qed.

  Proposition comp_functor_preserves_type_in_cat_univ
    : functor_preserves_type_in_cat_univ
        (F · G)
        (z_iso_comp (functor_on_z_iso G FA) GA)
        a₁
        a₃.
  Proof.
    use make_functor_preserves_type_in_cat_univ.
    - exact comp_functor_preserves_type_in_cat_univ_code_eq.
    - exact comp_functor_preserves_type_in_cat_univ_z_iso_eq.
  Qed.
End CompPreservation.

(** * 6. Instantiation to the examples *)

(** ** 6.1. Preservation of the code for the terminal object *)
Proposition id_functor_preserves_terminal_in_cat_univ
            {C : univ_cat_with_finlim_universe}
            (c : terminal_in_cat_univ C)
  : functor_preserves_terminal_in_cat_univ
      c
      c
      (identity _).
Proof.
  refine (functor_preserves_type_in_cat_univ_z_iso_eq
            _
            _
            (identity_preserves_type_in_cat_univ c)).
  use z_iso_eq.
  apply TerminalArrowEq.
Qed.

Proposition comp_functor_preserves_terminal_in_cat_univ
            {C₁ C₂ C₃ : univ_cat_with_finlim_universe}
            {F : functor_finlim_universe C₁ C₂}
            {G : functor_finlim_universe C₂ C₃}
            {c₁ : terminal_in_cat_univ C₁}
            {c₂ : terminal_in_cat_univ C₂}
            {c₃ : terminal_in_cat_univ C₃}
            (Fc : functor_preserves_terminal_in_cat_univ c₁ c₂ F)
            (Gc : functor_preserves_terminal_in_cat_univ c₂ c₃ G)
  : functor_preserves_terminal_in_cat_univ
      c₁
      c₃
      (F · G).
Proof.
  refine (functor_preserves_type_in_cat_univ_z_iso_eq
            _
            _
            (comp_functor_preserves_type_in_cat_univ F G Fc Gc)).
  use z_iso_eq.
  apply TerminalArrowEq.
Qed.

(** ** 6.2. Preservation of the code for the initial object *)
Proposition id_functor_preserves_initial_in_cat_univ
            {C : univ_cat_with_finlim_universe}
            {I : Initial C}
            (c : initial_in_cat_univ I)
  : functor_preserves_initial_in_cat_univ
      c
      c
      (identity _)
      (identity_preserves_initial _).
Proof.
  refine (functor_preserves_type_in_cat_univ_z_iso_eq
            _
            _
            (identity_preserves_type_in_cat_univ c)).
  use z_iso_eq.
  apply InitialArrowEq.
Qed.

Proposition comp_functor_preserves_initial_in_cat_univ
            {C₁ C₂ C₃ : univ_cat_with_finlim_universe}
            {F : functor_finlim_universe C₁ C₂}
            {HF : preserves_initial F}
            {G : functor_finlim_universe C₂ C₃}
            {HG : preserves_initial G}
            {I₁ : Initial C₁}
            {I₂ : Initial C₂}
            {I₃ : Initial C₃}
            {c₁ : initial_in_cat_univ I₁}
            {c₂ : initial_in_cat_univ I₂}
            {c₃ : initial_in_cat_univ I₃}
            (Fc : functor_preserves_initial_in_cat_univ c₁ c₂ F HF)
            (Gc : functor_preserves_initial_in_cat_univ c₂ c₃ G HG)
  : functor_preserves_initial_in_cat_univ
      c₁
      c₃
      (F · G)
      (composition_preserves_initial HF HG).
Proof.
  refine (functor_preserves_type_in_cat_univ_z_iso_eq
            _
            _
            (comp_functor_preserves_type_in_cat_univ F G Fc Gc)).
  use z_iso_eq.
  apply (InitialArrowEq
           (O := preserves_initial_to_initial _ (composition_preserves_initial HF HG) I₁)).
Qed.

(** ** 6.3. Preservation of the code for the parameterized natural numbers object *)
Proposition id_functor_preserves_pnno_in_cat_univ
            {C : univ_cat_with_finlim_universe}
            {N : parameterized_NNO
                   (terminal_univ_cat_with_finlim C)
                   (binproducts_univ_cat_with_finlim C)}
            (c : pnno_in_cat_univ N)
  : functor_preserves_pnno_in_cat_univ
      c
      c
      (identity _)
      (id_preserves_parameterized_NNO _ _ _).
Proof.
  exact (identity_preserves_type_in_cat_univ c).
Qed.

Proposition comp_functor_preserves_pnno_in_cat_univ
            {C₁ C₂ C₃ : univ_cat_with_finlim_universe}
            {F : functor_finlim_universe C₁ C₂}
            {G : functor_finlim_universe C₂ C₃}
            {N₁ : parameterized_NNO
                    (terminal_univ_cat_with_finlim C₁)
                    (binproducts_univ_cat_with_finlim C₁)}
            {N₂ : parameterized_NNO
                    (terminal_univ_cat_with_finlim C₂)
                    (binproducts_univ_cat_with_finlim C₂)}
            {N₃ : parameterized_NNO
                    (terminal_univ_cat_with_finlim C₃)
                    (binproducts_univ_cat_with_finlim C₃)}
            {c₁ : pnno_in_cat_univ N₁}
            {c₂ : pnno_in_cat_univ N₂}
            {c₃ : pnno_in_cat_univ N₃}
            {HF : preserves_parameterized_NNO
                    N₁ N₂
                    F
                    (functor_finlim_preserves_terminal F)}
            {HG : preserves_parameterized_NNO
                    N₂ N₃
                    G
                    (functor_finlim_preserves_terminal G)}
            (Fc : functor_preserves_pnno_in_cat_univ c₁ c₂ F HF)
            (Gc : functor_preserves_pnno_in_cat_univ c₂ c₃ G HG)
  : functor_preserves_pnno_in_cat_univ
      c₁
      c₃
      (F · G)
      (comp_preserves_parameterized_NNO HF HG).
Proof.
  exact (comp_functor_preserves_type_in_cat_univ F G Fc Gc).
Qed.

(** ** 6.4. Preservation of the code for the subobject classifier *)
Proposition id_functor_preserves_subobject_classifier_in_cat_univ
            {C : univ_cat_with_finlim_universe}
            {Ω : subobject_classifier (terminal_univ_cat_with_finlim C)}
            (c : subobject_classifier_in_cat_univ Ω)
  : functor_preserves_subobject_classifier_in_cat_univ
      c
      c
      (identity _)
      (identity_preserves_subobject_classifier _).
Proof.
  refine (functor_preserves_type_in_cat_univ_z_iso_eq
            _
            _
            (identity_preserves_type_in_cat_univ c)).
  use z_iso_eq ; cbn.
  apply mor_subobject_classifier_is_identity.
Qed.

Proposition comp_functor_preserves_subobject_classifier_in_cat_univ
            {C₁ C₂ C₃ : univ_cat_with_finlim_universe}
            {F : functor_finlim_universe C₁ C₂}
            {G : functor_finlim_universe C₂ C₃}
            {Ω₁ : subobject_classifier (terminal_univ_cat_with_finlim C₁)}
            {Ω₂ : subobject_classifier (terminal_univ_cat_with_finlim C₂)}
            {Ω₃ : subobject_classifier (terminal_univ_cat_with_finlim C₃)}
            {c₁ : subobject_classifier_in_cat_univ Ω₁}
            {c₂ : subobject_classifier_in_cat_univ Ω₂}
            {c₃ : subobject_classifier_in_cat_univ Ω₃}
            {HF : preserves_subobject_classifier
                    F
                    (terminal_univ_cat_with_finlim C₁)
                    (terminal_univ_cat_with_finlim C₂)
                    (functor_finlim_preserves_terminal F)}
            {HG : preserves_subobject_classifier
                    G
                    (terminal_univ_cat_with_finlim C₂)
                    (terminal_univ_cat_with_finlim C₃)
                    (functor_finlim_preserves_terminal G)}
            (Fc : functor_preserves_subobject_classifier_in_cat_univ c₁ c₂ F HF)
            (Gc : functor_preserves_subobject_classifier_in_cat_univ c₂ c₃ G HG)
  : functor_preserves_subobject_classifier_in_cat_univ
      c₁
      c₃
      (F · G)
      (comp_preserves_subobject_classifier HF HG).
Proof.
  refine (functor_preserves_type_in_cat_univ_z_iso_eq
            _
            _
            (comp_functor_preserves_type_in_cat_univ F G Fc Gc)).
  use z_iso_eq ; cbn.
  apply mor_subobject_classifier_is_composition.
Qed.

(** * 7. Univalence condition *)
Proposition type_in_cat_univ_univalence_lemma
            {C : univ_cat_with_finlim_universe}
            {A : C}
            {a₁ a₂ : type_in_cat_univ A}
            (Fc : functor_preserves_type_in_cat_univ
                     (identity _)
                     (identity_z_iso _)
                     a₁ a₂)
  : a₁ = a₂.
Proof.
  use type_in_cat_univ_eq.
  - pose (functor_preserves_type_in_cat_univ_code_eq _ Fc) as p.
    simpl in p.
    refine (!(id_right _) @ _).
    refine (p @ _).
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply TerminalArrowEq.
  - pose (functor_preserves_type_in_cat_univ_code_z_iso_eq _ Fc) as p.
    simpl in p.
    refine (!_).
    refine (!(id_right _) @ _).
    refine (p @ _).
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      use cat_el_map_pb_mor_subst_eq.
      {
        apply identity.
      }
      apply TerminalArrowEq.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite !(cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
    apply (cat_el_map_el_eq_eq (univ_cat_cat_stable_el_map C)).
Qed.

(** ** 7.1. Univalence condition for the terminal object *)
Proposition terminal_in_cat_univ_univalence_lemma
            {C : univ_cat_with_finlim_universe}
            {c₁ c₂ : terminal_in_cat_univ C}
            (Fc : functor_preserves_terminal_in_cat_univ c₁ c₂ (identity _))
  : c₁ = c₂.
Proof.
  use type_in_cat_univ_univalence_lemma.
  refine (functor_preserves_type_in_cat_univ_z_iso_eq
            _
            _
            Fc).
  use z_iso_eq.
  apply TerminalArrowEq.
Qed.

(** ** 7.2. Univalence condition for the initial object *)
Proposition initial_in_cat_univ_univalence_lemma
            {C : univ_cat_with_finlim_universe}
            {I : Initial C}
            {c₁ c₂ : initial_in_cat_univ I}
            (Fc : functor_preserves_initial_in_cat_univ
                    c₁ c₂
                    (identity _)
                    (identity_preserves_initial _))
  : c₁ = c₂.
Proof.
  use type_in_cat_univ_univalence_lemma.
  refine (functor_preserves_type_in_cat_univ_z_iso_eq
            _
            _
            Fc).
  use z_iso_eq.
  apply InitialArrowEq.
Qed.

(** ** 7.3. Univalence condition for the parameterized natural numbers object *)
Proposition pnno_in_cat_univ_univalence_lemma
            {C : univ_cat_with_finlim_universe}
            {N : parameterized_NNO
                   (terminal_univ_cat_with_finlim C)
                   (binproducts_univ_cat_with_finlim C)}
            {c₁ c₂ : pnno_in_cat_univ N}
            (Fc : functor_preserves_pnno_in_cat_univ
                    c₁ c₂
                    (identity _)
                    (id_preserves_parameterized_NNO _ _ _))
  : c₁ = c₂.
Proof.
  use type_in_cat_univ_univalence_lemma.
  exact Fc.
Qed.

(** ** 7.4. Univalence condition for the subobject classifier *)
Proposition subobject_classifier_in_cat_univ_univalence_lemma
            {C : univ_cat_with_finlim_universe}
            {Ω : subobject_classifier (terminal_univ_cat_with_finlim C)}
            {c₁ c₂ : subobject_classifier_in_cat_univ Ω}
            (Fc : functor_preserves_subobject_classifier_in_cat_univ
                    c₁ c₂
                    (identity _)
                    (identity_preserves_subobject_classifier _))
  : c₁ = c₂.
Proof.
  use type_in_cat_univ_univalence_lemma.
  refine (functor_preserves_type_in_cat_univ_z_iso_eq
            _
            _
            Fc).
  use z_iso_eq ; cbn.
  refine (!_).
  apply mor_subobject_classifier_is_identity.
Qed.
