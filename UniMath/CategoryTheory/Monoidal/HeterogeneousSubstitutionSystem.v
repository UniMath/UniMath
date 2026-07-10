Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.RModules.
Require Import UniMath.CategoryTheory.Monoidal.ModuleSignatures.
Require Import UniMath.CategoryTheory.Monoidal.SignaturesWithStrength.
Require Import UniMath.CategoryTheory.Monoidal.ModelsOfModuleSignature.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section HeterogeneousSubstitutionSystem.
  Context {C : monoidal_cat}.

  Local Notation "x ⊗l f" := (x ⊗^{C}_{l} f) (at level 31).
  Local Notation "f ⊗r y" := (f ⊗^{C}_{r} y) (at level 31).

  Section FixASignatureWithStrength.
    Context (Hθ : @signature_with_strength_cat C).
    Let H : C ⟶  C := pr1 Hθ.
    Let θ : strength_for_signature H := pr2 Hθ. 

    Definition heterogeneous_substitution_system_data
      := ∑ (R : C), I_{C} --> R × H R --> R.

    Context (Rηr : heterogeneous_substitution_system_data).
    Let R : C := pr1 Rηr.
    Let η : I_{C} --> R := pr12 Rηr.
    Let r : H R --> R := pr22 Rηr.

    Section HSS_Equalities.
      Context (Z : pointed) (f : pr1 Z --> R) (f' : R ⊗ pr1 Z --> R).

      Definition heterogeneous_substitution_system_law_eq_unit
        := η ⊗r pr1 Z · f' = lu^{C}_{_} · f.

      Definition heterogeneous_substitution_system_law_eq_out
        := r ⊗r pr1 Z · f' = θ R Z · #H f' · r.

      Definition heterogeneous_substitution_system_law_eq
        := heterogeneous_substitution_system_law_eq_unit
           × heterogeneous_substitution_system_law_eq_out. 
    End HSS_Equalities.

    Definition heterogeneous_substitution_system_law
      := ∏ (Z : pointed) (f : pr1 Z --> R), 
        ∃! f' : R ⊗ pr1 Z --> R, heterogeneous_substitution_system_law_eq Z f f'.

  End FixASignatureWithStrength.

  Definition heterogeneous_substitution_system
    (Hθ : signature_with_strength_cat)
    := ∑ (hss : heterogeneous_substitution_system_data Hθ),
        heterogeneous_substitution_system_law Hθ hss.

  Definition hss_object
    {Hθ : signature_with_strength_cat}
    (hss : heterogeneous_substitution_system Hθ)
    : C := pr11 hss.

  Definition hss_unit
    {Hθ : signature_with_strength_cat}
    (hss : heterogeneous_substitution_system Hθ)
    : I_{C} --> hss_object hss := pr121 hss.

  Definition hss_out
    {Hθ : signature_with_strength_cat}
    (hss : heterogeneous_substitution_system Hθ)
    : pr11 Hθ (hss_object hss) --> hss_object hss := pr221 hss.

  Definition hss_arrow
    {Hθ : signature_with_strength_cat}
    (hss : heterogeneous_substitution_system Hθ)
    {Z : pointed} (f : pr1 Z --> hss_object hss)
    : hss_object hss ⊗ pr1 Z --> hss_object hss := pr11 (pr2 hss Z f).

  Definition hss_arrow_unit
    {Hθ : signature_with_strength_cat}
    (hss : heterogeneous_substitution_system Hθ)
    {Z : pointed} {f : pr1 Z --> hss_object hss}
    : hss_unit hss ⊗r pr1 Z · hss_arrow hss f = lu^{C}_{_} · f
    := pr121 (pr2 hss Z f).

  Definition hss_arrow_out
    {H : C ⟶ C} {θ : strength_for_signature H}
    (hss : heterogeneous_substitution_system θ)
    {Z : pointed} {f : pr1 Z --> hss_object hss}
    : hss_out hss ⊗r pr1 Z · hss_arrow hss f
      = θ (hss_object hss) Z · #H (hss_arrow hss f) · hss_out hss
    := pr221 (pr2 hss Z f).

  Definition hss_arrow_unique
    {H : C ⟶ C} {θ : strength_for_signature H}
    (hss : heterogeneous_substitution_system θ)
    {Z : pointed} {f : pr1 Z --> hss_object hss}
    (arrow' : hss_object hss ⊗ pr1 Z --> hss_object hss)
    (arrow'_unit : hss_unit hss ⊗r pr1 Z · arrow' = lu^{C}_{_} · f)
    (arrow'_out : hss_out hss ⊗r pr1 Z · arrow' = θ (hss_object hss) Z · #H arrow' · hss_out hss)
    : arrow' = hss_arrow hss f
    := maponpaths pr1 (pr2 (pr2 hss Z f) (arrow' ,, arrow'_unit ,, arrow'_out)).

  Definition hss_object_pointed 
    {Hθ : signature_with_strength_cat} 
    (hss : heterogeneous_substitution_system Hθ)
    : pointed
    := hss_object hss ,, hss_unit hss.
    

  Section MonoidsFromHSS.
    Context (H : C ⟶ C) (θ : strength_for_signature H).
    Context (hss : heterogeneous_substitution_system θ).

    Let R : pointed := hss_object_pointed hss.

    Definition monoids_from_hss_monoid_multiplication : R ⊗ R --> R
      := hss_arrow hss (identity R).

    Definition monoids_from_hss_monoid_unit : I_{C} --> R
      := hss_unit hss.

    Let η_pointed : pointed ⟦ pointed_unit, R ⟧.
    Proof.
      exists monoids_from_hss_monoid_unit.
      use id_left.
    Defined.

    Local Lemma μ_pointed_lemma
      : luinv^{ C }_{_} · η_pointed #⊗ η_pointed · monoids_from_hss_monoid_multiplication = η_pointed. 
    Proof.
      rewrite tensor_split, <- tensor_mor_left, <- tensor_mor_right, assoc, <- assoc.
      etrans.
      { refine (maponpaths _ _); use (hss_arrow_unit hss (Z := R)). }
      etrans.
      { refine (maponpaths (λ x, x · _) _); use monoidal_leftunitorinvnat. }
      rewrite assoc, id_right, <- assoc; etrans.
      { refine (maponpaths _ (pr2 (monoidal_leftunitorisolaw _ _))). }
      use id_right.
    Qed.

    Let μ_pointed : pointed ⟦ pointed_prod R R, R ⟧.
    Proof.
      exists monoids_from_hss_monoid_multiplication.
      exact μ_pointed_lemma.
    Defined.


    Lemma monoids_from_hss_monoid_lunit
      : monoids_from_hss_monoid_unit ⊗r R · monoids_from_hss_monoid_multiplication 
          = lu^{ C }_{ R}.
    Proof.
      etrans.
      use (hss_arrow_unit hss).
      use id_right.
    Qed.

    Lemma monoids_from_hss_monoid_runit
      : R ⊗l monoids_from_hss_monoid_unit · monoids_from_hss_monoid_multiplication 
          = ru^{ C }_{ R}.
    Proof.
      refine (_ @ !_); swap 1 2; use (hss_arrow_unique hss (Z:= pointed_unit)); simpl.
      - exact monoids_from_hss_monoid_unit.
      - rewrite unitors_coincide_on_unit; use monoidal_rightunitornat.
      - rewrite monoidal_rightunitornat, signature_with_strength_unit.
        refine (!maponpaths (λ x , x · _) _).
        rewrite <- assoc, <- id_right, <- functor_comp, <- (functor_id H).
        do 2 refine (maponpaths _ _).
        use (pr2 (monoidal_rightunitorisolaw _ _)).
      - rewrite assoc, tensor_mor_right, tensor_mor_left.
        etrans; [refine (maponpaths (λ x, x · _) (tensor_swap _ _))|].
        rewrite <- tensor_mor_right, <- tensor_mor_left, <- monoidal_leftunitornat, <- assoc.
        use maponpaths; rewrite <- id_right.
        use (hss_arrow_unit hss (Z := R)).
      - rewrite assoc, functor_comp, assoc, tensor_mor_right, tensor_mor_left.
        etrans; [refine (maponpaths (λ x, x · _) (tensor_swap _ _))|].
        rewrite <- tensor_mor_right, <- tensor_mor_left, <- tensor_mor_left.
        etrans.
        { rewrite <- assoc; refine (maponpaths _ _).
          use (hss_arrow_out hss (Z := R)). }
        do 2 rewrite assoc.
        use (!maponpaths (λ x, x · _ · _) _).
        use (signature_with_strength_nat_right _ θ R pointed_unit R η_pointed).
    Qed.

    Lemma monoids_from_hss_monoid_assoc
      : α^{ C }_{ R, R, R} · R ⊗l monoids_from_hss_monoid_multiplication
          · monoids_from_hss_monoid_multiplication 
        = monoids_from_hss_monoid_multiplication ⊗r R
          · monoids_from_hss_monoid_multiplication.
    Proof.
      refine (_ @ _).
      {
        rewrite <- assoc; refine (maponpaths _ _).
        use (hss_arrow_unique hss (Z:= pointed_prod R R)); simpl.
        - use μ_pointed. 
        - rewrite assoc, tensor_mor_left, tensor_mor_right.
          etrans; [refine (maponpaths (λ x, x · _) _); use tensor_swap|].
          rewrite <- tensor_mor_left, <- tensor_mor_right, <- assoc.
          etrans.
          { refine (maponpaths _ _); use (hss_arrow_unit hss (Z := R)). }
          now rewrite id_right, <- monoidal_leftunitornat.
        - rewrite assoc, functor_comp, assoc.
          etrans.
          { rewrite tensor_mor_left, tensor_mor_right.
            refine (maponpaths (λ x, x · _) _); use tensor_swap. }
          rewrite <- tensor_mor_left, <- tensor_mor_right.
          symmetry; etrans.
          { refine (maponpaths (λ x, x · _ · _) (signature_with_strength_nat_right _ _ _ _ _ μ_pointed)). }
          repeat rewrite <- assoc; use maponpaths; repeat rewrite assoc.
          symmetry; use hss_arrow_out.
      }
      rewrite <- id_left, <- (pr1 (monoidal_associatorisolaw C _ _ _)), <- assoc.
      refine (! maponpaths _ _); use hss_arrow_unique.
      - do 2 rewrite assoc; refine (maponpaths (λ x, x · _) _).
        rewrite <- id_right, <- id_left.
        symmetry; etrans.
        { refine (!maponpaths (λ x, _ · (_ · x)) _); use tensor_id_id. }
        rewrite <- tensor_mor_right, assoc.
        etrans.
        { refine (!maponpaths (λ x, x · _ · _) _).
          use (pr2 (monoidal_associatorisolaw C _ _ _ )). }
        etrans.
        { refine (maponpaths (λ x, x · _) _); rewrite <- assoc.
          refine (maponpaths _ (right_whisker_with_lunitor _ _ _)). }
        etrans.
        { rewrite <- assoc, <- (bifunctor_rightcomp C); do 2 refine (maponpaths _ _).
          symmetry; use (hss_arrow_unit hss (Z := R)). }
        rewrite bifunctor_rightcomp, assoc; use (!maponpaths (λ x, x · _) _).
        use monoidal_associatorinvnatright.
      - do 2 rewrite functor_comp; repeat rewrite assoc.
        etrans.
        { refine (maponpaths (λ x, x · _ · _) _); use monoidal_associatorinvnatright. }
        rewrite signature_with_strength_prod.
        repeat rewrite <- assoc; use maponpaths.
        symmetry; etrans.
        { do 2 refine (maponpaths _ _); repeat rewrite assoc.
          refine (maponpaths (λ x, x · _ · _ · _) _).
          rewrite <- functor_comp.
          refine (maponpaths _ (pr1 (monoidal_associatorisolaw _ _ _ _))). }
        rewrite functor_id, id_left.
        etrans.
        { refine (maponpaths _ _); do 2 rewrite assoc.
          refine (maponpaths (λ x, x · _ · _) _).
          use signature_with_strength_nat_left. }
        repeat rewrite assoc.
        do 2 rewrite <- (bifunctor_rightcomp C).
        symmetry; etrans.
        { refine (maponpaths (λ x, x ⊗r _ · _) _); use hss_arrow_out. }
        do 2 rewrite (bifunctor_rightcomp C).
        etrans.
        { rewrite <- assoc; refine (maponpaths _ _); use hss_arrow_out. }
        now rewrite bifunctor_rightcomp, assoc, assoc.
    Qed.

    Definition monoids_from_hss_monoid
      : monoid C R.
    Proof.
      use make_monoid.
      - exact monoids_from_hss_monoid_multiplication.
      - exact monoids_from_hss_monoid_unit.
      - exact monoids_from_hss_monoid_lunit.
      - exact monoids_from_hss_monoid_runit.
      - exact monoids_from_hss_monoid_assoc.
    Defined.


    Definition monoids_from_hss : MON C := _ ,, monoids_from_hss_monoid.

    Definition models_from_hss : models_of_module_signatures_cat 
        (signature_with_strength_to_module_signatures θ).
    Proof.
      exists monoids_from_hss.
      use tpair; cbn.
      - use hss_out.
      - use (hss_arrow_out hss (Z := R)).
    Defined.

End HeterogeneousSubstitutionSystem.
