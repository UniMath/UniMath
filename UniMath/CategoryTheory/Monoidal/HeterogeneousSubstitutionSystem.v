Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Monoidal.RModules.
Require Import UniMath.CategoryTheory.Monoidal.ModuleSignatures.
Require Import UniMath.CategoryTheory.Monoidal.SignaturesWithStrength.
Require Import UniMath.CategoryTheory.Monoidal.ModelsOfModuleSignature.

Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Chains.All.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.GeneralizedMendlerIteration.

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
      Context (Z : pointed) (f : (Z : C) --> R) (f' : R ⊗ Z --> R).

      Definition heterogeneous_substitution_system_law_eq_unit
        := η ⊗r Z · f' = lu^{C}_{_} · f.

      Definition heterogeneous_substitution_system_law_eq_out
        := r ⊗r Z · f' = θ R Z · #H f' · r.

      Definition heterogeneous_substitution_system_law_eq
        := heterogeneous_substitution_system_law_eq_unit
           × heterogeneous_substitution_system_law_eq_out. 
    End HSS_Equalities.

    Definition heterogeneous_substitution_system_law
      := ∏ (Z : pointed) (f : (Z : C) --> R), 
        ∃! f' : R ⊗ Z --> R, heterogeneous_substitution_system_law_eq Z f f'.

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
    {Z : pointed} (f : (Z : C) --> hss_object hss)
    : hss_object hss ⊗ Z --> hss_object hss := pr11 (pr2 hss Z f).

  Definition hss_arrow_unit
    {Hθ : signature_with_strength_cat}
    (hss : heterogeneous_substitution_system Hθ)
    {Z : pointed} {f : (Z : C) --> hss_object hss}
    : hss_unit hss ⊗r Z · hss_arrow hss f = lu^{C}_{_} · f
    := pr121 (pr2 hss Z f).

  Definition hss_arrow_out
    {H : C ⟶ C} {θ : strength_for_signature H}
    (hss : heterogeneous_substitution_system θ)
    {Z : pointed} {f : (Z : C) --> hss_object hss}
    : hss_out hss ⊗r Z · hss_arrow hss f
      = θ (hss_object hss) Z · #H (hss_arrow hss f) · hss_out hss
    := pr221 (pr2 hss Z f).

  Definition hss_arrow_unique
    {H : C ⟶ C} {θ : strength_for_signature H}
    (hss : heterogeneous_substitution_system θ)
    {Z : pointed} {f : (Z : C) --> hss_object hss}
    (arrow' : hss_object hss ⊗ Z --> hss_object hss)
    (arrow'_unit : hss_unit hss ⊗r Z · arrow' = lu^{C}_{_} · f)
    (arrow'_out : hss_out hss ⊗r Z · arrow' = θ (hss_object hss) Z · #H arrow' · hss_out hss)
    : arrow' = hss_arrow hss f
    := maponpaths pr1 (pr2 (pr2 hss Z f) (arrow' ,, arrow'_unit ,, arrow'_out)).

  Definition hss_object_pointed 
    {Hθ : signature_with_strength_cat} 
    (hss : heterogeneous_substitution_system Hθ)
    : pointed
    := hss_object hss ,, hss_unit hss.
    

  Section ModelsFromHSS.
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
  End ModelsFromHSS.

  Section BuildingAnHSS.
    Context (Hθ : @omega_signature_with_strength_cat C).
    Let H : C ⟶ C := pr11 Hθ.
    Let θ : strength_for_signature H := pr21 Hθ.
    Let H_cocont : is_omega_cocont H := pr2 Hθ.

    Context (tens_cocont : ∏ (Z : pointed),
      is_omega_cocont (rightwhiskering_functor C Z)).
    Context (tens_init : ∏ (Z : pointed),
       preserves_initial (rightwhiskering_functor C Z)).
    Context (tens_bincopr : ∏ (Z : pointed),
       preserves_bincoproduct (rightwhiskering_functor C Z)).

    Context (O : Initial C) (Copr : BinCoproducts C).

    Let copr (A : C) (B : C) : C := BinCoproductObject (Copr A B).
    Local Notation "A ++ B" := (copr A B) (at level 60).

    Let inl {A B : C} : A --> (A ++ B) := BinCoproductIn1 _.
    Let inr {A B : C} : B --> (A ++ B) := BinCoproductIn2 _.

    Local Lemma iscopr {X Y : C} 
      : isBinCoproduct C X Y (X ++ Y) inl inr.
    Proof.
      use isBinCoproduct_BinCoproduct.
    Qed.

    Definition hss_from_omega_signature_with_strength_iter_functor : C ⟶ C
      := BinCoproduct_of_functors _ _ Copr (constant_functor _ _ I_{C}) H.
    
    Goal ∏ c, hss_from_omega_signature_with_strength_iter_functor c = I_{C} ++ H c.
    Proof.
      intro; use idpath.
    Qed.

    Lemma hss_from_omega_signature_with_strength_iter_functor_omega_cocont
      : is_omega_cocont hss_from_omega_signature_with_strength_iter_functor.
    Proof.
      use is_omega_cocont_BinCoproduct_of_functors.
      - use is_omega_cocont_constant_functor.
      - use H_cocont.
    Qed.

    Let Fchain := initChain O hss_from_omega_signature_with_strength_iter_functor.
    Variable (CC : ColimCocone Fchain).

    Let f : (I_{C} ++ H (colim CC)) --> colim CC
      := colim_algebra_mor _ hss_from_omega_signature_with_strength_iter_functor_omega_cocont CC.

    Let η : I_{C} --> colim CC := inl · f.
    Let r : H (colim CC) --> colim CC := inr · f.

    Definition hss_from_omega_signature_with_strength_data
      : heterogeneous_substitution_system_data θ
      := (colim CC ,, η ,, r).

    Section HSS_Law.
      Context (Z : @pointed C) (g : (Z : C) --> colim CC).
      
      Local Definition tens_copr {A B : C}
        : BinCoproduct (A ⊗ Z) (B ⊗ Z)
        := (make_BinCoproduct _ _ _ _ _ _ (tens_bincopr Z _ _ (A ++ B) _ _ iscopr)).

      Local Definition Ψ (A : C) (h : A ⊗ Z --> colim CC)
        : (I_{C} ++ H A) ⊗ Z --> colim CC.
      Proof.
        refine (_ · _ · _).
        - refine (BinCoproductOfArrows _ tens_copr (Copr _ _) lu^{C}_{_} (θ _ _)).
        - refine (BinCoproductOfArrows _ _ (Copr _ _) (identity _) (#H h)).
        - refine (BinCoproductArrow _ g r).
      Defined.

      Local Lemma Ψ_inl (A : C) (h : A ⊗ Z --> colim CC)
        : BinCoproductIn1 tens_copr · Ψ _ h = lu^{C}_{_} · g.
      Proof.
        unfold Ψ; do 2 rewrite assoc; etrans.
        { refine (maponpaths (λ x, x · _ · _) _); use (BinCoproductOfArrowsIn1 _ tens_copr). }
        do 2 rewrite <- assoc; use maponpaths; rewrite assoc.
        etrans.
        { refine (maponpaths (λ x, x · _) _); use BinCoproductOfArrowsIn1. }
        rewrite id_left.
        use BinCoproductIn1Commutes.
      Qed.

      Local Lemma Ψ_inr (A : C) (h : A ⊗ Z --> colim CC)
        : BinCoproductIn2 tens_copr · Ψ _ h = θ _ _ · #H h · r.
      Proof.
        unfold Ψ; do 2 rewrite assoc; etrans.
        { refine (maponpaths (λ x, x · _ · _) _); use (BinCoproductOfArrowsIn2 _ tens_copr). }
        do 3 rewrite <- assoc; use maponpaths; rewrite assoc.
        etrans.
        { refine (maponpaths (λ x, x · _) _); use BinCoproductOfArrowsIn2. }
        rewrite <- assoc; use maponpaths.
        use BinCoproductIn2Commutes.
      Qed.

      Local Lemma Ψ_nat (A B : C) (h : A ⊗ Z --> colim CC) (u : B --> A)
        : Ψ _ (u ⊗r Z · h) = (#hss_from_omega_signature_with_strength_iter_functor u) ⊗r Z · Ψ _ h.
      Proof.
        use (BinCoproductArrowsEq _ _ _ tens_copr).
        - rewrite assoc, Ψ_inl.
          cbn; symmetry; etrans.
          {
            refine (maponpaths (λ x, x · _) (!_ @ (maponpaths _ _))).
            + use (bifunctor_rightcomp C).
            + use BinCoproductOfArrowsIn1. 
          }
          rewrite bifunctor_rightcomp.
          etrans; [|use (Ψ_inl _ h)].
          use (maponpaths (λ x, x · _)).
          cbn; now rewrite @tensor_mor_right, tensor_id_id, id_left.
        - rewrite assoc, Ψ_inr, functor_comp, assoc, (signature_with_strength_nat_left _ θ).
          cbn; symmetry; etrans.
          {
            refine (maponpaths (λ x, x · _) (!_ @ (maponpaths _ _))).
            + use (bifunctor_rightcomp C).
            + use BinCoproductOfArrowsIn2. 
          }
          rewrite bifunctor_rightcomp.
          do 3 rewrite <- assoc; use maponpaths; rewrite assoc.
          use (Ψ_inr _ h).
      Qed.

      Definition hss_from_omega_signature_with_strength_arrow
        : colim CC ⊗ Z --> colim CC
        := mendler_iteration_arrow 
            hss_from_omega_signature_with_strength_iter_functor
            _ (tens_cocont Z) (tens_init Z) O (colim CC)
            Ψ Ψ_nat CC.

      Lemma hss_from_omega_signature_with_strength_arrow_unit
        : heterogeneous_substitution_system_law_eq_unit θ 
          hss_from_omega_signature_with_strength_data _ g
          hss_from_omega_signature_with_strength_arrow.
      Proof.
        unfold heterogeneous_substitution_system_law_eq_unit; cbn.
        rewrite <- (Ψ_inl (colim CC) hss_from_omega_signature_with_strength_arrow).
        symmetry; etrans.
        { refine (maponpaths _ _); use (mendler_iteration_arrow_commutes _ _ 
              hss_from_omega_signature_with_strength_iter_functor_omega_cocont _ (tens_init Z)). }
        rewrite assoc; fold hss_from_omega_signature_with_strength_arrow.
        cbn; unfold η; now rewrite (bifunctor_rightcomp C).
      Qed.
      
      Lemma hss_from_omega_signature_with_strength_arrow_out
        : heterogeneous_substitution_system_law_eq_out θ
          hss_from_omega_signature_with_strength_data Z
          hss_from_omega_signature_with_strength_arrow.
      Proof.
        unfold heterogeneous_substitution_system_law_eq_out; cbn.
        rewrite <- (Ψ_inr (colim CC) hss_from_omega_signature_with_strength_arrow).
        symmetry; etrans.
        { refine (maponpaths _ _); use (mendler_iteration_arrow_commutes _ _ 
              hss_from_omega_signature_with_strength_iter_functor_omega_cocont _ (tens_init Z)). }
        rewrite assoc; fold hss_from_omega_signature_with_strength_arrow.
        unfold r; now rewrite (bifunctor_rightcomp C).
      Qed.


      (* Uniqueness *)

      Context (triple : ∑ (h' : colim CC ⊗ Z --> colim CC),
        heterogeneous_substitution_system_law_eq θ 
        hss_from_omega_signature_with_strength_data Z g h').

      Let h' : colim CC ⊗ Z --> colim CC := pr1 triple.

      Let hyp_unit : heterogeneous_substitution_system_law_eq_unit θ
        hss_from_omega_signature_with_strength_data Z g h' 
        := pr12 triple.

      Let hyp_out : heterogeneous_substitution_system_law_eq_out θ
        hss_from_omega_signature_with_strength_data Z h'
        := pr22 triple.

      Lemma hss_from_omega_signature_with_strength_arrow_unique
        : h' = hss_from_omega_signature_with_strength_arrow.
      Proof.
        symmetry; use (mendler_iteration_unique _ _ hss_from_omega_signature_with_strength_iter_functor_omega_cocont _ (tens_init Z)).
        cbn; fold f.
        use (BinCoproductArrowsEq _ _ _ tens_copr); rewrite assoc; cbn.
        - etrans.
          { refine (!maponpaths (λ x, x · _) _); use (bifunctor_rightcomp C). }
          refine (hyp_unit @ !_); use Ψ_inl. 
        - etrans.
          { refine (!maponpaths (λ x, x · _) _); use (bifunctor_rightcomp C). }
          refine (hyp_out @ !_); use Ψ_inr. 
      Qed.

      Lemma hss_from_omega_signature_with_strength_arrow_unique_triple
        : triple =  hss_from_omega_signature_with_strength_arrow ,,
                    hss_from_omega_signature_with_strength_arrow_unit ,,
                    hss_from_omega_signature_with_strength_arrow_out.
      Proof.
        use invmap; [|use path_sigma_hprop|].
        use isapropdirprod; use homset_property.
        use hss_from_omega_signature_with_strength_arrow_unique.
      Qed.
    End HSS_Law.

    Lemma hss_from_omega_signature_with_strength_law
      : heterogeneous_substitution_system_law θ hss_from_omega_signature_with_strength_data.
    Proof.
      intros Z g.
      use tpair.
      - use tpair; [|split].
        + exact (hss_from_omega_signature_with_strength_arrow Z g).
        + use hss_from_omega_signature_with_strength_arrow_unit.
        + use hss_from_omega_signature_with_strength_arrow_out.
      - use hss_from_omega_signature_with_strength_arrow_unique_triple.
    Defined.


    Definition hss_from_omega_signature_with_strength
      : heterogeneous_substitution_system θ
      := hss_from_omega_signature_with_strength_data ,,
         hss_from_omega_signature_with_strength_law.

  End BuildingAnHSS.
End HeterogeneousSubstitutionSystem.
