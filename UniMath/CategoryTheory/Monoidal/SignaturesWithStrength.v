
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
Require Import UniMath.CategoryTheory.Monoidal.TotalCategoriesOfRModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.DisplayedSections.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.

Require Import UniMath.CategoryTheory.coslicecat.

Require Import UniMath.CategoryTheory.Chains.All.

Import BifunctorNotations.
Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope mor_disp.


Section SignaturesWithStrength.
  Context {C : monoidal_cat}.

  Local Notation "x ⊗l f" := (x ⊗^{C}_{l} f) (at level 31).
  Local Notation "f ⊗r y" := (f ⊗^{C}_{r} y) (at level 31).

  (* A Pointed Object is given by Z ∈ C and I --> Z in C *)
  Definition pointed : category := coslice_cat C I_{C}.

  Coercion pointed_to_ob (aA : pointed): C := pr1 aA.
  Coercion pointed_to_mor (aA : pointed): I_{C} --> aA := pr2 aA.
  Coercion pointed_mor_to_mor {aA bB : pointed} (f : aA --> bB) : C⟦aA, bB⟧ := pr1 f.

  Definition pointed_unit : pointed := I_{C} ,, identity _.

  Definition pointed_prod (aA bB : pointed) : pointed
    := (aA ⊗ bB ,, luinv^{C}_{_} · aA #⊗ bB).

  Section FixAnEndofunctor.
    Context (H : C ⟶ C).

    Definition strength_for_signature_data
      := ∏(A : C) (bB : pointed), H A ⊗ bB --> H (A ⊗ bB).

    Section FixAStrength.
      Context (θ : strength_for_signature_data).

      Definition strength_for_signature_law_nat
        := ∏ (A A' : C) (f : A --> A')
             (bB bB' : pointed) (g : bB --> bB'),
             θ A bB · #H (f #⊗ g) = #H f #⊗ g · θ A' bB'.
           
      Definition strength_for_signature_law_prod
        := ∏ (A : C) (bB cC : pointed), 
          θ A (pointed_prod bB cC) = αinv^{C}_{_,_,_} · θ A bB ⊗r cC · θ (A ⊗ bB) cC · #H α^{C}_{_,_,_}.

      Definition strength_for_signature_law_unit
        := ∏(A : C), θ A pointed_unit = ru^{C}_{_} · #H ruinv^{C}_{_}.

      Definition strength_for_signature_laws
        := strength_for_signature_law_prod 
           × strength_for_signature_law_unit
           × strength_for_signature_law_nat. 

      Lemma isaprop_strength_for_signature_laws
        : isaprop strength_for_signature_laws.
      Proof.
        repeat use isapropdirprod; repeat (use impred; intro); use homset_property.
      Qed.
    End FixAStrength.

    Definition strength_for_signature
      := ∑ (θ : strength_for_signature_data), strength_for_signature_laws θ. 

    Definition make_strength_for_signature 
      (θ: ∏(A : C) (bB : pointed), H A ⊗ bB --> H (A ⊗ bB))
      (H_unit : ∏(A : C), θ A pointed_unit = ru^{C}_{_} · #H ruinv^{C}_{_})
      (H_prod : ∏ (A : C) (bB cC : pointed), 
          θ A (pointed_prod bB cC) = αinv^{C}_{_,_,_} · θ A bB ⊗r cC · θ (A ⊗ bB) cC · #H α^{C}_{_,_,_})
      (H_nat : ∏ (A A' : C) (f : A --> A') (bB bB' : pointed) (g : bB --> bB'),
             θ A bB · #H (f #⊗ g) = #H f #⊗ g · θ A' bB')
      : strength_for_signature
      := θ ,, H_prod ,, H_unit ,, H_nat. 
  End FixAnEndofunctor.

  Definition strength_for_signature_to_data {H : C ⟶ C} 
    (θ : strength_for_signature H) 
    : strength_for_signature_data H
    := pr1 θ.

  Definition strength_for_signature_to_data_func {H : C ⟶ C} 
    (θ : strength_for_signature H) 
    : ∏(A : C) (bB : pointed), H A ⊗ bB --> H (A ⊗ bB)
    := strength_for_signature_to_data θ.

  Coercion strength_for_signature_to_data_func
    : strength_for_signature >-> Funclass.

  Definition signature_with_strength_prod
    (H : C ⟶ C) (θ : strength_for_signature H) (A : C) (bB cC : pointed)
      : θ A (pointed_prod bB cC) = αinv^{C}_{_,_,_} · θ A bB ⊗r cC · θ (A ⊗ bB) cC · #H α^{C}_{_,_,_}
      := pr12 θ A bB cC.

  Definition signature_with_strength_unit
    (H : C ⟶ C) (θ : strength_for_signature H) (A : C)
      : θ A pointed_unit = ru^{C}_{_} · #H ruinv^{C}_{_}
      := pr122 θ A.

  Definition signature_with_strength_nat
    (H : C ⟶ C) (θ : strength_for_signature H) 
    (A A' : C) (bB bB' : pointed)
    (f : A --> A') (g : bB --> bB')
      : θ A bB · #H (f #⊗ g) = #H f #⊗ g · θ A' bB'
      := pr222 θ A A' f bB bB' g.

  Lemma signature_with_strength_nat_left
    (H : C ⟶ C) (θ : strength_for_signature H) 
    (A A' : C) (bB : pointed) (f : A --> A')
      : θ A bB · #H (f ⊗r bB) = #H f ⊗r bB · θ A' bB.
  Proof.
    etrans; [etrans|]; swap 1 2.
    - use (signature_with_strength_nat _ θ _ _ _ _ f (identity _)).
    - do 2 use maponpaths; use tensor_mor_right.
    - use (maponpaths (λ x, x · _)); symmetry; use tensor_mor_right.
  Qed.

  Lemma signature_with_strength_nat_right
    (H : C ⟶ C) (θ : strength_for_signature H) 
    (A : C) (bB bB' : pointed) (g : bB --> bB')
      : θ A bB · #H (A ⊗l g) = H A ⊗l g · θ A bB'.
  Proof.
    etrans; [etrans|]; swap 1 2.
    - use (signature_with_strength_nat _ θ _ _ _ _ (identity _) g).
    - do 2 use maponpaths; use tensor_mor_left.
    - use (maponpaths (λ x, x · _)); now rewrite functor_id, tensor_mor_left.
  Qed.

  Section FixANatTrans.
    Context (H H' : C ⟶ C).
    Context (θ : strength_for_signature H).
    Context (θ' : strength_for_signature H').
    Context (h : H ⟹ H'). 

    Definition is_a_morphism_of_signatures_with_strength
      := ∏ (A : C) (bB : pointed),
          θ A bB · h (A ⊗ bB) = h A ⊗r bB · θ' A bB.
    
    Lemma isaprop_is_a_morphism_of_signatures_with_strength :
      isaprop is_a_morphism_of_signatures_with_strength.
    Proof.
      do 2 (use impred; intro); use homset_property.
    Qed.

  End FixANatTrans.

  Definition strength_for_signature_disp_cat_ob_mor
    : disp_cat_ob_mor [C, C].
  Proof.
    use tpair.
    - use strength_for_signature.
    - use is_a_morphism_of_signatures_with_strength.
  Defined.

  Lemma strength_for_signature_disp_cat_id_comp
    : disp_cat_id_comp [C,C] strength_for_signature_disp_cat_ob_mor.
  Proof.
    split.
    - intros H θ A bB; cbn.
      now rewrite tensor_mor_right, tensor_id_id, id_left, id_right.
    - cbn; intros H H' H'' h h' θ θ' θ'' hyp hyp' A bB.
      unfold nat_trans_comp; cbn.
      transitivity (h A ⊗r bB · θ' A bB  · h' (A ⊗ bB)).
      + rewrite assoc; use (maponpaths (λ x, x · _)); use hyp.
      + rewrite (bifunctor_rightcomp C), <- assoc, <- assoc.
        use maponpaths; use hyp'.
  Qed.

  Definition strength_for_signature_disp_cat_data : disp_cat_data [C, C]
    := strength_for_signature_disp_cat_ob_mor ,, 
        strength_for_signature_disp_cat_id_comp.

  Lemma strength_for_signature_disp_cat_axioms 
    : disp_cat_axioms _ strength_for_signature_disp_cat_data.
  Proof.
    repeat split; intros.
    1-3: use proofirrelevance.
    4: use isasetaprop.
    all: use isaprop_is_a_morphism_of_signatures_with_strength.
  Qed.

  Definition strength_for_signature_disp_cat : disp_cat [C,C] 
    := strength_for_signature_disp_cat_data ,,
        strength_for_signature_disp_cat_axioms.

  Definition signature_with_strength_cat : category
    := total_category strength_for_signature_disp_cat.

  Coercion strength_for_signature_to_signature_with_strength 
    {H : C ⟶ C} (θ : strength_for_signature H) 
    : signature_with_strength_cat := H ,, θ.


  Definition trivial_signature_with_strength
    : strength_for_signature (functor_identity C).
  Proof.
    use make_strength_for_signature; intros; cbn.
    - use identity.
    - abstract (exact (!pr1 (monoidal_rightunitorisolaw C _))).
    - abstract (
        rewrite id_right, tensor_mor_right, tensor_id_id, id_right;
        exact (!pr2 (monoidal_associatorisolaw C _ _ _))
      ).
    - abstract (now rewrite id_right, id_left).
  Defined.

  Section ProductSignatureWithStrength.
    Context (H : C ⟶ C) (θ : strength_for_signature H) (D : C). 

    Definition product_signature_functor : C ⟶ C
      := H ∙ bifunctor_to_functorintoendofunctorcat C D.

    Goal ∏ (A : C), product_signature_functor A = D ⊗ H A.
    Proof.
      exact (λ _, idpath _).
    Qed.

    Definition product_signature_strength_mor (A : C) (bB : pointed) 
      : D ⊗_{ C} H A ⊗ bB --> D ⊗_{ C} H (A ⊗ bB)
      := α^{C}_{_,_,_} · D ⊗l θ A bB.

    Lemma product_signature_strength_law_id (A : C)
      : α^{ C }_{ D, H A, I_{ C}} · D ⊗^{ C}_{l} θ A pointed_unit
        = ru^{ C }_{ D ⊗_{ C} H A} · D ⊗^{ C}_{l} # H ruinv^{ C }_{ A}.
    Proof.
      etrans.
      - refine (maponpaths (λ x, _ · D ⊗l x) _).
        use signature_with_strength_unit.
      - rewrite (bifunctor_leftcomp C), assoc; use (maponpaths (λ x, x · _)).
        use left_whisker_with_runitor.
    Qed.

    Lemma product_signature_strength_law_prod (A : C) (bB cC : pointed)
      : α^{ C }_{ D, H A, bB ⊗ cC} · D ⊗^{ C}_{l} θ A (pointed_prod bB cC) =
        αinv^{ C }_{ D ⊗_{ C} H A, bB, cC}
        · (α^{ C }_{ D, H A, bB} · D ⊗^{ C}_{l} θ A bB) ⊗^{ C}_{r} cC
        · (α^{ C }_{ D, H (A ⊗ bB), cC} · D ⊗^{ C}_{l} θ (A ⊗ bB) cC)
        · D ⊗^{ C}_{l} # H α^{ C }_{ A, bB, cC}.
    Proof.
      rewrite assoc, (bifunctor_rightcomp C), assoc.
      symmetry; etrans; etrans; symmetry; cycle 3.
      - refine (maponpaths (λ x, _ · D ⊗l x) _).
        use signature_with_strength_prod.
      - refine (maponpaths (λ x, x · _ · _) _).
        rewrite <- assoc; refine (maponpaths _ _).
        use monoidal_associatornatleftright.
      - rewrite assoc; refine (maponpaths (λ x, x · _ · _ · _) _);
        rewrite <- assoc; refine (maponpaths (λ x, _ · x) _).
        rewrite <- id_right; refine (maponpaths (λ x, _ · x) _).
        eassert (_ ⊗l α^{C}_{_,_,_} · _ ⊗l αinv^{C}_{_,_,_} = identity _) as hyp
        by now rewrite <- (bifunctor_leftcomp C), 
          (pr1 (monoidal_associatorisolaw C _ _ _)),
          @tensor_mor_left, tensor_id_id.
        use hyp.
      - do 3 rewrite (bifunctor_leftcomp C), assoc, assoc.
        do 4 use (maponpaths (λ x, x · _)); etrans; swap 1 2.
        + do 2 rewrite <- assoc; refine (maponpaths _ _); rewrite assoc.
          use (!monoidal_pentagonidentity C _ _ _ _).
        + symmetry; rewrite <- id_left, assoc; symmetry.
          use (maponpaths (λ x, x · _)).
          use (!pr2 (monoidal_associatorisolaw C _ _ _)).
    Qed.


    Lemma product_signature_strength_law_nat (A A' : C) (f : C ⟦ A, A' ⟧) 
      (bB bB' : pointed) (g : bB --> bB')
      : α^{ C }_{ D, H A, bB} · D ⊗^{ C}_{l} θ A bB · D ⊗^{ C}_{l} # H (f #⊗ g) 
      = (D ⊗^{ C}_{l} # H f) #⊗ g · (α^{ C }_{ D, H A', bB'} · D ⊗^{ C}_{l} θ A' bB').
    Proof.
      rewrite assoc; etrans.
      - rewrite <- assoc, <- (bifunctor_leftcomp C); do 2 refine (maponpaths _ _).
        use signature_with_strength_nat.
      - rewrite bifunctor_leftcomp, assoc; use (maponpaths (λ x, x · _)).
        do 2 rewrite @tensor_mor_left; symmetry; use tensor_lassociator.
    Qed.


    Definition product_signature_strength
      : strength_for_signature product_signature_functor.
    Proof.
      use make_strength_for_signature.
      - use product_signature_strength_mor.
      - use product_signature_strength_law_id.
      - use product_signature_strength_law_prod.
      - use product_signature_strength_law_nat.
    Defined.

  End ProductSignatureWithStrength.

  Section ToModuleSignatures.

    Section FixASignatureWithStrength.
      Context (H : C ⟶ C) (θ : strength_for_signature H).


      Section FixAMonoid.
        Context (R : MON C).

        Let HR : C := H (pr1 R).
        Let R_η : pointed := _ ,, η (pr1 R) (pr2 R). 
        Let RR_η : pointed := pointed_prod R_η R_η.

        Local Definition pointed_monoid_unit : pointed ⟦ pointed_unit, R_η ⟧
          := η (pr1 R) (pr2 R) ,, id_left _.

        Local Lemma pointed_multiplication_lemma 
          : luinv^{ C }_{ I_{ C}} 
            · η (pr1 R) (pr2 R) #⊗ η (pr1 R) (pr2 R)
            · μ (pr1 R) (pr2 R) 
            = η (pr1 R) (pr2 R).
        Proof.
          rewrite tensor_split, <- tensor_mor_left, <- tensor_mor_right, assoc.
          etrans; [etrans|].
          - refine (maponpaths (λ x, x · _ · _) _); use monoidal_leftunitorinvnat.
          - rewrite <- assoc; refine (maponpaths _ _); use monoid_to_unit_left_law.
          - rewrite <- id_right, <- assoc; use maponpaths.
            use (pr2 (monoidal_leftunitorisolaw C _)).
        Qed.

        Local Definition pointed_multiplication : pointed ⟦ RR_η, R_η ⟧
          := μ _ _ ,, pointed_multiplication_lemma.

        Local Definition HR_module_subst : HR ⊗ (pr1 R) --> HR
          := θ (pr1 R) R_η  · #H (μ (pr1 R) (pr2 R)).

        Local Lemma HR_module_subst_assoc
          : module_laws_assoc (pr1 R) (pr2 R) HR_module_subst.
        Proof.
          unfold module_laws_assoc, HR_module_subst.
          do 2 rewrite assoc; rewrite (bifunctor_rightcomp C).
          etrans; etrans.
          - do 2 rewrite <- assoc; refine (maponpaths _ _).
            rewrite assoc; refine (maponpaths (λ x, x · _) _).
            use (!signature_with_strength_nat_right _ θ _ _ _ pointed_multiplication).
          - cbn; do 2 rewrite assoc; refine (maponpaths (λ x, _ · x · _ · _) _).
            use (signature_with_strength_prod _ _ _ R_η R_η).
          - do 3 rewrite assoc.
            rewrite (pr1 (monoidal_associatorisolaw C _ _ _)), id_left.
            do 2 rewrite <- assoc; refine (maponpaths _ _).
            rewrite assoc, <- functor_comp; etrans.
            + use (!functor_comp _ _ _).
            + refine (maponpaths _ _); use monoid_to_assoc_law.
          - rewrite functor_comp, assoc; use (maponpaths (λ x, x · _)).
            repeat rewrite <- assoc; use maponpaths.
            use signature_with_strength_nat_left.
        Qed.

        Local Lemma HR_module_subst_unit
          : module_laws_unit (pr1 R) (pr2 R) HR_module_subst.
        Proof.
          unfold module_laws_unit, HR_module_subst; cbn.
          rewrite assoc; etrans; etrans.
          - refine (maponpaths (λ x, x · _) _);
            use (!signature_with_strength_nat_right _ _ _ _ _ pointed_monoid_unit).
          - rewrite <- assoc. refine (maponpaths _ (!functor_comp _ _ _)).
          - do 2 refine (maponpaths _ _); use monoid_to_unit_right_law.
          - rewrite signature_with_strength_unit, <- id_right, <- assoc.
            use maponpaths.
            refine (!functor_comp H _ _ @ maponpaths _ _ @ functor_id _ _).
            use (pr2 (monoidal_rightunitorisolaw C _)).
        Qed.

        Local Definition module_for_HR : module (pr1 R) (pr2 R) HR
          := make_module _ _ _ HR_module_subst_unit HR_module_subst_assoc.

      End FixAMonoid.

      Section FixAMonoidMorphism.
        Context (R R' : MON C) (r : R --> R').

        Let HR : C := H (pr1 R).
        Let HR' : C := H (pr1 R').
        Let Hr : HR --> HR' := #H (pr1 r).

        Local Definition pointed_monoid_mor_unit
          : pointed ⟦ pr1 R,, η _ (pr2 R), pr1 R',, η _ (pr2 R') ⟧
          := pr1 r ,, pr22 r.

        Local Lemma Hr_is_module_morphism
          : is_module_mor _ _ (module_for_HR R)
            (pullback_functor_funct _ (module_for_HR R') _ (pr2 r)) Hr.
        Proof.
          unfold is_module_mor, pullback_functor_funct; cbn.
          unfold HR_module_subst, Hr; cbn.
          do 2 rewrite assoc.
          symmetry; etrans.
          - rewrite <- assoc, <- functor_comp;
            do 2 refine (maponpaths _ _); use (!pr12 r).
          - rewrite functor_comp, assoc; refine (maponpaths (λ x, x · _) _).
            use (signature_with_strength_nat _ _ _ _ _ _ _ pointed_monoid_mor_unit).
        Qed.
      End FixAMonoidMorphism.

      Definition to_module_signatures_data
        : @module_signature_data C.
      Proof.
        use tpair.
        - exact (λ R, _ ,, module_for_HR R).
        - exact (λ R R' r, _ ,, Hr_is_module_morphism _ _ r).
      Defined.

      Lemma to_module_signatures_axioms
        : module_signature_axioms to_module_signatures_data.
      Proof.
        split; intros; cbn.
        - use invmap; [|use path_sigma_hprop|].
          use isaprop_is_module_mor.
          use functor_id.
        - use invmap; [|use path_sigma_hprop|].
          use isaprop_is_module_mor.
          use functor_comp.
      Qed.

      Definition to_module_signatures
        : @module_signature_cat C
        := to_module_signatures_data ,, to_module_signatures_axioms.
    End FixASignatureWithStrength.

    Section FixAMorphismOfSignaturesWithStrength.
      Context (H : C ⟶ C) (θ : strength_for_signature H).
      Context (H' : C ⟶ C) (θ' : strength_for_signature H').
      Context (h : signature_with_strength_cat⟦ H ,, θ, H' ,, θ'⟧).

      Lemma hR_is_module_morphism (R : MON C)
        : is_module_mor _ _ (module_for_HR H θ R) 
          (pullback_functor_funct _ (module_for_HR H' θ' R) _ (id_disp (pr2 R)))
          ((pr11 h) (pr1 R)).
      Proof.
        unfold is_module_mor, pullback_functor_funct; cbn.
        unfold HR_module_subst; cbn.
        do 2 rewrite assoc.
        etrans; [etrans|].
        - refine (maponpaths (λ x, x · _ · _) _).
          now rewrite tensor_mor_left, tensor_id_id, id_right.
        - refine (maponpaths (λ x, x · _) (!pr2 h _ (_ ,, η _ _))).
        - do 2 rewrite <- assoc; refine (!maponpaths _ _); use (pr21 h).
      Qed.

      Definition to_module_signatures_funct
        : to_module_signatures H θ --> to_module_signatures H' θ'.
      Proof.
        exists (λ R, _ ,, hR_is_module_morphism R).
        abstract (
          intros R R' r;
          use invmap; [|use path_sigma_hprop|];
          [ use isaprop_is_module_mor
          | unfold mor_disp;
            cbn; rewrite transportf_total2;
            cbn; rewrite transportf_const;
            use (pr21 h)
          ]
        ).
      Defined.
    End FixAMorphismOfSignaturesWithStrength.

    Definition signature_with_strength_to_module_signatures_data
      : functor_data signature_with_strength_cat (@module_signature_cat C).
    Proof.
      use tpair.
      - intros (H , θ); use (to_module_signatures H θ).
      - intros (H , θ) (H' , θ') h. 
        use to_module_signatures_funct.
        exact h.
    Defined.

    Lemma signature_with_strength_to_module_signatures_is_functor
      : is_functor signature_with_strength_to_module_signatures_data.
    Proof.
      split.
      - intros H.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_section_nat_trans_disp_axioms.
        use funextsec; intro.
        use invmap; [|use path_sigma_hprop|easy].
        use isaprop_is_module_mor.
      - intros H H' H'' f g.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_section_nat_trans_disp_axioms.
        use funextsec; intro.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_module_mor.
        cbn; unfold mor_disp.
        cbn; rewrite transportf_total2.
        cbn; now rewrite transportf_const.
    Qed.

    Definition signature_with_strength_to_module_signatures
      : signature_with_strength_cat ⟶ module_signature_cat
      := signature_with_strength_to_module_signatures_data ,,
      signature_with_strength_to_module_signatures_is_functor.


    Proposition signature_with_strength_to_module_signatures_trivial
      : signature_with_strength_to_module_signatures
        trivial_signature_with_strength
        = trivial_signature.
    Proof.
      use module_signature_equality.
      - intro. use total2_paths_f.
        + use idpath.
        + abstract (
            use invmap; [|use path_sigma_hprop|use id_left]; 
            use isaprop_module_laws
          ).
      - intros; etrans.
        + refine (maponpaths _ _); use transportf_total2_paths_f.
        + use (transportf_total2_paths_f (λ x, x --> _)).
    Qed.

    Proposition signature_with_strength_to_module_signatures_product
      (H : C ⟶ C) (θ : strength_for_signature H) (D : C)
      : signature_with_strength_to_module_signatures (product_signature_strength H θ D)
        = product_signature (signature_with_strength_to_module_signatures θ) D.
    Proof.
      use module_signature_equality.
      - intro; use total2_paths_f.
        + use idpath.
        + abstract (
            use invmap; [|use path_sigma_hprop|];
            [ use isaprop_module_laws
            | cbn; unfold HR_module_subst;
              now rewrite (bifunctor_leftcomp C), assoc ]
          ).
      - intros; etrans.
        + refine (maponpaths _ _); use transportf_total2_paths_f.
        + use (transportf_total2_paths_f (λ x, x --> _)).
    Qed.
  End ToModuleSignatures.

  Let forgetful : signature_with_strength_cat ⟶ [C, C]
    := pr1_category _.

  Section Limits.
    Context {g : graph}.
    Context (lims_g : Lims_of_shape g C).
    Context (F : diagram g signature_with_strength_cat).
    Let F' := mapdiagram forgetful F.

    Definition limit_sig_functor_cone : LimCone F'
      := LimsFunctorCategory_of_shape g C _ lims_g _.

    Definition limit_sig_functor : C ⟶ C 
      := lim limit_sig_functor_cone.

    Lemma limit_sig_strength_forms_cone (A : C) (bB : pointed)
      : forms_cone (diagram_pointwise F' (A ⊗ bB)) (λ v, 
        limOut (lims_g (diagram_pointwise F' A)) v ⊗r bB · (pr12 (dob F v)) A bB).
    Proof.
      intros u v e; cbn; etrans.
      - rewrite <- assoc; refine (maponpaths _ (pr2 (dmor F e) _ _)).
      - rewrite assoc, <- (bifunctor_rightcomp C).
        use (maponpaths (λ x, x ⊗r _ · _) _).
        use limOutCommutes.
    Qed.

    Definition limit_sig_strength_data
      : strength_for_signature_data limit_sig_functor.
    Proof.
      intros A bB; use limArrow.
      use make_cone; [|use limit_sig_strength_forms_cone].
    Defined.

    Lemma limit_sig_strength_nat
      : strength_for_signature_law_nat _ limit_sig_strength_data.
    Proof.
      do 6 intro.
      use arr_to_LimCone_eq; intro u; cbn.
      symmetry; etrans; etrans; cycle 3; symmetry. 4: etrans.
      - rewrite <- assoc. refine (maponpaths _ _).
        use (limOfArrowsOut _ _ 
          (lims_g (diagram_pointwise F' _)) 
          (lims_g (diagram_pointwise F' _))).
      - rewrite <- assoc; refine (!maponpaths _ _).
        use (limArrowCommutes (lims_g (diagram_pointwise F' _))).
      - cbn; unfold LimFunctor_mor.
        rewrite tensor_split, <- tensor_mor_right, <- assoc; refine (maponpaths _ _).
        rewrite assoc; refine (maponpaths (λ x, x · _) _).
        etrans; [|use (bifunctor_rightcomp C _ _ _ _ _ _)].
        refine (!maponpaths (λ x, x ⊗r bB') _).
        use (limOfArrowsOut _ _ 
          (lims_g (diagram_pointwise F' _)) 
          (lims_g (diagram_pointwise F' _))).
      - cbn; rewrite assoc; refine (maponpaths (λ x, x · _) _).
        use (limArrowCommutes (lims_g (diagram_pointwise F' _))).
      - rewrite assoc, (bifunctor_rightcomp C), assoc, <- tensor_mor_left.
        unfold LimFunctor_ob; cbn; etrans.
        + rewrite <- assoc; refine (maponpaths _ _).
          use signature_with_strength_nat.
        + rewrite assoc; refine (maponpaths (λ x, x · _) _); etrans.
          * rewrite tensor_mor_right; symmetry; use tensor_comp_r_id_l.
          * now rewrite tensor_split, <- tensor_mor_left, <- tensor_mor_right, (bifunctor_rightcomp C), assoc.
    Qed.


    Lemma limit_sig_strength_unit
      : strength_for_signature_law_unit _ limit_sig_strength_data.
    Proof.
      intro.
      use arr_to_LimCone_eq; intro u; cbn.
      etrans; etrans; swap 2 4.
      - use (limArrowCommutes (lims_g (diagram_pointwise F' _))).
      - rewrite <- assoc; refine (!maponpaths _ _).
        use (limOfArrowsOut _ _ 
          (lims_g (diagram_pointwise F' _)) 
          (lims_g (diagram_pointwise F' _))).
      - cbn; rewrite assoc; refine (maponpaths (λ x, x · _) _).
        use monoidal_rightunitornat.
      - cbn; rewrite <- assoc; use maponpaths.
        use signature_with_strength_unit.
    Qed.

    Lemma limit_sig_strength_prod
      : strength_for_signature_law_prod _ limit_sig_strength_data.
    Proof.
      do 3 intro; use arr_to_LimCone_eq; intro u; cbn; symmetry.
      etrans; [etrans; etrans|etrans]; symmetry; cycle 5.
      - use (limArrowCommutes (lims_g (diagram_pointwise F' _))).
      - rewrite <- assoc; refine (!maponpaths _ _).
        use (limOfArrowsOut _ _ 
          (lims_g (diagram_pointwise F' _)) 
          (lims_g (diagram_pointwise F' _))).
      - cbn; rewrite <- assoc; refine (!maponpaths _ _).
        rewrite assoc; refine (maponpaths (λ x, x · _) _).
        use (limArrowCommutes (lims_g (diagram_pointwise F' _))).
      - cbn; rewrite <- assoc; refine (!maponpaths _ _).
        rewrite assoc; refine (maponpaths (λ x, x · _) _).
        rewrite assoc, <- (bifunctor_rightcomp C).
        refine (maponpaths (λ x, x ⊗r _ · _) _).
        use (limArrowCommutes (lims_g (diagram_pointwise F' _))).
      - cbn. rewrite (bifunctor_rightcomp C); do 3 rewrite assoc.
        refine (maponpaths (λ x, x · _ · _ · _) _).
        use monoidal_associatorinvnatright.
      - cbn; repeat rewrite <- assoc; use maponpaths.
        repeat rewrite assoc; use signature_with_strength_prod.
    Qed.

    Definition limit_sig_strength 
      : strength_for_signature limit_sig_functor.
    Proof.
      use make_strength_for_signature.
      - exact limit_sig_strength_data.
      - exact limit_sig_strength_unit.
      - exact limit_sig_strength_prod.
      - exact limit_sig_strength_nat.
    Defined.


    Definition limit_signature_with_strength : signature_with_strength_cat
      := limit_sig_strength.

    Definition limit_signature_with_strength_out (v : vertex g)
      : pr11 limit_signature_with_strength ⟹ pr11 (dob F v)
      := limOut limit_sig_functor_cone v.

    Lemma limit_signature_with_strength_out_is_mor (v : vertex g)
      : is_a_morphism_of_signatures_with_strength 
        (LimFunctor F' _) _ limit_sig_strength 
        (pr2 (dob F v)) (lim_nat_trans_in_data F' _ v).
    Proof.
      intros A bB; unfold lim_nat_trans_in_data; cbn.
      use (limArrowCommutes (lims_g (diagram_pointwise F' _))).
    Qed.

    Lemma limit_signature_with_strength_cone_is_cone
      : forms_cone F (λ v : vertex g,
           limit_signature_with_strength_out v,,
           limit_signature_with_strength_out_is_mor v).
    Proof.
      intros u v e.
      use invmap; [|use path_sigma_hprop|].
      use isaprop_is_a_morphism_of_signatures_with_strength.
      use limOutCommutes.
    Qed.

    Definition limit_signature_with_strength_cone
      : cone F limit_signature_with_strength
      := make_cone _ limit_signature_with_strength_cone_is_cone.

    Section FixACone.
      Context (H' : C ⟶ C) (θ' : strength_for_signature H').
      Context (cc : cone F (H' ,, θ')).
       
      Definition limit_signature_with_strength_arrow_data
        : H' ⟹ limit_sig_functor
        := limArrow _ _ (mapcone forgetful F cc).

      Lemma limit_signature_with_strength_arrow_is_mor
        : is_a_morphism_of_signatures_with_strength 
          H' limit_sig_functor θ'
          limit_sig_strength limit_signature_with_strength_arrow_data.
      Proof.
        intros A bB; use arr_to_LimCone_eq; intro u; cbn.
        etrans; etrans; swap 2 4.
        - rewrite <- assoc; refine (maponpaths _ _).
          use (limArrowCommutes (lims_g (diagram_pointwise F' _))).
        - rewrite <- assoc; refine (!maponpaths _ _).
          use (limArrowCommutes (lims_g (diagram_pointwise F' _))).
        - cbn; rewrite assoc, <- (bifunctor_rightcomp C).
          refine (!maponpaths (λ x, x ⊗r _ · _) _).
          use (limArrowCommutes (lims_g (diagram_pointwise F' _))).
        - cbn; use (pr2 (coneOut cc u)).
      Qed.

      Definition limit_signature_with_strength_arrow
        : signature_with_strength_cat ⟦ H',, θ', limit_signature_with_strength ⟧
        := limit_signature_with_strength_arrow_data ,,
           limit_signature_with_strength_arrow_is_mor.

      Lemma limit_signature_with_strength_arrow_is_cone_mor
        : is_cone_mor cc limit_signature_with_strength_cone limit_signature_with_strength_arrow.
      Proof.
        intro u.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_a_morphism_of_signatures_with_strength.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_nat_trans; use homset_property.
        use funextsec; intro A.
        use (limArrowCommutes (lims_g (diagram_pointwise F' _))).
      Qed.
      
      Context (f_Hf : 
        ∑(f : signature_with_strength_cat ⟦ H',, θ', limit_signature_with_strength ⟧),
        is_cone_mor cc limit_signature_with_strength_cone f
      ).

      Let f : signature_with_strength_cat ⟦ H',, θ', limit_signature_with_strength ⟧
        := pr1 f_Hf.

      Let Hf : is_cone_mor cc limit_signature_with_strength_cone f
        := pr2 f_Hf.

      Lemma limit_signature_with_strength_arrow_unique
        : f = limit_signature_with_strength_arrow.
      Proof.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_a_morphism_of_signatures_with_strength.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_nat_trans; use homset_property.
        use funextsec; intro A; use limArrowUnique; intro u; cbn.
        exact (maponpaths (λ x, pr11 x A) (Hf u)).
      Qed.

      Lemma limit_signature_with_strength_arrow_unique_pair
        : f_Hf = (_ ,, limit_signature_with_strength_arrow_is_cone_mor).
      Proof.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_cone_mor.
        use limit_signature_with_strength_arrow_unique.
      Qed.

    End FixACone.


    Definition limit_signature_with_strength_cone_is_lim_cone
      : isLimCone F _ limit_signature_with_strength_cone
      := λ _ A, 
        (_ ,, limit_signature_with_strength_arrow_is_cone_mor _ _ A) ,,
        limit_signature_with_strength_arrow_unique_pair _ _ A.


    Definition limit_signature_with_strength_lim_cone : LimCone F.
    Proof.
      use make_LimCone.
      - exact limit_signature_with_strength.
      - exact limit_signature_with_strength_cone.
      - exact limit_signature_with_strength_cone_is_lim_cone.
    Defined.
  End Limits.


  Theorem signature_with_strength_inherits_limits 
    (g : graph) (l : Lims_of_shape g C)
    : Lims_of_shape g signature_with_strength_cat.
  Proof.
    exact (limit_signature_with_strength_lim_cone l).
  Defined.


  Section Colimits.
    Context {g : graph}.
    Context (colims_g : Colims_of_shape g C).
    Context (H_prod : ∏ B : pointed, 
      preserves_colimits_of_shape (rightwhiskering_functor C B) g).
    Context (F : diagram g signature_with_strength_cat).
    Let F' := mapdiagram forgetful F.

    Definition colimit_sig_functor_cocone : ColimCocone F'
      := ColimsFunctorCategory_of_shape g C _ colims_g _.

    Definition colimit_sig_functor : C ⟶ C 
      := colim colimit_sig_functor_cocone.

    Let H (A : C) : C := colimit_sig_functor A.

    (* Colim Cocone for H(A) *)
    Local Definition H_Cocone {A : C}
      : ColimCocone (diagram_pointwise F' A)
      := (colims_g (diagram_pointwise F' A)).

    (* Colim Cocone for H(A) ⊗ B *)
    Local Definition H_Cocone_Prod {A : C} {bB : pointed}
      : ColimCocone (mapdiagram (rightwhiskering_functor C bB)
        (diagram_pointwise F' A))
      := make_ColimCocone _ _ _ (H_prod bB _ _ _ 
        (pr2 (colims_g (diagram_pointwise F' A)))).

    Goal ∏ A bB, colim (@H_Cocone_Prod A bB) = H A ⊗ bB. 
    Proof.
      intros; use idpath.
    Qed.

    Definition colimit_sig_strength_data (A : C) (B : pointed)
      : H A ⊗ B --> H (A ⊗ B).
    Proof.
      use (colimOfArrows H_Cocone_Prod H_Cocone).
      - intro u; use (pr12 (dob F u)).
      - intros u v e; use (!pr2 (dmor F e) _ _).
    Defined.

    Lemma colimit_sig_strength_unit
      : strength_for_signature_law_unit _ colimit_sig_strength_data.
    Proof.
      intro A; use (colimArrowUnique' (H_Cocone_Prod (bB := pointed_unit))).
      intro u; simpl.
      etrans.
      {
        use (colimOfArrowsIn _ _ (H_Cocone_Prod (bB := pointed_unit)) H_Cocone).
      }
      simpl; symmetry; etrans.
      {
        unfold ColimFunctor_mor.
        eassert (colimIn (H_Cocone_Prod (bB := pointed_unit)) u = (colimIn _) u ⊗r I_{C}) by use idpath.
        rewrite X, assoc, monoidal_rightunitornat, <- assoc.
        refine (maponpaths _ _); use (colimOfArrowsIn _ _ H_Cocone).
      }
      cbn. rewrite assoc. refine (!maponpaths (λ x, x · _) _).
      use signature_with_strength_unit.
    Qed.

    Lemma colimit_sig_strength_nat
      : strength_for_signature_law_nat _ colimit_sig_strength_data.
    Proof.
      do 6 intro. use (colimArrowUnique' H_Cocone_Prod).
      intro u; simpl.
      etrans.
      {
        rewrite assoc; refine (maponpaths (λ x, x · _) _).
        use (colimOfArrowsIn _ _ H_Cocone_Prod).
      }
      simpl; symmetry; etrans.
      {
        rewrite tensor_split', <- tensor_mor_left, <- tensor_mor_right, assoc, assoc.
        refine (maponpaths (λ x, x · _ · _) _).
        eassert (colimIn H_Cocone_Prod u = colimIn H_Cocone u ⊗r bB) by use idpath.
        rewrite X.
        etrans; [use (!bifunctor_rightcomp C _ _ _ _ _ _)|]. 
        refine (maponpaths _ _); use (colimOfArrowsIn _ _ H_Cocone H_Cocone).
      }
      simpl; etrans.
      {
        refine (maponpaths (λ x, x · _) _).
        rewrite tensor_mor_right, tensor_mor_left.
        etrans; [use tensor_swap|].
        now rewrite <- tensor_mor_right, <- tensor_mor_left.
      }
      etrans.
      {
        rewrite (bifunctor_rightcomp C), <- assoc, <- assoc.
        do 2 refine (maponpaths _ _).
        use (colimOfArrowsIn _ _ H_Cocone_Prod H_Cocone).
      }
      simpl; symmetry; etrans.
      {
        rewrite <- assoc; refine (maponpaths _ _).
        use (colimOfArrowsIn _ _ H_Cocone).
      }
      simpl; do 3 rewrite assoc.
      use (maponpaths (λ x, x · _) _).
      etrans.
      {
        use signature_with_strength_nat.
      }
      now rewrite tensor_mor_left, tensor_mor_right, tensor_split.
    Qed.
    
    Lemma colimit_sig_strength_prod
      : strength_for_signature_law_prod _ colimit_sig_strength_data.
    Proof.
      do 3 intro. use (colimArrowUnique' H_Cocone_Prod).
      intro u.
      etrans. use colimOfArrowsIn. 
      do 3 rewrite assoc.
      eassert (∏ bB : pointed, colimIn H_Cocone_Prod u
        = colimIn H_Cocone u ⊗r bB) by (intro; use idpath).
      symmetry; etrans.
      {
        rewrite X; refine (maponpaths (λ x, x · _ · _ · _) _).
        use monoidal_associatorinvnatright.
      }
      etrans.
      {
        repeat rewrite <- assoc; refine (maponpaths _ _).
        repeat rewrite assoc; rewrite <- (bifunctor_rightcomp C).
        refine (maponpaths (λ x, x ⊗r _ · _ · _) _).
        use (colimOfArrowsIn _ _ H_Cocone_Prod).
      }
      etrans.
      {
        rewrite (bifunctor_rightcomp C), <- assoc, <- assoc.
        do 2 refine (maponpaths _ _).
        rewrite assoc; refine (maponpaths (λ x, x · _) _).
        use (colimOfArrowsIn _ _ H_Cocone_Prod).
      }
      etrans.
      {
        simpl.
        repeat rewrite assoc.
        rewrite <- assoc.
        refine (maponpaths _ _).
        use (colimOfArrowsIn _ _ H_Cocone H_Cocone).
      }
      simpl; rewrite assoc.
      use (!maponpaths (λ x, x · _) _).
      use signature_with_strength_prod.
    Qed.


    Definition colimit_sig_strength
      : strength_for_signature colimit_sig_functor.
    Proof.
      use make_strength_for_signature.
      - exact colimit_sig_strength_data.
      - exact colimit_sig_strength_unit.
      - exact colimit_sig_strength_prod.
      - exact colimit_sig_strength_nat.
    Defined.

    Definition colimit_signature_with_strength 
      : signature_with_strength_cat
      := colimit_sig_strength.

    Definition colimit_signature_with_strength_in_data (v : vertex g)
      : pr1 (dob F' v) ⟹ colimit_sig_functor
      := colimIn colimit_sig_functor_cocone v.

    Lemma colimit_signature_with_strength_in_is_mor (v : vertex g)
      : is_a_morphism_of_signatures_with_strength _ _ (pr2 (dob F v)) 
        colimit_sig_strength (colimit_signature_with_strength_in_data v).
    Proof.
      intros A bB. symmetry. use (colimOfArrowsIn _ _ H_Cocone_Prod).
    Qed.

    Definition colimit_signature_with_strength_in (v : vertex g)
      : dob F v --> colimit_signature_with_strength
      := colimit_signature_with_strength_in_data v ,,
         colimit_signature_with_strength_in_is_mor v.

    Lemma colimit_signature_with_strength_cocone_is_cocone
      : forms_cocone F colimit_signature_with_strength_in.
    Proof.
      intros u v e.
      use invmap; [|use path_sigma_hprop|].
      use isaprop_is_a_morphism_of_signatures_with_strength.
      use (colimInCommutes colimit_sig_functor_cocone).
    Qed.

    Definition colimit_signature_with_strength_cocone
      : cocone F colimit_signature_with_strength
      := make_cocone _ colimit_signature_with_strength_cocone_is_cocone.


    Section FixACocone.
      Context (H' : C ⟶ C) (θ' : strength_for_signature H').
      Context (cc : cocone F (H' ,, θ')).

      Definition colimit_signature_with_strength_arrow_data
        : colimit_sig_functor ⟹ H'
        := colimArrow _ _ (mapcocone forgetful F cc).

      Lemma colimit_signature_with_strength_arrow_is_mor
        : is_a_morphism_of_signatures_with_strength colimit_sig_functor H'
            colimit_sig_strength θ' colimit_signature_with_strength_arrow_data.
      Proof.
        intros A bB. use (colimArrowUnique' H_Cocone_Prod).
        intro u; etrans.
        {
          rewrite assoc; refine (maponpaths (λ x, x ·_) _).
          use (colimOfArrowsIn _ _ H_Cocone_Prod).
        }
        simpl; etrans.
        {
          rewrite <- assoc; refine (maponpaths _ _).
          use (colimArrowCommutes H_Cocone).
        }
        simpl; symmetry; etrans.
        {
          eassert (colimIn H_Cocone_Prod u = colimIn H_Cocone u ⊗r bB) by use idpath.
          rewrite X, assoc, <- (bifunctor_rightcomp C).
          refine (maponpaths (λ x, x ⊗r bB · _) _).
          use (colimArrowCommutes H_Cocone).
        }
        use (!pr2 (coconeIn cc u) _ _).
      Qed.

      Definition colimit_signature_with_strength_arrow
        : signature_with_strength_cat⟦colimit_signature_with_strength, (H',,θ')⟧ 
        := colimit_signature_with_strength_arrow_data ,,
           colimit_signature_with_strength_arrow_is_mor.

      Lemma  colimit_signature_with_strength_arrow_is_cocone_mor
        : is_cocone_mor colimit_signature_with_strength_cocone cc
            colimit_signature_with_strength_arrow.
      Proof.
        intro u.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_a_morphism_of_signatures_with_strength.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_nat_trans; use homset_property.
        use funextsec; intro A.
        use (colimArrowCommutes (colims_g (diagram_pointwise F' _))).
      Qed.
      
      Context (f_Hf : 
        ∑(f : signature_with_strength_cat ⟦colimit_signature_with_strength, H',, θ' ⟧),
        is_cocone_mor colimit_signature_with_strength_cocone cc f
      ).

      Let f : signature_with_strength_cat ⟦colimit_signature_with_strength, H',, θ' ⟧
        := pr1 f_Hf.

      Let Hf : is_cocone_mor colimit_signature_with_strength_cocone  cc f
        := pr2 f_Hf.

      Lemma colimit_signature_with_strength_arrow_unique
        : f = colimit_signature_with_strength_arrow.
      Proof.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_a_morphism_of_signatures_with_strength.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_nat_trans; use homset_property.
        use funextsec; intro A; use colimArrowUnique; intro u; cbn.
        exact (maponpaths (λ x, pr11 x A) (Hf u)).
      Qed.

      Lemma colimit_signature_with_strength_arrow_unique_pair
        : f_Hf = (_ ,, colimit_signature_with_strength_arrow_is_cocone_mor).
      Proof.
        use invmap; [|use path_sigma_hprop|].
        use isaprop_is_cocone_mor.
        use colimit_signature_with_strength_arrow_unique.
      Qed.
    End FixACocone.

    Definition colimit_signature_with_strength_cocone_is_colim_cocone
      : isColimCocone F _ colimit_signature_with_strength_cocone
      := λ _ A, 
        (_ ,, colimit_signature_with_strength_arrow_is_cocone_mor _ _ A) ,,
        colimit_signature_with_strength_arrow_unique_pair _ _ A.


    Definition colimit_signature_with_strength_colim_cocone : ColimCocone F.
    Proof.
      use make_ColimCocone.
      - exact colimit_signature_with_strength.
      - exact colimit_signature_with_strength_cocone.
      - exact colimit_signature_with_strength_cocone_is_colim_cocone.
    Defined.
  End Colimits.

  Theorem signature_with_strength_inherits_colimits 
    (g : graph) (cl : Colims_of_shape g C)
    (H_prod : ∏ bB : pointed, 
      preserves_colimits_of_shape (rightwhiskering_functor C bB) g)
    : Colims_of_shape g signature_with_strength_cat.
  Proof.
    use (colimit_signature_with_strength_colim_cocone cl H_prod).
  Defined.
End SignaturesWithStrength.

Section OmegaCocontSignaturewWithStrength.
  Context {C : monoidal_cat}.

  Local Notation "x ⊗l f" := (x ⊗^{C}_{l} f) (at level 31).
  Local Notation "f ⊗r y" := (f ⊗^{C}_{r} y) (at level 31).

  Definition omega_signature_with_strength_law
    (Hθ : @signature_with_strength_cat C)
    := is_omega_cocont (pr1 Hθ).

  Lemma isaprop_omega_signature_with_strength_law 
    (Hθ : signature_with_strength_cat)
    : isaprop (omega_signature_with_strength_law Hθ).
  Proof.
    do 4 (use impred; intro).
    use isaprop_isColimCocone.
  Qed.

  Definition omega_signature_with_strength_cat : category
    := full_subcat _ omega_signature_with_strength_law.
End OmegaCocontSignaturewWithStrength.
