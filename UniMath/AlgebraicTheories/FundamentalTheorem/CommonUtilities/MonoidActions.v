(**************************************************************************************************

  Right actions of a monoid

  For any monoid M, there is a category of sets with a right M-action. This file defines the objects
  and morphisms in this category, defines the category itself, and shows that it has a terminal
  object, binary products and exponentials. Also, a morphism between two monoids induces
  "restriction" and "extension" of scalar functors between their categories of monoid actions. The
  extension functor preserves the terminal object and binary product.

  Contents
  1.  The definition of a right M-action [monoid_action]
  2.  The definition of a morphism of M-actions [monoid_action_morphism]
  3.  The category of M-actions [monoid_action_category]
  4.  The terminal M-action [terminal_monoid_action]
  5.  The binary product of M-actions [binproducts_monoid_action_category]
  6.  The exponential M-action [is_exponentiable_monoid_action]
  7.  A characterization of isomorphisms [make_monoid_action_z_iso]
  8.  An isomorphism between the set of global elements and the set of fixpoints of a monoid action [monoid_action_global_element_fixpoint_iso]
  9.  Restriction of scalars [scalar_restriction_functor]
  10. Extension of scalars [scalar_extension_functor]
  10.1. Extension of scalars preserves monoid monoid action
    [scalar_extension_preserves_monoid_monoid_action]
  10.2. Extension of scalars preserves the terminal [scalar_extension_preserves_terminal]
  10.3. Extension of scalars preserves binary products [scalar_extension_preserves_binproducts]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.
Local Open Scope multmonoid.
Local Open Scope type_scope.

Section MonoidAction.

  Context (M : monoid).

(** * 1. The definition of a right M-action *)

  Definition monoid_action_data : UU
    := ∑ (X: hSet), X → M → X.

  Definition make_monoid_action_data
    (X : hSet)
    (op : X → M → X)
    : monoid_action_data
    := X ,, op.

  Coercion monoid_action_data_to_hset (x : monoid_action_data) : hSet := pr1 x.
  Definition op {X : monoid_action_data} : X → M → X := pr2 X.

  Definition is_monoid_action (X : monoid_action_data) :=
    (∏ (x : X), op x (unel M) = x) ×
    (∏ (x : X) y y', op x (y * y') = op (op x y) y').

  Definition make_is_monoid_action
    {X : monoid_action_data}
    (unax : ∏ (x : X), op x (unel M) = x)
    (assocax : ∏ (x : X) y y', op x (y * y') = op (op x y) y')
    : is_monoid_action X
    := unax ,, assocax.

  Definition monoid_action :=
    ∑ (X : monoid_action_data), is_monoid_action X.

  Definition make_monoid_action
    (X : monoid_action_data)
    (H : is_monoid_action X)
    : monoid_action
    := X ,, H.

  Coercion monoid_action_to_monoid_action_data (f : monoid_action) : monoid_action_data := pr1 f.

  Definition monoid_action_unax {X : monoid_action} : ∏ (x : X), op x (unel M) = x := pr12 X.
  Definition monoid_action_assocax {X : monoid_action} : ∏ (x : X) y y', op x (y * y') = op (op x y) y' := pr22 X.

  Lemma isaprop_is_monoid_action (X : monoid_action_data)
    : isaprop (is_monoid_action X).
  Proof.
    apply isapropdirprod;
      repeat (apply impred_isaprop; intro);
      apply setproperty.
  Qed.

  Lemma monoid_action_eq
    (X X' : monoid_action)
    (H1 : (X : hSet) = (X' : hSet))
    (H2 : (transportf (λ x : hSet, x → M → x) H1 op = op))
    : X = X'.
  Proof.
    apply subtypePath.
    {
      intro.
      apply isaprop_is_monoid_action.
    }
    use total2_paths_f.
    - exact H1.
    - exact H2.
  Qed.

  Definition monoid_monoid_action
    : monoid_action.
  Proof.
    use make_monoid_action.
    - use make_monoid_action_data.
      + exact M.
      + exact (λ x y, x * y).
    - abstract (
        use make_is_monoid_action;
        [ intro;
          apply runax
        | intros;
          symmetry;
          apply assocax ]
      ).
  Defined.

(** * 2. The definition of a morphism of M-actions *)

  Definition monoid_action_morphism_data
    (X X' : monoid_action_data)
    : UU
    := X → X'.

  Definition monoid_action_morphism_data_to_function {X X' : monoid_action_data} (f : monoid_action_morphism_data X X') : X → X' := f.
  Coercion monoid_action_morphism_data_to_function : monoid_action_morphism_data >-> Funclass.

  Definition is_monoid_action_morphism
    {X X' : monoid_action_data}
    (f : monoid_action_morphism_data X X')
    : UU
    := ∏ x m, f (op x m) = op (f x) m.

  Definition monoid_action_morphism
    (X X' : monoid_action_data)
    := ∑ (f: monoid_action_morphism_data X X'), is_monoid_action_morphism f.

  Definition make_monoid_action_morphism
    {X X' : monoid_action_data}
    (f : monoid_action_morphism_data X X')
    (H : is_monoid_action_morphism f)
    : monoid_action_morphism X X'
    := f ,, H.

  Coercion monoid_action_morphism_to_function
    {X X' : monoid_action_data}
    (f : monoid_action_morphism X X')
    : monoid_action_morphism_data X X'
    := pr1 f.

  Definition monoid_action_morphism_commutes
    {X X' : monoid_action_data}
    (f : monoid_action_morphism X X')
    (x : X)
    (m : M)
    : f (op x m) = op (f x) m
    := pr2 f x m.

  Lemma isaprop_is_monoid_action_morphism
    {X X' : monoid_action_data}
    (f : monoid_action_morphism_data X X')
    : isaprop (is_monoid_action_morphism f).
  Proof.
    do 2 (apply impred_isaprop; intro).
    apply setproperty.
  Qed.

  Lemma monoid_action_morphism_eq
    {X X' : monoid_action_data}
    (f f' : monoid_action_morphism X X')
    (H : ∏ x, f x = f' x)
    : f = f'.
  Proof.
    apply subtypePath.
    {
      intro.
      apply isaprop_is_monoid_action_morphism.
    }
    apply funextfun.
    exact H.
  Qed.

  Lemma isaset_monoid_action_morphism
    (X X' : monoid_action_data)
    : isaset (monoid_action_morphism X X').
  Proof.
    apply isaset_total2.
    - apply isaset_set_fun_space.
    - intro.
      apply isasetaprop.
      apply isaprop_is_monoid_action_morphism.
  Qed.

  Definition id_monoid_action_morphism
    (X : monoid_action)
    : monoid_action_morphism X X.
  Proof.
    use make_monoid_action_morphism.
    - exact (idfun X).
    - abstract easy.
  Defined.

  Definition comp_monoid_action_morphism
    {X X' X'' : monoid_action}
    (f : monoid_action_morphism X X')
    (g : monoid_action_morphism X' X'')
    : monoid_action_morphism X X''.
  Proof.
    use make_monoid_action_morphism.
    - exact (λ x, g (f x)).
    - abstract (
        intros x m;
        refine (_ @ monoid_action_morphism_commutes _ _ _);
        apply maponpaths;
        apply monoid_action_morphism_commutes
      ).
  Defined.

(** * 3. The category of M-actions *)

  Definition monoid_action_category
    : category.
  Proof.
    use make_category.
    - use make_precategory.
      + use make_precategory_data.
        * use make_precategory_ob_mor.
          -- exact monoid_action.
          -- exact monoid_action_morphism.
        * exact id_monoid_action_morphism.
        * do 3 intro.
          exact comp_monoid_action_morphism.
      + abstract (
          use make_is_precategory;
          intros;
          apply monoid_action_morphism_eq;
          trivial
        ).
    - intros a b.
      apply isaset_monoid_action_morphism.
  Defined.

(** * 4. The terminal M-action *)

  Section Terminal.

    Definition action_terminal_object
      : monoid_action.
    Proof.
      use make_monoid_action.
      - use make_monoid_action_data.
        + exact unitset.
        + intros x m.
          exact x.
      - abstract (use make_is_monoid_action; trivial).
    Defined.

    Section Arrow.

      Context (X : monoid_action).

      Definition action_terminal_arrow
        : monoid_action_morphism X action_terminal_object.
      Proof.
        use make_monoid_action_morphism.
        - exact (λ _, tt).
        - abstract easy.
      Defined.

      Lemma action_terminal_arrow_unique
        (t : monoid_action_morphism X action_terminal_object)
        : t = action_terminal_arrow.
      Proof.
        apply monoid_action_morphism_eq.
        intro x.
        apply iscontrunit.
      Qed.

    End Arrow.

    Definition terminal_monoid_action
      : Terminal monoid_action_category.
    Proof.
      use make_Terminal.
      - exact action_terminal_object.
      - use make_isTerminal.
        intro X.
        use make_iscontr.
        + exact (action_terminal_arrow X).
        + exact (action_terminal_arrow_unique X).
    Defined.

  End Terminal.

(** * 5. The binary product of M-actions *)

  Section BinProducts.

    Context (X1 X2 : monoid_action).

    Definition action_binproduct_object_data
      : monoid_action_data.
    Proof.
      use make_monoid_action_data.
      - exact (setdirprod X1 X2).
      - intros x m.
        exact (op (pr1 x) m ,, op (pr2 x) m).
    Defined.

    Lemma action_binproduct_is_object
      : is_monoid_action action_binproduct_object_data.
    Proof.
      use make_is_monoid_action.
      - intro.
        use pathsdirprod;
          apply monoid_action_unax.
      - intros.
        use pathsdirprod;
          apply monoid_action_assocax.
    Qed.

    Definition action_binproduct_object
      : monoid_action
      := make_monoid_action _ action_binproduct_is_object.

    Definition action_binproduct_pr1
      : monoid_action_morphism action_binproduct_object X1.
    Proof.
      use make_monoid_action_morphism.
      - exact pr1.
      - abstract easy.
    Defined.

    Definition action_binproduct_pr2
      : monoid_action_morphism action_binproduct_object X2.
    Proof.
      use make_monoid_action_morphism.
      - exact pr2.
      - abstract easy.
    Defined.

    Section Arrow.

      Context {Y : monoid_action}.
      Context (f1 : monoid_action_morphism Y X1).
      Context (f2 : monoid_action_morphism Y X2).

      Definition action_binproduct_arrow_data
        (y : Y)
        : action_binproduct_object
        := f1 y ,, f2 y.

      Lemma action_binproduct_arrow_is_morphism
        : ∏ y m, action_binproduct_arrow_data (op y m) = op (action_binproduct_arrow_data y) m.
      Proof.
        intros.
        use pathsdirprod;
          apply monoid_action_morphism_commutes.
      Qed.

      Definition action_binproduct_arrow
        : monoid_action_morphism Y action_binproduct_object
        := make_monoid_action_morphism _ action_binproduct_arrow_is_morphism.

      Lemma action_binproduct_arrow_commutes1
        : (action_binproduct_arrow : monoid_action_category⟦_, _⟧) · action_binproduct_pr1 = f1.
      Proof.
        now use monoid_action_morphism_eq.
      Qed.

      Lemma action_binproduct_arrow_commutes2
        : (action_binproduct_arrow : monoid_action_category⟦_, _⟧) · action_binproduct_pr2 = f2.
      Proof.
        now use monoid_action_morphism_eq.
      Qed.

      Lemma action_binproduct_arrow_unique
        (t : ∑ (f : monoid_action_category⟦_, _⟧), f · action_binproduct_pr1 = f1 × f · action_binproduct_pr2 = f2)
        : t = (action_binproduct_arrow ,, (action_binproduct_arrow_commutes1 ,, action_binproduct_arrow_commutes2)).
      Proof.
        use subtypePairEquality.
        {
          intro.
          use isapropdirprod;
          apply homset_property.
        }
        apply monoid_action_morphism_eq.
        intro.
        apply pathsdirprod.
        - apply (maponpaths (λ f, (f : monoid_action_morphism _ _) x) (pr12 t)).
        - apply (maponpaths (λ f, (f : monoid_action_morphism _ _) x) (pr22 t)).
      Qed.

    End Arrow.

    Definition action_binproduct_is_binproduct
      : isBinProduct
        monoid_action_category _ _
        action_binproduct_object
        action_binproduct_pr1
        action_binproduct_pr2.
    Proof.
      use make_isBinProduct.
      intros Y f1 f2.
      use make_iscontr.
      - exists (action_binproduct_arrow f1 f2).
        split.
        + exact (action_binproduct_arrow_commutes1 f1 f2).
        + exact (action_binproduct_arrow_commutes2 f1 f2).
      - exact (action_binproduct_arrow_unique f1 f2).
    Defined.

    Definition binproduct_monoid_action_category
      : BinProduct monoid_action_category X1 X2.
    Proof.
      use make_BinProduct.
      - exact action_binproduct_object.
      - exact action_binproduct_pr1.
      - exact action_binproduct_pr2.
      - exact action_binproduct_is_binproduct.
    Defined.

  End BinProducts.

  Definition binproducts_monoid_action_category
    : BinProducts monoid_action_category
    := binproduct_monoid_action_category.

(** * 6. The exponential M-action *)

  Section ExponentialObject.

    Context (X X' : monoid_action).

    Let binproduct_monoid_action
      (Y Y' : monoid_action)
      : monoid_action
      := BinProductObject _ (binproducts_monoid_action_category Y Y').

    Section ActionOnMorphism.

      Context (f : monoid_action_morphism (binproduct_monoid_action monoid_monoid_action X) X').
      Context (m : M).

      Definition action_on_morphism_data
        : monoid_action_morphism_data (binproduct_monoid_action monoid_monoid_action X) X'
        := λ x, f (m * pr1 x ,, pr2 x).

      Lemma action_on_morphism_is_morphism
        : is_monoid_action_morphism action_on_morphism_data.
      Proof.
        intros x m'.
        refine (_ @ monoid_action_morphism_commutes _ _ _).
        exact (maponpaths (λ x, f (x ,, _)) (!assocax M _ _ _)).
      Qed.

      Definition action_on_morphism
        : monoid_action_morphism (binproduct_monoid_action monoid_monoid_action X) X'
        := make_monoid_action_morphism _ action_on_morphism_is_morphism.

    End ActionOnMorphism.

    Definition exponential_object_data
      : monoid_action_data.
    Proof.
      use make_monoid_action_data.
      - exact (make_hSet _
          (isaset_monoid_action_morphism (binproduct_monoid_action monoid_monoid_action X) X')).
      - exact action_on_morphism.
    Defined.

    Lemma exponential_is_object
      : is_monoid_action exponential_object_data.
    Proof.
      use make_is_monoid_action;
        refine (λ (f : monoid_action_morphism _ _), _);
        intros;
        apply monoid_action_morphism_eq;
        intro;
        refine (maponpaths (λ x, f (x ,, _)) _).
      - apply unax.
      - apply assocax.
    Qed.

    Definition exponential_object
      : monoid_action
      := make_monoid_action _ exponential_is_object.

    Definition exponential_object_morphism_data
      : monoid_action_morphism_data (binproduct_monoid_action X exponential_object) X'
      := λ x, (pr2 x : monoid_action_morphism _ _) (1 ,, pr1 x).

    Lemma exponential_object_is_morphism
      : is_monoid_action_morphism exponential_object_morphism_data.
    Proof.
      intros x m.
      refine (_ @ monoid_action_morphism_commutes _ _ _).
      apply (maponpaths (λ y, (pr2 x : monoid_action_morphism _ _) (y ,, _))).
      exact (runax _ _ @ !lunax _ _).
    Qed.

    Definition exponential_object_morphism
      : monoid_action_morphism (binproduct_monoid_action X exponential_object) X'
      := make_monoid_action_morphism _ exponential_object_is_morphism.

    Section ArrowIsUniversal.

      Context {X'': monoid_action}.
      Context (F: monoid_action_morphism (binproduct_monoid_action X X'') X').

      Section InducedMorphismData.

        Context (x'' : X'').

        Definition monoid_action_cat_induced_morphism_data_morphism_data
          : monoid_action_morphism_data (binproduct_monoid_action monoid_monoid_action X) X'
          := λ x, F (pr2 x ,, op x'' (pr1 x)).

        Definition monoid_action_cat_induced_morphism_data_is_morphism
          : is_monoid_action_morphism monoid_action_cat_induced_morphism_data_morphism_data.
        Proof.
          intros x m.
          refine (_ @ monoid_action_morphism_commutes _ _ _).
          apply (maponpaths (λ x, F (_ ,, x))).
          apply monoid_action_assocax.
        Qed.

        Definition monoid_action_cat_induced_morphism_data_morphism
          : monoid_action_morphism (binproduct_monoid_action monoid_monoid_action X) X'
          := make_monoid_action_morphism _ monoid_action_cat_induced_morphism_data_is_morphism.

      End InducedMorphismData.

      Definition monoid_action_cat_induced_morphism_data
        : monoid_action_morphism_data X'' exponential_object
        := monoid_action_cat_induced_morphism_data_morphism.

      Lemma monoid_action_cat_induced_is_morphism
        : is_monoid_action_morphism monoid_action_cat_induced_morphism_data.
      Proof.
        intros x m.
        apply monoid_action_morphism_eq.
        intro.
        exact (maponpaths (λ x, F (_ ,, x)) (!monoid_action_assocax _ _ _)).
      Qed.

      Definition monoid_action_cat_induced_morphism
        : monoid_action_morphism X'' exponential_object
        := make_monoid_action_morphism _ monoid_action_cat_induced_is_morphism.

      Lemma monoid_action_cat_induced_morphism_commutes
        : F = # (constprod_functor1 binproducts_monoid_action_category X) monoid_action_cat_induced_morphism · exponential_object_morphism.
      Proof.
        apply monoid_action_morphism_eq.
        intro.
        apply (maponpaths (λ x, F (_ ,, x))).
        exact (!monoid_action_unax _).
      Qed.

      Lemma monoid_action_cat_induced_morphism_unique
        (t : ∑ (f' : monoid_action_morphism X'' exponential_object), F = # (constprod_functor1 binproducts_monoid_action_category X) f' · exponential_object_morphism)
        : t = monoid_action_cat_induced_morphism ,, monoid_action_cat_induced_morphism_commutes.
      Proof.
        use subtypePath.
        {
          intro.
          apply (homset_property monoid_action_category).
        }
        use monoid_action_morphism_eq.
        intro x''.
        use monoid_action_morphism_eq.
        intro x.
        refine (!_ @ maponpaths (λ x, (x : monoid_action_morphism _ _) _) (!(pr2 t))).
        refine (maponpaths (λ x, (_ x) _) (monoid_action_morphism_commutes _ _ _) @ _).
        refine (maponpaths (λ x, (pr1 t x'' : monoid_action_morphism _ _) (x ,, _)) _).
        apply runax.
      Qed.

    End ArrowIsUniversal.

  End ExponentialObject.

  Definition is_exponentiable_monoid_action
    (X : monoid_action_category)
    : is_exponentiable binproducts_monoid_action_category X.
  Proof.
    use left_adjoint_from_partial.
    - exact (exponential_object X).
    - exact (exponential_object_morphism X).
    - intros X' X'' F.
      use make_iscontr.
      + use tpair.
        * exact (monoid_action_cat_induced_morphism _ _ F).
        * exact (monoid_action_cat_induced_morphism_commutes _ _ F).
      + exact (monoid_action_cat_induced_morphism_unique _ _ F).
  Defined.

(** * 7. A characterization of isomorphisms *)

  Definition make_monoid_action_z_iso
    (A A' : monoid_action)
    (f : z_iso (C := HSET) (A : hSet) (A' : hSet))
    (Hf : is_monoid_action_morphism (morphism_from_z_iso _ _ f : A → A'))
    : z_iso (A : monoid_action_category) (A' : monoid_action_category).
  Proof.
    use make_z_iso.
    - use make_monoid_action_morphism.
      + exact (morphism_from_z_iso _ _ f).
      + exact Hf.
    - use make_monoid_action_morphism.
      + exact (inv_from_z_iso f).
      + abstract (
          intros x m;
          refine (!_ @ eqtohomot (z_iso_inv_after_z_iso f) _);
          apply (maponpaths (inv_from_z_iso f));
          refine (Hf _ _ @ _);
          exact (maponpaths (λ y, op (y x) m) (z_iso_after_z_iso_inv f))
        ).
    - abstract (
        split;
        apply monoid_action_morphism_eq;
        intro;
        [ apply (eqtohomot (z_iso_inv_after_z_iso f))
        | apply (eqtohomot (z_iso_after_z_iso_inv f)) ]
      ).
  Defined.

(** * 8. An isomorphism between the set of global elements and the set of fixpoints of a monoid action *)

  Section GlobalElements.

    Context (X : monoid_action).

    Definition global_element : UU
      := monoid_action_morphism
        (TerminalObject terminal_monoid_action : monoid_action)
        X.

    Lemma isaset_global_element
      : isaset global_element.
    Proof.
      use (isaset_carrier_subset (_ ,, _) (λ _, make_hProp _ _)).
      - apply funspace_isaset.
        apply setproperty.
      - do 2 (apply impred_isaprop; intro).
        apply setproperty.
    Qed.

    Definition global_element_set
      : hSet
      := make_hSet _ isaset_global_element.

    Definition fixpoint : UU
      := ∑ x : X, ∏ m, op x m = x.

    Lemma isaset_fixpoint
      : isaset fixpoint.
    Proof.
      use (isaset_carrier_subset _ (λ _, make_hProp _ _)).
      apply impred_isaprop.
      intro.
      apply setproperty.
    Qed.

    Definition fixpoint_set
      : hSet
      := make_hSet _ isaset_fixpoint.

    Definition global_element_to_fixpoint
      (f : global_element)
      : fixpoint.
    Proof.
      exists ((f : monoid_action_morphism _ _) tt).
      abstract (
        intro m;
        exact (!monoid_action_morphism_commutes f tt m)
      ).
    Defined.

    Definition fixpoint_to_global_element
      (a : fixpoint)
      : global_element.
    Proof.
      use make_monoid_action_morphism.
      - intro t.
        exact (pr1 a).
      - abstract (
          intros t m;
          exact (!pr2 a m)
        ).
    Defined.

    Lemma global_element_fixpoint_inverse
      : is_inverse_in_precat (C := HSET) (a := global_element_set) (b := fixpoint_set)
      global_element_to_fixpoint fixpoint_to_global_element.
    Proof.
      split.
      - apply funextfun.
        intro f.
        use monoid_action_morphism_eq.
        intro t.
        now induction t.
      - apply funextfun.
        intro a.
        refine (subtypePath _ _).
        {
          intro.
          apply impred_isaprop.
          intro.
          apply setproperty.
        }
        apply idpath.
    Qed.

    Definition monoid_action_global_element_fixpoint_iso
      : z_iso (C := HSET) global_element_set fixpoint_set
      := make_z_iso (C := HSET) (a := global_element_set) (b := fixpoint_set)
        global_element_to_fixpoint
        fixpoint_to_global_element
        global_element_fixpoint_inverse.

  End GlobalElements.

End MonoidAction.

(** * 9. Restriction of scalars *)

Section ScalarRestriction.

  Context (M M' : monoid).
  Context (f : monoidfun M M').

  Section Ob.

    Context (X : monoid_action M').

    Definition restriction_functor_ob_monoid_action_data
      : monoid_action_data M.
    Proof.
      use make_monoid_action_data.
      - exact X.
      - exact (λ x m, op _ x (f m)).
    Defined.

    Lemma restriction_functor_ob_is_monoid_action
      : is_monoid_action _ restriction_functor_ob_monoid_action_data.
    Proof.
      use make_is_monoid_action.
      - intro.
        refine (maponpaths _ (monoidfununel f) @ _).
        apply monoid_action_unax.
      - intros.
        refine (maponpaths _ (monoidfunmul f _ _) @ _).
        apply monoid_action_assocax.
    Qed.

    Definition restriction_functor_ob_monoid_action
      : monoid_action M
      := make_monoid_action _ _ restriction_functor_ob_is_monoid_action.

  End Ob.

  Section Mor.

    Context (X X' : monoid_action M').
    Context (F : monoid_action_morphism M' X X').

    Definition restriction_functor_mor_monoid_action_morphism_data
      : monoid_action_morphism_data _ (restriction_functor_ob_monoid_action X) (restriction_functor_ob_monoid_action X')
      := F.

    Lemma restriction_functor_mor_is_monoid_action_morphism
      : is_monoid_action_morphism _ restriction_functor_mor_monoid_action_morphism_data.
    Proof.
      intros x m.
      apply (monoid_action_morphism_commutes _ F).
    Qed.

    Definition restriction_functor_mor_monoid_action_morphism
      : monoid_action_morphism _ (restriction_functor_ob_monoid_action X) (restriction_functor_ob_monoid_action X')
      := make_monoid_action_morphism _ _ restriction_functor_mor_is_monoid_action_morphism.

  End Mor.

  Definition scalar_restriction_functor_data
    : functor_data (monoid_action_category M') (monoid_action_category M)
    := make_functor_data (C := monoid_action_category M') (C' := monoid_action_category M)
      restriction_functor_ob_monoid_action
      restriction_functor_mor_monoid_action_morphism.

  Lemma scalar_restriction_is_functor
    : is_functor scalar_restriction_functor_data.
  Proof.
    split.
    - intro X.
      apply monoid_action_morphism_eq.
      easy.
    - intros X X' X'' F F''.
      apply monoid_action_morphism_eq.
      easy.
  Qed.

  Definition scalar_restriction_functor
    : monoid_action_category M' ⟶ monoid_action_category M
    := make_functor _ scalar_restriction_is_functor.

End ScalarRestriction.

(** * 10. Extension of scalars *)

Section ScalarExtension.

  Context (M M' : monoid).
  Context (f : monoidfun M M').

  Section Ob.

    Context (X : monoid_action M).

    Definition hrelation
      : hrel (X × monoid_monoid_action M').
    Proof.
      intros x x'.
      exact (
        ∃ (a : M),
          (pr1 x' = op _ (pr1 x) a) ×
          (pr2 x = (f a) * pr2 x')).
    Defined.

    Lemma isrefl_hrelation
      : isrefl hrelation.
    Proof.
      intro x.
      apply hinhpr.
      exists 1.
      split.
      - exact (!monoid_action_unax _ _).
      - exact (!lunax _ _ @ !maponpaths (λ x, x * _) (monoidfununel f)).
    Qed.

    Definition eqrelation
      : eqrel (X × monoid_monoid_action M')
      := _ ,, iseqrel_eqrel_from_hrel hrelation.

    Definition extension_functor_ob_monoid_action_data
      : monoid_action_data M'.
    Proof.
      use make_monoid_action_data.
      - refine (setquotinset (X := X × monoid_monoid_action M') _).
        exact eqrelation.
      - intros x m.
        revert x.
        refine (setquotfun _ _ (λ x, pr1 x ,, pr2 x * m) _).
        abstract (
          apply iscomprelrelfun_eqrel_from_hrel;
          intros x x' H;
          refine (hinhfun _ H);
          intro H1;
          exists (pr1 H1);
          split;
          [ exact (pr12 H1)
          | exact (maponpaths (λ x, x * m) (pr22 H1) @ assocax _ _ _ _) ]
        ).
    Defined.

    Lemma extension_functor_ob_is_monoid_action
      : is_monoid_action _ extension_functor_ob_monoid_action_data.
    Proof.
      use make_is_monoid_action.
      - intro x.
        use (issurjsetquotpr _ x (_ ,, isasetsetquot _ _ _) _).
        intro y.
        rewrite <- (pr2 y).
        refine (setquotfuncomm _ _ _ _ _ @ _).
        apply (maponpaths (λ x, _ (_ ,, x))).
        apply runax.
      - intros x m m'.
        use (issurjsetquotpr _ x (_ ,, isasetsetquot _ _ _) _).
        intro y.
        rewrite <- (pr2 y).
        refine (setquotfuncomm _ _ _ _ _ @ !_).
        refine (maponpaths _ (setquotfuncomm _ _ _ _ _) @ _).
        refine (setquotfuncomm _ _ _ _ _ @ !_).
        apply (maponpaths (λ x, _ (_ ,, x))).
        symmetry.
        apply assocax.
    Qed.

    Definition extension_functor_ob_monoid_action
      : monoid_action M'
      := make_monoid_action _ _ extension_functor_ob_is_monoid_action.

  End Ob.

  Section Mor.

    Context (X X' : monoid_action M).
    Context (F : monoid_action_morphism M X X').

    Definition extension_functor_mor_monoid_action_morphism_data
      : monoid_action_morphism_data _ (extension_functor_ob_monoid_action X) (extension_functor_ob_monoid_action X').
    Proof.
      refine (setquotfun _ (eqrelation X') (λ x, F (pr1 x) ,, (pr2 x : M')) _).
      abstract (
        apply iscomprelrelfun_eqrel_from_hrel;
        intros x x' Hx;
        refine (hinhfun _ Hx);
        intro H1;
        exists (pr1 H1);
        split;
        [ exact (maponpaths _ (pr12 H1) @ monoid_action_morphism_commutes _ _ _ _)
        | apply (pr22 H1) ]
      ).
    Defined.

    Lemma extension_functor_mor_is_monoid_action_morphism
      : is_monoid_action_morphism _ extension_functor_mor_monoid_action_morphism_data.
    Proof.
      intros x m.
      use (issurjsetquotpr _ x (_ ,, isasetsetquot _ _ _) _).
      intro y.
      now rewrite <- (pr2 y).
    Qed.

    Definition extension_functor_mor_monoid_action_morphism
      : monoid_action_morphism _ (extension_functor_ob_monoid_action X) (extension_functor_ob_monoid_action X')
      := make_monoid_action_morphism _ _ extension_functor_mor_is_monoid_action_morphism.

  End Mor.

  Definition scalar_extension_functor_data
    : functor_data (monoid_action_category M) (monoid_action_category M')
    := make_functor_data (C := monoid_action_category M) (C' := monoid_action_category M')
      extension_functor_ob_monoid_action
      extension_functor_mor_monoid_action_morphism.

  Lemma scalar_extension_is_functor
    : is_functor scalar_extension_functor_data.
  Proof.
    split.
    - intro X.
      apply monoid_action_morphism_eq.
      intro x.
      use (issurjsetquotpr _ x (_ ,, isasetsetquot _ _ _) _).
      intro y.
      now rewrite <- (pr2 y).
    - intros X X' X'' F F''.
      apply monoid_action_morphism_eq.
      intro x.
      use (issurjsetquotpr _ x (_ ,, isasetsetquot _ _ _) _).
      intro y.
      now rewrite <- (pr2 y).
  Qed.

  Definition scalar_extension_functor
    : monoid_action_category M ⟶ monoid_action_category M'
    := make_functor _ scalar_extension_is_functor.

(** ** 10.1. Extension of scalars preserves monoid monoid action *)

  Section PreservesMonoidMonoidAction.

    Definition scalar_extension_preserves_monoid_monoid_action_mor_fun
      : monoid_monoid_action M × monoid_monoid_action M' → monoid_monoid_action M'
      := λ x, f (pr1 x) * pr2 x.

    Lemma scalar_extension_preserves_monoid_monoid_action_mor_iscomprelfun
      : iscomprelfun (eqrelation _) scalar_extension_preserves_monoid_monoid_action_mor_fun.
    Proof.
      intros x x' Hx.
      use (Hx (make_eqrel (λ x x', make_hProp _ _) _) _).
      - apply setproperty.
      - repeat split.
        + intros y y' y'' Hy Hy'.
          now rewrite Hy, Hy'.
        + now intros y y' Hy.
      - intros y y' Hy.
        use Hy.
        intro H.
        refine (maponpaths _ (pr22 H) @ !_).
        refine (maponpaths (λ x, _ x * _) (pr12 H) @ _).
        refine (maponpaths (λ x, x * _) (monoidfunmul f _ _) @ _).
        apply assocax.
    Qed.

    Definition scalar_extension_preserves_monoid_monoid_action_mor
      : (scalar_extension_functor (monoid_monoid_action M) : monoid_action M') → monoid_monoid_action M'
      := setquotuniv _ _ _ scalar_extension_preserves_monoid_monoid_action_mor_iscomprelfun.

    Definition scalar_extension_preserves_monoid_monoid_action_inv
      : monoid_monoid_action M' → (scalar_extension_functor (monoid_monoid_action M) : monoid_action M')
      := λ m, setquotpr _ (1 ,, m).

    Lemma scalar_extension_preserves_monoid_monoid_action_is_inverse
      : is_inverse_in_precat (C := HSET) scalar_extension_preserves_monoid_monoid_action_mor scalar_extension_preserves_monoid_monoid_action_inv.
    Proof.
      split.
      - apply funextfun.
        intro x.
        use (issurjsetquotpr _ x (_ ,, isasetsetquot _ _ _) _).
        intro y.
        refine (!maponpaths _ (pr2 y) @ _ @ pr2 y).
        apply iscompsetquotpr.
        apply eqrel_impl.
        apply hinhpr.
        exists (pr11 y).
        split.
        + exact (!lunax _ _).
        + apply idpath.
      - apply funextfun.
        intro m.
        refine (maponpaths (λ x, x * _) (monoidfununel f) @ _).
        exact (lunax _ _).
    Qed.

    Lemma scalar_extension_preserves_monoid_monoid_action_is_monoid_action_morphism
      : is_monoid_action_morphism M' scalar_extension_preserves_monoid_monoid_action_mor.
    Proof.
      intros x m.
      use (issurjsetquotpr _ x (_ ,, setproperty _ _ _) _).
      intro y.
      refine (!_ @ maponpaths (λ x, _ x * _) (pr2 y)).
      refine (!_ @ maponpaths (λ x, _ (_ x)) (pr2 y)).
      apply (!assocax _ _ _ _).
    Qed.

    Definition scalar_extension_preserves_monoid_monoid_action
      : z_iso (scalar_extension_functor (monoid_monoid_action M)) (monoid_monoid_action M')
      := make_monoid_action_z_iso _ _ _
        (make_z_iso (C := HSET)
          scalar_extension_preserves_monoid_monoid_action_mor
          scalar_extension_preserves_monoid_monoid_action_inv
          scalar_extension_preserves_monoid_monoid_action_is_inverse)
        scalar_extension_preserves_monoid_monoid_action_is_monoid_action_morphism.

  End PreservesMonoidMonoidAction.

(** ** 10.2. Extension of scalars preserves the terminal *)

  Section PreservesTerminal.

    Context (terminal_element : M').
    Context (element_is_terminal : ∏ (m' : M'), ∑ (m : M), f(m) * m' = terminal_element).

    Definition scalar_extension_terminal_iso_mor
      : (scalar_extension_functor (terminal_monoid_action M) : monoid_action _) → (TerminalObject (terminal_monoid_action M') : monoid_action _)
      := λ x, tt.

    Definition scalar_extension_terminal_iso_inv
      : (TerminalObject (terminal_monoid_action M') : monoid_action _) → (scalar_extension_functor (terminal_monoid_action M) : monoid_action _)
      := λ x, setquotpr _ (tt ,, terminal_element).

    Lemma scalar_extension_terminal_iso_is_iso
      : is_inverse_in_precat (C := HSET) scalar_extension_terminal_iso_mor scalar_extension_terminal_iso_inv.
    Proof.
      split.
      - use funextfun.
        intro x.
        use (issurjsetquotpr _ x (_ ,, isasetsetquot _ _ _) _).
        intro y.
        refine (!maponpaths _ (pr2 y) @ _ @ pr2 y).
        apply iscompsetquotpr.
        apply eqrel_impl.
        apply hinhpr.
        exists (pr1 (element_is_terminal (pr21 y))).
        split.
        + apply iscontrunit.
        + exact (!pr2 (element_is_terminal _)).
      - use funextfun.
        intro t.
        exact (!pr2 iscontrunit _).
    Qed.

    Lemma scalar_extension_terminal_iso_is_morphism
      : is_monoid_action_morphism M' scalar_extension_terminal_iso_mor.
    Proof.
      easy.
    Qed.

    Definition scalar_extension_terminal_iso
      : z_iso (scalar_extension_functor (terminal_monoid_action M)) (terminal_monoid_action M')
      := make_monoid_action_z_iso _ _ _
        (make_z_iso (C := HSET)
          scalar_extension_terminal_iso_mor
          scalar_extension_terminal_iso_inv
          scalar_extension_terminal_iso_is_iso)
        scalar_extension_terminal_iso_is_morphism.

    Definition scalar_extension_preserves_terminal
      : preserves_terminal scalar_extension_functor.
    Proof.
      use preserves_terminal_if_preserves_chosen.
      - apply terminal_monoid_action.
      - apply (iso_to_Terminal (terminal_monoid_action _)).
        exact (z_iso_inv scalar_extension_terminal_iso).
    Defined.

  End PreservesTerminal.

(** ** 10.3. Extension of scalars preserves binary products *)

  Section PreservesProduct.

    Context (terminal_element :
      ∏ (b1 b2 : M'),
      ∑ (c : M') (a1 a2 : M), (b1 = f(a1) * c) × (b2 = f(a2) * c)).

    Context (element_is_terminal :
      ∏ (b1 b2 : M') (t := (terminal_element b1 b2)) (t' : ∑ (c : M') (a1 a2 : M), (b1 = f(a1) * c) × (b2 = f(a2) * c)),
      ∑ (a : M), (pr1 t) = f(a) * (pr1 t') × (pr12 t) * a = (pr12 t') × (pr122 t) * a = (pr122 t')).

    Section Isomorphism.

      Context (X X' : monoid_action M).

      Definition scalar_extension_binproduct_iso_mor_data
        (x : (X × X') × M')
        : (X × M') × X' × M'
        := (pr11 x ,, pr2 x) ,, (pr21 x ,, pr2 x).

      Lemma scalar_extension_binproduct_iso_mor_iscomprelrelfun
        : iscomprelrelfun
          (eqrelation (BinProductObject _ (binproducts_monoid_action_category M X X')))
          (eqreldirprod (eqrelation X) (eqrelation X')) scalar_extension_binproduct_iso_mor_data.
      Proof.
        refine (transportf (λ x, iscomprelrelfun _ x _) (eqrel_from_hreldirprod _ _ (isrefl_hrelation _) (isrefl_hrelation _)) _).
        apply iscomprelrelfun_eqrel_from_hrel.
        intros x x' Hx.
        split.
        - revert Hx.
          apply hinhfun.
          intro Hx.
          exists (pr1 Hx).
          split.
          ++ exact (base_paths _ _ (pr12 Hx)).
          ++ exact (pr22 Hx).
        - revert Hx.
          apply hinhfun.
          intro Hx.
          exists (pr1 Hx).
          split.
          ++ refine (!maponpaths (λ x, x _) (transportf_const _ _) @ fiber_paths (pr12 Hx)).
          ++ exact (pr22 Hx).
      Qed.

      Definition scalar_extension_binproduct_iso_mor
        : setquot (eqrel_from_hrel (hrelation (action_binproduct_object M X X'))) →
          setquot (eqrel_from_hrel (hrelation X)) × setquot (eqrel_from_hrel (hrelation X'))
        := funcomp
          (setquotfun _ _ _ scalar_extension_binproduct_iso_mor_iscomprelrelfun)
          (setquottodirprod (eqrelation X) (eqrelation X')).

      Definition scalar_extension_binproduct_iso_inv_data
        (x : (X × M') × X' × M')
        (t := terminal_element (pr21 x) (pr22 x))
        : (X × X') × M'
        := ((
          op _ (pr11 x) (pr12 t) ,,
          op _ (pr12 x) (pr122 t)) ,,
          pr1 t).

      Lemma scalar_extension_binproduct_iso_inv_iscomprelrelfun
        : iscomprelrelfun (eqreldirprod (eqrelation X) (eqrelation X')) (eqrelation (BinProductObject _ (binproducts_monoid_action_category M X X'))) scalar_extension_binproduct_iso_inv_data.
      Proof.
        refine (transportf (λ x, iscomprelrelfun x _ _) (eqrel_from_hreldirprod _ _ (isrefl_hrelation _) (isrefl_hrelation _)) _).
        apply iscomprelrelfun_eqrel_from_hrel.
        intros x x' Hx.
        set (t := terminal_element (pr21 x) (pr22 x)).
        set (t' := terminal_element (pr21 x') (pr22 x')).
        induction Hx as [Hx1 Hx2].
        revert Hx1 Hx2.
        apply hinhfun2.
        intros Hx1 Hx2.
        epose (t'' := element_is_terminal _ _ (_ ,, _ ,, _ ,,
          (pr22 Hx1 @ maponpaths _ (pr1 (pr222 t')) @ !assocax _ _ _ _ @ !maponpaths (λ x, x * _) (monoidfunmul f _ _)) ,,
          (pr22 Hx2 @ maponpaths _ (pr2 (pr222 t')) @ !assocax _ _ _ _ @ !maponpaths (λ x, x * _) (monoidfunmul f _ _))
        )).
        refine (pr1 t'' ,, _ ,, pr12 t'').
        apply pathsdirprod.
        - refine (maponpaths (λ x, _ x _) (pr12 Hx1) @ _).
          do 2 refine (!_ @ monoid_action_assocax _ _ _ _).
          exact (!maponpaths _ (pr122 t'')).
        - refine (maponpaths (λ x, _ x _) (pr12 Hx2) @ _).
          do 2 refine (!_ @ monoid_action_assocax _ _ _ _).
          exact (!maponpaths _ (pr222 t'')).
      Qed.

      Definition scalar_extension_binproduct_iso_inv
        : setquot (eqrel_from_hrel (hrelation X)) × setquot (eqrel_from_hrel (hrelation X')) →
          setquot (eqrel_from_hrel (hrelation (action_binproduct_object M X X')))
        := funcomp
          (dirprodtosetquot (eqrelation X) (eqrelation X'))
          (setquotfun _ _ _ scalar_extension_binproduct_iso_inv_iscomprelrelfun).

      Lemma scalar_extension_binproduct_iso_is_iso
        : is_inverse_in_precat
        (C := HSET)
        (a := setquotinset (eqrelation _))
        (b := setdirprod (setquotinset (eqrelation _)) (setquotinset (eqrelation _)))
        scalar_extension_binproduct_iso_mor
        scalar_extension_binproduct_iso_inv.
      Proof.
        pose (prodiso := hset_equiv_weq_z_iso (setquotinset _) (setdirprod (setquotinset _) (setquotinset _)) (weqsetquottodirprod (eqrelation X) (eqrelation X'))).
        split.
        - apply funextfun.
          intro.
          refine (maponpaths _ (eqtohomot (z_iso_inv_after_z_iso prodiso) _) @ _).
          use (issurjsetquotpr _ x (_ ,, isasetsetquot _ _ _) _).
          intro y.
          rewrite <- (pr2 y).
          apply iscompsetquotpr.
          pose (t := terminal_element (pr21 y) (pr21 y)).
          pose (t' := element_is_terminal (pr21 y) (pr21 y) (pr1 t ,, pr12 t ,, pr12 t ,, pr1 (pr222 t) ,, pr1 (pr222 t))).
          apply (eqreltrans _ _
            ((op M (pr111 y) (pr12 t * pr1 t') ,, op M (pr211 y) (pr122 t * pr1 t')) ,, pr1 t)).
          + apply eqrel_impl.
            apply hinhpr.
            use (pr1 t' ,, _ ,, pr12 t').
            use pathsdirprod;
            exact (monoid_action_assocax _ _ _ _).
          + apply eqrelsymm.
            apply eqrel_impl.
            apply hinhpr.
            use (pr12 t * pr1 t' ,, _ ,, _).
            * apply (pathsdirprod (idpath _)).
              apply maponpaths.
              exact (pr222 t' @ !pr122 t').
            * refine (pr1 (pr222 t) @ _).
              refine (maponpaths _ (pr12 t') @ _).
              refine (!assocax _ _ _ _ @ _).
              exact (maponpaths (λ x, x * _) (!monoidfunmul f _ _)).
        - apply funextfun.
          intro.
          refine (_ @ eqtohomot (z_iso_after_z_iso_inv prodiso) _).
          apply (maponpaths (morphism_from_z_iso _ _ prodiso)).
          refine ((idpath _ : _ = (λ y, setquotfun _ _ _ _ (setquotfun _ _ _ _ y)) (inv_from_z_iso prodiso x)) @ _).
          use (issurjsetquotpr _ (inv_from_z_iso prodiso x) (_ ,, isasetsetquot _ _ _) _).
          intro y.
          rewrite <- (pr2 y).
          apply iscompsetquotpr.
          split.
          + apply eqrelsymm.
            apply eqrel_impl.
            apply hinhpr.
            use (pr12 (terminal_element (pr211 y) (pr221 y)) ,, idpath _ ,, _).
            exact (pr1 (pr222 (terminal_element (pr211 y) (pr221 y)))).
          + apply eqrelsymm.
            apply eqrel_impl.
            apply hinhpr.
            use (pr122 (terminal_element (pr211 y) (pr221 y)) ,, idpath _ ,, _).
            exact (pr2 (pr222 (terminal_element (pr211 y) (pr221 y)))).
      Qed.

      Lemma scalar_extension_binproduct_iso_is_morphism
        : is_monoid_action_morphism M'
          (X := (scalar_extension_functor (binproducts_monoid_action_category M X X')) : monoid_action M')
          (X' := BinProductObject _(binproducts_monoid_action_category M' (scalar_extension_functor X) (scalar_extension_functor X')) : monoid_action M')
          scalar_extension_binproduct_iso_mor.
      Proof.
        intros x m.
        use (issurjsetquotpr _ x (_ ,, isasetdirprod _ _ (isasetsetquot _) (isasetsetquot _) _ _)).
        intro y.
        now rewrite <- (pr2 y).
      Qed.

      Definition scalar_extension_binproduct_iso
        : z_iso
          (scalar_extension_functor (binproducts_monoid_action_category M X X'))
          (binproducts_monoid_action_category M' (scalar_extension_functor X) (scalar_extension_functor X'))
        := make_monoid_action_z_iso _
          (scalar_extension_functor (binproducts_monoid_action_category M X X'))
          (BinProductObject _ (binproducts_monoid_action_category _ (scalar_extension_functor X) (scalar_extension_functor X')))
          (make_z_iso
            (C := HSET)
            (a := setquotinset _)
            (b := setdirprod (setquotinset _) (setquotinset _))
            scalar_extension_binproduct_iso_mor
            scalar_extension_binproduct_iso_inv
            scalar_extension_binproduct_iso_is_iso)
          scalar_extension_binproduct_iso_is_morphism.

    End Isomorphism.

    Definition scalar_extension_preserves_binproducts
      : preserves_binproduct scalar_extension_functor.
    Proof.
      use preserves_binproduct_if_preserves_chosen.
      - apply binproducts_monoid_action_category.
      - intros Y Y'.
        use (isBinProduct_eq_arrow _ _ (iso_to_isBinProduct _ _ (z_iso_to_iso (scalar_extension_binproduct_iso Y Y'))));
        abstract now (
          apply monoid_action_morphism_eq;
          intro;
          use (issurjsetquotpr _ x (_ ,, isasetsetquot _ _ _) _);
          intro y;
          rewrite <- (pr2 y)
        ).
    Defined.

  End PreservesProduct.

End ScalarExtension.
