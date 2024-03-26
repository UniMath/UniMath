(**************************************************************************************

 Facts about the fiber of the codomain

 We establish some basic facts for the fiber of the codomain. In addition, we give some
 calculational lemmas which are useful when working with the fiber.

 Contents
 1. Accessors for the fiber of the codomain
 2. Builders for the fiber of the codomain
 3. Standard objects and morphisms in the codomain
 4. Calculations for codomain fiber
 5. The fiber of terminal objects

 **************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.

Definition cod_slice
           {C : category}
           (x : C)
  : category
  := (disp_codomain C)[{x}].

Notation "C / x" := (@cod_slice C x) : cat.

Proposition is_univalent_cod_slice
            {C : univalent_category}
            (x : C)
  : is_univalent (C/x).
Proof.
  use is_univalent_fiber.
  apply disp_univalent_disp_codomain.
Qed.

Definition cod_pb
           {C : category}
           (HC : Pullbacks C)
           {x y : C}
           (f : x --> y)
           (HD := disp_codomain_cleaving HC)
  : (C/y) ⟶ (C/x)
  := fiber_functor_from_cleaving _ HD f.

Section CodomainFiber.
  Context {C : category}.

  (** * 1. Accessors for the fiber of the codomain *)
  Definition cod_dom
             {y : C}
             (f : C/y)
    : C
    := pr1 f.

  Definition cod_mor
             {y : C}
             (f : C/y)
    : cod_dom f --> y
    := pr2 f.

  Definition dom_mor
             {y : C}
             {f₁ f₂ : C/y}
             (g : f₁ --> f₂)
    : cod_dom f₁ --> cod_dom f₂
    := pr1 g.

  Proposition mor_eq
              {y : C}
              {f₁ f₂ : C/y}
              (g : f₁ --> f₂)
    : dom_mor g · cod_mor f₂ = cod_mor f₁.
  Proof.
    exact (pr2 g @ id_right _).
  Qed.

  Proposition eq_mor_cod_fib
              {y : C}
              {f₁ f₂ : C/y}
              {g₁ g₂ : f₁ --> f₂}
              (p : dom_mor g₁ = dom_mor g₂)
    : g₁ = g₂.
  Proof.
    use eq_cod_mor.
    exact p.
  Qed.

  (** * 2. Builders for the fiber of the codomain *)
  Definition make_cod_fib_ob
             {x y : C}
             (f : x --> y)
    : C/y
    := x ,, f.

  Definition make_cod_fib_mor
             {x : C}
             {f₁ f₂ : C/x}
             (g : cod_dom f₁ --> cod_dom f₂)
             (p : g · cod_mor f₂ = cod_mor f₁)
    : f₁ --> f₂.
  Proof.
    refine (g ,, _).
    exact (p @ !(id_right _)).
  Defined.

  (** * 3. Standard objects and morphisms in the codomain *)
  Definition cod_fib_id
             (x : C)
    : C/x
    := make_cod_fib_ob (identity x).

  Definition mor_to_cod_fib_id
             {x : C}
             (f : C/x)
    : f --> cod_fib_id x.
  Proof.
    simple refine (make_cod_fib_mor _ _).
    - exact (cod_mor f).
    - abstract
        (cbn ;
         apply id_right).
  Defined.

  Definition cod_fib_comp
             {x y : C}
             (f : x --> y)
             (g : C/x)
    : C/y
    := make_cod_fib_ob (cod_mor g · f).

  Definition pr_cod_fib
             (P : BinProducts C)
             (x : C)
             (y : C)
    : C/x.
  Proof.
    use make_cod_fib_ob.
    - exact (P x y).
    - apply BinProductPr1.
  Defined.

  Definition mor_to_pr_cod_fib
             (P : BinProducts C)
             {x : C}
             {y : C}
             (f : C/x)
             (g : cod_dom f --> y)
    : f --> pr_cod_fib P x y.
  Proof.
    use make_cod_fib_mor.
    - use BinProductArrow.
      + exact (cod_mor f).
      + exact g.
    - apply BinProductPr1Commutes.
  Defined.

  (** * 4. Calculations for codomain fiber *)
  Proposition comp_in_cod_fib
              {x : C}
              {gz₁ gz₂ gz₃ : C/x}
              (φp : gz₁ --> gz₂)
              (ψq : gz₂ --> gz₃)
    : dom_mor (φp · ψq) = dom_mor φp · dom_mor ψq.
  Proof.
    cbn ; unfold dom_mor.
    rewrite transportf_cod_disp.
    apply idpath.
  Qed.

  Context (HC : Pullbacks C).

  Definition cod_fib_pb_comp
             {x y : C}
             (f : x --> y)
             (zg : C/x)
    : zg --> cod_pb HC f (cod_fib_comp f zg).
  Proof.
    simple refine (_ ,, _).
    - use PullbackArrow.
      + exact (identity _).
      + exact (pr2 zg).
      + abstract
          (apply id_left).
    - abstract
        (cbn ;
         rewrite PullbackArrow_PullbackPr2 ;
         rewrite id_right ;
         apply idpath).
  Defined.

  Definition cod_fiber_functor_pb
             {x y : C}
             (f : x --> y)
             {zg₁ zg₂ : C/y}
             (gp : zg₁ --> zg₂)
    : cod_pb HC f zg₁
      -->
      cod_pb HC f zg₂.
  Proof.
    simple refine (_ ,, _) ; cbn.
    - use PullbackArrow.
      + exact (PullbackPr1 _ · pr1 gp).
      + apply PullbackPr2.
      + abstract
          (refine (_ @ PullbackSqrCommutes (HC y (pr1 zg₁) x (pr2 zg₁) f)) ;
           rewrite !assoc' ;
           apply maponpaths ;
           refine (pr2 gp @ _) ;
           apply id_right).
    - abstract
        (rewrite PullbackArrow_PullbackPr2 ;
         rewrite id_right ;
         apply idpath).
  Defined.

  Proposition cod_fiber_functor_on_mor
              {x y : C}
              (f : x --> y)
              {zg₁ zg₂ : C/y}
              (gp : zg₁ --> zg₂)
    : #(cod_pb HC f) gp
      =
      cod_fiber_functor_pb f gp.
  Proof.
    use eq_mor_cod_fib.
    cbn.
    unfold cartesian_cod_disp_map.
    use (MorphismsIntoPullbackEqual
           (isPullback_Pullback (HC y (pr1 zg₂) x (pr2 zg₂) f))) ; cbn.
    - rewrite !PullbackArrow_PullbackPr1.
      etrans.
      {
        apply (PullbackArrow_PullbackPr1 (HC y (pr1 zg₂) x (pr2 zg₂) f)).
      }
      rewrite transportf_cod_disp.
      cbn.
      apply idpath.
    - rewrite !PullbackArrow_PullbackPr2.
      etrans.
      {
        apply (PullbackArrow_PullbackPr2 (HC y (pr1 zg₂) x (pr2 zg₂) f)).
      }
      apply id_right.
  Qed.

  Definition cod_fiber_functor_on_eq_mor
             {x y : C}
             {f g : x --> y}
             (p : f = g)
             (φ : C/y)
    : fiber_functor_from_cleaving (disp_codomain C) (disp_codomain_cleaving HC) f φ
      -->
      fiber_functor_from_cleaving (disp_codomain C) (disp_codomain_cleaving HC) g φ.
  Proof.
    use make_cod_fib_mor.
    - use PullbackArrow.
      + apply PullbackPr1.
      + apply PullbackPr2.
      + abstract
          (refine (PullbackSqrCommutes (HC y (pr1 φ) x (pr2 φ) f) @ _) ;
           apply maponpaths ;
           exact p).
    - abstract
        (cbn ;
         rewrite PullbackArrow_PullbackPr2 ;
         apply idpath).
  Defined.

  Let HD : cleaving (disp_codomain C) := disp_codomain_cleaving HC.

  Proposition cod_fiber_functor_on_eq
              {x y : C}
              {f g : x --> y}
              (p : f = g)
              (φ : C/y)
    : fiber_functor_on_eq HD p φ
      =
      cod_fiber_functor_on_eq_mor p φ.
  Proof.
    induction p.
    use eq_mor_cod_fib.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    - cbn.
      rewrite PullbackArrow_PullbackPr1.
      rewrite id_left.
      apply idpath.
    - cbn.
      rewrite PullbackArrow_PullbackPr2.
      rewrite id_left.
      apply idpath.
  Qed.

  Definition cod_fiber_functor_from_cleaving_comp_mor
              {x y z : C}
              (f : x --> y)
              (g : y --> z)
              (φ : C/z)
    : cod_pb HC f (cod_pb HC g φ) --> cod_pb HC (f · g) φ.
  Proof.
    use make_cod_fib_mor.
    - use PullbackArrow.
      + exact (PullbackPr1 _ · PullbackPr1 _).
      + exact (PullbackPr2 _).
      + abstract
          (rewrite !assoc ;
           refine (_ @ maponpaths (λ z, z · g) (PullbackSqrCommutes _)) ;
           rewrite !assoc' ;
           apply maponpaths ;
           cbn ;
           apply PullbackSqrCommutes).
    - abstract
        (cbn ;
         rewrite PullbackArrow_PullbackPr2 ;
         apply idpath).
  Defined.

  Proposition cod_fiber_functor_from_cleaving_comp
              {x y z : C}
              (f : x --> y)
              (g : y --> z)
              (φ : C/z)
    : fiber_functor_from_cleaving_comp HD g f φ
      =
      cod_fiber_functor_from_cleaving_comp_mor f g φ.
  Proof.
    use eq_mor_cod_fib.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    - cbn.
      unfold cartesian_cod_disp_map ; cbn.
      refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
      rewrite PullbackArrow_PullbackPr1.
      unfold transportb ; cbn.
      rewrite pr1_transportf, transportf_const.
      cbn.
      apply idpath.
    - cbn.
      unfold cartesian_cod_disp_map ; cbn.
      refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
      rewrite PullbackArrow_PullbackPr2.
      apply id_right.
  Qed.

  Definition cod_fiber_functor_from_cleaving_comp_mor_inv
              {x y z : C}
              (f : x --> y)
              (g : y --> z)
              (φ : C/z)
    : cod_pb HC (f · g) φ --> cod_pb HC f (cod_pb HC g φ).
  Proof.
    use make_cod_fib_mor.
    - use PullbackArrow.
      + use PullbackArrow.
        * exact (PullbackPr1 _).
        * exact (PullbackPr2 _ · f).
        * abstract
            (refine (PullbackSqrCommutes _ @ _) ;
             apply assoc).
      + exact (PullbackPr2 _).
      + abstract
          (cbn ;
           rewrite PullbackArrow_PullbackPr2 ;
           apply idpath).
    - abstract
        (cbn ;
         rewrite PullbackArrow_PullbackPr2 ;
         apply idpath).
  Defined.

  Proposition cod_fiber_functor_from_cleaving_comp_inv
              {x y z : C}
              (f : x --> y)
              (g : y --> z)
              (φ : C/z)
    : fiber_functor_from_cleaving_comp_inv HD g f φ
      =
      cod_fiber_functor_from_cleaving_comp_mor_inv f g φ.
  Proof.
    use eq_mor_cod_fib.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    - cbn.
      unfold cartesian_cod_disp_map ; cbn.
      refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
      rewrite PullbackArrow_PullbackPr1.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      + refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
        rewrite PullbackArrow_PullbackPr1.
        rewrite pr1_transportf, transportf_const ; cbn.
        apply idpath.
      + refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
        rewrite PullbackArrow_PullbackPr2.
        rewrite id_left.
        apply idpath.
    - cbn.
      unfold cartesian_cod_disp_map ; cbn.
      refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
      rewrite PullbackArrow_PullbackPr2.
      apply id_right.
  Qed.

  (** * 5. The fiber of terminal objects *)
  Section FibTerminal.
    Context (T : Terminal C).

    Definition cod_fib_terminal_to_base_data
      : functor_data (C/T) C.
    Proof.
      use make_functor_data.
      - exact (λ yf, cod_dom yf).
      - exact (λ _ _ φp, dom_mor φp).
    Defined.

    Proposition cod_fib_terminal_to_base_laws
      : is_functor cod_fib_terminal_to_base_data.
    Proof.
      split.
      - intro x ; cbn.
        apply idpath.
      - intro ; intros ; cbn ; unfold dom_mor.
        rewrite transportf_cod_disp.
        cbn.
        apply idpath.
    Qed.

    Definition cod_fib_terminal_to_base
      : (C/T) ⟶ C.
    Proof.
      use make_functor.
      - exact cod_fib_terminal_to_base_data.
      - exact cod_fib_terminal_to_base_laws.
    Defined.

    Definition cod_fib_terminal_from_base_data
      : functor_data C (C/T).
    Proof.
      use make_functor_data.
      - exact (λ x, make_cod_fib_ob (TerminalArrow T x)).
      - simple refine (λ _ _ f, make_cod_fib_mor _ _).
        + exact f.
        + abstract
            (cbn ;
             apply TerminalArrowEq).
    Defined.

    Proposition cod_fib_terminal_from_base_laws
      : is_functor cod_fib_terminal_from_base_data.
    Proof.
      split.
      - intro x.
        use eq_mor_cod_fib ; cbn.
        apply idpath.
      - intro ; intros.
        use eq_mor_cod_fib.
        rewrite comp_in_cod_fib.
        apply idpath.
    Qed.

    Definition cod_fib_terminal_from_base
      : C ⟶ (C/T).
    Proof.
      use make_functor.
      - exact cod_fib_terminal_from_base_data.
      - exact cod_fib_terminal_from_base_laws.
    Defined.

    Definition cod_fib_terminal_unit
      : functor_identity _
        ⟹
        cod_fib_terminal_to_base ∙ cod_fib_terminal_from_base.
    Proof.
      use make_nat_trans.
      - simple refine (λ x, make_cod_fib_mor _ _).
        + apply identity.
        + abstract
            (cbn ;
             apply TerminalArrowEq).
      - abstract
          (intros x y f ;
           use eq_mor_cod_fib ;
           rewrite !comp_in_cod_fib ;
           cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Definition cod_fib_terminal_counit
      : cod_fib_terminal_from_base ∙ cod_fib_terminal_to_base
        ⟹
        functor_identity C.
    Proof.
      use make_nat_trans.
      - exact (λ x, identity _).
      - abstract
          (intros x y f ; cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Definition cod_fib_terminal_equivalence
      : equivalence_of_cats (C/T) C.
    Proof.
      use make_equivalence_of_cats.
      - use make_adjunction_data.
        + exact cod_fib_terminal_to_base.
        + exact cod_fib_terminal_from_base.
        + exact cod_fib_terminal_unit.
        + exact cod_fib_terminal_counit.
      - split.
        + intro x.
          use is_z_iso_fiber_from_is_z_iso_disp.
          use is_z_iso_disp_codomain.
          apply identity_is_z_iso.
        + intro x.
          apply identity_is_z_iso.
    Defined.

    Definition cod_fib_terminal
      : adj_equivalence_of_cats
          cod_fib_terminal_to_base
      := adjointification cod_fib_terminal_equivalence.
  End FibTerminal.
End CodomainFiber.
