(***************************************************************************************

 Structure of the codomain fibration

 In this file, we establish some structure of the codomain fibration. More specifically,
 we first show that the reindexing functor has a left adjoint, which is given by the
 composition operation. From this we directly obtain that reindexing preserves all limits.
 Next we show that every fiber has a terminal object (given by the identity morphism),
 binary products (given by pullbacks), and equalizers (given by equalizers). Along the way,
 we also establish necessary and sufficient conditions to be a terminal object, product,
 or an equalizer in the fiber categories.

 We also give some useful operations on fiber categories of the codomain fibration. In
 addition, we should use that the fiber of the terminal object is equivalent to the base
 category.


 Contents
 1. Constructions on fiber of codomain
 2. Fiber of terminal objects
 3. Substitution functor
 3. Left adjoint for substitution
 4. Preservation of substitution
 5. Fiberwise terminal objects
 6. Fiberwise binary products
 7. Fiberwise equalizers

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseEqualizers.

Local Open Scope cat.

(* TODO: MOVE TO THE PULLBACKS FILE *)
Section EqualizersFromPullbackProducts.
  Context {C : category}
          (PB : Pullbacks C)
          (P : BinProducts C).

  Section EqualizerConstruction.
    Context {x y : C}
            (f g : x --> y).

    Let Δ : y --> P y y := diagonalMap' P y.
    Let φ : x --> P y y := BinProductArrow _ (P y y) f g.

    Let e : Pullback Δ φ := PB _ _ _ Δ φ.
    Let i : e --> x := PullbackPr2 e.

    Proposition equalizer_from_pb_prod_eq
      : i · f = i · g.
    Proof.
      pose (maponpaths (λ z, z · BinProductPr1 _ _) (PullbackSqrCommutes e)) as p.
      cbn in p.
      rewrite !assoc' in p.
      unfold Δ, φ, diagonalMap' in p.
      rewrite !BinProductPr1Commutes in p.
      rewrite id_right in p.
      refine (!p @ _).
      clear p.
      pose (maponpaths (λ z, z · BinProductPr2 _ _) (PullbackSqrCommutes e)) as p.
      cbn in p.
      rewrite !assoc' in p.
      unfold Δ, φ, diagonalMap' in p.
      rewrite !BinProductPr2Commutes in p.
      rewrite id_right in p.
      exact p.
    Qed.

    Section UMP.
      Context {w : C}
              {h : w --> x}
              (p : h · f = h · g).

      Proposition equalizer_from_pb_prod_map_eq
        : h · f · Δ = h · φ.
      Proof.
        unfold Δ, diagonalMap', φ.
        use BinProductArrowsEq.
        - rewrite !assoc'.
          rewrite !BinProductPr1Commutes.
          rewrite id_right.
          apply idpath.
        - rewrite !assoc'.
          rewrite !BinProductPr2Commutes.
          rewrite id_right.
          exact p.
      Qed.

      Proposition equalizer_from_pb_prod_unique
        : isaprop (∑ (ζ : w --> e), ζ · i = h).
      Proof.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        use (MorphismsIntoPullbackEqual (isPullback_Pullback e)).
        - use (diagonalMap_isMonic P y).
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            exact (PullbackSqrCommutes e).
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (pr2 ζ₁).
          }
          rewrite !assoc'.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            exact (PullbackSqrCommutes e).
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (pr2 ζ₂).
          }
          apply idpath.
        - exact (pr2 ζ₁ @ !(pr2 ζ₂)).
      Qed.

      Definition equalizer_from_pb_prod_map
        : w --> e.
      Proof.
        use (PullbackArrow e _ (h · f) h).
        apply equalizer_from_pb_prod_map_eq.
      Defined.

      Proposition equalizer_from_pb_prod_comm
        : equalizer_from_pb_prod_map · i = h.
      Proof.
        exact (PullbackArrow_PullbackPr2 e _ (h · f) h equalizer_from_pb_prod_map_eq).
      Qed.
    End UMP.

    Definition equalizer_from_pb_prod
      : Equalizer f g.
    Proof.
      use make_Equalizer.
      - exact e.
      - exact i.
      - exact equalizer_from_pb_prod_eq.
      - intros w h p.
        use iscontraprop1.
        + apply equalizer_from_pb_prod_unique.
        + refine (equalizer_from_pb_prod_map p ,, _).
          exact (equalizer_from_pb_prod_comm p).
    Defined.
  End EqualizerConstruction.

  Definition equalizers_from_pullbacks_prods
    : Equalizers C.
  Proof.
    intros x y f g.
    apply equalizer_from_pb_prod.
  Defined.
End EqualizersFromPullbackProducts.

Definition equalizers_from_pullbacks_terminal
           {C : category}
           (PB : Pullbacks C)
           (T : Terminal C)
  : Equalizers C.
Proof.
  use equalizers_from_pullbacks_prods.
  - exact PB.
  - exact (BinProductsFromPullbacks PB T).
Defined.

Section CodomainStructure.
  Context {C : category}.

  Let D : disp_cat C := disp_codomain C.

  (** * 1. Constructions on fiber of codomain *)
  Definition cod_fib_id
             (x : C)
    : D [{x}].
  Proof.
    refine (x ,, _).
    exact (identity x).
  Defined.

  Definition mor_to_cod_fib_id
             {x : C}
             (fy : D[{x}])
    : fy --> cod_fib_id x.
  Proof.
    refine (pr2 fy ,, _).
    abstract
      (cbn ;
       apply idpath).
  Defined.

  Definition cod_fib_comp
             {x y : C}
             (f : x --> y)
             (gz : D [{x}])
    : D [{y}]
    := pr1 gz ,, pr2 gz · f.

  Proposition comp_in_cod_fib
              {x : C}
              {gz₁ gz₂ gz₃ : D[{x}]}
              (φp : gz₁ --> gz₂)
              (ψq : gz₂ --> gz₃)
    : pr1 (φp · ψq) = pr1 φp · pr1 ψq.
  Proof.
    cbn.
    rewrite transportf_cod_disp.
    apply idpath.
  Qed.

  (** * 2. Fiber of terminal objects *)
  Section FibTerminal.
    Context (T : Terminal C).

    Definition cod_fib_terminal_to_base_data
      : functor_data D[{T}] C.
    Proof.
      use make_functor_data.
      - exact (λ yf, pr1 yf).
      - exact (λ _ _ φp, pr1 φp).
    Defined.

    Proposition cod_fib_terminal_to_base_laws
      : is_functor cod_fib_terminal_to_base_data.
    Proof.
      split.
      - intro x ; cbn.
        apply idpath.
      - intro ; intros ; cbn.
        rewrite transportf_cod_disp.
        cbn.
        apply idpath.
    Qed.

    Definition cod_fib_terminal_to_base
      : D[{T}] ⟶ C.
    Proof.
      use make_functor.
      - exact cod_fib_terminal_to_base_data.
      - exact cod_fib_terminal_to_base_laws.
    Defined.

    Definition cod_fib_terminal_from_base_data
      : functor_data C D[{T}].
    Proof.
      use make_functor_data.
      - exact (λ x, x ,, TerminalArrow T x).
      - refine (λ _ _ f, f ,, _).
        abstract
          (cbn ;
           apply TerminalArrowEq).
    Defined.

    Proposition cod_fib_terminal_from_base_laws
      : is_functor cod_fib_terminal_from_base_data.
    Proof.
      split.
      - intro x.
        use eq_cod_mor ; cbn.
        apply idpath.
      - intro ; intros.
        use eq_cod_mor ; cbn.
        rewrite transportf_cod_disp.
        apply idpath.
    Qed.

    Definition cod_fib_terminal_from_base
      : C ⟶ D[{T}].
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
      - refine (λ x, identity _ ,, _).
        abstract
          (cbn ;
           apply TerminalArrowEq).
      - abstract
          (intros x y f ;
           use eq_cod_mor ;
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
      : equivalence_of_cats (D[{T}]) C.
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

  (** * 3. Substitution functor *)
  Context (HC : Pullbacks C).

  Let HD : cleaving D := disp_codomain_cleaving HC.

  Definition cod_fib_pb_comp
             {x y : C}
             (f : x --> y)
             (zg : D[{x}])
    : zg --> fiber_functor_from_cleaving D HD f (cod_fib_comp f zg).
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
             {zg₁ zg₂ : D[{y}]}
             (gp : zg₁ --> zg₂)
    : fiber_functor_from_cleaving D HD f zg₁
      -->
      fiber_functor_from_cleaving D HD f zg₂.
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
              {zg₁ zg₂ : D[{y}]}
              (gp : zg₁ --> zg₂)
    : # (fiber_functor_from_cleaving D HD f) gp
      =
      cod_fiber_functor_pb f gp.
  Proof.
    use eq_cod_mor.
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

  (** * 4. Left adjoint for substitution *)
  Section LeftAdjoint.
    Context {x y : C}
            {f : x --> y}
            {zg : D[{x}]}
            {wh : D[{y}]}
            (φp : zg --> fiber_functor_from_cleaving D HD f wh).

    Let z : C := pr1 zg.
    Let g : z --> x := pr2 zg.
    Let w : C := pr1 wh.
    Let h : w --> y := pr2 wh.
    Let φ : pr1 zg --> pr1 (fiber_functor_from_cleaving D HD f wh) := pr1 φp.

    Proposition cod_fiber_functor_adj_unique
      : isaprop
          (∑ (f' : cod_fib_comp f zg --> wh),
           cod_fib_pb_comp f zg · # (fiber_functor_from_cleaving D HD f) f'
           =
           φp).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use eq_cod_mor.
      pose (maponpaths pr1 (pr2 ζ₁ @ !(pr2 ζ₂))) as p.
      rewrite !cod_fiber_functor_on_mor in p.
      rewrite !comp_in_cod_fib in p.
      cbn in p.
      pose (maponpaths (λ z, z · PullbackPr1 _) p) as p'.
      cbn in p'.
      rewrite !assoc' in p'.
      rewrite !PullbackArrow_PullbackPr1 in p'.
      rewrite !assoc in p'.
      rewrite !PullbackArrow_PullbackPr1 in p'.
      rewrite !id_left in p'.
      exact p'.
    Qed.

    Definition cod_fiber_functor_adj_mor
      : cod_fib_comp f zg --> wh.
    Proof.
      simple refine (_ ,, _).
      - exact (φ · PullbackPr1 (HC y (pr1 wh) x (pr2 wh) f)).
      - abstract
          (cbn ;
           rewrite !id_right ;
           rewrite !assoc' ;
           rewrite (PullbackSqrCommutes (HC y (pr1 wh) x (pr2 wh) f)) ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           refine (pr2 φp @ _) ;
           apply id_right).
    Defined.

    Proposition cod_fiber_functor_adj_comm
      : cod_fib_pb_comp f zg
        · # (fiber_functor_from_cleaving D HD f) cod_fiber_functor_adj_mor
        =
        φp.
    Proof.
      rewrite cod_fiber_functor_on_mor.
      use eq_cod_mor.
      rewrite comp_in_cod_fib.
      cbn.
      use (MorphismsIntoPullbackEqual
             (isPullback_Pullback (HC y (pr1 wh) x (pr2 wh) f))).
      - rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        rewrite !assoc.
        rewrite PullbackArrow_PullbackPr1.
        rewrite id_left.
        apply idpath.
      - rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr2.
        rewrite PullbackArrow_PullbackPr2.
        refine (!(pr2 φp @ _)).
        apply id_right.
    Qed.
  End LeftAdjoint.

  Definition is_universal_arrow_to_cod_fiber_functor
             {x y : C}
             (f : x --> y)
             (zg : D[{x}])
    : is_universal_arrow_to
        (fiber_functor_from_cleaving D HD f)
        zg
        (cod_fib_comp f zg)
        (cod_fib_pb_comp f zg).
  Proof.
    intros wh φp.
    use iscontraprop1.
    - apply cod_fiber_functor_adj_unique.
    - refine (cod_fiber_functor_adj_mor φp ,, _).
      exact (cod_fiber_functor_adj_comm φp).
  Defined.

  Definition is_right_adjoint_cod_fiber_functor
             {x y : C}
             (f : x --> y)
    : is_right_adjoint (fiber_functor_from_cleaving D HD f).
  Proof.
    use right_adjoint_left_from_partial.
    - exact (λ zg, cod_fib_comp f zg).
    - exact (λ zg, cod_fib_pb_comp f zg).
    - exact (is_universal_arrow_to_cod_fiber_functor f).
  Defined.

  Definition cod_fiber_sigma_adjunction
             {x y : C}
             (f : x --> y)
    : adjunction D[{x}] D[{y}].
  Proof.
    use right_adjoint_to_adjunction.
    - exact (fiber_functor_from_cleaving D HD f).
    - exact (is_right_adjoint_cod_fiber_functor f).
  Defined.

  (** * 5. Preservation of substitution *)
  Proposition codomain_fib_preserves_terminal
              {x y : C}
              (f : x --> y)
    : preserves_terminal (fiber_functor_from_cleaving D HD f).
  Proof.
    exact (right_adjoint_preserves_terminal _ (cod_fiber_sigma_adjunction f)).
  Qed.

  Proposition codomain_fib_preserves_binproduct
              {x y : C}
              (f : x --> y)
    : preserves_binproduct (fiber_functor_from_cleaving D HD f).
  Proof.
    exact (right_adjoint_preserves_binproduct _ (cod_fiber_sigma_adjunction f)).
  Qed.

  Proposition codomain_fib_preserves_equalizer
              {x y : C}
              (f : x --> y)
    : preserves_equalizer (fiber_functor_from_cleaving D HD f).
  Proof.
    exact (right_adjoint_preserves_equalizer _ (cod_fiber_sigma_adjunction f)).
  Qed.

  (** * 6. Fiberwise terminal objects *)
  Proposition isTerminal_codomain_fib
              {x : C}
              (yf : D[{x}])
              (H : is_z_isomorphism (pr2 yf))
    : isTerminal (D[{x}]) yf.
  Proof.
    pose (f := (_ ,, H) : z_iso _ _).
    intro zg.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use eq_cod_mor ;
         use (cancel_z_iso _ _ f) ;
         exact (pr2 φ₁ @ !(pr2 φ₂))).
    - simple refine (_ ,, _).
      + exact (pr2 zg · inv_from_z_iso f).
      + abstract
          (cbn ;
           rewrite !assoc' ;
           apply maponpaths ;
           apply (z_iso_after_z_iso_inv f)).
  Defined.

  Proposition is_z_iso_from_isTerminal_codomain
              {x : C}
              (yf : D[{x}])
              (H : isTerminal (D[{x}]) yf)
    : is_z_isomorphism (pr2 yf).
  Proof.
    pose (T := (_ ,, H) : Terminal _).
    pose (φ := TerminalArrow T (cod_fib_id x)).
    simple refine (_ ,, _ ,, _).
    - exact (pr1 φ).
    - abstract
        (use (maponpaths pr1 (TerminalArrowEq (T := T) (_ · _ ,, _) (identity _))) ;
         cbn ;
         rewrite !assoc' ;
         apply maponpaths ;
         refine (pr2 φ @ _) ; cbn ;
         apply id_right).
    - abstract
        (refine (pr2 φ @ _) ; cbn ;
         apply id_right).
  Defined.

  Definition codomain_fib_terminal
             (x : C)
    : Terminal D[{x}].
  Proof.
    use make_Terminal.
    - refine (x ,, _).
      exact (identity x).
    - use isTerminal_codomain_fib.
      apply identity_is_z_iso.
  Defined.

  Definition codomain_fiberwise_terminal
    : fiberwise_terminal HD.
  Proof.
    split.
    - exact codomain_fib_terminal.
    - exact (λ x y, codomain_fib_preserves_terminal).
  Defined.

  (** * 7. Fiberwise binary products *)
  Definition fib_isPullback
             {x : C}
             {fy₁ fy₂ gp : D[{x}]}
             (π₁ : gp --> fy₁)
             (π₂ : gp --> fy₂)
    : pr1 π₁ · pr2 fy₁ = pr1 π₂ · pr2 fy₂.
  Proof.
    exact (pr2 π₁ @ !(pr2 π₂)).
  Qed.

  Section ToIsProd.
    Context {x : C}
            {fy₁ fy₂ gp : D[{x}]}
            {π₁ : gp --> fy₁}
            {π₂ : gp --> fy₂}
            (H : isPullback (fib_isPullback π₁ π₂))
            {wh : D[{x}]}
            (φq : wh --> fy₁)
            (ψr : wh --> fy₂).

    Let P : Pullback (pr2 fy₁) (pr2 fy₂)
      := make_Pullback _ H.

    Proposition isPullback_to_isBinproduct_cod_fib_unique
      : isaprop (∑ (fg : wh --> gp), fg · π₁ = φq × fg · π₂ = ψr).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use eq_cod_mor.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback P) _ _ _ _ _).
      - pose (s := maponpaths pr1 (pr12 ζ₁ @ !(pr12 ζ₂))).
        rewrite !comp_in_cod_fib in s.
        exact s.
      - pose (s := maponpaths pr1 (pr22 ζ₁ @ !(pr22 ζ₂))).
        rewrite !comp_in_cod_fib in s.
        exact s.
    Qed.

    Definition isPullback_to_isBinproduct_cod_fib_mor
      : wh --> gp.
    Proof.
      simple refine (_ ,, _).
      - use (PullbackArrow P).
        + exact (pr1 φq).
        + exact (pr1 ψr).
        + abstract
            (exact (pr2 φq @ !(pr2 ψr))).
      - abstract
          (cbn ;
           pose (pr2 π₁) as s ;
           cbn in s ;
           rewrite id_right in s ;
           rewrite <- s ;
           rewrite !assoc ;
           rewrite (PullbackArrow_PullbackPr1 P) ;
           exact (pr2 φq)).
    Defined.

    Proposition isPullback_to_isBinproduct_cod_fib_pr1
      : isPullback_to_isBinproduct_cod_fib_mor · π₁ = φq.
    Proof.
      use eq_cod_mor.
      rewrite comp_in_cod_fib.
      apply (PullbackArrow_PullbackPr1 P).
    Qed.

    Proposition isPullback_to_isBinproduct_cod_fib_pr2
      : isPullback_to_isBinproduct_cod_fib_mor · π₂ = ψr.
    Proof.
      use eq_cod_mor.
      rewrite comp_in_cod_fib.
      apply (PullbackArrow_PullbackPr2 P).
    Qed.
  End ToIsProd.

  Definition isPullback_to_isBinProduct_cod_fib
             {x : C}
             {fy₁ fy₂ gp : D[{x}]}
             (π₁ : gp --> fy₁)
             (π₂ : gp --> fy₂)
             (H : isPullback (fib_isPullback π₁ π₂))
    : isBinProduct _ fy₁ fy₂ gp π₁ π₂.
  Proof.
    intros wh φq ψr.
    use iscontraprop1.
    - apply (isPullback_to_isBinproduct_cod_fib_unique H).
    - simple refine (_ ,, _ ,, _).
      + exact (isPullback_to_isBinproduct_cod_fib_mor H φq ψr).
      + apply isPullback_to_isBinproduct_cod_fib_pr1.
      + apply isPullback_to_isBinproduct_cod_fib_pr2.
  Defined.

  Section ToIsPb.
    Context {x : C}
            {fy₁ fy₂ gp : D[{x}]}
            {π₁ : gp --> fy₁}
            {π₂ : gp --> fy₂}
            (H : isBinProduct _ fy₁ fy₂ gp π₁ π₂)
            {w : C}
            (φ : w --> pr1 fy₁)
            (ψ : w --> pr1 fy₂)
            (s : φ · pr2 fy₁ = ψ · pr2 fy₂).

    Let P : BinProduct _ _ _ := make_BinProduct _ _ _ _ _ _ H.

    Let wh : D[{x}].
    Proof.
      refine (w ,, _).
      exact (φ · pr2 fy₁).
    Defined.

    Local Definition φq
      : wh --> fy₁.
    Proof.
      refine (φ ,, _).
      abstract
        (cbn ;
         rewrite id_right ;
         apply idpath).
    Defined.

    Local Definition ψr
      : wh --> fy₂.
    Proof.
      refine (ψ ,, _).
      abstract
        (cbn ;
         rewrite id_right ;
         rewrite s ;
         apply idpath).
    Defined.

    Proposition isBinProduct_to_isPullback_cod_fib_unique
      : isaprop (∑ (hk : w --> pr1 gp), hk · pr1 π₁ = φ × hk · pr1 π₂ = ψ).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use (maponpaths
             pr1
             (BinProductArrowsEq _ _ _ P wh (_ ,, _) (_ ,, _) _ _)).
      - cbn.
        etrans.
        {
          apply maponpaths.
          refine (_ @ !(pr2 π₁)).
          exact (!(id_right _)).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (pr12 ζ₁).
        }
        rewrite id_right.
        apply idpath.
      - cbn.
        etrans.
        {
          apply maponpaths.
          refine (_ @ !(pr2 π₁)).
          exact (!(id_right _)).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (pr12 ζ₂).
        }
        rewrite id_right.
        apply idpath.
      - use eq_cod_mor.
        refine (comp_in_cod_fib _ _ @ _ @ !(comp_in_cod_fib _ _)).
        cbn.
        exact (pr12 ζ₁ @ !(pr12 ζ₂)).
      - use eq_cod_mor.
        refine (comp_in_cod_fib _ _ @ _ @ !(comp_in_cod_fib _ _)).
        cbn.
        exact (pr22 ζ₁ @ !(pr22 ζ₂)).
    Qed.

    Definition isBinProduct_to_isPullback_cod_fib_mor
      : pr1 wh --> pr1 gp
      := pr1 (BinProductArrow _ P φq ψr).

    Proposition isBinProduct_to_isPullback_cod_fib_pr1
      : isBinProduct_to_isPullback_cod_fib_mor · pr1 π₁ = φ.
    Proof.
      refine (_ @ maponpaths pr1 (BinProductPr1Commutes _ _ _ P _ φq ψr)).
      rewrite comp_in_cod_fib.
      apply idpath.
    Qed.

    Proposition isBinProduct_to_isPullback_cod_fib_pr2
      : isBinProduct_to_isPullback_cod_fib_mor · pr1 π₂ = ψ.
    Proof.
      refine (_ @ maponpaths pr1 (BinProductPr2Commutes _ _ _ P _ φq ψr)).
      rewrite comp_in_cod_fib.
      apply idpath.
    Qed.
  End ToIsPb.

  Definition isBinProduct_to_isPullback_cod_fib
             {x : C}
             {fy₁ fy₂ gp : D[{x}]}
             (π₁ : gp --> fy₁)
             (π₂ : gp --> fy₂)
             (H : isBinProduct _ fy₁ fy₂ gp π₁ π₂)
    : isPullback (fib_isPullback π₁ π₂).
  Proof.
    intros w φ ψ s.
    use iscontraprop1.
    - apply (isBinProduct_to_isPullback_cod_fib_unique H).
    - simple refine (_ ,, _ ,, _).
      + exact (isBinProduct_to_isPullback_cod_fib_mor H φ ψ s).
      + apply isBinProduct_to_isPullback_cod_fib_pr1.
      + apply isBinProduct_to_isPullback_cod_fib_pr2.
  Defined.

  Definition codomain_fib_binproducts
             (x : C)
    : BinProducts D[{x}].
  Proof.
    intros fy₁ fy₂.
    pose (P := HC _ _ _ (pr2 fy₁) (pr2 fy₂)).
    use make_BinProduct.
    - refine (PullbackObject P ,, _).
      exact (PullbackPr1 P · pr2 fy₁).
    - refine (PullbackPr1 P ,, _).
      abstract
        (cbn ;
         rewrite id_right ;
         apply idpath).
    - refine (PullbackPr2 P ,, _).
      abstract
        (cbn ;
         rewrite PullbackSqrCommutes ;
         rewrite id_right ;
         apply idpath).
    - use isPullback_to_isBinProduct_cod_fib.
      apply P.
  Defined.

  Definition codomain_fiberwise_binproducts
    : fiberwise_binproducts HD.
  Proof.
    split.
    - exact codomain_fib_binproducts.
    - exact (λ x y, codomain_fib_preserves_binproduct).
  Defined.

  (** * 8. Fiberwise equalizers *)
  Section EqualizerCodFib.
    Context {x : C}
            {ee fy₁ fy₂ : D[{x}]}
            (φp ψq : fy₁ --> fy₂)
            (ρr : ee --> fy₁)
            (s : ρr · φp = ρr · ψq).

    Let y₁ : C := pr1 fy₁.
    Let f₁ : y₁ --> x := pr2 fy₁.

    Let y₂ : C := pr1 fy₂.
    Let f₂ : y₂ --> x := pr2 fy₂.

    Let e : C := pr1 ee.
    Let m : e --> x := pr2 ee.

    Let φ : y₁ --> y₂ := pr1 φp.
    Let ψ : y₁ --> y₂ := pr1 ψq.
    Let ρ : e --> y₁ := pr1 ρr.

    Context (s' : ρ · φ = ρ · ψ).

    Section ToEqCodFib.
      Context (H : isEqualizer φ ψ ρ s')
              {wh : D[{x}]}
              (τp : wh --> fy₁)
              (p : τp · φp = τp · ψq).

      Let E : Equalizer φ ψ := make_Equalizer _ _ _ _ H.

      Let w : C := pr1 wh.
      Let h : w --> x := pr2 wh.
      Let τ : w --> y₁ := pr1 τp.

      Proposition to_isEqualizer_cod_fib_unique
        : isaprop (∑ (ζ : wh --> ee), ζ · ρr = τp).
      Proof.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        use eq_cod_mor.
        use (EqualizerInsEq E).
        refine (_ @ maponpaths pr1 (pr2 ζ₁ @ !(pr2 ζ₂)) @ _).
        - rewrite comp_in_cod_fib.
          apply idpath.
        - rewrite comp_in_cod_fib.
          apply idpath.
      Qed.

      Definition to_isEqualizer_cod_fib_mor
        : wh --> ee.
      Proof.
        simple refine (_ ,, _).
        - use (EqualizerIn E _ τ).
          abstract
            (refine (_ @ maponpaths pr1 p @ _) ;
             rewrite comp_in_cod_fib ;
             apply idpath).
        - abstract
            (cbn ;
             pose (pr2 ρr) as hp ;
             cbn in hp ;
             rewrite id_right in hp ;
             rewrite <- hp ;
             rewrite !assoc ;
             etrans ;
             [ apply maponpaths_2 ;
               apply (EqualizerCommutes E)
             | ] ;
             exact (pr2 τp)).
      Defined.

      Proposition to_isEqualizer_cod_fib_comm
        : to_isEqualizer_cod_fib_mor · ρr = τp.
      Proof.
        use eq_cod_mor.
        rewrite comp_in_cod_fib.
        apply (EqualizerCommutes E).
      Qed.
    End ToEqCodFib.

    Definition to_isEqualizer_cod_fib
               (H : isEqualizer φ ψ ρ s')
      : isEqualizer φp ψq ρr s.
    Proof.
      intros wh τp p.
      use iscontraprop1.
      - exact (to_isEqualizer_cod_fib_unique H τp).
      - simple refine (_ ,, _).
        + exact (to_isEqualizer_cod_fib_mor H τp p).
        + exact (to_isEqualizer_cod_fib_comm H τp p).
    Defined.

    Section FromEqCodFib.
      Context (H : isEqualizer φp ψq ρr s)
              {w : C}
              (h : w --> y₁)
              (p : h · φ = h · ψ).

      Let E : Equalizer φp ψq := make_Equalizer _ _ _ _ H.

      Local Definition w' : D[{x}]
        := w ,, h · f₁.

      Local Definition h'
        : w' --> fy₁.
      Proof.
        refine (h ,, _).
        abstract
          (cbn ;
           rewrite id_right ;
           apply idpath).
      Defined.

      Local Lemma p'
        : h' · φp = h' · ψq.
      Proof.
        use eq_cod_mor.
        rewrite !comp_in_cod_fib.
        exact p.
      Qed.

      Proposition from_isEqualizer_cod_fib_unique
        : isaprop (∑ (ζ : w --> e), ζ · ρ = h).
      Proof.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        assert (H₁ : pr1 ζ₁ · pr2 ee = h · f₁ · identity x).
        {
          etrans.
          {
            apply maponpaths.
            refine (_ @ !(pr2 ρr)).
            exact (!(id_right _)).
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (pr2 ζ₁).
          }
          rewrite id_right.
          apply idpath.
        }
        assert (H₂ : pr1 ζ₂ · pr2 ee = h · f₁ · identity x).
        {
          etrans.
          {
            apply maponpaths.
            refine (_ @ !(pr2 ρr)).
            exact (!(id_right _)).
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (pr2 ζ₂).
          }
          rewrite id_right.
          apply idpath.
        }
        pose (ζ₁' := (pr1 ζ₁ ,, H₁) : w' --> ee).
        pose (ζ₂' := (pr1 ζ₂ ,, H₂) : w' --> ee).
        refine (maponpaths pr1 (EqualizerInsEq E ζ₁' ζ₂' _)).
        use eq_cod_mor.
        rewrite !comp_in_cod_fib.
        exact (pr2 ζ₁ @ !(pr2 ζ₂)).
      Qed.

      Definition from_isEqualizer_cod_fib_mor
        : w --> e
        := pr1 (EqualizerIn E w' h' p').

      Proposition from_isEqualizer_cod_fib_comm
        : from_isEqualizer_cod_fib_mor · ρ = h.
      Proof.
        refine (_ @ maponpaths pr1 (EqualizerCommutes E w' h' p')).
        rewrite comp_in_cod_fib.
        apply idpath.
      Qed.
    End FromEqCodFib.

    Definition from_isEqualizer_cod_fib
               (H : isEqualizer φp ψq ρr s)
      : isEqualizer φ ψ ρ s'.
    Proof.
      intros w h p.
      use iscontraprop1.
      - apply (from_isEqualizer_cod_fib_unique H).
      - simple refine (_ ,, _).
        + exact (from_isEqualizer_cod_fib_mor H h p).
        + exact (from_isEqualizer_cod_fib_comm H h p).
    Defined.
  End EqualizerCodFib.

  Definition codomain_fib_equalizer
             (H : Equalizers C)
             (x : C)
    : Equalizers (D[{x}]).
  Proof.
    intros fy₁ fy₂ φp ψq.
    pose (E := H (pr1 fy₁) (pr1 fy₂) (pr1 φp) (pr1 ψq)).
    use make_Equalizer.
    - refine (EqualizerObject E ,, _).
      exact (EqualizerArrow E · pr2 fy₁).
    - refine (EqualizerArrow E ,, _).
      abstract
        (cbn ;
         rewrite id_right ;
         apply idpath).
    - abstract
        (use eq_cod_mor ;
         rewrite !comp_in_cod_fib ;
         cbn ;
         apply EqualizerEqAr).
    - use to_isEqualizer_cod_fib.
      + apply EqualizerEqAr.
      + exact (isEqualizer_Equalizer E).
  Defined.

  Definition codomain_fiberwise_equalizers_from_equalizers
             (H : Equalizers C)
    : fiberwise_equalizers HD.
  Proof.
    split.
    - exact (codomain_fib_equalizer H).
    - exact (λ x y, codomain_fib_preserves_equalizer).
  Defined.

  Definition codomain_fiberwise_equalizers
             (T : Terminal C)
    : fiberwise_equalizers HD.
  Proof.
    use codomain_fiberwise_equalizers_from_equalizers.
    use equalizers_from_pullbacks_terminal.
    - exact HC.
    - exact T.
  Defined.
End CodomainStructure.
