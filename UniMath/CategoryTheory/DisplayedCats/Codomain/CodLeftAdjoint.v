(***************************************************************************************

 Left adjoint to substitution for the codomain

 The fibers of the codomain fibration are given by slice categories and the functors
 between them are given by taking the pullback. Each of these functors has a left adjoint,
 which is given by composition. In this file, we establish this fact.

 There are multiple ways to construct this adjoint. We construct the unit and counit
 of this adjunction directly rather than using universal arrows. The reason for doing
 so, is because we want the right adjoint of this functor to compute nicely. For that
 reason, we construct it explicitly. The advantage of having nice computational behavior
 of this right adjoint, is that it helps with verifying the Beck-Chevalley conditions.

 We also verify that the codomain fibration has dependent sums. The main work here lies
 in calculating the Beck-Chevalley map.

 Contents
 1. The left adjoint
 2. The unit
 3. The counit
 4. The triangle equalities
 5. The adjunction
 6. The Beck-Chevalley condition
 7. Dependent sums for the codomain

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.

Local Open Scope cat.

Section CodomainLeftAdj.
  Context {C : category}
          (HC : Pullbacks C)
          {x y : C}
          (f : x --> y).

  (** * 1. The left adjoint *)
  Definition comp_functor_data
    : functor_data (C/x) (C/y).
  Proof.
    use make_functor_data.
    - exact (cod_fib_comp f).
    - simple refine (λ g₁ g₂ h, make_cod_fib_mor _ _).
      + exact (dom_mor h).
      + abstract
          (cbn ;
           rewrite !assoc ;
           rewrite mor_eq ;
           apply idpath).
  Defined.

  Proposition comp_functor_laws
    : is_functor comp_functor_data.
  Proof.
    split.
    - intro g.
      use eq_mor_cod_fib ; cbn.
      apply idpath.
    - intros g₁ g₂ g₃ h₁ h₂.
      use eq_mor_cod_fib.
      cbn -[fiber_category].
      rewrite !comp_in_cod_fib.
      apply idpath.
  Qed.

  Definition comp_functor
    : (C/x) ⟶ (C/y).
  Proof.
    use make_functor.
    - exact comp_functor_data.
    - exact comp_functor_laws.
  Defined.

  Proposition dom_mor_comp_functor
              {g₁ g₂ : C/x}
              (h : g₁ --> g₂)
    : dom_mor (#comp_functor h) = dom_mor h.
  Proof.
    apply idpath.
  Qed.

  (** * 2. The unit *)
  Definition comp_functor_unit_data
    : nat_trans_data
        (functor_identity (C / x))
        (comp_functor ∙ cod_pb HC f).
  Proof.
    simple refine (λ g, make_cod_fib_mor _ _).
    - use PullbackArrow.
      + exact (identity (cod_dom g)).
      + exact (cod_mor g).
      + abstract
          (cbn ;
           apply id_left).
    - abstract
        (cbn ;
         rewrite PullbackArrow_PullbackPr2 ;
         apply idpath).
  Defined.

  Proposition comp_functor_unit_laws
    : is_nat_trans _ _ comp_functor_unit_data.
  Proof.
    intros g₁ g₂ h.
    use eq_mor_cod_fib.
    cbn -[fiber_category].
    rewrite !comp_in_cod_fib.
    cbn.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    - rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr1.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply (PullbackArrow_PullbackPr1 (HC y (cod_dom g₂) x (cod_mor g₂ · f) f)).
      }
      rewrite transportf_cod_disp.
      cbn.
      rewrite !assoc.
      rewrite PullbackArrow_PullbackPr1.
      rewrite id_left, id_right.
      apply idpath.
    - rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr2.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply (PullbackArrow_PullbackPr2 (HC y (cod_dom g₂) x (cod_mor g₂ · f) f)).
      }
      cbn.
      rewrite !assoc.
      rewrite PullbackArrow_PullbackPr2.
      refine (_ @ !(mor_eq h)).
      apply id_right.
  Qed.

  Definition comp_functor_unit
    : functor_identity _ ⟹ comp_functor ∙ cod_pb HC f.
  Proof.
    use make_nat_trans.
    - exact comp_functor_unit_data.
    - exact comp_functor_unit_laws.
  Defined.

  (** * 3. The counit *)
  Definition comp_functor_counit_data
    : nat_trans_data (cod_pb HC f ∙ comp_functor) (functor_identity (C / y)).
  Proof.
    simple refine (λ g, make_cod_fib_mor _ _).
    - apply PullbackPr1.
    - abstract
        (cbn ;
         apply PullbackSqrCommutes).
  Defined.

  Proposition comp_functor_counit_laws
    : is_nat_trans _ _ comp_functor_counit_data.
  Proof.
    intros g₁ g₂ h.
    use eq_mor_cod_fib.
    cbn -[fiber_category].
    rewrite !comp_in_cod_fib.
    cbn.
    etrans.
    {
      apply (PullbackArrow_PullbackPr1 (HC y (pr1 g₂) x (pr2 g₂) f)).
    }
    rewrite transportf_cod_disp.
    cbn.
    apply idpath.
  Qed.

  Definition comp_functor_counit
    : cod_pb HC f ∙ comp_functor ⟹ functor_identity _.
  Proof.
    use make_nat_trans.
    - exact comp_functor_counit_data.
    - exact comp_functor_counit_laws.
  Defined.

  (** * 4. The triangle equalities *)
  Proposition form_adj_comp_cod_pb
    : form_adjunction
        comp_functor
        (cod_pb HC f)
        comp_functor_unit
        comp_functor_counit.
  Proof.
    split.
    - intro g.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      cbn.
      rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    - intro g.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (HC y (pr1 g) x (pr2 g) f))).
      + rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1 (HC y (pr1 g) x (pr2 g) f)).
        }
        rewrite transportf_cod_disp.
        cbn.
        rewrite !assoc.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      + rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2 (HC y (pr1 g) x (pr2 g) f)).
        }
        cbn.
        rewrite !assoc.
        rewrite PullbackArrow_PullbackPr2.
        rewrite id_left, id_right.
        apply idpath.
  Qed.

  (** * 5. The adjunction *)
  Definition is_right_adjoint_cod_fiber_functor
    : is_right_adjoint (cod_pb HC f).
  Proof.
    simple refine (_ ,, _).
    - exact comp_functor.
    - simple refine ((_ ,, _) ,, _).
      + exact comp_functor_unit.
      + exact comp_functor_counit.
      + exact form_adj_comp_cod_pb.
  Defined.

  Definition cod_fiber_sigma_adjunction
    : adjunction (C/x) (C/y).
  Proof.
    use right_adjoint_to_adjunction.
    - exact (cod_pb HC f).
    - exact is_right_adjoint_cod_fiber_functor.
  Defined.
End CodomainLeftAdj.

Arguments comp_functor_unit_data {C} HC {x y} f /.
Arguments comp_functor_counit_data {C} HC {x y} f /.

(** * 6. The Beck-Chevalley condition *)
Section BeckChevalley.
  Context {C : category}
          (HC : Pullbacks C)
          {w x y z : C}
          (f : x --> w)
          (g : y --> w)
          (h : z --> y)
          (k : z --> x)
          (p : k · f = h · g)
          (H : isPullback p).

  Let HD : cleaving (disp_codomain C) := disp_codomain_cleaving HC.
  Let P : Pullback f g := make_Pullback _ H.

  Definition cod_left_beck_chevalley_mor
             (φ : C/x)
    : cod_dom (cod_pb HC k φ)
      -->
      cod_dom (cod_pb HC g (cod_fib_comp f φ)).
  Proof.
    use PullbackArrow.
    - exact (PullbackPr1 _).
    - exact (PullbackPr2 _ · h).
    - abstract
        (cbn ;
         rewrite !assoc ;
         refine (maponpaths (λ z, z ·  _) (PullbackSqrCommutes _) @ _) ;
         rewrite !assoc' ;
         rewrite p ;
         apply idpath).
  Defined.

  Definition cod_left_beck_chevalley_mor_inv
             (φ : C/x)
    : cod_dom (cod_pb HC g (cod_fib_comp f φ))
      -->
      cod_dom (cod_pb HC k φ).
  Proof.
    use PullbackArrow.
    - exact (PullbackPr1 _).
    - use (PullbackArrow P).
      + exact (PullbackPr1 _ · cod_mor φ).
      + exact (PullbackPr2 _).
      + abstract
          (cbn ;
           rewrite !assoc' ;
           apply PullbackSqrCommutes).
    - abstract
        (exact (!(PullbackArrow_PullbackPr1 P _ _ _ _))).
  Defined.

  Proposition cod_left_beck_chevalley_mor_mor_inv
              (φ : C/x)
    : cod_left_beck_chevalley_mor φ · cod_left_beck_chevalley_mor_inv φ
      =
      identity _.
  Proof.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    - unfold cod_left_beck_chevalley_mor, cod_left_beck_chevalley_mor_inv.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      }
      etrans.
      {
        apply PullbackArrow_PullbackPr1.
      }
      rewrite id_left.
      apply idpath.
    - unfold cod_left_beck_chevalley_mor, cod_left_beck_chevalley_mor_inv.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply PullbackArrow_PullbackPr2.
      }
      rewrite id_left.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback P)).
      + rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1 P).
        }
        rewrite !assoc.
        rewrite PullbackArrow_PullbackPr1.
        apply PullbackSqrCommutes.
      + rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2 P).
        }
        apply PullbackArrow_PullbackPr2.
  Qed.

  Proposition cod_left_beck_chevalley_mor_inv_mor
              (φ : C/x)
    : cod_left_beck_chevalley_mor_inv φ · cod_left_beck_chevalley_mor φ
      =
      identity _.
  Proof.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    - unfold cod_left_beck_chevalley_mor, cod_left_beck_chevalley_mor_inv.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      }
      etrans.
      {
        apply PullbackArrow_PullbackPr1.
      }
      rewrite id_left.
      apply idpath.
    - unfold cod_left_beck_chevalley_mor, cod_left_beck_chevalley_mor_inv.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply PullbackArrow_PullbackPr2.
      }
      rewrite id_left.
      rewrite !assoc.
      rewrite PullbackArrow_PullbackPr2.
      apply (PullbackArrow_PullbackPr2 P).
  Qed.

  Definition is_z_isomorphism_cod_left_beck_chevalley_mor
             (φ : C/x)
    : is_z_isomorphism (cod_left_beck_chevalley_mor φ).
  Proof.
    use make_is_z_isomorphism.
    - exact (cod_left_beck_chevalley_mor_inv φ).
    - split.
      + apply cod_left_beck_chevalley_mor_mor_inv.
      + apply cod_left_beck_chevalley_mor_inv_mor.
  Defined.

  Proposition cod_left_beck_chevalley_eq
              (φ : C/x)
    : cod_left_beck_chevalley_mor φ
      =
      dom_mor
        (left_beck_chevalley_nat_trans
           (is_right_adjoint_cod_fiber_functor HC f)
           (is_right_adjoint_cod_fiber_functor HC h)
           (comm_nat_z_iso HD f g h k p)
           φ).
  Proof.
    refine (!_).
    rewrite left_beck_chevalley_nat_trans_ob.
    rewrite !comp_in_cod_fib.
    etrans.
    {
      apply maponpaths.
      simpl.
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (dom_mor_comp_functor h _ @ _).
      rewrite (cod_fiber_functor_on_mor HC k).
      cbn.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (dom_mor_comp_functor h _ @ _).
      etrans.
      {
        apply maponpaths.
        exact (comm_nat_z_iso_ob HD f g h k p _).
      }
      etrans.
      {
        apply (comp_in_cod_fib
                 _
                 (fiber_functor_from_cleaving_comp_inv HD g h _)).
      }
      etrans.
      {
        apply maponpaths_2.
        apply comp_in_cod_fib.
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply cod_fiber_functor_from_cleaving_comp_inv.
      }
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          do 2 apply maponpaths.
          apply cod_fiber_functor_on_eq.
        }
        apply maponpaths_2.
        apply maponpaths.
        apply cod_fiber_functor_from_cleaving_comp.
      }
      cbn.
      apply idpath.
    }
    rewrite !assoc'.
    rewrite PullbackArrow_PullbackPr1.
    unfold cod_left_beck_chevalley_mor.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    - rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr1.
      etrans.
      {
        do 3 apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      }
      rewrite !PullbackArrow_PullbackPr1.
      rewrite !assoc.
      rewrite PullbackArrow_PullbackPr1.
      rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr1.
      apply id_right.
    - rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr2.
      etrans.
      {
        do 3 apply maponpaths.
        apply PullbackArrow_PullbackPr2.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite !PullbackArrow_PullbackPr2.
      apply idpath.
  Qed.

  Definition cod_left_beck_chevalley
    : left_beck_chevalley
        HD
        f g h k
        p
        (is_right_adjoint_cod_fiber_functor HC f)
        (is_right_adjoint_cod_fiber_functor HC h).
  Proof.
    intro φ.
    use is_z_iso_fiber_from_is_z_iso_disp.
    use is_z_iso_disp_codomain.
    use is_z_isomorphism_path.
    - exact (cod_left_beck_chevalley_mor φ).
    - exact (cod_left_beck_chevalley_eq φ).
    - exact (is_z_isomorphism_cod_left_beck_chevalley_mor φ).
  Defined.
End BeckChevalley.

(** * 7. Dependent sums for the codomain *)
Definition cod_fiber_has_dependent_sum
           {C : category}
           (HC : Pullbacks C)
           (HD := disp_codomain_cleaving HC)
  : has_dependent_sums HD.
Proof.
  simple refine (_ ,, _).
  - exact (λ x y f, is_right_adjoint_cod_fiber_functor HC f).
  - exact (λ w x y z f g h k p H, cod_left_beck_chevalley HC f g h k p H).
Defined.
