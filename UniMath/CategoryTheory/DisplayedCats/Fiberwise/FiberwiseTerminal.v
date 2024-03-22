(***************************************************************************************

 Fiberwise terminal objects

 A fibration has a fiberwise terminal object if
 - Every fiber has a terminal object
 - These terminal objects are preserved under reindexing
 In this file, we define the notion of fiberwise terminal objects.

 Fiberwise terminal objects can be characterized by saying that the fibration has a
 right adjoint. We show that our definition implies the existence of the right adjoint.

 We also define when a displayed functor preserves fiberwise terminal objects. For this,
 it suffices to say that it preserves terminal objects for every fiber.

 Contents
 1. Fiberwise terminal objects
 2. Right adjoint from fiberwise terminal objects
 3. Preservation of fiberwise terminal objects

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

(** * 1. Fiberwise terminal objects *)
Definition fiberwise_terminal
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
  : UU
  := (∏ (x : C),
      Terminal (D[{x}]))
     ×
     (∏ (x y : C)
        (f : x --> y),
      preserves_terminal (fiber_functor_from_cleaving D HD f)).

Definition terminal_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (T : fiberwise_terminal HD)
           (x : C)
  : Terminal (D[{x}])
  := pr1 T x.

Definition terminal_obj_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (T : fiberwise_terminal HD)
           (x : C)
  : D[{x}]
  := terminal_in_fib T x.

Definition isTerminal_terminal_obj_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (T : fiberwise_terminal HD)
           (x : C)
  : isTerminal _ (terminal_obj_in_fib T x)
  := pr2 (pr1 T x).

Definition preserves_terminal_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (T : fiberwise_terminal HD)
           {x y : C}
           (f : x --> y)
  : preserves_terminal (fiber_functor_from_cleaving D HD f)
  := pr2 T x y f.

Definition lift_terminal_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (T : fiberwise_terminal HD)
           {x y : C}
           (f : x --> y)
  : Terminal (D[{x}])
  := make_Terminal
       _
       (preserves_terminal_in_fib T f _ (isTerminal_terminal_obj_in_fib T y)).

Proposition isaprop_fiberwise_terminal
            {C : category}
            {D : disp_univalent_category C}
            (HD : cleaving D)
  : isaprop (fiberwise_terminal HD).
Proof.
  use isapropdirprod.
  - use impred ; intro.
    apply isaprop_Terminal.
    use is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  - do 3 (use impred ; intro).
    apply isaprop_preserves_terminal.
Qed.

(** * 2. Right adjoint from fiberwise terminal objects *)
Section RightAdjointFromTerminal.
  Context {C : category}
          {D : disp_cat C}
          (HD : cleaving D)
          (T : fiberwise_terminal HD).

  Let E : category := total_category D.
  Let π : E ⟶ C := pr1_category D.

  Definition terminal_mor_lift
             {x y : C}
             (f : x --> y)
    : terminal_obj_in_fib T x -->[ f ] terminal_obj_in_fib T y
    := transportf
         _
         (id_left f)
         (TerminalArrow (lift_terminal_in_fib T f) _
          ;;
          HD y x f (terminal_obj_in_fib T y))%mor_disp.

  Proposition terminal_mor_factorization_eq
              {x y : C}
              {f : x --> x}
              (p : identity _ = f)
              {g g' : x --> y}
              (q : g = g')
              {xx : D x}
              (ff : xx -->[ f ] pr1 (HD y x g (terminal_obj_in_fib T y)))
              (gg : xx -->[ g' ] terminal_obj_in_fib T y)
    : (ff ;; HD y x g (terminal_obj_in_fib T y))%mor_disp
      =
      transportb
        (λ z, _ -->[ z ] _)
        (maponpaths (λ z, z · _) (!p) @ id_left _ @ q)
        gg.
  Proof.
    induction p, q.
    refine (_ @ cartesian_factorisation_commutes
                  (pr22 (HD y x g (terminal_obj_in_fib T y)))
                  _
                  _).
    apply maponpaths_2.
    apply (TerminalArrowEq (T := lift_terminal_in_fib T g)).
  Qed.

  Definition terminal_functor_data
    : functor_data C E.
  Proof.
    use make_functor_data.
    - exact (λ x, x ,, terminal_obj_in_fib T x).
    - exact (λ x y f, f ,, terminal_mor_lift f).
  Defined.

  Proposition is_functor_terminal_functor
    : is_functor terminal_functor_data.
  Proof.
    split.
    - intros x ; cbn.
      apply maponpaths.
      use (TerminalArrowEq (T := terminal_in_fib T x)).
    - intros x y z f g ; cbn.
      apply maponpaths.
      unfold terminal_mor_lift.
      cbn.
      rewrite mor_disp_transportf_postwhisker.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        use (terminal_mor_factorization_eq
               (idpath _)
               _
               _
               (TerminalArrow (lift_terminal_in_fib T f) (terminal_obj_in_fib T x)
                ;; HD y x f (terminal_obj_in_fib T y)
                ;; (TerminalArrow
                      (lift_terminal_in_fib T g)
                      (terminal_obj_in_fib T y)
                    ;; HD z y g (terminal_obj_in_fib T z)))%mor_disp).
        refine (maponpaths (λ z, _ · z) (!(id_left _)) @ _).
        apply maponpaths_2.
        exact (!(id_left _)).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition terminal_functor
    : C ⟶ E.
  Proof.
    use make_functor.
    - exact terminal_functor_data.
    - exact is_functor_terminal_functor.
  Defined.

  Definition terminal_functor_unit_data
    : nat_trans_data (functor_identity E) (π ∙ terminal_functor)
    := λ x, identity _ ,, TerminalArrow (terminal_in_fib T (pr1 x)) _.

  Proposition terminal_functor_unit_laws
    : is_nat_trans _ _ terminal_functor_unit_data.
  Proof.
    intros x y f ; unfold terminal_functor_unit_data ; cbn.
    use total2_paths_f ; cbn.
    - exact (id_right _ @ !(id_left _)).
    - unfold terminal_mor_lift.
      rewrite mor_disp_transportf_prewhisker.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (terminal_mor_factorization_eq
                 (!(id_right _))
                 (!(id_right _))
                 _
                 (pr2 f ;; TerminalArrow (terminal_in_fib T (pr1 y)) (pr2 y))%mor_disp).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition terminal_functor_unit
    : functor_identity E ⟹ π ∙ terminal_functor.
  Proof.
    use make_nat_trans.
    - exact terminal_functor_unit_data.
    - exact terminal_functor_unit_laws.
  Defined.

  Definition terminal_functor_counit
    : terminal_functor ∙ π ⟹ functor_identity C.
  Proof.
    use make_nat_trans.
    - exact (λ x, identity _).
    - abstract
        (intros x y f ; cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Proposition pr1_category_form_adjunction
    : form_adjunction
        π
        terminal_functor
        terminal_functor_unit
        terminal_functor_counit.
  Proof.
    split.
    - intros x ; cbn.
      apply id_left.
    - intros x ; cbn.
      use total2_paths_f.
      + apply id_left.
      + use (TerminalArrowEq (T := terminal_in_fib T x)).
  Qed.

  Definition is_left_adjoint_pr1_category
    : is_left_adjoint π.
  Proof.
    use are_adjoints_to_is_left_adjoint.
    - exact terminal_functor.
    - use make_are_adjoints.
      + exact terminal_functor_unit.
      + exact terminal_functor_counit.
      + exact pr1_category_form_adjunction.
  Defined.
End RightAdjointFromTerminal.

(** * 3. Preservation of fiberwise terminal objects *)
Definition preserves_fiberwise_terminal
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           (FF : disp_functor F D₁ D₂)
  : UU
  := ∏ (x : C₁),
     preserves_terminal (fiber_functor FF x).

Proposition isaprop_preserves_fiberwise_terminal
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {D₁ : disp_cat C₁}
            {D₂ : disp_cat C₂}
            (FF : disp_functor F D₁ D₂)
  : isaprop (preserves_fiberwise_terminal FF).
Proof.
  use impred ; intro.
  apply isaprop_preserves_terminal.
Qed.

Definition id_preserves_fiberwise_terminal
           {C : category}
           (D : disp_cat C)
  : preserves_fiberwise_terminal (disp_functor_identity D).
Proof.
  intros x y Hy.
  exact Hy.
Defined.

Definition comp_preserves_fiberwise_terminal
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           {D₃ : disp_cat C₃}
           {FF : disp_functor F D₁ D₂}
           (HFF : preserves_fiberwise_terminal FF)
           {GG : disp_functor G D₂ D₃}
           (HGG : preserves_fiberwise_terminal GG)
  : preserves_fiberwise_terminal (disp_functor_composite FF GG).
Proof.
  intros x y Hy ; cbn.
  apply HGG.
  apply HFF.
  exact Hy.
Defined.
