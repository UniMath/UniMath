Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.

Local Open Scope cat.

(*
 Approach:
 - The main thing that needs to be done, is some cleaning
 - The cleaning clarifies structure. The cleaning will be illuminating
 - The right adjoint of the terminal object functor: think about it, but that might not be an immediate goal
 - only fiberwise terminals, not more

 First goals:
 - Bicat with compcat with all desired type formers
 - Pseudofunctor from finlim to that bicat

 we need to further develop our interface for comprehension categories
 each operation must be named and get a notation

 think of levels and associativity

 main operations on contexts and substitutions: via `C`
 *)
Definition empty_Con
           (C : full_comp_cat)
  : Terminal C
  := empty_context C.

Definition comp_cat_Ty
           {C : full_comp_cat}
           (Γ : C)
  : UU
  := disp_cat_of_types C Γ.

Notation "'Ty'" := comp_cat_Ty.

Definition comp_cat_ext
           {C : full_comp_cat}
           (Γ : C)
           (A : Ty Γ)
  : C
  := comprehension_functor_ob (comp_cat_comprehension C) A.

Notation "Γ '&' A" := (comp_cat_ext Γ A) (at level 20).

Definition comp_cat_proj
           {C : full_comp_cat}
           (Γ : C)
           (A : Ty Γ)
  : Γ & A --> Γ
  := comprehension_functor_cod_mor (comp_cat_comprehension C) A.

Notation "'π'" := (comp_cat_proj _).

Definition subst_Ty
           {C : full_comp_cat}
           {Γ Δ : C}
           (s : Γ --> Δ)
           (A : Ty Δ)
  : Ty Γ
  := cleaving_ob (cleaving_of_types C) s A.

Notation "A '[[' s ']]'" := (subst_Ty s A) (at level 20).

Definition mor_to_ext
           {C : full_comp_cat}
           {Γ Δ : C}
           {A : Ty Δ}
           (s : Γ --> Δ)
           (t : Γ --> Γ & (A[[s]]))
  : Γ --> Δ & A.
Proof.
  pose (make_Pullback
          _
          (cartesian_isPullback_in_cod_disp
             _
             (full_comp_cat_comprehension_cartesian
                C
                _ _ _ _ _ _
                (cartesian_lift_is_cartesian _ _ (cleaving_of_types C _ _ s A))))).
  refine (t · PullbackPr1 p).
Defined.



Definition extended_Tm
           {C : full_comp_cat}
           {Γ : C}
           (A B : Ty Γ)
  : UU
  := fiber_category (disp_cat_of_types C) Γ ⟦ A , B ⟧.

Definition ext_extended_Tm
           {C : full_comp_cat}
           {Γ : C}
           {A B : Ty Γ}
           (t : extended_Tm A B)
  : Γ & A --> Γ & B
  := comprehension_functor_mor (comp_cat_comprehension C) t.

Definition ext_extended_Tm_comm
           {C : full_comp_cat}
           {Γ : C}
           {A B : Ty Γ}
           (t : extended_Tm A B)
  : ext_extended_Tm t · π B = π A.
Proof.
  refine (comprehension_functor_mor_comm (comp_cat_comprehension C) t @ _).
  apply id_right.
Qed.

(* also stuff for fullness *)
Definition extended_Tm_from_cod
           {C : full_comp_cat}
           {Γ : C}
           {A B : Ty Γ}
           (t : Γ & A --> Γ & B)
           (p : t · π B = π A)
  : extended_Tm A B.
Proof.
Admitted.

Definition extended_Tm_from_cod'
           {C : full_comp_cat}
           {Γ Δ : C}
           (s : Γ --> Δ)
           {A : Ty Γ}
           {B : Ty Δ}
           (t : Γ & A --> Δ & B)
           (p : t · π B = π A · s)
  : A -->[ s ] B.
Proof.
  use (disp_functor_ff_inv _ (full_comp_cat_comprehension_fully_faithful C)).
  exact (t ,, p).
Defined.

(*
Definition lol
           {C : full_comp_cat}
           {Γ Δ : C}
           (s : Γ --> Δ)
           (A : Ty Δ)
  : UU.
Proof.
  (*
  A[s] ----> A
                  cartesian
   Γ   ----> Δ

 after comprehension

         Γ & A[s] -------> Δ & A
           |                 |
  π (A[s]) |                 | π A         is pullback
           |                 |
           V                 V
           Γ --------------> Δ
                    s

  to make Γ --> Δ & A
  we need to give:
  - Γ --> Δ
  - Γ --> Γ & A[s] that is a section of the projection

   *)
  pose (cartesian_isPullback_in_cod_disp
          _
          (full_comp_cat_comprehension_cartesian
             C
             _ _ _ _ _ _
             (cartesian_lift_is_cartesian _ _ (cleaving_of_types C _ _ s A)))).

 *)

(* *)


Definition has_unit
           (C : full_comp_cat)
  : UU
  := ∑ (T : fiberwise_terminal (cleaving_of_types C)),
     ∏ (Γ : C),
     is_z_isomorphism (comp_cat_proj Γ (terminal_obj_in_fib T Γ)).

Definition fiberwise_terminal_of_unit
           {C : full_comp_cat}
           (T : has_unit C)
  : fiberwise_terminal (cleaving_of_types C)
  := pr1 T.

Definition unit_Ty
           {C : full_comp_cat}
           (T : has_unit C)
           (Γ : C)
  : Ty Γ
  := terminal_obj_in_fib (fiberwise_terminal_of_unit T) Γ.

Definition ext_unit_of_unit
           {C : full_comp_cat}
           (T : has_unit C)
           (Γ : C)
  : is_z_isomorphism
      (comp_cat_proj
         Γ
         (terminal_obj_in_fib (fiberwise_terminal_of_unit T) Γ))
  := pr2 T Γ.

Definition ext_unit_iso_of_unit
           {C : full_comp_cat}
           (T : has_unit C)
           (Γ : C)
  : z_iso (Γ & unit_Ty T Γ) Γ.
Proof.
  refine (_ ,, ext_unit_of_unit T Γ).
Defined.



Definition koe
  : disp_bicat bicat_full_comp_cat.
Proof.
  use disp_subbicat.
  - exact has_unit.
  - exact (λ (C₁ C₂ : full_comp_cat)
             _ _
             (F : full_comp_cat_functor C₁ C₂),
           ∏ (Γ : C₁),
           preserves_terminal (fiber_functor (comp_cat_type_functor F) Γ)).
  - intros C T Γ A H.
    apply H.
  - intros.
    intros ? ? H.
    apply X0.
    apply X.
    exact H.
Defined.


Print full_comp_cat.
Check bicat_of_full_comp_cat.

Section RightAdjTerminal.
  Context {C : full_comp_cat}
          (T : has_unit C).

  Let E : category := total_category (disp_cat_of_types C).
  Let F : C ⟶ E
    := terminal_functor (cleaving_of_types C) (fiberwise_terminal_of_unit T).

  Definition ext_total
             (ΓA : E)
    : C
    := pr1 ΓA & pr2 ΓA.

  Definition is_left_adjoint_terminal_counit
             (ΓA : E)
    : F(ext_total ΓA) --> ΓA.
  Proof.
    refine (π _ ,, _).
    use extended_Tm_from_cod'.
    - apply π.
    - apply idpath.
  Defined.

  Section Universal.
    Context {ΓA : E}
            {Δ : C}
            (f : E ⟦ F Δ, ΓA ⟧).

    Let Γ : C := pr1 ΓA.
    Let A : Ty Γ := pr2 ΓA.
    Let s : Δ --> Γ := pr1 f.
    Let t : unit_Ty T Δ -->[ s ] A := pr2 f.

    Proposition is_univalent_arrow_left_adjoint_terminal_unique
      : isaprop
          (∑ (f' : Δ --> ext_total ΓA),
           f = # F f' · is_left_adjoint_terminal_counit ΓA).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      pose (maponpaths pr1 (!(pr2 ζ₁) @ pr2 ζ₂)) as p.
      cbn in p.
    Admitted.

    Definition is_univalent_arrow_left_adjoint_terminal_mor
      : Δ --> Γ & A.
    Proof.
      refine (inv_from_z_iso (ext_unit_iso_of_unit T Δ) · _).
      exact (comprehension_functor_mor (comp_cat_comprehension C) t).

      (*

         𝟙 ------> A

         Δ ------> Γ

         -----------

         Δ & 𝟙 --------> Γ & A
           |               |
         π |               | π
           |               |
           V               V
           Δ ------------> Γ

        So: it should be the inverse of π followed by a projection


         Δ & A[s] -------> Γ & A
           |                 |
         π |                 | π
           |                 |
           V                 V
           Δ --------------> Γ
       *)
    Defined.

    Definition TODO { X : UU } : X.
    Admitted.

    Proposition is_univalent_arrow_left_adjoint_terminal_comm
      : f
        =
        # F is_univalent_arrow_left_adjoint_terminal_mor
        · is_left_adjoint_terminal_counit ΓA.
    Proof.
      (* we need a good equality principle here *)
      use total2_paths_f.
      - apply TODO.
        (*cbn.
        unfold is_univalent_arrow_left_adjoint_terminal_mor.
        rewrite !assoc'.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (comprehension_functor_mor_comm (comp_cat_comprehension C) t).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (z_iso_after_z_iso_inv (ext_unit_iso_of_unit T Δ)).
        }
        apply id_left.*)
      - cbn.
        unfold terminal_mor_lift.
        rewrite mor_disp_transportf_postwhisker.
        Search "prewhis".
        cbn.
        unfold is_univalent_arrow_left_adjoint_terminal_mor.
        cbn.
    Admitted.
  End Universal.

  Proposition is_univalent_arrow_left_adjoint_terminal
              (ΓA : E)
    : is_universal_arrow_from
        _ _
        (ext_total ΓA) (is_left_adjoint_terminal_counit ΓA).
  Proof.
    intros Δ f.
    use iscontraprop1.
    - admit.
    - refine (is_univalent_arrow_left_adjoint_terminal_mor f ,, _).
      apply is_univalent_arrow_left_adjoint_terminal_comm.
  Admitted.

  Definition is_left_adjoint_terminal
    : is_left_adjoint F.
  Proof.
    use left_adjoint_from_partial.
    - exact ext_total.
    - exact is_left_adjoint_terminal_counit.
    - exact is_univalent_arrow_left_adjoint_terminal.
  Defined.
