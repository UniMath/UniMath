(**

 Sheafification

 Let `C` be a site. A central result in the theory of sheaves is that the inclusion functor
 from the category of sheaves over `C` to the category of presheaves over `C` has a left
 adjoint, called sheafification. Intuitively, this result says that every presheaf `F` over
 `C` can be completed into a sheaf `a(F)`, and natural transformations from `a(F)` to some
 sheaf `G` are the same as natural transformations from the presheaf `F` to `G`. In addition,
 sheafification preserves finite limits, and it is a canonical example of a geometric
 morphism between toposes.

 In this file, we construct the sheafification and show that it is left adjoint to the
 inclusion. Our approach is based on Section V.3 in 'Sheaves in Geometry and Logic' by
 Mac Lane and Moerdijk. Usually, the sheafification is constructed using the ++-construction,
 but we refrain from doing so. The reasoning is as follows. We can construct the sheafification
 as an infinitary quotient inductive type, and we can construct this quotient inductive type
 in two steps using quotient types. However, there is an issue if we use quotient types: we
 need some version of choice (axiom of multiple choice or WISC) to get this construction to
 work. The construction in Section V.3 of 'Sheaves in Geometry and Logic' is different, and
 one does not need any form of choice for this construction.

 Let `F` be a presheaf over `C`. We write `Ω` for the subobject classifier of presheaves over
 `C` and we write `Ω_j` for the subobject classifier of sheaves over `C`. To construct the
 sheafification of `F`, we take the following steps.
 1. We observe that we have a morphism `F --> Ω^F`. Intuitively, this morphism maps every
    element to a singleton set.
 2. By composition, we observe that we have a morphism `F --> Ω_j^F`. It is important to note
    that `Ω_j^F` is a sheaf. This is because `Ω_j` is a sheaf and because sheaves form an
    exponential ideal in the category of presheaves. Concretely, this means that whenever we
    have a presheaf `G₁` and ` sheaf `G₂`, then `G₂^G₁` is a sheaf.
 3. We take the image factorisation the morphism `F --> Ω_j^F`, which gives us a subobject
    `im` of `Ω_j^F`. Note that `im` is a separated presheaf (i.e., amalgamations of matching
    families are unique, but they might not exist), and that `im` is a subobject of the sheaf
    `Ω_j^F`.
 4. Since `im` is a subobject of a sheaf, we can take its closure to obtain a sheaf `a(F)`.
    This sheaf is the sheafification of `F`.

 The universal property of sheafification can be proven rather nicely from this construction.
 It is based on two observations.
 1. In any topos, the image of a map is the coequaliser of its kernel pair. From this
    observation, we get a universal property that allows to make maps from the image to any
    sheaf.
 2. If we have some presheaf `F` and a sheaf `G`, then maps from the closure of `F` to `G`
    are the same as maps from `F` to `G`.
 We can directly prove the universal property of sheafification (i.e., sheafification is a
 left adjoint) by combining these observations. Since the inclusion from sheaves into
 presheaves is fully faithful, we get that the category of sheaves us a reflective subcategory
 of the category of sheaves. Hence, the sheafification of a sheaf `F` is ismorphic to `F`.
 Since the terminal presheaf is a sheaf, we can directly prove that sheafification preserves
 terminal objects.

 If `Y` is some set, then the constant presheaf on `Y` is not necessarily a sheaf. There is
 a simple counterexample to this. Let `X` be a topological space that is not connected, which
 means that we can write `X` as the disjoint union of two open sets `X₁` and `X₂`. We consider
 the constant presheaf over `X` that maps every open set to the natural numbers. This constant
 presheaf is not a sheaf. We have an open cover given by `X₁` and `X₂`, and over that cover we
 construct the following matching family: `X₁` gets mapped to `1` and `X₂` gets mapped to `2`.
 This matching family does not have an amalgamation since `1` and `2` are unequal.

 We can use sheafification to construct constant sheaves. If `Y` is some set, then the constant
 sheaf on `Y` is defined to be the sheafification of the constant presheaf on `Y`. We can also
 construct the natural numbers object of sheaves using sheafification.

 References
 - 'Sheaves in Geometry and Logic' by Mac Lane and Moerdijk

 Content
 1. Some preliminary notation
 2. The construction of the sheafification
 2.1. Step 1: the singleton map into the power sheaf
 2.2. Step 2: the image of singleton map into the power sheaf
 2.3. Step 3: the sheafification as the closure of the image
 3. The universal property of the sheafification
 4. Sheafification is a left adjoint
 5. Sheafification of sheaves
 6. Preservation of terminal objects
 7. Constant sheaves
 8. Natural numbers object of sheaves

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Reflections.
Require Import UniMath.CategoryTheory.Arithmetic.NNO.
Require Import UniMath.CategoryTheory.Arithmetic.NNOLeftAdjoint.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifierSheaf.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.Presheaves.ConstructionsSheaves.
Require Import UniMath.CategoryTheory.Presheaves.ClosedSieves.
Require Import UniMath.CategoryTheory.Presheaves.PiTypes.
Require Import UniMath.CategoryTheory.Presheaves.PiSheaf.
Require Import UniMath.CategoryTheory.Presheaves.ClosureSubobject.
Require Import UniMath.CategoryTheory.Presheaves.NaturalNumbers.

Local Open Scope cat.

Section Sheafification.
  Context {C : site}
          (F : C^op ⟶ HSET).

  (** * 1. Some preliminary notation *)
  Let power_psh : C^op ⟶ HSET := exp_psh F subobject_classifier_psh.
  Let power_sheaf : sheaf C := exp_sheaf F subobject_classifier_sheaf.

  Definition power_sheaf_to_power_psh
    : power_sheaf ⟹ power_psh
    := exp_psh_fun_cod _ subobject_classifier_sheaf_inclusion.

  Definition power_psh_to_power_sheaf
    : power_psh ⟹ power_sheaf
    := exp_psh_fun_cod _ subobject_classifier_psh_closure.

  Definition diagonal_sieve_nat_trans
    : BinProduct_of_functors _ _ BinProductsHSET F F
      ⟹
      subobject_classifier_psh.
  Proof.
    use make_nat_trans.
    - intros x xx.
      exact (tt ,, sieve_of_equality (pr1 xx) (pr2 xx)).
    - abstract
        (intros x y f ;
         use funextsec ;
         intros [ xx yy ] ;
         cbn ;
         apply maponpaths ;
         use sieve_eq ; cbn ;
         [ intros z g p ;
           refine (eqtohomot (functor_comp F f g) xx @ _) ;
           refine (_ @ !(eqtohomot (functor_comp F f g) yy)) ;
           cbn ;
           exact p
         | intros z g p ;
           refine (!(eqtohomot (functor_comp F f g) xx) @ _) ;
           refine (_ @ eqtohomot (functor_comp F f g) yy) ;
           exact p ]).
  Defined.

  (** * 2. The construction of the sheafification *)

  (** ** 2.1. Step 1: the singleton map into the power sheaf *)
  Definition singleton_power_psh
    : F ⟹ power_psh
    := exp_psh_lam _ _ diagonal_sieve_nat_trans.

  Definition singleton_power_sheaf
    : F ⟹ power_sheaf
    := nat_trans_comp
         _ _ _
         singleton_power_psh
         power_psh_to_power_sheaf.

  (** * 2.2. Step 2: the image of singleton map into the power sheaf *)
  Definition singleton_power_sheaf_im
    : C^op ⟶ HSET
    := psh_nat_trans_im singleton_power_sheaf.

  Definition singleton_power_sheaf_to_im
    : F ⟹ singleton_power_sheaf_im
    := psh_nat_trans_to_im singleton_power_sheaf.

  Definition singleton_power_sheaf_im_incl
    : singleton_power_sheaf_im ⟹ power_sheaf
    := psh_nat_trans_im_incl singleton_power_sheaf.

  Proposition isMonic_singleton_power_sheaf_im_incl
    : isMonic (C := PreShv C) singleton_power_sheaf_im_incl.
  Proof.
    apply isMonic_psh_nat_trans_im_incl.
  Qed.

  (** * 2.3. Step 3: the sheafification as the closure of the image *)
  Definition sheafification
    : sheaf C
    := closure_subobject isMonic_singleton_power_sheaf_im_incl.

  Definition nat_trans_to_sheafification
    : F ⟹ sheafification
    := nat_trans_comp
         _ _ _
         singleton_power_sheaf_to_im
         (closure_subobject_mor _).

  (** * 3. The universal property of the sheafification *)
  Context {G : sheaf C}
          (τ : F ⟹ G).

  Proposition singleton_power_sheaf_el_eq_closed
              {x : C}
              {xx₁ xx₂ : (F x : hSet)}
              (p : singleton_power_sheaf x xx₁ = singleton_power_sheaf x xx₂)
    : C x (sieve_of_equality xx₁ xx₂).
  Proof.
    assert (closure_closed_sieve (sieve_of_equality xx₁ xx₂)
            =
            truth_closed_sieve _) as H.
    {
      assert (pr2 (singleton_power_sheaf x xx₁) = pr2 (singleton_power_sheaf x xx₂))
        as q₁.
      {
        refine (!_ @ fiber_paths p).
        enough (base_paths (singleton_power_sheaf x xx₁) (singleton_power_sheaf x xx₂) p
                =
                  idpath _) as ->.
        {
          apply idpath.
        }
        apply isapropunit.
      }
      pose proof (maponpaths (λ z, pr1 z _ (identity _) xx₁) q₁) as q₂.
      cbn in q₂.
      pose proof (fiber_paths q₂) as q₃.
      cbn in q₃.
      rewrite transportf_const in q₃.
      cbn in q₃.
      clear q₁ q₂.
      rewrite !id_precomp_sieve in q₃.
      rewrite !(eqtohomot (functor_comp F (identity x) (identity x))) in q₃.
      cbn in q₃.
      rewrite !(eqtohomot (functor_id F x)) in q₃.
      cbn in q₃.
      rewrite sieve_of_equality_refl in q₃.
      refine (!q₃ @ _).
      use closed_sieve_eq.
      exact (closure_closed_sieve_eq (truth_closed_sieve x)).
    }
    pose (H' := from_sieve_eq_r (sieve_eq_from_closed H) (identity _) tt).
    cbn in H'.
    rewrite id_precomp_sieve in H'.
    exact H'.
  Qed.

  Definition singleton_power_sheaf_el_eq_matching_family
             {x : C}
             (xx₁ xx₂ : (F x : hSet))
    : matching_family G (sieve_of_equality xx₁ xx₂).
  Proof.
    use make_matching_family.
    - exact (λ y f q, τ y (#F f xx₁)).
    - abstract
        (cbn ;
         intros y₁ y₂ f₁ f₂ g p q r ;
         induction p ;
         refine (!(eqtohomot (nat_trans_ax τ _ _ g) _) @ !_) ;
         cbn ;
         apply maponpaths ;
         exact (eqtohomot (functor_comp F f₂ g) xx₁)).
  Defined.

  Proposition singleton_power_sheaf_el_eq
              {x : C}
              {xx₁ xx₂ : (F x : hSet)}
              (p : singleton_power_sheaf x xx₁ = singleton_power_sheaf x xx₂)
    : τ x xx₁ = τ x xx₂.
  Proof.
    cbn -[singleton_power_psh power_psh_to_power_sheaf] in p.
    use (sheaf_amalgamation_unique (is_sheaf_sheaf G)).
    - exact (sieve_of_equality xx₁ xx₂).
    - exact (singleton_power_sheaf_el_eq_closed p).
    - exact (singleton_power_sheaf_el_eq_matching_family xx₁ xx₂).
    - cbn.
      intros y f q.
      exact (!(eqtohomot (nat_trans_ax τ _ _ f) xx₁)).
    - cbn.
      intros y f q.
      refine (!(eqtohomot (nat_trans_ax τ _ _ f) xx₂) @ _).
      cbn.
      rewrite q.
      apply idpath.
  Qed.

  Definition nat_trans_from_im
    : singleton_power_sheaf_im ⟹ G.
  Proof.
    use map_from_psh_nat_trans_im.
    - exact τ.
    - intros x a₁ a₂.
      exact singleton_power_sheaf_el_eq.
  Defined.

  Definition nat_trans_from_sheafification
    : sheafification ⟹ G.
  Proof.
    use extend_mor_to_closure.
    exact nat_trans_from_im.
  Defined.

  Proposition nat_trans_from_sheafification_eq
    : τ
      =
      nat_trans_comp
        _ _ _
        nat_trans_to_sheafification
        nat_trans_from_sheafification.
  Proof.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use funextsec.
    intro xx.
    unfold nat_trans_from_sheafification.
    refine (!_).
    etrans.
    {
      exact (extend_mor_to_closure_restrict_pt
               isMonic_singleton_power_sheaf_im_incl
               G
               nat_trans_from_im
               (singleton_power_sheaf_to_im x xx)).
    }
    apply map_from_psh_nat_trans_im_comm_pt.
  Qed.

  Proposition nat_trans_from_sheafification_unique
              (θ : sheaf_nat_trans sheafification G)
              (p : τ = nat_trans_comp _ _ _ nat_trans_to_sheafification θ)
    : pr1 θ = nat_trans_from_sheafification.
  Proof.
    use extend_mor_to_closure_unique.
    - apply nat_trans_from_im.
    - use map_from_psh_nat_trans_im_unique_mor.
      + exact τ.
      + intros c a₁ a₂.
        exact singleton_power_sheaf_el_eq.
      + refine (_ @ !p).
        use nat_trans_eq.
        {
          apply homset_property.
        }
        intro x.
        use funextsec.
        intro xx.
        apply idpath.
      + apply map_from_psh_nat_trans_im_comm.
    - apply extend_mor_to_closure_restrict.
  Qed.
End Sheafification.

#[global] Opaque sheafification.
#[global] Opaque nat_trans_to_sheafification.
#[global] Opaque nat_trans_from_sheafification.

(** * 4. Sheafification is a left adjoint *)
Definition is_right_adjoint_sheaf_incl
           (C : site)
  : is_right_adjoint (sheaf_incl C).
Proof.
  use reflections_to_is_right_adjoint.
  intros F.
  use make_reflection.
  - use make_reflection_data.
    + exact (sheafification F).
    + exact (nat_trans_to_sheafification F).
  - intros G.
    induction G as [ G τ ].
    use make_iscontr.
    + simple refine (_ ,, _).
      * use make_sheaf_nat_trans.
        exact (nat_trans_from_sheafification F τ).
      * exact (nat_trans_from_sheafification_eq F τ).
    + abstract
        (intros [ θ p ] ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use sheaf_nat_trans_eq ;
         exact (nat_trans_from_sheafification_unique F _ θ p)).
Defined.

Definition sheafification_functor
           (C : site)
  : PreShv C ⟶ cat_of_sheaves C
  := left_adjoint (is_right_adjoint_sheaf_incl C).

Definition sheafification_unit
           (C : site)
  : functor_identity _ ⟹ sheafification_functor C ∙ sheaf_incl C
  := unit_from_right_adjoint (is_right_adjoint_sheaf_incl C).

(** * 5. Sheafification of sheaves *)
Definition sheafification_sheaf
           {C : site}
           (F : sheaf C)
  : z_iso (sheafification F) F.
Proof.
  pose (R := is_right_adjoint_sheaf_incl C).
  use make_z_iso.
  - exact (counit_from_right_adjoint R F).
  - use make_sheaf_nat_trans.
    exact (unit_from_right_adjoint R (sheaf_incl C F)).
  - split.
    + abstract
        (refine (!_) ;
         refine (_ @ nat_trans_ax (counit_from_right_adjoint R) _ _ _) ;
         exact (!(pr122 (is_right_adjoint_sheaf_incl C) (sheaf_incl C F)))).
    + abstract
        (use sheaf_nat_trans_eq ;
         exact (pr222 (is_right_adjoint_sheaf_incl C) F)).
Defined.

Definition sheafification_counit
           (C : site)
  : nat_z_iso (sheaf_incl C ∙ sheafification_functor C) (functor_identity _).
Proof.
  use make_nat_z_iso.
  - exact (counit_from_right_adjoint (is_right_adjoint_sheaf_incl C)).
  - intro F.
    exact (pr2 (sheafification_sheaf F)).
Defined.

Proposition sheafification_triangle_1
            {C : site}
            (F : C^op ⟶ HSET)
  : #(sheafification_functor C) (sheafification_unit C F)
    · sheafification_counit C (sheafification F)
    =
    identity (sheafification F).
Proof.
  exact (pr122 (is_right_adjoint_sheaf_incl C) F).
Qed.

Proposition sheafification_triangle_2
            {C : site}
            (F : sheaf C)
  : sheafification_unit C (sheaf_incl C F)
    · #(sheaf_incl C) (sheafification_counit C F)
    =
    identity (sheaf_incl C F).
Proof.
  exact (pr222 (is_right_adjoint_sheaf_incl C) F).
Qed.

#[global] Opaque sheafification_functor.
#[global] Opaque sheafification_counit.
#[global] Opaque sheafification_unit.

(** * 6. Preservation of terminal objects *)
Proposition preserves_terminal_sheafification
            (C : site)
  : preserves_terminal (left_adjoint (is_right_adjoint_sheaf_incl C)).
Proof.
  use preserves_terminal_if_preserves_chosen.
  {
    exact Terminal_PreShv.
  }
  use iso_to_Terminal.
  - exact (sheaf_terminal C).
  - use z_iso_inv.
    exact (sheafification_sheaf (terminal_sheaf C)).
Qed.

(** * 7. Constant sheaves *)
Definition constant_sheaf
           (C : site)
           (Y : hSet)
  : sheaf C
  := sheafification (constant_functor C^op HSET Y).

(** * 8. Natural numbers object of sheaves *)
Definition nno_cat_of_sheaves
           (C : site)
  : NNO (sheaf_terminal C).
Proof.
  refine (left_adjoint_on_NNO _ (is_right_adjoint_sheaf_incl C) _ _ _ (nno_cat_of_psh C)).
  apply preserves_terminal_sheafification.
Defined.
