(**

 Functors between locally Cartesian closed categories

 We define structure preserving functors between locally Cartesian closed categories. We
 phrase this in terms of functors between displayed categories that preserve dependent
 products. Concretely, this means that preservation of exponentials is expressed via the
 Beck-Chevalley condition, so we say that the canonical map is an isomorphism. This canonical
 map expresses what one would intuitively expect, namely that we have an isomorphism between
 the exponentials ([preserves_locally_cartesian_closed_z_iso]). Since there already are some
 example of functors that satisfy the Beck-Chevalley condition, we can directly conclude that
 the identity preserves exponentials and that preservation of exponentials is closed under
 composition. In both cases, we calculate the mediating isomorphism.

 Finally, we look at a naturality condition ([preserves_locally_cartesian_closed_natural]).
 Exponentials are functorial in both arguments (contravariant in the first and covariant in
 the second). This naturality condition says that the preservation isomorphism is natural
 with respect to both arguments of the exponential. Unfortunately, the proof requires quite
 some calculations. The preservation isomorphism is defined as a composition of various
 natural transformations, but from this we only get naturality with respect to the covariant
 argument. The main work lies in verifying the other naturality condition.

 Contents
 1. Structure preserving functors between LCCCs
 2. The identity is structure preserving
 3. The composition is structure preserving
 4. Naturality of preservation

                                                                                          *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodRightAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.

Local Open Scope cat.

(** * 1. Structure preserving functors between LCCCs *)
Definition preserves_locally_cartesian_closed
           {C₁ C₂ : category}
           {PB₁ : Pullbacks C₁}
           {PB₂ : Pullbacks C₂}
           {F : C₁ ⟶ C₂}
           (HF : preserves_pullback F)
           (H₁ : is_locally_cartesian_closed PB₁)
           (H₂ : is_locally_cartesian_closed PB₂)
  : UU
  := preserves_dependent_products
       (cartesian_disp_codomain_functor F HF)
       (cod_dependent_products H₁)
       (cod_dependent_products H₂).

Proposition isaprop_preserves_locally_cartesian_closed
            {C₁ C₂ : category}
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            {F : C₁ ⟶ C₂}
            (HF : preserves_pullback F)
            (H₁ : is_locally_cartesian_closed PB₁)
            (H₂ : is_locally_cartesian_closed PB₂)
  : isaprop (preserves_locally_cartesian_closed HF H₁ H₂).
Proof.
  apply isaprop_preserves_dependent_products.
Qed.

Definition preserves_locally_cartesian_closed_z_iso_fib
           {C₁ C₂ : category}
           {PB₁ : Pullbacks C₁}
           {PB₂ : Pullbacks C₂}
           {F : C₁ ⟶ C₂}
           {HF : preserves_pullback F}
           {H₁ : is_locally_cartesian_closed PB₁}
           {H₂ : is_locally_cartesian_closed PB₂}
           (HFF : preserves_locally_cartesian_closed HF H₁ H₂)
           {Γ : C₁}
           (πA : C₁/Γ)
           (πB : C₁/cod_dom πA)
  : z_iso
      (fiber_functor
         (cartesian_disp_codomain_functor F HF)
         Γ
         (lccc_exp_fib H₁ πA πB))
      (lccc_exp_fib H₂ (functor_on_cod_fib F πA) (functor_on_cod_fib F πB))
  := right_beck_chevalley_nat_trans _ _ _ _ ,, HFF _ _ (cod_mor πA) πB.

Definition preserves_locally_cartesian_closed_z_iso
           {C₁ C₂ : category}
           {PB₁ : Pullbacks C₁}
           {PB₂ : Pullbacks C₂}
           {F : C₁ ⟶ C₂}
           {HF : preserves_pullback F}
           {H₁ : is_locally_cartesian_closed PB₁}
           {H₂ : is_locally_cartesian_closed PB₂}
           (HFF : preserves_locally_cartesian_closed HF H₁ H₂)
           {Γ : C₁}
           (πA : C₁/Γ)
           (πB : C₁/cod_dom πA)
  : z_iso
      (F (lccc_exp H₁ πA πB))
      (lccc_exp H₂ (functor_on_cod_fib F πA) (functor_on_cod_fib F πB))
  := z_iso_to_cod_dom
       _ _ _
       (preserves_locally_cartesian_closed_z_iso_fib HFF πA πB).

(** * 2. The identity is structure preserving *)
Proposition id_preserves_locally_cartesian_closed
            {C : category}
            {PB : Pullbacks C}
            (H : is_locally_cartesian_closed PB)
  : preserves_locally_cartesian_closed (identity_preserves_pullback C) H H.
Proof.
  unfold preserves_locally_cartesian_closed.
  refine (transportf
            (λ z, preserves_dependent_products z _ _)
            _
            (id_preserves_dependent_products (cod_dependent_products H))).
  use subtypePath.
  {
    intro.
    apply isaprop_is_cartesian_disp_functor.
  }
  use subtypePath.
  {
    intro.
    apply isaprop_disp_functor_axioms.
  }
  use total2_paths_f.
  - apply idpath.
  - cbn.
    repeat (use funextsec ; intro).
    use eq_cod_mor ; cbn.
    apply idpath.
Qed.

Definition fiber_functor_codomain_id
           {C : category}
           (Γ : C)
  : nat_z_iso
      (fiber_functor
         (cartesian_disp_codomain_functor
            (functor_identity C)
            (identity_preserves_pullback C))
         Γ)
      (fiber_functor (id_cartesian_disp_functor (disp_codomain C)) Γ).
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + exact (λ _, identity _).
    + abstract
        (intros x y f ;
         use eq_mor_cod_fib ;
         refine (comp_in_cod_fib _ _ @ _ @ !(comp_in_cod_fib _ _)) ;
         exact (id_right _ @ !(id_left _))).
  - intro.
    apply is_z_isomorphism_identity.
Defined.

Proposition fiber_functor_codomain_id_natural_eq_left
            {C : category}
            {PB : Pullbacks C}
            {Γ : C}
            (πA πB : C/Γ)
  : dom_mor
      (fiber_functor_natural_nat_z_iso
         (disp_codomain_cleaving PB)
         (disp_codomain_cleaving PB)
         (id_cartesian_disp_functor (disp_codomain C))
         (cod_mor πA)
         πB)
    =
    identity _.
Proof.
  use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
  - refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
    rewrite transportf_cod_disp.
    refine (!_).
    simpl.
    apply id_left.
  - refine (PullbackArrow_PullbackPr2 _ _ _ _ _ @ _).
    simpl.
    rewrite id_left, id_right.
    apply idpath.
Qed.

Proposition fiber_functor_codomain_id_natural_eq_right
            {C : category}
            {PB : Pullbacks C}
            {Γ : C}
            (πA πB : C/Γ)
  : dom_mor
      (fiber_functor_natural_nat_z_iso
         (disp_codomain_cleaving PB)
         (disp_codomain_cleaving PB)
         (cartesian_disp_codomain_functor
            (functor_identity C)
            (identity_preserves_pullback C))
         (cod_mor πA)
         πB)
    =
    identity _.
Proof.
  pose (identity_preserves_pullback
          _ _ _ _ _ _ _ _ _ _
          (PullbackSqrCommutes _)
          (cartesian_isPullback_in_cod_disp
             (disp_codomain_cleaving PB Γ (cod_dom πA) (cod_mor πA) πB)
             (disp_codomain_cleaving PB Γ (cod_dom πA) (cod_mor πA) πB)))
    as H.
  use (MorphismsIntoPullbackEqual H).
  - etrans.
    {
      apply (PullbackArrow_PullbackPr1 (make_Pullback _ H)).
    }
    rewrite transportf_cod_disp.
    refine (!_).
    simpl.
    apply id_left.
  - etrans.
    {
      apply (PullbackArrow_PullbackPr2 (make_Pullback _ H)).
    }
    simpl.
    rewrite id_left, id_right.
    apply idpath.
Qed.

Proposition preserves_locally_cartesian_closed_z_iso_id
            {C : category}
            {PB : Pullbacks C}
            {H : is_locally_cartesian_closed PB}
            {Γ : C}
            (πA : C/Γ)
            (πB : C/cod_dom πA)
  : identity _
    =
    preserves_locally_cartesian_closed_z_iso
      (id_preserves_locally_cartesian_closed H)
      πA πB.
Proof.
  refine (!_).
  pose (right_beck_chevalley_nat_trans_id _ (H (cod_dom πA) Γ (cod_mor πA)) πB) as p.
  refine (_ @ maponpaths dom_mor p).
  refine (maponpaths dom_mor _).
  cbn -[right_beck_chevalley_nat_trans].
  pose (right_beck_chevalley_nat_trans_eq_nat_trans
          (H (cod_dom πA) Γ (cod_mor πA))
          (H (cod_dom πA) Γ (cod_mor πA))
          (fiber_functor_natural_nat_z_iso
             _ _
             (cartesian_disp_codomain_functor
                (functor_identity C)
                (identity_preserves_pullback C))
             (cod_mor πA))
          (fiber_functor_natural_nat_z_iso
             _ _
             (id_cartesian_disp_functor (disp_codomain C))
             (cod_mor πA))
          (fiber_functor_codomain_id Γ)
          (nat_z_iso_inv (fiber_functor_codomain_id _)))
    as q.
  refine (q _ πB @ _).
  {
    intro πB'.
    refine (!_).
    refine (id_right _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply functor_id.
    }
    use eq_mor_cod_fib.
    refine (comp_in_cod_fib _ _ @ _).
    refine (id_left _ @ _).
    etrans.
    {
      exact (fiber_functor_codomain_id_natural_eq_left πA πB').
    }
    refine (!_).
    etrans.
    {
      exact (fiber_functor_codomain_id_natural_eq_right πA πB').
    }
    apply idpath.
  }
  refine (assoc' _ _ _ @ _).
  refine (id_left _ @ _).
  refine (_ @ id_right _).
  apply maponpaths.
  apply (functor_id (right_adjoint (H (cod_dom πA) Γ (cod_mor πA)))).
Qed.

(** * 3. The composition is structure preserving *)
Proposition comp_preserves_locally_cartesian_closed
            {C₁ C₂ C₃ : category}
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            {PB₃ : Pullbacks C₃}
            {H₁ : is_locally_cartesian_closed PB₁}
            {H₂ : is_locally_cartesian_closed PB₂}
            {H₃ : is_locally_cartesian_closed PB₃}
            {F : C₁ ⟶ C₂}
            {HF : preserves_pullback F}
            (HFF : preserves_locally_cartesian_closed HF H₁ H₂)
            {G : C₂ ⟶ C₃}
            {HG : preserves_pullback G}
            (HGG : preserves_locally_cartesian_closed HG H₂ H₃)
  : preserves_locally_cartesian_closed
      (composition_preserves_pullback HF HG)
      H₁
      H₃.
Proof.
  unfold preserves_locally_cartesian_closed.
  refine (transportf
            (λ z, preserves_dependent_products z _ _)
            _
            (comp_preserves_dependent_products HFF HGG)).
  use subtypePath.
  {
    intro.
    apply isaprop_is_cartesian_disp_functor.
  }
  use subtypePath.
  {
    intro.
    apply isaprop_disp_functor_axioms.
  }
  use total2_paths_f.
  - apply idpath.
  - cbn.
    repeat (use funextsec ; intro).
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    cbn.
    apply idpath.
Qed.

Definition fiber_functor_codomain_comp
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           (HF : preserves_pullback F)
           {G : C₂ ⟶ C₃}
           (HG : preserves_pullback G)
           (Γ : C₁)
  : nat_z_iso
      (fiber_functor
         (cartesian_disp_codomain_functor
            (F ∙ G)
            (composition_preserves_pullback HF HG))
         Γ)
      (fiber_functor
         (comp_cartesian_disp_functor
            (cartesian_disp_codomain_functor F HF)
            (cartesian_disp_codomain_functor G HG))
         Γ).
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + exact (λ _, identity _).
    + abstract
        (intros x y f ;
         refine (id_right _ @ _ @ !(id_left _)) ;
         use eq_mor_cod_fib ;
         refine (disp_codomain_fiber_functor_mor _ _ _ @ !_) ;
         apply transportf_cod_disp).
  - intro.
    apply is_z_isomorphism_identity.
Defined.

Proposition fiber_functor_codomain_comp_eq
            {C₁ C₂ C₃ : category}
            {PB₁ : Pullbacks C₁}
            {PB₃ : Pullbacks C₃}
            {F : C₁ ⟶ C₂}
            (HF : preserves_pullback F)
            {G : C₂ ⟶ C₃}
            (HG : preserves_pullback G)
            {Γ : C₁}
            (πA πB : C₁/Γ)
  : dom_mor
      (fiber_functor_natural_nat_z_iso
         (disp_codomain_cleaving PB₁)
         (disp_codomain_cleaving PB₃)
         (comp_cartesian_disp_functor
            (cartesian_disp_codomain_functor F HF)
            (cartesian_disp_codomain_functor G HG))
         (cod_mor πA)
         πB)
    =
    dom_mor
      (fiber_functor_natural_nat_z_iso
         (disp_codomain_cleaving PB₁)
         (disp_codomain_cleaving PB₃)
         (cartesian_disp_codomain_functor
            (F ∙ G)
            (composition_preserves_pullback HF HG))
         (cod_mor πA)
         πB).
Proof.
  apply maponpaths.
  use (cartesian_factorisation_unique
         (disp_functor_composite_is_cartesian_disp_functor
            (is_cartesian_disp_codomain_functor F HF)
            (is_cartesian_disp_codomain_functor G HG)
            Γ (cod_dom πA) (cod_mor πA) πB
            _
            (disp_codomain_cleaving PB₁ Γ (cod_dom πA) (cod_mor πA) πB)
            (disp_codomain_cleaving PB₁ Γ (cod_dom πA) (cod_mor πA) πB))).
  etrans.
  {
    apply cartesian_factorisation_commutes.
  }
  refine (!_).
  etrans.
  {
    pose (is_cartesian_disp_codomain_functor
            (F ∙ G)
            (composition_preserves_pullback HF HG)
            Γ
            (cod_dom πA) (cod_mor πA) πB
            _
            (disp_codomain_cleaving PB₁ Γ (cod_dom πA) (cod_mor πA) πB)
            (disp_codomain_cleaving PB₁ Γ (cod_dom πA) (cod_mor πA) πB))
      as H.
    refine (_ @ cartesian_factorisation_commutes H _ _).
    apply maponpaths.
    use subtypePath.
    {
      intro ; apply homset_property.
    }
    apply idpath.
  }
  use subtypePath.
  {
    intro ; apply homset_property.
  }
  rewrite !transportf_cod_disp.
  apply idpath.
Qed.

Proposition comp_preserves_locally_cartesian_closed_z_iso
            {C₁ C₂ C₃ : category}
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            {PB₃ : Pullbacks C₃}
            {H₁ : is_locally_cartesian_closed PB₁}
            {H₂ : is_locally_cartesian_closed PB₂}
            {H₃ : is_locally_cartesian_closed PB₃}
            {F : C₁ ⟶ C₂}
            {HF : preserves_pullback F}
            (HFF : preserves_locally_cartesian_closed HF H₁ H₂)
            {G : C₂ ⟶ C₃}
            {HG : preserves_pullback G}
            (HGG : preserves_locally_cartesian_closed HG H₂ H₃)
            {Γ : C₁}
            (πA : C₁/Γ)
            (πB : C₁/cod_dom πA)
  : #G(preserves_locally_cartesian_closed_z_iso HFF πA πB)
    · preserves_locally_cartesian_closed_z_iso HGG _ _
    =
    preserves_locally_cartesian_closed_z_iso
      (comp_preserves_locally_cartesian_closed HFF HGG)
      πA
      πB.
Proof.
  refine (!_).
  cbn -[right_beck_chevalley_nat_trans].
  pose (right_beck_chevalley_nat_trans_comp
          (cartesian_disp_codomain_functor F HF)
          (cartesian_disp_codomain_functor G HG)
          _
          πB
          (H₁ (cod_dom πA) Γ (cod_mor πA))
          (H₂ (F(cod_dom πA)) (F Γ) (#F(cod_mor πA)))
          (H₃ (G(F(cod_dom πA))) (G(F Γ)) (#G(#F (cod_mor πA)))))
    as p.
  refine (_ @ maponpaths dom_mor p @ _).
  - apply (maponpaths dom_mor).
    pose (right_beck_chevalley_nat_trans_eq_nat_trans
            (H₁ (cod_dom πA) Γ (cod_mor πA))
            (H₃ (G(F(cod_dom πA))) (G(F Γ)) (#G(#F (cod_mor πA))))
            (fiber_functor_natural_nat_z_iso
               (disp_codomain_cleaving PB₁)
               (disp_codomain_cleaving PB₃)
               (cartesian_disp_codomain_functor
                  (F ∙ G)
                  (composition_preserves_pullback HF HG))
               (cod_mor πA))
            (fiber_functor_natural_nat_z_iso
               (disp_codomain_cleaving PB₁)
               (disp_codomain_cleaving PB₃)
               (comp_cartesian_disp_functor
                  (cartesian_disp_codomain_functor F HF)
                  (cartesian_disp_codomain_functor G HG))
               (cod_mor πA))
            (fiber_functor_codomain_comp HF HG Γ)
            (nat_z_iso_inv (fiber_functor_codomain_comp HF HG _)))
      as q.
    refine (q _ πB @ _).
    {
      intro πB'.
      refine (!_).
      refine (id_right _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply functor_id.
      }
      use eq_mor_cod_fib.
      refine (comp_in_cod_fib _ _ @ _).
      refine (id_left _ @ _).
      exact (fiber_functor_codomain_comp_eq HF HG πA πB').
    }
    refine (assoc' _ _ _ @ _).
    refine (id_left _ @ _).
    refine (_ @ id_right _).
    apply maponpaths.
    apply (functor_id (right_adjoint _)).
  - refine (comp_in_cod_fib _ _ @ _).
    use maponpaths_compose.
    + exact (disp_codomain_fiber_functor_mor _ _ _).
    + apply idpath.
Qed.

(** 4. Naturality of preservation *)
Definition preserves_locally_cartesian_closed_natural_mor
           {C₁ C₂ : category}
           {PB₁ : Pullbacks C₁}
           (PB₂ : Pullbacks C₂)
           {F : C₁ ⟶ C₂}
           (HF : preserves_pullback F)
           {Γ : C₁}
           {πA₁ πA₂ : C₁/Γ}
           {πB₁ : C₁/cod_dom πA₁}
           {πB₂ : C₁/cod_dom πA₂}
           (hf : πA₂ --> πA₁)
           (hg : cod_pb PB₁ (dom_mor hf) πB₁ --> πB₂)
  : cod_pb PB₂ (dom_mor (functor_on_cod_fib_mor F hf)) (functor_on_cod_fib F πB₁)
    -->
    functor_on_cod_fib F πB₂.
Proof.
  use make_cod_fib_mor.
  - exact (preserve_pullback_to_z_iso_inv _ _ HF _ _ · #F (dom_mor hg)).
  - abstract
      (simpl ;
       rewrite !assoc' ;
       rewrite <- functor_comp ;
       etrans ; [ do 2 apply maponpaths ; exact (mor_eq hg) | ] ;
       apply (PullbackArrow_PullbackPr2 (functor_preserves_pullback_on_pullback _ _ _ _))).
Defined.

Definition preserves_locally_cartesian_closed_natural_id_mor
           {C₁ C₂ : category}
           {PB₁ : Pullbacks C₁}
           (PB₂ : Pullbacks C₂)
           (F : C₁ ⟶ C₂)
           {Γ : C₁}
           {πA₁ πA₂ : C₁/Γ}
           {πB₁ : C₁/cod_dom πA₁}
           {πB₂ : C₁/cod_dom πA₂}
           (hf : πA₂ --> πA₁)
           (hg : cod_pb PB₁ (dom_mor hf) πB₁ --> πB₂)
  : cod_pb
      PB₂
      (identity _)
      (functor_on_cod_fib F (cod_pb PB₁ (dom_mor hf) πB₁))
    -->
    functor_on_cod_fib F πB₂.
Proof.
  use make_cod_fib_mor.
  - exact (PullbackPr1 _ · #F (dom_mor hg)).
  - abstract
      (simpl ;
       rewrite !assoc' ;
       rewrite <- functor_comp ;
       etrans ;
       [ do 2 apply maponpaths ;
         exact (mor_eq hg)
       | ] ;
       refine (PullbackSqrCommutes _ @ _) ;
       apply id_right).
Defined.

Proposition preserves_locally_cartesian_closed_natural_eq
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {Γ : C₁}
            {πA₁ πA₂ : C₁/Γ}
            (hf : πA₂ --> πA₁)
  : cod_mor (functor_on_cod_fib F πA₂)
    =
    dom_mor (functor_on_cod_fib_mor F hf) · cod_mor (functor_on_cod_fib F πA₁).
Proof.
  simpl.
  rewrite <- functor_comp.
  apply maponpaths.
  exact (!(mor_eq hf)).
Qed.

Proposition preserves_locally_cartesian_closed_nat_trans_ax
            {C₁ C₂ : category}
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            {F : C₁ ⟶ C₂}
            {HF : preserves_pullback F}
            {H₁ : is_locally_cartesian_closed PB₁}
            {H₂ : is_locally_cartesian_closed PB₂}
            (HFF : preserves_locally_cartesian_closed HF H₁ H₂)
            {Γ : C₁}
            {πA₁ πA₂ : C₁/Γ}
            {πB₁ : C₁/cod_dom πA₁}
            {πB₂ : C₁/cod_dom πA₂}
            (hf : πA₂ --> πA₁)
            (hg : cod_pb PB₁ (dom_mor hf) πB₁ --> πB₂)
  : #F (dom_mor (#(right_adjoint (H₁ (cod_dom πA₂) Γ (cod_mor πA₂))) hg))
    · preserves_locally_cartesian_closed_z_iso HFF πA₂ πB₂
    =
    preserves_locally_cartesian_closed_z_iso HFF πA₂ (cod_pb PB₁ (dom_mor hf) πB₁)
    · lccc_exp_functor
        H₂
        (!(id_left (cod_mor (functor_on_cod_fib F πA₂))))
        (preserves_locally_cartesian_closed_natural_id_mor PB₂ F hf hg).
Proof.
  pose (right_beck_chevalley_nat_trans
          (H₁ (cod_dom πA₂) Γ (cod_mor πA₂))
          (H₂ (F (cod_dom πA₂)) (F Γ) (# F (cod_mor πA₂)))
          (fiber_functor_natural_nat_z_iso
             (disp_codomain_cleaving PB₁)
             (disp_codomain_cleaving PB₂)
             (cartesian_disp_codomain_functor F HF)
             (cod_mor πA₂)))
    as τ.
  etrans.
  {
    refine (_ @ maponpaths dom_mor (nat_trans_ax τ _ _ hg) @ comp_in_cod_fib _ _).
    refine (_ @ !(comp_in_cod_fib _ _)).
    apply maponpaths_2.
    refine (!_).
    apply disp_codomain_fiber_functor_mor.
  }
  apply maponpaths.

  refine (!_).
  refine (comp_in_cod_fib _ _ @ _).
  etrans.
  {
    apply maponpaths_2.
    apply comp_in_cod_fib.
  }
  refine (assoc' _ _ _ @ _).
  refine (!_).
  etrans.
  {
    refine (!(id_left _) @ _).
    apply maponpaths_2.
    refine (!_).
    exact (maponpaths
             dom_mor
             (triangle_id_right_ad (pr2 (H₂ _ _ _)) _)).
  }
  rewrite comp_in_cod_fib.
  rewrite !assoc'.
  apply maponpaths.
  refine (_ @ comp_in_cod_fib _ _).
  refine (!(comp_in_cod_fib _ _) @ _).
  apply maponpaths.
  refine (_ @ functor_comp (right_adjoint _) _ _).
  refine (!(functor_comp (right_adjoint _) _ _) @ _).
  apply maponpaths.
  use eq_mor_cod_fib.
  rewrite !comp_in_cod_fib.
  etrans.
  {
    apply maponpaths.
    apply disp_codomain_fiber_functor_mor.
  }
  refine (!_).
  etrans.
  {
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    apply PullbackArrow_PullbackPr1.
  }
  apply maponpaths_2.
  refine (_ @ id_left _).
  apply maponpaths_2.
  refine (_ @ cod_pb_left_functorial_id _ _).
  apply maponpaths.
  use eq_mor_cod_fib.
  apply idpath.
Qed.

Definition preserves_locally_cartesian_closed_natural_base_mor_pb
           {C₁ C₂ : category}
           {PB₁ : Pullbacks C₁}
           {PB₂ : Pullbacks C₂}
           {F : C₁ ⟶ C₂}
           (HF : preserves_pullback F)
           {Γ : C₁}
           {πA₁ πA₂ : C₁/Γ}
           (πB : C₁/cod_dom πA₁)
           (hf : πA₂ --> πA₁)
           (p : cod_mor πA₂ = dom_mor hf · cod_mor πA₁)
  : cod_dom (cod_pb PB₂ (# F (dom_mor hf)) (functor_on_cod_fib F πB))
    -->
    cod_dom (functor_on_cod_fib F (cod_pb PB₁ (dom_mor (make_cod_fib_mor _ (!p))) πB)).
Proof.
  use (PullbackArrow (functor_preserves_pullback_on_pullback _ HF _ _)).
  - exact (PullbackPr1 _).
  - exact (PullbackPr2 _).
  - abstract
      (apply PullbackSqrCommutes).
Defined.

Definition preserves_locally_cartesian_closed_natural_base_mor
           {C₁ C₂ : category}
           {PB₁ : Pullbacks C₁}
           {PB₂ : Pullbacks C₂}
           {F : C₁ ⟶ C₂}
           {HF : preserves_pullback F}
           {H₁ : is_locally_cartesian_closed PB₁}
           {H₂ : is_locally_cartesian_closed PB₂}
           (HFF : preserves_locally_cartesian_closed HF H₁ H₂)
           {Γ : C₁}
           {πA₁ πA₂ : C₁/Γ}
           {πB : C₁/cod_dom πA₁}
           (hf : πA₂ --> πA₁)
           (p : cod_mor πA₂ = dom_mor hf · cod_mor πA₁)
  : lccc_exp H₂ (functor_on_cod_fib F πA₁) (functor_on_cod_fib F πB)
    -->
    lccc_exp
      H₂
      (functor_on_cod_fib F πA₂)
      (functor_on_cod_fib
         F
         (cod_pb PB₁ (dom_mor (make_cod_fib_mor (dom_mor hf) (!p))) πB)).
Proof.
  use lccc_exp_functor.
  - exact (#F (dom_mor hf)).
  - abstract
      (simpl ;
       rewrite <- !functor_comp ;
       rewrite p ;
       apply idpath).
  - use make_cod_fib_mor.
    + exact (preserves_locally_cartesian_closed_natural_base_mor_pb HF πB hf p).
    + abstract
        (apply (PullbackArrow_PullbackPr2
                  (functor_preserves_pullback_on_pullback _ HF _ _))).
Defined.

Proposition preserves_locally_cartesian_closed_natural_base
            {C₁ C₂ : category}
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            {F : C₁ ⟶ C₂}
            {HF : preserves_pullback F}
            {H₁ : is_locally_cartesian_closed PB₁}
            {H₂ : is_locally_cartesian_closed PB₂}
            (HFF : preserves_locally_cartesian_closed HF H₁ H₂)
            {Γ : C₁}
            {πA₁ πA₂ : C₁/Γ}
            {πB : C₁/cod_dom πA₁}
            (hf : πA₂ --> πA₁)
            (p : cod_mor πA₂ = dom_mor hf · cod_mor πA₁)
  : #F (dom_mor (lccc_exp_functor_base_fib H₁ (make_cod_fib_mor (dom_mor hf) (!p))))
    · preserves_locally_cartesian_closed_z_iso
        HFF πA₂
        (cod_pb PB₁ (dom_mor (make_cod_fib_mor (dom_mor hf) (!p))) πB)
    =
    preserves_locally_cartesian_closed_z_iso HFF πA₁ πB
    · preserves_locally_cartesian_closed_natural_base_mor HFF hf p.
Proof.
  etrans.
  {
    apply maponpaths.
    pose (right_beck_chevalley_nat_trans_ob
            (H₁ (cod_dom πA₂) Γ (cod_mor πA₂))
            (H₂ (F (cod_dom πA₂)) (F Γ) (# F (cod_mor πA₂)))
            (fiber_functor_natural_nat_z_iso
               (disp_codomain_cleaving PB₁)
               (disp_codomain_cleaving PB₂)
               (cartesian_disp_codomain_functor F HF)
               (cod_mor πA₂))
            (cod_pb PB₁ (dom_mor (make_cod_fib_mor (dom_mor hf) (!p))) πB))
      as q.
    exact (maponpaths dom_mor q).
  }
  rewrite !comp_in_cod_fib.
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    pose (φ := functor_on_cod_fib_mor
                 F
                 (lccc_exp_functor_base_fib
                    H₁
                    (πB := πB)
                    (make_cod_fib_mor (dom_mor hf) (!p)))).
    pose (nat_trans_ax
            (unit_from_left_adjoint (H₂ (F (cod_dom πA₂)) (F Γ) (# F (cod_mor πA₂))))
            _ _
            φ)
      as q.
    refine (_ @ maponpaths dom_mor q).
    rewrite comp_in_cod_fib.
    apply idpath.
  }
  rewrite comp_in_cod_fib.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite <- !comp_in_cod_fib.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      exact (!(functor_comp (right_adjoint (H₂ _ _ _))) _ _).
    }
    exact (!(functor_comp (right_adjoint (H₂ _ _ _))) _ _).
  }
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    cbn -[right_beck_chevalley_nat_trans].
    pose (right_beck_chevalley_nat_trans_ob
            (H₁ (cod_dom πA₁) Γ (cod_mor πA₁))
            (H₂ (F (cod_dom πA₁)) (F Γ) (# F (cod_mor πA₁)))
            (fiber_functor_natural_nat_z_iso
               (disp_codomain_cleaving PB₁)
               (disp_codomain_cleaving PB₂)
               (cartesian_disp_codomain_functor F HF)
               (cod_mor πA₁))
            πB)
      as q.
    exact (maponpaths dom_mor q).
  }
  etrans.
  {
    apply maponpaths.
    apply comp_in_cod_fib.
  }
  refine (assoc _ _ _ @ _).
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    apply comp_in_cod_fib.
  }
  etrans.
  {
    apply maponpaths_2.
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    pose (nat_trans_ax
            (unit_from_left_adjoint
               (H₂ (cod_dom (functor_on_cod_fib F πA₂))
                  (F Γ)
                  (cod_mor (functor_on_cod_fib F πA₂))))
            _ _
            (unit_from_left_adjoint
               (H₂ (F (cod_dom πA₁)) (F Γ) (# F (cod_mor πA₁)))
               (fiber_functor
                  (cartesian_disp_codomain_functor F HF)
                  Γ
                  (right_adjoint (H₁ (cod_dom πA₁) Γ (cod_mor πA₁)) πB))
             · #(right_adjoint (H₂ (F (cod_dom πA₁)) (F Γ) (# F (cod_mor πA₁))))
                (fiber_functor_natural_nat_z_iso
                   (disp_codomain_cleaving PB₁)
                   (disp_codomain_cleaving PB₂)
                   (cartesian_disp_codomain_functor F HF)
                   (cod_mor πA₁)
                   (right_adjoint (H₁ (cod_dom πA₁) Γ (cod_mor πA₁)) πB))
             · # (right_adjoint (H₂ (F (cod_dom πA₁)) (F Γ) (# F (cod_mor πA₁))))
                 (#(fiber_functor (cartesian_disp_codomain_functor F HF) (cod_dom πA₁))
                    (counit_from_left_adjoint (H₁ (cod_dom πA₁) Γ (cod_mor πA₁)) πB))))
      as q.
    refine (_ @ maponpaths dom_mor q).
    exact (!(comp_in_cod_fib _ _)).
  }
  rewrite !comp_in_cod_fib.
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    apply maponpaths.
    exact (!(comp_in_cod_fib _ _)).
  }
  refine (!(comp_in_cod_fib _ _) @ _).
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      exact (!(functor_comp (right_adjoint (H₂ _ _ _))) _ _).
    }
    exact (!(functor_comp (right_adjoint (H₂ _ _ _))) _ _).
  }
  do 2 apply maponpaths.
  use eq_mor_cod_fib.
  rewrite !comp_in_cod_fib.
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    apply disp_codomain_fiber_functor_mor.
  }
  refine (!_).
  use (MorphismsIntoPullbackEqual
         (isPullback_Pullback
            (functor_preserves_pullback_on_pullback _ HF _ _))).
  - rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply (PullbackArrow_PullbackPr1
               (functor_preserves_pullback_on_pullback _ HF _ _)).
    }
    etrans.
    {
      apply maponpaths.
      apply PullbackArrow_PullbackPr1.
    }
    refine (!_).
    etrans.
    {
      rewrite !assoc.
      do 2 apply maponpaths_2.
      refine (!(comp_in_cod_fib _ _) @ _).
      apply maponpaths.
      pose (nat_trans_ax
              (fiber_functor_natural_nat_z_iso
                 (disp_codomain_cleaving PB₁)
                 (disp_codomain_cleaving PB₂)
                 (cartesian_disp_codomain_functor F HF)
                 (cod_mor πA₂))
              _ _
              (lccc_exp_functor_base_fib H₁ (πB := πB) (make_cod_fib_mor (dom_mor hf) (! p))))
        as q.
      refine (_ @ q).
      apply maponpaths_2.
      refine (maponpaths (#(cod_pb _ _)) _).
      refine (!_).
      use eq_mor_cod_fib.
      apply disp_codomain_fiber_functor_mor.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply maponpaths_2.
      apply disp_codomain_fiber_functor_mor.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply (functor_comp F).
      }
      refine (!(functor_comp F _ _) @ _).
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (!(comp_in_cod_fib _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply functor_comp.
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply (nat_trans_ax (counit_from_left_adjoint (H₁ (cod_dom πA₂) Γ (cod_mor πA₂)))).
      }
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply (triangle_id_left_ad (pr2 (H₁ (cod_dom πA₂) Γ (cod_mor πA₂)))).
      }
      apply id_left.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply PullbackArrow_PullbackPr1.
    }
    rewrite functor_comp.
    rewrite !assoc.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply cod_pb_left_functorial_natural.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply functor_comp.
      }
      rewrite comp_in_cod_fib.
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          do 2 apply maponpaths.
          exact (!(functor_comp (right_adjoint (H₂ _ _ _))) _ _).
        }
        pose (lccc_exp_eval_fib H₂ (functor_on_cod_fib F πA₁) (functor_on_cod_fib F πB))
          as ψ.
        refine (!(comp_in_cod_fib _ ψ) @ _).
        apply maponpaths.
        apply (nat_trans_ax
                (counit_from_left_adjoint
                   (H₂ _ _ (cod_mor (functor_on_cod_fib F πA₁))))).
      }
      rewrite comp_in_cod_fib.
      rewrite assoc.
      etrans.
      {
        apply maponpaths_2.
        rewrite <- comp_in_cod_fib.
        apply maponpaths.
        apply (triangle_id_left_ad (pr2 (H₂ (F (cod_dom πA₁)) (F Γ) (# F (cod_mor πA₁))))).
      }
      apply id_left.
    }
    etrans.
    {
      apply maponpaths.
      apply (comp_in_cod_fib
               _
               (#(fiber_functor (cartesian_disp_codomain_functor F HF) (cod_dom πA₁))
                 (counit_from_left_adjoint (H₁ (cod_dom πA₁) Γ (cod_mor πA₁)) πB))).
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths.
      apply disp_codomain_fiber_functor_mor.
    }
    apply maponpaths_2.
    use (MorphismsIntoPullbackEqual
           (isPullback_Pullback
              (functor_preserves_pullback_on_pullback _ HF _ _))).
    + rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (codomain_fiber_functor_natural_nat_z_iso_pr1 _ _ _ _ _ _).
      }
      etrans.
      {
        apply PullbackArrow_PullbackPr1.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (!(functor_comp F _ _) @ _).
        apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      }
      exact (codomain_fiber_functor_natural_nat_z_iso_pr1 _ _ _ _ _ _).
    + rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (codomain_fiber_functor_natural_nat_z_iso_pr2 _ _ _ _ _ _).
      }
      etrans.
      {
        apply PullbackArrow_PullbackPr2.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (!(functor_comp F _ _) @ _).
        apply maponpaths.
        apply PullbackArrow_PullbackPr2.
      }
      rewrite functor_comp.
      rewrite assoc.
      apply maponpaths_2.
      exact (codomain_fiber_functor_natural_nat_z_iso_pr2 _ _ _ _ _ _).
  - rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply (PullbackArrow_PullbackPr2
               (functor_preserves_pullback_on_pullback _ HF _ _)).
    }
    etrans.
    {
      apply maponpaths.
      apply PullbackArrow_PullbackPr2.
    }

    refine (!_).
    etrans.
    {
      rewrite !assoc.
      do 2 apply maponpaths_2.
      refine (!(comp_in_cod_fib _ _) @ _).
      apply maponpaths.
      pose (nat_trans_ax
              (fiber_functor_natural_nat_z_iso
                 (disp_codomain_cleaving PB₁)
                 (disp_codomain_cleaving PB₂)
                 (cartesian_disp_codomain_functor F HF)
                 (cod_mor πA₂))
              _ _
              (lccc_exp_functor_base_fib H₁ (πB := πB) (make_cod_fib_mor (dom_mor hf) (! p))))
        as q.
      refine (_ @ q).
      apply maponpaths_2.
      refine (maponpaths (#(cod_pb _ _)) _).
      refine (!_).
      use eq_mor_cod_fib.
      apply disp_codomain_fiber_functor_mor.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply maponpaths_2.
      apply disp_codomain_fiber_functor_mor.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply (functor_comp F).
      }
      refine (!(functor_comp F _ _) @ _).
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (!(comp_in_cod_fib _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply functor_comp.
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply (nat_trans_ax (counit_from_left_adjoint (H₁ (cod_dom πA₂) Γ (cod_mor πA₂)))).
      }
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply (triangle_id_left_ad (pr2 (H₁ (cod_dom πA₂) Γ (cod_mor πA₂)))).
      }
      apply id_left.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply PullbackArrow_PullbackPr2.
    }
    refine (!_).
    etrans.
    {
      rewrite cod_fiber_functor_on_mor.
      apply PullbackArrow_PullbackPr2.
    }
    refine (!_).
    exact (codomain_fiber_functor_natural_nat_z_iso_pr2 _ _ _ _ _ _).
Qed.

Proposition preserves_locally_cartesian_closed_natural
            {C₁ C₂ : category}
            {PB₁ : Pullbacks C₁}
            {PB₂ : Pullbacks C₂}
            {F : C₁ ⟶ C₂}
            {HF : preserves_pullback F}
            {H₁ : is_locally_cartesian_closed PB₁}
            {H₂ : is_locally_cartesian_closed PB₂}
            (HFF : preserves_locally_cartesian_closed HF H₁ H₂)
            {Γ : C₁}
            {πA₁ πA₂ : C₁/Γ}
            {πB₁ : C₁/cod_dom πA₁}
            {πB₂ : C₁/cod_dom πA₂}
            (hf : πA₂ --> πA₁)
            (hg : cod_pb PB₁ (dom_mor hf) πB₁ --> πB₂)
            (p : cod_mor πA₂ = dom_mor hf · cod_mor πA₁)
  : #F(lccc_exp_functor H₁ p hg)
    · preserves_locally_cartesian_closed_z_iso HFF πA₂ πB₂
    =
    preserves_locally_cartesian_closed_z_iso HFF πA₁ πB₁
    · lccc_exp_functor
        H₂
        (preserves_locally_cartesian_closed_natural_eq hf)
        (preserves_locally_cartesian_closed_natural_mor _ HF hf hg).
Proof.
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      apply comp_in_cod_fib.
    }
    apply functor_comp.
  }
  refine (assoc' _ _ _ @ _).
  etrans.
  {
    apply maponpaths.
    apply preserves_locally_cartesian_closed_nat_trans_ax.
  }
  rewrite assoc.
  etrans.
  {
    apply maponpaths_2.
    apply (preserves_locally_cartesian_closed_natural_base HFF).
  }
  rewrite !assoc'.
  apply maponpaths.
  unfold preserves_locally_cartesian_closed_natural_base_mor.
  etrans.
  {
    apply lccc_exp_functor_on_comp.
  }
  use lccc_exp_functor_eq.
  {
    abstract
      (apply id_left).
  }
  rewrite !comp_in_cod_fib.
  rewrite  cod_fiber_functor_on_mor.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    apply PullbackArrow_PullbackPr1.
  }
  simpl.
  rewrite !assoc.
  apply maponpaths_2.
  etrans.
  {
    apply maponpaths_2.
    apply PullbackArrow_PullbackPr1.
  }
  unfold preserve_pullback_to_z_iso_inv.
  use (MorphismsIntoPullbackEqual
         (isPullback_Pullback
            (functor_preserves_pullback_on_pullback _ HF _ _))).
  - rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply (PullbackArrow_PullbackPr1
               (functor_preserves_pullback_on_pullback _ HF _ _)).
    }
    etrans.
    {
      apply PullbackArrow_PullbackPr1.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (PullbackArrow_PullbackPr1
               (functor_preserves_pullback_on_pullback _ HF _ _)).
    }
    apply PullbackArrow_PullbackPr1.
  - rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply (PullbackArrow_PullbackPr2
               (functor_preserves_pullback_on_pullback _ HF _ _)).
    }
    etrans.
    {
      apply PullbackArrow_PullbackPr2.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (PullbackArrow_PullbackPr2
               (functor_preserves_pullback_on_pullback _ HF _ _)).
    }
    rewrite id_right.
    apply PullbackArrow_PullbackPr2.
Qed.
