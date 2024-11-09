(*******************************************************************************************

 Dependent products in fibrations

 A fibration supports dependent products if every fiber functor `D[{y}] ⟶ D[{x}]` has a
 right adjoint for which the Beck-Chevalley condition is satisfied. In the context of
 first-order logic (i.e., hyperdoctrines), this represents universal quantification, and in
 the context of dependent type theory (i.e., comprehension categories), this represents the
 dependent product operation. In this file, we define the basic notions involving dependent
 products i fibrations and we define when functors preserve dependent products, and we prove
 some basic properties.

 Contents
 1. The Beck-Chevalley condition for right adjoints
 2. Dependent products
 3. Accessors for dependent products
 4. Preservation of dependent products by functors between fibrations
 5. Examples of functors that preserve dependent products

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Local Open Scope cat.

(** * 1. The Beck-Chevalley condition for right adjoints *)
Definition right_beck_chevalley_nat_trans
           {C₁ C₂ C₃ C₄ : category}
           {F : C₁ ⟶ C₂}
           {G : C₁ ⟶ C₃}
           {H : C₃ ⟶ C₄}
           {K : C₂ ⟶ C₄}
           (HF : is_left_adjoint F)
           (FR := right_adjoint HF)
           (ε₁ := counit_from_left_adjoint HF)
           (HH : is_left_adjoint H)
           (HR := right_adjoint HH)
           (η₂ := unit_from_left_adjoint HH)
           (τ : nat_z_iso (G ∙ H) (F ∙ K))
  : FR ∙ G ⟹ K ∙ HR
  := nat_trans_comp
       _ _ _
       (pre_whisker (FR ∙ G) η₂)
       (nat_trans_comp
          _ _ _
          (post_whisker (pre_whisker FR τ) HR)
          (post_whisker ε₁ (K ∙ HR))).

Proposition right_beck_chevalley_nat_trans_ob
            {C₁ C₂ C₃ C₄ : category}
            {F : C₁ ⟶ C₂}
            {G : C₁ ⟶ C₃}
            {H : C₃ ⟶ C₄}
            {K : C₂ ⟶ C₄}
            (HF : is_left_adjoint F)
            (FR := right_adjoint HF)
            (ε₁ := counit_from_left_adjoint HF)
            (HH : is_left_adjoint H)
            (HR := right_adjoint HH)
            (η₂ := unit_from_left_adjoint HH)
            (τ : nat_z_iso (G ∙ H) (F ∙ K))
            (x : C₂)
  : right_beck_chevalley_nat_trans HF HH τ x
    =
    η₂ (G(FR x)) · #HR(τ(FR x)) · #HR(#K(ε₁ x)).
Proof.
  apply assoc.
Qed.

Section DependentProduct.
  Context {C : category}
          {D : disp_cat C}
          (HD : cleaving D).

  (** * 2. Dependent products *)
  Definition dependent_product
             {x y : C}
             (f : x --> y)
    : UU
    := is_left_adjoint
         (fiber_functor_from_cleaving D HD f).

  Definition comm_nat_z_iso_inv
             {w x y z : C}
             (f : x --> w)
             (g : y --> w)
             (h : z --> y)
             (k : z --> x)
             (p : k · f = h · g)
             (F := fiber_functor_from_cleaving D HD f : D[{w}] ⟶ D[{x}])
             (G := fiber_functor_from_cleaving D HD g : D[{w}] ⟶ D[{y}])
             (H := fiber_functor_from_cleaving D HD h : D[{y}] ⟶ D[{z}])
             (K := fiber_functor_from_cleaving D HD k : D[{x}] ⟶ D[{z}])
    : nat_z_iso (G ∙ H) (F ∙ K)
    := nat_z_iso_inv (comm_nat_z_iso HD f g h k p).

  Proposition comm_nat_z_iso_inv_ob
              {w x y z : C}
              (f : x --> w)
              (g : y --> w)
              (h : z --> y)
              (k : z --> x)
              (p : k · f = h · g)
              (F := fiber_functor_from_cleaving D HD f : D[{w}] ⟶ D[{x}])
              (G := fiber_functor_from_cleaving D HD g : D[{w}] ⟶ D[{y}])
              (H := fiber_functor_from_cleaving D HD h : D[{y}] ⟶ D[{z}])
              (K := fiber_functor_from_cleaving D HD k : D[{x}] ⟶ D[{z}])
              (φ : D[{w}])
    : comm_nat_z_iso_inv f g h k p φ
      =
      fiber_functor_from_cleaving_comp _ _ _ φ
      · fiber_functor_on_eq HD (!p) φ
      · fiber_functor_from_cleaving_comp_inv _ _ _ φ.
  Proof.
    cbn -[fiber_category fiber_functor_from_cleaving_comp].
    apply maponpaths_2.
    apply maponpaths.
    induction p.
    cbn.
    apply idpath.
  Qed.

  Definition right_beck_chevalley
             {w x y z : C}
             (f : x --> w)
             (g : y --> w)
             (h : z --> y)
             (k : z --> x)
             (p : k · f = h · g)
             (R₁ : dependent_product f)
             (R₂ : dependent_product h)
    : UU
    := ∏ (a : D[{x}]),
       is_z_isomorphism
         (right_beck_chevalley_nat_trans R₁ R₂ (comm_nat_z_iso_inv f g h k p) a).

  Proposition isaprop_right_beck_chevalley
              {w x y z : C}
              (f : x --> w)
              (g : y --> w)
              (h : z --> y)
              (k : z --> x)
              (p : k · f = h · g)
              (R₁ : dependent_product f)
              (R₂ : dependent_product h)
    : isaprop (right_beck_chevalley f g h k p R₁ R₂).
  Proof.
    use impred ; intro.
    apply isaprop_is_z_isomorphism.
  Qed.

  Definition has_dependent_products
    : UU
    := ∑ (R : ∏ (x y : C) (f : x --> y), dependent_product f),
       ∏ (w x y z : C)
         (f : x --> w)
         (g : y --> w)
         (h : z --> y)
         (k : z --> x)
         (p : k · f = h · g)
         (H : isPullback p),
       right_beck_chevalley f g h k p (R _ _ f) (R _ _ h).
End DependentProduct.

Section DependentProductPoset.
  Context {C : category}
          {D : disp_cat C}
          (HD : cleaving D)
          (HD' : locally_propositional D)
          (all : ∏ (Γ₁ Γ₂ : C) (s : Γ₁ --> Γ₂), D[{Γ₁}] → D[{Γ₂}])
          (all_e : ∏ (Γ₁ Γ₂ : C)
                     (s : Γ₁ --> Γ₂)
                     (φ : D[{Γ₁}]),
                   pr1 (HD _ _ s (all _ _ s φ)) -->[ identity _ ] φ)
          (all_i : ∏ (Γ₁ Γ₂ : C)
                     (s : Γ₁ --> Γ₂)
                     (ψ : D[{Γ₁}])
                     (χ : D[{Γ₂}])
                     (p : pr1 (HD Γ₂ Γ₁ s χ) -->[ identity _ ] ψ),
                   χ -->[ identity _ ] all Γ₁ Γ₂ s ψ)
          (all_sub : ∏ (Γ₁ Γ₂ Γ₃ Γ₄ : C)
                       (s₁ : Γ₂ --> Γ₁)
                       (s₂ : Γ₃ --> Γ₁)
                       (s₃ : Γ₄ --> Γ₃)
                       (s₄ : Γ₄ --> Γ₂)
                       (p : s₄ · s₁ = s₃ · s₂)
                       (Hp : isPullback p)
                       (φ : D[{Γ₂}]),
                     all Γ₄ Γ₃ s₃ (pr1 (HD Γ₂ Γ₄ s₄ φ))
                     -->[ identity Γ₃]
                     pr1 (HD Γ₁ Γ₃ s₂ (all Γ₂ Γ₁ s₁ φ))).

  Definition make_dependent_product_of_mor_poset
             {Γ₁ Γ₂ : C}
             (s : Γ₁ --> Γ₂)
    : dependent_product HD s.
  Proof.
    use left_adjoint_from_partial.
    - exact (all _ _ s).
    - exact (all_e _ _ s).
    - intros ψ χ p.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros ζ₁ ζ₂ ;
           use subtypePath ; [ intro ; apply homset_property | ] ;
           apply HD').
      + simple refine (_ ,, _) ; [ | apply HD' ].
        apply all_i.
        exact p.
  Defined.

  Definition make_has_dependent_products_poset
    : has_dependent_products HD.
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _ s, make_dependent_product_of_mor_poset s).
    - abstract
        (intros Γ₁ Γ₂ Γ₃ Γ₄ s₁ s₂ s₃ s₄ p Hp φ ;
         simple refine (_ ,, _ ,, _) ; [ | apply HD' | apply HD' ] ;
         exact (all_sub _ _ _ _ _ _ _ _ _ Hp φ)).
  Defined.
End DependentProductPoset.

(** * 3. Accessors for dependent products *)
Section DependentProduct.
  Context {C : category}
          {D : disp_cat C}
          {HD : cleaving D}
          (P : has_dependent_products HD)
          {x y : C}
          (f : x --> y).

  Definition dep_prod
             (xx : D[{x}])
    : D[{y}]
    := right_adjoint (pr1 P x y f) xx.

  Definition dep_prod_mor
             {xx₁ xx₂ : D[{x}]}
             (ff : xx₁ --> xx₂)
    : dep_prod xx₁ --> dep_prod xx₂
    := #(right_adjoint (pr1 P x y f)) ff.

  Definition dep_prod_unit
             (yy : D[{y}])
    : yy -->[ identity y ] dep_prod (fiber_functor_from_cleaving D HD f yy)
    := unit_from_left_adjoint (pr1 P x y f) yy.

  Definition dep_prod_counit
             (xx : D[{x}])
    : fiber_functor_from_cleaving D HD f (dep_prod xx) -->[ identity x ] xx
    := counit_from_left_adjoint (pr1 P x y f) xx.
End DependentProduct.

(** * 4. Preservation of dependent products by functors between fibrations *)
Definition preserves_dependent_products
           {C₁ C₂ : category}
           {D₁ : disp_cat C₁}
           {HD₁ : cleaving D₁}
           {D₂ : disp_cat C₂}
           {HD₂ : cleaving D₂}
           {F : C₁ ⟶ C₂}
           (FF : cartesian_disp_functor F D₁ D₂)
           (R₁ : has_dependent_products HD₁)
           (R₂ : has_dependent_products HD₂)
  : UU
  := ∏ (x y : C₁)
       (f : x --> y)
       (a : D₁[{x}]),
     is_z_isomorphism
       (right_beck_chevalley_nat_trans
          (pr1 R₁ x y f)
          (pr1 R₂ (F x) (F y) (#F f))
          (fiber_functor_natural_nat_z_iso HD₁ HD₂ FF f)
          a).

Proposition isaprop_preserves_dependent_products
            {C₁ C₂ : category}
            {D₁ : disp_cat C₁}
            {HD₁ : cleaving D₁}
            {D₂ : disp_cat C₂}
            {HD₂ : cleaving D₂}
            {F : C₁ ⟶ C₂}
            (FF : cartesian_disp_functor F D₁ D₂)
            (R₁ : has_dependent_products HD₁)
            (R₂ : has_dependent_products HD₂)
  : isaprop (preserves_dependent_products FF R₁ R₂).
Proof.
  do 4 (use impred ; intro).
  apply isaprop_is_z_isomorphism.
Qed.

(** * 5. Examples of functors that preserve dependent products *)
Section IdPreserves.
  Context {C : category}
          {D : disp_cat C}
          {HD : cleaving D}
          {x y : C}
          (f : x --> y)
          (P : dependent_product HD f)
          (a : D[{x}]).

  Let R : D[{x}] ⟶ D[{y}]
    := right_adjoint P.
  Let η : functor_identity D[{y}] ⟹ fiber_functor_from_cleaving D HD f ∙ R
    := unit_from_left_adjoint P.
  Let ε : R ∙ fiber_functor_from_cleaving D HD f ⟹ functor_identity _
    := counit_from_left_adjoint P.

  Lemma right_beck_chevalley_nat_trans_id_on_ob
    : right_beck_chevalley_nat_trans
        P P
        (fiber_functor_natural_nat_z_iso HD HD (id_cartesian_disp_functor D) f)
        a
      =
      η (R a)
      · #R (fiber_functor_natural_nat_z_iso HD HD (id_cartesian_disp_functor D) f (R a))
      · #R (ε a).
  Proof.
    rewrite right_beck_chevalley_nat_trans_ob.
    apply idpath.
  Qed.

  Lemma right_beck_chevalley_nat_trans_id_natural
    : fiber_functor_natural_nat_z_iso HD HD (id_cartesian_disp_functor D) f (R a)
      =
      identity _.
  Proof.
    cbn.
    use (cartesian_factorisation_unique
           (disp_functor_identity_is_cartesian_disp_functor
              D y x f (R a)
              (HD y x f (R a))
              (HD y x f (R a))
              (HD y x f (R a)))).
    rewrite cartesian_factorisation_commutes.
    cbn.
    rewrite id_left_disp.
    unfold transportb.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Proposition right_beck_chevalley_nat_trans_id
    : right_beck_chevalley_nat_trans
        P P
        (fiber_functor_natural_nat_z_iso HD HD (id_cartesian_disp_functor D) f)
        a
      =
      identity _.
  Proof.
    rewrite right_beck_chevalley_nat_trans_id_on_ob.
    rewrite right_beck_chevalley_nat_trans_id_natural.
    rewrite functor_id.
    rewrite id_right.
    exact (pr222 P a).
  Qed.
End IdPreserves.

Definition id_preserves_dependent_products
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (P : has_dependent_products HD)
  : preserves_dependent_products (id_cartesian_disp_functor D) P P.
Proof.
  intros x y f a.
  use (is_z_isomorphism_path (!(right_beck_chevalley_nat_trans_id f _ a))).
  apply is_z_isomorphism_identity.
Qed.

Section CompPreserves.
  Context {C₁ C₂ C₃ : category}
          {D₁ : disp_cat C₁}
          {HD₁ : cleaving D₁}
          {D₂ : disp_cat C₂}
          {HD₂ : cleaving D₂}
          {D₃ : disp_cat C₃}
          {HD₃ : cleaving D₃}
          {F : C₁ ⟶ C₂}
          {G : C₂ ⟶ C₃}
          (FF : cartesian_disp_functor F D₁ D₂)
          (GG : cartesian_disp_functor G D₂ D₃)
          {x y : C₁}
          (f : x --> y)
          (a : D₁[{x}])
          (P₁ : dependent_product HD₁ f)
          (P₂ : dependent_product HD₂ (#F f))
          (P₃ : dependent_product HD₃ (#G (#F f))).

  Let R₁ : D₁[{x}] ⟶ D₁[{y}]
    := right_adjoint P₁.
  Let η₁ : functor_identity _ ⟹ fiber_functor_from_cleaving D₁ HD₁ f ∙ R₁
    := unit_from_left_adjoint P₁.
  Let ε₁ : R₁ ∙ fiber_functor_from_cleaving D₁ HD₁ f ⟹ functor_identity _
    := counit_from_left_adjoint P₁.

  Let R₂ : D₂[{F x}] ⟶ D₂[{F y}]
    := right_adjoint P₂.
  Let η₂ : functor_identity _ ⟹ fiber_functor_from_cleaving D₂ HD₂ (#F f) ∙ R₂
    := unit_from_left_adjoint P₂.
  Let ε₂ : R₂ ∙ fiber_functor_from_cleaving D₂ HD₂ (#F f) ⟹ functor_identity _
    := counit_from_left_adjoint P₂.

  Let R₃ : D₃[{G(F x)}] ⟶ D₃[{G(F y)}]
    := right_adjoint P₃.
  Let η₃ : functor_identity _ ⟹ fiber_functor_from_cleaving D₃ HD₃ (#G(#F f)) ∙ R₃
    := unit_from_left_adjoint P₃.
  Let ε₃ : R₃ ∙ fiber_functor_from_cleaving D₃ HD₃ (#G(#F f)) ⟹ functor_identity _
    := counit_from_left_adjoint P₃.

  Lemma right_beck_chevalley_nat_trans_comp_ob
    : right_beck_chevalley_nat_trans
        P₁ P₃
        (fiber_functor_natural_nat_z_iso HD₁ HD₃ (comp_cartesian_disp_functor FF GG) f)
        a
      =
      η₃ _
      · #R₃ (fiber_functor_natural_nat_z_iso HD₁ HD₃ (comp_cartesian_disp_functor FF GG) f _)
      · #R₃ (# (fiber_functor (comp_cartesian_disp_functor FF GG) x) (ε₁ _)).
  Proof.
    apply right_beck_chevalley_nat_trans_ob.
  Qed.

  Lemma right_beck_chevalley_nat_trans_comp_ob_on_left
    : right_beck_chevalley_nat_trans
        P₁ P₂
        (fiber_functor_natural_nat_z_iso HD₁ HD₂ FF f)
        a
      =
      η₂ _
      · #R₂ (fiber_functor_natural_nat_z_iso HD₁ HD₂ FF f _)
      · #R₂ (# (fiber_functor FF x) (ε₁ _)).
  Proof.
    apply right_beck_chevalley_nat_trans_ob.
  Qed.

  Lemma right_beck_chevalley_nat_trans_comp_ob_on_right
    : right_beck_chevalley_nat_trans
        P₂ P₃
        (fiber_functor_natural_nat_z_iso HD₂ HD₃ GG (#F f)) (FF x a)
      =
      η₃ _
      · #R₃ (fiber_functor_natural_nat_z_iso HD₂ HD₃ GG (#F f) _)
      · #R₃ (# (fiber_functor GG (F x)) (ε₂ _)).
  Proof.
    apply right_beck_chevalley_nat_trans_ob.
  Qed.

  Let φ
    := #(fiber_functor GG (F y))
          (η₂ (fiber_functor FF y (R₁ a))
           · # R₂ (fiber_functor_natural_nat_z_iso HD₁ HD₂ FF f (R₁ a))
           · # R₂ (# (fiber_functor FF x) (ε₁ a))).

  Lemma right_beck_chevalley_nat_trans_comp_natural
    : φ · η₃ _ = η₃ _ · #R₃(#(fiber_functor_from_cleaving D₃ HD₃ (#G(#F f))) φ).
  Proof.
    apply (nat_trans_ax η₃).
  Qed.

  Lemma fiber_functor_natural_comp
    : fiber_functor_natural HD₁ HD₃ (comp_cartesian_disp_functor FF GG) f (R₁ a)
      =
      fiber_functor_natural HD₂ HD₃ GG (#F f) (FF _ (R₁ a))
      · #(fiber_functor GG (F x)) (fiber_functor_natural HD₁ HD₂ FF f (R₁ a)).
  Proof.
    cbn.
    use (cartesian_factorisation_unique
           (disp_functor_composite_is_cartesian_disp_functor
              (cartesian_disp_functor_is_cartesian FF)
              (cartesian_disp_functor_is_cartesian GG) y x f (R₁ a) (HD₁ y x f (R₁ a))
              (HD₁ y x f (R₁ a))
              (HD₁ y x f (R₁ a)))).
    rewrite cartesian_factorisation_commutes.
    refine (!_).
    etrans.
    {
      rewrite mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      cbn.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite <- (disp_functor_comp_var GG).
      rewrite cartesian_factorisation_commutes.
      rewrite disp_functor_transportf.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite !transport_f_f.
      apply idpath.
    }
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Proposition right_beck_chevalley_nat_trans_comp
    : right_beck_chevalley_nat_trans
        P₁ P₃
        (fiber_functor_natural_nat_z_iso HD₁ HD₃ (comp_cartesian_disp_functor FF GG) f)
        a
      =
      #(fiber_functor GG _)
          (right_beck_chevalley_nat_trans
             P₁ P₂
             (fiber_functor_natural_nat_z_iso HD₁ HD₂ FF f)
             a)
      · right_beck_chevalley_nat_trans
          P₂ P₃
          (fiber_functor_natural_nat_z_iso HD₂ HD₃ GG (#F f))
          (FF _ a).
  Proof.
    rewrite right_beck_chevalley_nat_trans_comp_ob.
    rewrite right_beck_chevalley_nat_trans_comp_ob_on_left.
    rewrite right_beck_chevalley_nat_trans_comp_ob_on_right.
    refine (!_).
    etrans.
    {
      rewrite !assoc.
      do 2 apply maponpaths_2.
      apply right_beck_chevalley_nat_trans_comp_natural.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ functor_comp R₃ _ _).
    etrans.
    {
      apply maponpaths.
      exact (!(functor_comp R₃ _ _)).
    }
    refine (!(functor_comp R₃ _ _) @ _).
    apply maponpaths.
    unfold φ.
    etrans.
    {
      rewrite !assoc.
      apply maponpaths_2.
      apply (nat_trans_ax (fiber_functor_natural HD₂ HD₃ GG (# F f))).
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!(functor_comp (fiber_functor GG (F x)) _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          do 2 apply maponpaths.
          exact (!(functor_comp R₂ _ _)).
        }
        apply functor_comp.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply (nat_trans_ax ε₂).
      }
      rewrite !assoc.
      apply maponpaths_2.
      exact (pr122 P₂ (fiber_functor FF y (R₁ a))).
    }
    rewrite id_left.
    etrans.
    {
      apply maponpaths.
      apply (functor_comp (fiber_functor GG (F x))).
    }
    rewrite assoc.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact fiber_functor_natural_comp.
    }
    rewrite !assoc'.
    apply maponpaths.
    apply maponpaths.
    cbn.
    rewrite disp_functor_transportf.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.
End CompPreserves.

Definition comp_preserves_dependent_products
           {C₁ C₂ C₃ : category}
           {D₁ : disp_cat C₁}
           {HD₁ : cleaving D₁}
           {D₂ : disp_cat C₂}
           {HD₂ : cleaving D₂}
           {D₃ : disp_cat C₃}
           {HD₃ : cleaving D₃}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {FF : cartesian_disp_functor F D₁ D₂}
           {GG : cartesian_disp_functor G D₂ D₃}
           {P₁ : has_dependent_products HD₁}
           {P₂ : has_dependent_products HD₂}
           {P₃ : has_dependent_products HD₃}
           (HFF : preserves_dependent_products FF P₁ P₂)
           (HGG : preserves_dependent_products GG P₂ P₃)
  : preserves_dependent_products
      (comp_cartesian_disp_functor FF GG)
      P₁
      P₃.
Proof.
  intros x y f a.
  use (is_z_isomorphism_path
         (!(right_beck_chevalley_nat_trans_comp
              FF GG
              f a
              (pr1 P₁ _ _ f)
              (pr1 P₂ _ _ (#F f))
              (pr1 P₃ _ _ (#G (#F f)))))).
  use is_z_isomorphism_comp.
  - use functor_on_is_z_isomorphism.
    apply HFF.
  - apply HGG.
Defined.
