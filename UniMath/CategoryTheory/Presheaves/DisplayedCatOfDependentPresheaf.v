(**

 The displayed category of dependent presheaves and natural transformations

 In this file, we show that dependent presheaves and natural transformations form a
 displayed category over the category of presheaves. We also establish various facts
 about this displayed category, and in particular, we show that it is univalent.

 The relevance of this displayed category comes from the presheaf model of dependent
 type theory, because it gives us the category of types in this model. We also construct
 a cleaving for this displayed category, and we construct a comprehension functor.

 Contents
 1. The displayed category of dependent presheaves
 2. Isomorphisms in this displaed category
 3. This displayed category is univalent
 4. The cleaving
 5. The comprehension functor
 6. The comprehension functor is Cartesian
 7. The comprehension functor is fully faithful
 8. Useful calculational lemmas

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.

Local Open Scope cat.

Section DispCatDepPsh.
  Context (C : category).

  (** * 1. The displayed category of dependent presheaves *)
  Definition disp_cat_dep_psh_ob_mor
    : disp_cat_ob_mor (PreShv C).
  Proof.
    simple refine (_ ,, _).
    - exact (λ Γ, dep_psh Γ).
    - exact (λ Γ₁ Γ₂ A B s, dep_psh_nat_trans A B s).
  Defined.

  Definition disp_cat_dep_psh_id_comp
    : disp_cat_id_comp _ disp_cat_dep_psh_ob_mor.
  Proof.
    split.
    - exact (λ Γ A, dep_psh_id_nat_trans A).
    - exact (λ Γ₁ Γ₂ Γ₃ s₁ s₂ A₁ A₂ A₃ τ₁ τ₂, dep_psh_comp_nat_trans τ₁ τ₂).
  Defined.

  Definition disp_cat_dep_psh_data
    : disp_cat_data (PreShv C).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_dep_psh_ob_mor.
    - exact disp_cat_dep_psh_id_comp.
  Defined.

  Proposition transportf_dep_psh_nat_trans
              {Γ₁ Γ₂ : C^op ⟶ HSET}
              {s₁ s₂ : Γ₁ ⟹ Γ₂}
              (p : s₂ = s₁)
              {A : dep_psh Γ₁}
              {B : dep_psh Γ₂}
              (τ : dep_psh_nat_trans A B s₂)
              (x : C)
              (xx : (Γ₁ x : hSet))
              (a : A x xx)
    : (transportf (mor_disp (D := disp_cat_dep_psh_data) _ _) p τ : dep_psh_nat_trans _ _ _)
        x xx a
      =
      transportf (B x) (maponpaths (λ z, pr1 z x xx) p) (τ x xx a).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition transportb_dep_psh_nat_trans
              {Γ₁ Γ₂ : C^op ⟶ HSET}
              {s₁ s₂ : Γ₁ ⟹ Γ₂}
              (p : s₁ = s₂)
              {A : dep_psh Γ₁}
              {B : dep_psh Γ₂}
              (τ : dep_psh_nat_trans A B s₂)
              (x : C)
              (xx : (Γ₁ x : hSet))
              (a : A x xx)
    : (transportb (mor_disp (D := disp_cat_dep_psh_data) _ _) p τ : dep_psh_nat_trans _ _ _)
        x xx a
      =
      transportb (B x) (maponpaths (λ z, pr1 z x xx) p) (τ x xx a).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition disp_cat_dep_psh_axioms
    : disp_cat_axioms _ disp_cat_dep_psh_data.
  Proof.
    repeat split.
    - intros Γ₁ Γ₂ s A B τ.
      use dep_psh_nat_trans_eq.
      intros x xx a.
      rewrite transportb_dep_psh_nat_trans.
      cbn.
      refine (!_).
      apply (transportf_set ((B : dep_psh _) x)).
      apply setproperty.
    - intros Γ₁ Γ₂ s A B τ.
      use dep_psh_nat_trans_eq.
      intros x xx a.
      rewrite transportb_dep_psh_nat_trans.
      cbn.
      refine (!_).
      apply (transportf_set ((B : dep_psh _) x)).
      apply setproperty.
    - intros Γ₁ Γ₂ Γ₃ Γ₄ s₁ s₂ s₃ A₁ A₂ A₃ A₄ τ₁ τ₂ τ₃.
      use dep_psh_nat_trans_eq.
      intros x xx a.
      rewrite transportb_dep_psh_nat_trans.
      cbn.
      refine (!_).
      apply (transportf_set ((A₄ : dep_psh _) x)).
      apply setproperty.
    - intros.
      apply isaset_nat_trans.
      apply homset_property.
  Qed.

  Definition disp_cat_dep_psh
    : disp_cat (PreShv C).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_dep_psh_data.
    - exact disp_cat_dep_psh_axioms.
  Defined.

  (** * 2. Isomorphisms in this displaed category *)
  Section FromIsomorphisms.
    Context {Γ : C^op ⟶ HSET}
            {A₁ A₂ : dep_psh Γ}
            (τ : z_iso_disp (D := disp_cat_dep_psh) (identity_z_iso _) A₁ A₂).

    Definition dep_psh_to_iso
               (x : C)
               (xx : (Γ x : hSet))
      : A₁ x xx ≃ A₂ x xx.
    Proof.
      use weq_iso.
      - exact (λ a, pr11 τ (x ,, xx) a).
      - exact (λ a, pr112 τ (x ,, xx) a).
      - abstract
          (intro a ;
           refine (eqtohomot (nat_trans_eq_pointwise (pr222 τ) (x ,, xx)) a @ _) ;
           refine (transportb_dep_psh_nat_trans _ _ _ _ _ @ _) ;
           apply (transportf_set ((A₁ : dep_psh _) x)) ;
           apply setproperty).
      - abstract
          (intro a ;
           refine (eqtohomot (nat_trans_eq_pointwise (pr122 τ) (x ,, xx)) a @ _) ;
           refine (transportb_dep_psh_nat_trans _ _ _ _ _ @ _) ;
           apply (transportf_set ((A₂ : dep_psh _) x)) ;
           apply setproperty).
    Defined.

    Proposition dep_psh_to_iso_nat_trans
                {x : C}
                {xx : (Γ x : hSet)}
                {y : C}
                {yy : (Γ y : hSet)}
                (f : y --> x)
                (p : #Γ f xx = yy)
                (a : A₁ x xx)
      : dep_psh_to_iso y yy (#d A₁ f p a) = #d A₂ f p (dep_psh_to_iso x xx a).
    Proof.
      pose proof (nat_trans_ax (pr1 τ) (x ,, xx) (y ,, yy) (f ,, p)) as q.
      pose (eqtohomot q a) as q'.
      cbn in q'.
      refine (q' @ _).
      cbn.
      apply dep_psh_mor_path_eq.
      apply idpath.
    Qed.
  End FromIsomorphisms.

  Section Isomorphisms.
    Context {Γ : C^op ⟶ HSET}
            {A₁ A₂ : dep_psh Γ}
            (τ : ∏ (x : C)
                   (xx : (Γ x : hSet)),
                 A₁ x xx ≃ A₂ x xx)
            (q : ∏ (x : C)
                   (xx : (Γ x : hSet))
                   (y : C)
                   (yy : (Γ y : hSet))
                   (f : y --> x)
                   (p : #Γ f xx = yy)
                   (a : A₁ x xx),
                 τ y yy (#d A₁ f p a) = #d A₂ f p (τ x xx a)).

    Definition psh_to_disp_z_iso_mor
      : dep_psh_nat_trans A₁ A₂ (nat_trans_id _).
    Proof.
      use make_dep_psh_nat_trans.
      - exact (λ x xx a, τ x xx a).
      - abstract
          (intros x y xx yy f p₁ p₂ a ; cbn ;
           refine (q x xx y yy f _ a @ _) ;
           apply dep_psh_mor_path_eq ;
           apply idpath).
    Defined.

    Definition psh_to_disp_z_iso_inv
      : dep_psh_nat_trans A₂ A₁ (nat_trans_id _).
    Proof.
      use make_dep_psh_nat_trans.
      - exact (λ x xx a, invmap (τ x xx) a).
      - abstract
          (intros x y xx yy f p₁ p₂ a ; cbn ;
           pose (maponpaths (invmap (τ y yy)) (q x xx y yy f p₁ (invmap (τ x xx) a)))
             as r ;
           rewrite homotweqinvweq in r ;
           refine (!r @ _) ;
           rewrite homotinvweqweq ;
           apply dep_psh_mor_path_eq ;
           apply idpath).
    Defined.

    Definition psh_to_disp_z_iso
      : z_iso_disp (D := disp_cat_dep_psh) (identity_z_iso _) A₁ A₂.
    Proof.
      simple refine (_ ,, _ ,, _ ,, _).
      - exact psh_to_disp_z_iso_mor.
      - exact psh_to_disp_z_iso_inv.
      - abstract
          (use dep_psh_nat_trans_eq ;
           intros x xx a ;
           rewrite transportb_dep_psh_nat_trans ;
           cbn ;
           rewrite homotweqinvweq ;
           refine (!_) ;
           apply (transportf_set ((A₂ : dep_psh _) _)) ;
           apply setproperty).
      - abstract
          (use dep_psh_nat_trans_eq ;
           intros x xx a ;
           rewrite transportb_dep_psh_nat_trans ;
           cbn ;
           rewrite homotinvweqweq ;
           refine (!_) ;
           apply (transportf_set ((A₁ : dep_psh _) _)) ;
           apply setproperty).
    Defined.
  End Isomorphisms.

  Definition dep_psh_iso_weq
             {Γ : C^op ⟶ HSET}
             (A₁ A₂ : dep_psh Γ)
    : (∑ (τ : ∏ (x : C) (xx : (Γ x : hSet)), A₁ x xx ≃ A₂ x xx),
       ∏ (x : C)
         (xx : (Γ x : hSet))
         (y : C)
         (yy : (Γ y : hSet))
         (f : y --> x)
         (p : #Γ f xx = yy)
         (a : A₁ x xx),
       τ y yy (#d A₁ f p a) = #d A₂ f p (τ x xx a))
      ≃
      z_iso_disp (D := disp_cat_dep_psh) (identity_z_iso _) A₁ A₂.
  Proof.
    use weq_iso.
    - exact (λ τ, psh_to_disp_z_iso (pr1 τ) (pr2 τ)).
    - refine (λ τ, dep_psh_to_iso τ ,, λ x y xx yy f p a, _).
      exact (dep_psh_to_iso_nat_trans τ f p a).
    - abstract
        (intros τ ;
         use subtypePath ;
         [ intro ;
           repeat (use impred ; intro) ;
           apply setproperty
         | ] ;
         cbn ;
         use funextsec ; intro x ;
         use funextsec ; intro xx ;
         use subtypePath ; [ intro ; apply isapropisweq | ] ;
         apply idpath).
    - abstract
        (intros τ ;
         use subtypePath ;
         [ intro ;
           apply isaprop_is_z_iso_disp
         | ] ;
         use dep_psh_nat_trans_eq ;
         intros ;
         apply idpath).
  Defined.

  (** * 3. This displayed category is univalent *)
  Proposition is_univalent_disp_disp_cat_dep_psh
    : is_univalent_disp disp_cat_dep_psh.
  Proof.
    use is_univalent_disp_from_fibers.
    intros Γ A₁ A₂.
    use weqhomot.
    - refine (_ ∘ path_sigma_hprop _ _ _ _)%weq.
      {
        apply isaprop_is_functor.
        apply homset_property.
      }
      refine (_ ∘ total2_paths_equiv' _ _ _)%weq.
      refine (dep_psh_iso_weq _ _ ∘ _)%weq.
      use weqtotal2.
      + refine (_ ∘ weqtoforallpaths _ _ _)%weq.
        refine (_ ∘ weqsecovertotal2 _ _)%weq.
        use weqonsecfibers.
        intros x.
        use weqonsecfibers.
        intros xx.
        apply hSet_univalence.
      + induction A₁ as [ [ A₁ H₁ ] H₁' ].
        induction A₂ as [ [ A₂ H₂ ] H₂' ].
        cbn.
        intro p.
        induction p.
        cbn.
        refine (_ ∘ weqtoforallpaths _ _ _)%weq.
        refine (_ ∘ weqsecovertotal2 _ _)%weq.
        use weqonsecfibers.
        intro x.
        use weqonsecfibers.
        intro xx.
        refine (_ ∘ weqtoforallpaths _ _ _)%weq.
        refine (_ ∘ weqsecovertotal2 _ _)%weq.
        use weqonsecfibers.
        intro y.
        use weqonsecfibers.
        intro yy.
        refine (_ ∘ weqtoforallpaths _ _ _)%weq.
        refine (_ ∘ weqsecovertotal2 _ _)%weq.
        use weqonsecfibers.
        intro f.
        use weqonsecfibers.
        intro p.
        cbn.
        apply weqtoforallpaths.
    - intro p.
      induction p.
      use eq_z_iso_disp.
      use dep_psh_nat_trans_eq.
      intros ; cbn.
      apply idpath.
  Qed.

  Definition univalent_disp_cat_dep_psh
    : disp_univalent_category (PreShv C).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_dep_psh.
    - exact is_univalent_disp_disp_cat_dep_psh.
  Defined.

  (** * 4. The cleaving *)
  Definition cleaving_disp_cat_dep_psh
    : cleaving disp_cat_dep_psh.
  Proof.
    intros Γ₁ Γ₂ s A.
    simple refine (_ ,, _).
    - exact (dep_psh_subst s A).
    - simple refine (_ ,, _).
      + exact (dep_psh_subst_nat_trans s A).
      + intros Γ' s' B τ.
        use make_iscontr.
        * simple refine (_ ,, _).
          ** exact (dep_psh_factor_nat_trans τ).
          ** abstract
              (use dep_psh_nat_trans_eq ;
               intros x xx a ; cbn ;
               apply idpath).
        * abstract
            (intros τ' ;
             use subtypePath ; [ intro ; apply homsets_disp | ] ;
             use dep_psh_nat_trans_eq ;
             intros x xx a ; cbn ;
             exact (eqtohomot (maponpaths (λ z, pr1 z (x ,, xx)) (pr2 τ')) a)).
  Defined.

  (** * 5. The comprehension functor *)
  Definition dep_psh_comprehension_data
    : disp_functor_data
        (functor_identity _)
        disp_cat_dep_psh
        (disp_codomain (PreShv C)).
  Proof.
    simple refine (_ ,, _).
    - exact (λ Γ A, total_psh A ,, total_psh_pr A).
    - refine (λ Γ₁ Γ₂ A B s τ, total_psh_nat_trans s τ ,, _).
      abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         apply idpath).
  Defined.

  Proposition dep_psh_comprehension_laws
    : disp_functor_axioms dep_psh_comprehension_data.
  Proof.
    split.
    - intros Γ A.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn.
      apply idpath.
    - intros Γ₁ Γ₂ Γ₃ A₁ A₂ A₃ s₁ s₂ τ₁ τ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn.
      apply idpath.
  Qed.

  Definition dep_psh_comprehension
    : disp_functor
        (functor_identity _)
        disp_cat_dep_psh
        (disp_codomain (PreShv C)).
  Proof.
    simple refine (_ ,, _).
    - exact dep_psh_comprehension_data.
    - exact dep_psh_comprehension_laws.
  Defined.

  (** * 6. The comprehension functor is Cartesian *)
  Section ComprehensionCartesian.
    Context {Γ₁ Γ₂ Γ₃ : C^op ⟶ HSET}
            {s₁ : Γ₁ ⟹ Γ₂}
            {s₂ : Γ₂ ⟹ Γ₃}
            (A : dep_psh Γ₃)
            (τ : Γ₁ ⟹ total_psh A)
            (p : nat_trans_comp _ _ _ τ (total_psh_pr A) = nat_trans_comp _ _ _ s₁ s₂).

    Definition dep_psh_comprehension_pb_mor_data
      : nat_trans_data Γ₁ (total_psh (dep_psh_subst s₂ A)).
    Proof.
      intros x xx.
      refine (s₁ x xx ,, _).
      refine (#d A (identity _) _ (pr2 (τ x xx))).
      abstract
        (refine (_ @ eqtohomot (nat_trans_eq_pointwise p x) xx) ;
         apply (eqtohomot (functor_id Γ₃ _))).
    Defined.

    Proposition dep_psh_comprehension_pb_mor_laws
      : is_nat_trans _ _ dep_psh_comprehension_pb_mor_data.
    Proof.
      intros x y f.
      use funextsec.
      intros xx.
      use dep_psh_total_space_path.
      - exact (eqtohomot (nat_trans_ax s₁ _ _ f) xx).
      - cbn.
        rewrite !dep_psh_mor_comp'.
        etrans.
        {
          apply maponpaths.
          exact (dep_psh_total_space_pr2_path' _ (eqtohomot (nat_trans_ax τ _ _ f) xx)).
        }
        cbn.
        rewrite !dep_psh_mor_comp'.
        apply dep_psh_mor_path_eq.
        rewrite !id_left, id_right.
        apply idpath.
    Qed.

    Definition dep_psh_comprehension_pb_mor
      : Γ₁ ⟹ total_psh (dep_psh_subst s₂ A).
    Proof.
      use make_nat_trans.
      - exact dep_psh_comprehension_pb_mor_data.
      - exact dep_psh_comprehension_pb_mor_laws.
    Defined.

    Proposition dep_psh_comprehension_pb_mor_eq
      : nat_trans_comp
          _ _ _
          dep_psh_comprehension_pb_mor
          (total_psh_nat_trans s₂ (dep_psh_subst_nat_trans s₂ A))
        =
        τ.
    Proof.
      use nat_trans_eq ; [ apply homset_property | ].
      intro x.
      use funextsec.
      intro xx.
      use dep_psh_total_space_path ; cbn.
      - exact (!(eqtohomot (nat_trans_eq_pointwise p x) xx)).
      - rewrite dep_psh_mor_comp'.
        apply dep_psh_mor_id'.
        rewrite id_left.
        apply idpath.
    Qed.

    Proposition dep_psh_comprehension_pb_mor_unique
                (τ' : Γ₁ ⟹ total_psh_data (dep_psh_subst s₂ A))
                (q : nat_trans_comp
                       _ _ _
                       τ'
                       (total_psh_nat_trans s₂ (dep_psh_subst_nat_trans s₂ A))
                     =
                     τ)
                (r : nat_trans_comp
                       _ _ _
                       τ'
                       (total_psh_pr (dep_psh_subst s₂ A))
                     =
                     s₁)
      : τ' = dep_psh_comprehension_pb_mor.
    Proof.
      use nat_trans_eq ; [ apply homset_property | ].
      intro x.
      use funextsec.
      intro xx.
      use dep_psh_total_space_path.
      - exact (eqtohomot (nat_trans_eq_pointwise r x) xx).
      - pose (dep_psh_total_space_pr2_path' _ (eqtohomot (nat_trans_eq_pointwise q x) xx))
          as r'.
        cbn ; cbn in r'.
        etrans.
        {
          apply maponpaths.
          exact r'.
        }
        rewrite dep_psh_mor_comp'.
        apply dep_psh_mor_path_eq.
        apply id_left.
    Qed.
  End ComprehensionCartesian.

  Proposition is_cartesian_dep_psh_comprehension
    : is_cartesian_disp_functor dep_psh_comprehension.
  Proof.
    use is_cartesian_disp_functor_chosen_lifts.
    {
      exact cleaving_disp_cat_dep_psh.
    }
    intros Γ₂ Γ₃ s₂ A.
    use isPullback_cartesian_in_cod_disp.
    intros Γ₁ τ s₁ p.
    use make_iscontr.
    - simple refine (_ ,, _).
      + exact (dep_psh_comprehension_pb_mor A τ p).
      + split.
        * exact (dep_psh_comprehension_pb_mor_eq A τ p).
        * abstract
            (use nat_trans_eq ; [ apply homset_property | ] ;
             intro x ;
             use funextsec ;
             intro xx ;
             cbn ;
             apply idpath).
    - abstract
        (intro τ' ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         exact (dep_psh_comprehension_pb_mor_unique A τ p (pr1 τ') (pr12 τ') (pr22 τ'))).
  Defined.

  (** * 7. The comprehension functor is fully faithful *)
  Definition dep_psh_nat_trans_from_total
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             {A : dep_psh Γ₁}
             {B : dep_psh Γ₂}
             {s : Γ₁ ⟹ Γ₂}
             (τ : total_psh A ⟹ total_psh B)
             (p : nat_trans_comp _ _ _ τ (total_psh_pr B)
                  =
                  nat_trans_comp _ _ _ (total_psh_pr A) s)
    : dep_psh_nat_trans A B s.
  Proof.
    use make_dep_psh_nat_trans.
    - refine (λ x xx a, #d B (identity _) _ (pr2 (τ x (xx ,, a)))).
      abstract
        (refine (eqtohomot (functor_id Γ₂ _) _ @ _) ; cbn ;
         exact (eqtohomot (nat_trans_eq_pointwise p x) (xx ,, a))).
    - abstract
        (intros x y xx yy f q r a ; cbn ;
         pose proof (dep_psh_total_space_pr2_path'
                       _
                       (eqtohomot (nat_trans_ax τ _ _ f) (xx ,, a))) as r' ;
         cbn in r' ;
         induction q ;
         simple refine (dep_psh_mor_path_eq _ _ _ (idpath _) _
                        @ maponpaths (#d B (identity _) _) r'
                        @ _) ;
         [ cbn ;
           refine (_ @ r) ;
           refine (eqtohomot (functor_id Γ₂ _) _ @ _) ;
           refine (maponpaths pr1 (eqtohomot (nat_trans_ax τ _ _ f) (xx ,, a)) @ _) ;
           cbn ;
           apply maponpaths ;
           exact (eqtohomot (nat_trans_eq_pointwise p x) (xx ,, a))
         | rewrite !dep_psh_mor_comp' ;
           apply dep_psh_mor_path_eq ;
           rewrite !id_left, id_right ;
           apply idpath ]).
  Defined.

  Proposition disp_functor_ff_dep_psh_comprehension
    : disp_functor_ff dep_psh_comprehension.
  Proof.
    intros Γ₁ Γ₂ A B s.
    use isweq_iso.
    - intros τ.
      exact (dep_psh_nat_trans_from_total (pr1 τ) (pr2 τ)).
    - abstract
        (intro τ ;
         use dep_psh_nat_trans_eq ;
         intros x xx a ; cbn ;
         apply dep_psh_mor_id).
    - abstract
        (intros [ τ p ] ; cbn in p ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intros x ;
         use funextsec ;
         intros xx ;
         pose (eqtohomot (nat_trans_eq_pointwise p x) xx) as q ;
         use dep_psh_total_space_path ; [ exact (!q) | ] ;
         cbn ;
         rewrite dep_psh_mor_comp' ;
         apply dep_psh_mor_id' ;
         exact (!(id_left _))).
  Defined.

  (** * 8. Useful calculational lemmas *)
  Proposition dep_psh_fiber_comp
              {Γ : C^op ⟶ HSET}
              {A₁ A₂ A₃ : dep_psh Γ}
              (τ₁ : (disp_cat_dep_psh [{ Γ }]) ⟦ A₁ , A₂ ⟧)
              (τ₂ : (disp_cat_dep_psh [{ Γ }]) ⟦ A₂ , A₃ ⟧)
              {x : C}
              {xx : (Γ x : hSet)}
              (a : A₁ x xx)
              (θ₁ := τ₁ : dep_psh_nat_trans A₁ A₂ (nat_trans_id _))
              (θ₂ := τ₂ : dep_psh_nat_trans A₂ A₃ (nat_trans_id _))
    : (τ₁ · τ₂ : dep_psh_nat_trans A₁ A₃ (nat_trans_id _)) x xx a
      =
      θ₂ x xx (θ₁ x xx a).
  Proof.
    cbn.
    refine (transportf_dep_psh_nat_trans
              (id_right (C := PreShv C) _)
              (dep_psh_comp_nat_trans τ₁ τ₂)
              x xx a
            @ _).
    apply (transportf_set (A₃ x)).
    apply setproperty.
  Qed.

  Proposition dep_psh_fiber_functor_from_cleaving
              {Γ₁ Γ₂ : C^op ⟶ HSET}
              (s : Γ₁ ⟹ Γ₂)
              {A₁ A₂ : dep_psh Γ₂}
              (τ : dep_psh_nat_trans A₁ A₂ (nat_trans_id _))
              {x : C}
              {xx : (Γ₁ x : hSet)}
              (a : A₁ x (s x xx))
              (HD := cleaving_disp_cat_dep_psh)
    : (#(fiber_functor_from_cleaving _ HD s) τ : dep_psh_nat_trans _ _ _) x xx a
      =
      τ x _ a.
  Proof.
    cbn.
    refine (transportf_dep_psh_nat_trans
              (id_right (C := PreShv C) _ @ !(id_left _))
              _
              _ _ _
            @ _).
    apply (transportf_set (A₂ x)).
    apply setproperty.
  Qed.
End DispCatDepPsh.
