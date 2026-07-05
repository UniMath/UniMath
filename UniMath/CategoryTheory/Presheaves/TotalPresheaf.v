(**

 The total presheaf of a dependent presheaf

 Every dependent presheaf `A` over some presheaf `Γ` induces a presheaf that maps
 objects `x : C` to pairs of `xx : Γ x` and `a : A x xx`. In the presheaf model,
 this operation represents context extension. In this file, we provide the necessary
 definitions to construct the comprehension functor of the presheaf model, and we
 characterise terms in the presheaf model.

 Content
 1. The total presheaf of a dependent presheaf
 2. The projection
 3. The total presheaf and natural transformations
 4. Sections of the projection
 5. Some operations on terms

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Categories.CategoryOfElementsPsh.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.

Local Open Scope cat.

Section TotalSpace.
  Context {C : category}
          {Γ : C^op ⟶ HSET}
          (A : dep_psh Γ).

  (** * 1. The total presheaf of a dependent presheaf *)
  Definition dep_psh_total_space
             (x : C)
    : hSet
    := (∑ (xx : (Γ x : hSet)), A x xx)%set.

  Proposition dep_psh_total_space_path
              {x : C}
              {xx₁ xx₂ : dep_psh_total_space x}
              (p : pr1 xx₁ = pr1 xx₂)
              (q : #d A (identity _) (eqtohomot (functor_id Γ x) _ @ p) (pr2 xx₁) = pr2 xx₂)
    : xx₁ = xx₂.
  Proof.
    induction xx₁ as [ x₁ a₁ ], xx₂ as [ x₂ a₂ ].
    cbn in *.
    induction p.
    apply maponpaths.
    refine (!_ @ q).
    apply dep_psh_mor_id.
  Qed.

  Proposition dep_psh_total_space_pr1_path
              {x : C}
              {xx₁ xx₂ : dep_psh_total_space x}
              (p : xx₁ = xx₂)
    : pr1 xx₁ = pr1 xx₂.
  Proof.
    induction p.
    apply idpath.
  Defined.

  Proposition dep_psh_total_space_pr2_path
              {x : C}
              {xx₁ xx₂ : dep_psh_total_space x}
              (p : xx₁ = xx₂)
    : #d A (identity _)
           (eqtohomot (functor_id Γ x) _ @ dep_psh_total_space_pr1_path p)
           (pr2 xx₁)
      =
      pr2 xx₂.
  Proof.
    induction p.
    cbn.
    apply dep_psh_mor_id'.
    apply idpath.
  Qed.

  Proposition dep_psh_total_space_pr2_path'
              {x : C}
              {xx₁ xx₂ : dep_psh_total_space x}
              (p : xx₁ = xx₂)
    : pr2 xx₁
      =
      #d A (identity _)
           (eqtohomot (functor_id Γ x) _ @ !(dep_psh_total_space_pr1_path p))
           (pr2 xx₂).
  Proof.
    induction p.
    cbn.
    refine (!_).
    apply dep_psh_mor_id'.
    apply idpath.
  Qed.

  Definition total_psh_data
    : functor_data C^op HSET.
  Proof.
    use make_functor_data.
    - exact dep_psh_total_space.
    - exact (λ x y s xx, #Γ s (pr1 xx) ,, #d A s (idpath _) (pr2 xx)).
  Defined.

  Proposition total_psh_laws
    : is_functor total_psh_data.
  Proof.
    split.
    - intro x.
      use funextsec.
      intro xx.
      use dep_psh_total_space_path.
      + exact (eqtohomot (functor_id Γ _) _).
      + cbn.
        refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
        apply dep_psh_mor_id'.
        exact (!(id_left _)).
    - intros x y z f g.
      use funextsec.
      intro xx.
      use dep_psh_total_space_path.
      + exact (eqtohomot (functor_comp Γ _ _) _).
      + cbn.
        refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
        refine (_ @ !(dep_psh_mor_comp' _ _ _ _ _ _)).
        apply dep_psh_mor_path_eq.
        exact (id_left _).
  Qed.

  Definition total_psh
    : C^op ⟶ HSET.
  Proof.
    use make_functor.
    - exact total_psh_data.
    - exact total_psh_laws.
  Defined.

  (** * 2. The projection *)
  Definition total_psh_pr
    : total_psh ⟹ Γ.
  Proof.
    use make_nat_trans.
    - exact (λ x xx, pr1 xx).
    - abstract
        (intros x y f ;
         use funextsec ;
         intro xx ; cbn ;
         apply idpath).
  Defined.
End TotalSpace.

(** * 3. The total presheaf and natural transformations *)
Definition total_psh_nat_trans
           {C : category}
           {Γ₁ Γ₂ : C^op ⟶ HSET}
           {A : dep_psh Γ₁}
           {B : dep_psh Γ₂}
           (s : Γ₁ ⟹ Γ₂)
           (τ : dep_psh_nat_trans A B s)
  : total_psh A ⟹ total_psh B.
Proof.
  use make_nat_trans.
  - exact (λ x xx, s x (pr1 xx) ,, τ _ _ (pr2 xx)).
  - abstract
      (intros x y f ;
       use funextsec ;
       intros xx ; cbn ;
       use dep_psh_total_space_path ;
       [ exact (eqtohomot (nat_trans_ax s _ _ f) (pr1 xx)) | ] ;
       cbn ;
       etrans ;
       [ apply maponpaths ;
         exact (dep_psh_nat_trans_ax' τ f _ (pr2 xx))
       | ] ;
       rewrite dep_psh_mor_comp' ;
       apply dep_psh_mor_path_eq ;
       apply id_left).
Defined.

(** * 4. Sections of the projection *)
Definition psh_term_data
           {C : category}
           {Γ : C^op ⟶ HSET}
           (A : dep_psh Γ)
  : UU
  := ∏ (x : C) (xx : (Γ x : hSet)), A x xx.

Definition psh_term_law
           {C : category}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           (t : psh_term_data A)
  : UU
  := ∏ (x y : C)
       (f : y --> x)
       (xx : (Γ x : hSet)),
     t y (#Γ f xx)
     =
     #d A f (idpath _) (t x xx).

Proposition isaprop_psh_term_law
            {C : category}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            (t : psh_term_data A)
  : isaprop (psh_term_law t).
Proof.
  repeat (use impred ; intro).
  apply setproperty.
Qed.

Definition psh_term
           {C : category}
           {Γ : C^op ⟶ HSET}
           (A : dep_psh Γ)
  : UU
  := ∑ (t : psh_term_data A), psh_term_law t.

Definition make_psh_term
           {C : category}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           (t : psh_term_data A)
           (p : psh_term_law t)
  : psh_term A
  := t ,, p.

Definition psh_term_to_data
           {C : category}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           (t : psh_term A)
           (x : C)
           (xx : (Γ x : hSet))
  : A x xx
  := pr1 t x xx.

Coercion psh_term_to_data : psh_term >-> Funclass.

Proposition psh_term_naturality
            {C : category}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            (t : psh_term A)
            {x y : C}
            (f : y --> x)
            (xx : (Γ x : hSet))
  : t y (#Γ f xx)
    =
    #d A f (idpath _) (t x xx).
Proof.
  exact (pr2 t x y f xx).
Defined.

Proposition psh_term_on_eq
            {C : category}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            (t : psh_term A)
            {x : C}
            {xx₁ xx₂ : (Γ x : hSet)}
            (p : xx₁ = xx₂)
  : #d A (identity _) (eqtohomot (functor_id Γ _) _ @ p) (t x xx₁)
    =
    t x xx₂.
Proof.
  induction p ; cbn.
  apply dep_psh_mor_id'.
  apply idpath.
Qed.

Proposition isaset_psh_term
            {C : category}
            {Γ : C^op ⟶ HSET}
            (A : dep_psh Γ)
  : isaset (psh_term A).
Proof.
  use isaset_total2.
  - repeat (use impred_isaset ; intro).
    apply setproperty.
  - intro t.
    use isasetaprop.
    apply isaprop_psh_term_law.
Qed.

Proposition psh_term_eq
            {C : category}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            {t₁ t₂ : psh_term A}
            (p : ∏ (x : C) (xx : (Γ x : hSet)), t₁ x xx = t₂ x xx)
  : t₁ = t₂.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_psh_term_law.
  }
  use funextsec ; intro x.
  use funextsec ; intro xx.
  exact (p x xx).
Qed.

Definition make_psh_section
           {C : category}
           {Γ : C^op ⟶ HSET}
           (A : dep_psh Γ)
           (t : psh_term A)
  : section_of_mor (C := PreShv C) (total_psh_pr A).
Proof.
  use make_section_of_mor.
  - use make_nat_trans.
    + simple refine (λ x xx, _ ,, _).
      * exact xx.
      * exact (t x xx).
    + abstract
        (intros x y f ;
         use funextsec ;
         intro xx ;
         cbn ;
         apply maponpaths ;
         exact (psh_term_naturality t f xx)).
  - abstract
      (use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ;
       use funextsec ;
       intro xx ;
       cbn ;
       apply idpath).
Defined.

Definition psh_section_pt
           {C : category}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           (t : section_of_mor (C := PreShv C) (total_psh_pr A))
           {x : C}
           (xx : (Γ x : hSet))
  : A x xx.
Proof.
  refine (#d A (identity _) _ (pr2 ((section_of_mor_to_mor t : _ ⟹ _) x xx))).
  abstract
    (refine (_ @ eqtohomot (nat_trans_eq_pointwise (section_of_mor_eq t) x) xx) ;
     cbn ;
     exact (eqtohomot (functor_id Γ _) _)).
Defined.

Proposition psh_section_natural
            {C : category}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            (t : section_of_mor (C := PreShv C) (total_psh_pr A))
            (x y : C)
            (f : y --> x)
            (xx : (Γ x : hSet))
  : psh_section_pt t (#Γ f xx)
    =
    #d A f (idpath _) (psh_section_pt t xx).
Proof.
  unfold psh_section_pt.
  pose (eqtohomot (nat_trans_ax (section_of_mor_to_mor t) _ _ f) xx) as p.
  cbn in p.
  etrans.
  {
    apply maponpaths.
    exact (dep_psh_total_space_pr2_path' _ p).
  }
  cbn.
  rewrite !dep_psh_mor_comp'.
  use dep_psh_mor_path_eq.
  rewrite !id_left, id_right.
  apply idpath.
Qed.

Definition psh_section_weq
           {C : category}
           {Γ : C^op ⟶ HSET}
           (A : dep_psh Γ)
  : section_of_mor (C := PreShv C) (total_psh_pr A)
    ≃
    psh_term A.
Proof.
  use weq_iso.
  - intro t.
    use make_psh_term.
    + exact (λ x xx, psh_section_pt t xx).
    + exact (psh_section_natural t).
  - exact (make_psh_section A).
  - abstract
      (intros t ;
       use eq_section_of_mor ;
       use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ; cbn ;
       use funextsec ;
       intro xx ;
       use dep_psh_total_space_path ;
       [ exact (!(eqtohomot (nat_trans_eq_pointwise (section_of_mor_eq t) x) xx))
       | ] ;
       cbn ;
       unfold psh_section_pt ;
       rewrite dep_psh_mor_comp' ;
       apply dep_psh_mor_id' ;
       rewrite id_left ;
       apply idpath).
  - abstract
      (intros t ;
       use psh_term_eq ;
       intros x xx ;
       unfold psh_section_pt ; cbn ;
       apply dep_psh_mor_id).
Defined.

(** * 5. Some operations on terms *)
Proposition psh_term_pt_eq
            {C : category}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            (t : psh_term A)
            {x : C}
            {xx₁ xx₂ : (Γ x : hSet)}
            (p : xx₁ = xx₂)
  : t x xx₁
    =
    #d A (identity _) (eqtohomot (functor_id Γ _) _ @ !p) (t x xx₂).
Proof.
  induction p.
  refine (!_).
  apply dep_psh_mor_id.
Qed.

Definition psh_term_subst
           {C : category}
           {Γ₁ Γ₂ : C^op ⟶ HSET}
           (s : Γ₁ ⟹ Γ₂)
           {A : dep_psh Γ₂}
           (t : psh_term A)
  : psh_term (dep_psh_subst s A).
Proof.
  use make_psh_term.
  - exact (λ x xx, t x (s x xx)).
  - abstract
      (intros x y f xx ; cbn ;
       refine (psh_term_pt_eq t (eqtohomot (nat_trans_ax s _ _ f) xx) @ _) ;
       refine (maponpaths (#d A _ _) (psh_term_naturality t f (s x xx)) @ _) ;
       cbn ;
       rewrite dep_psh_mor_comp' ;
       use dep_psh_mor_path_eq ;
       apply id_left).
Defined.

Definition psh_term_coerce
           {C : category}
           {Γ : C^op ⟶ HSET}
           {A B : dep_psh Γ}
           (τ : dep_psh_nat_trans A B (nat_trans_id _))
           (t : psh_term A)
  : psh_term B.
Proof.
  use make_psh_term.
  - exact (λ x xx, τ x xx (t x xx)).
  - abstract
      (intros x y f xx ;
       refine (_ @ dep_psh_nat_trans_ax τ f (idpath _) (idpath _) (t x xx)) ;
       apply maponpaths ;
       apply (psh_term_naturality t)).
Defined.

Definition psh_term_var
           {C : category}
           (Γ : C^op ⟶ HSET)
           (A : dep_psh Γ)
  : psh_term (dep_psh_subst (total_psh_pr A) A).
Proof.
  use make_psh_term.
  - exact (λ x xx, pr2 xx).
  - abstract
      (intros x y f xx ; cbn ;
       apply dep_psh_mor_path_eq ;
       apply idpath).
Defined.
