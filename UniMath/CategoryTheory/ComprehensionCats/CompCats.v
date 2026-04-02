
(* Comprehension Categories


  This file builds on Displayedcats.Comprehensionc and follows a similar line as
  Bicategories.ComprehensionCat.CompCatNotations by considering the internal language
  of comprehension categories. The comprehension categories in Bicategories.ComprehensionCat.CompCatNotations are
  assumed to be full but we do not assume fullness here. We also do not assume splitness.
  Following the rules given in "From Semantics to Syntax: A Type Theory for Comprehension Categories" by Najmaei,
  Van der Weide, Ahrens, and North, we take morphisms between types in a fiber to be witnesses for coercions between types.

  References
  - "From Semantics to Syntax: A Type Theory for Comprehension Categories" by Najmaei,
   Van der Weide, Ahrens, and North


  Contents
  1. Notations and Accesories for Comprehension Categories
  2. Comprehension Structure and Substitution of Terms
  3. Morphisms in Fibers as Coercions
  4. Comprehension of Cartesian Lifts
  5. Isomorphisms in Fibers
  6. Lemmas for Coercing Terms
  7. Comprehension Structure ctd.
  8. Variable Rule
  9. Extension of Substitution with Term
 *)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.FibrationToIndexedCategory.



Local Open Scope cat.
Local Open Scope mor_disp_scope.

Declare Scope comp_cat.
Local Open Scope comp_cat.

(** * Notations and Accesories for Comprehension Categories  *)


Definition comp_cat
  : UU
  := total2 comprehension_cat_structure.

Coercion comp_cat_to_ctx (C : comp_cat)
  : category
  := pr1 C.

Definition comp_cat_morphisms (C: comp_cat)
  : C -> C -> UU
                    := pr2(pr1 (pr1 (pr1 (pr1 C)))).

Definition disp_cat_of_types
           (C : comp_cat)
  : disp_cat C
  := pr1 (pr2 C).

Definition comp_cat_ty {C : comp_cat}
                       (Γ : pr1 C)
  : UU
  := pr1 (pr2 C) Γ.

Definition comp_cat_coercion
           {C : comp_cat}
           {Γ : C}
           (A B : comp_cat_ty Γ)
  : UU
  := fiber_category _ _ ⟦ A , B ⟧.

Notation "A <: B" := (comp_cat_coercion A B) (at level 55).

Definition comp_cat_ext
           {C : comp_cat}
           (Γ : C)
           (A : comp_cat_ty Γ)
  : C
  := pr1 ((pr11 (comprehension (pr2 C))) Γ A).

Notation "Γ '&' A" := (comp_cat_ext Γ A) (at level 20) : comp_cat.

Definition comp_cat_proj
           {C : comp_cat}
           (Γ : C)
           (A : comp_cat_ty Γ)
  : Γ & A --> Γ
  := pr2 ((pr11 (comprehension (pr2 C))) Γ A).

Notation "'π'" := (comp_cat_proj _) : comp_cat.

Definition comp_cat_tm {C : comp_cat}
                       {Γ : C} (A : comp_cat_ty Γ)
  : UU
  := ∑ (t : Γ --> Γ & A), t · π A = identity Γ.

Coercion comp_cat_tm_to_section {C : comp_cat}
                       {Γ : C} {A : comp_cat_ty Γ}
                       (t : comp_cat_tm A)
  : Γ --> Γ & A
  := pr1 t.

Definition make_comp_cat_tm {C : comp_cat} {Γ : C}
           {A : comp_cat_ty Γ} (t : Γ --> Γ & A) (p : t · π A = identity Γ)
  : comp_cat_tm A
  := t ,, p.

Lemma comp_cat_tm_eq {C : comp_cat} {Γ : C} {A : comp_cat_ty Γ}
  (t1 t2 : comp_cat_tm A) (p : (pr1 t1 : _ ) = pr1 t2)
  : t1 = t2.
Proof.
  use subtypePath.
  intro. apply homset_property.
  exact p.
Qed.

Definition comp_cat_tm_isaset {C : comp_cat} {Γ : C} {A : comp_cat_ty Γ}
  : isaset (comp_cat_tm A).
Proof.
  apply isaset_total2.
  - apply homset_property.
  - intro t. apply isasetaprop. apply homset_property.
Qed.

Definition cleaving_of_types (C : comp_cat)
  : cleaving (disp_cat_of_types C)
  := pr1 (pr22 C).

Definition comp_cat_subst_ty {C : comp_cat} {Γ Δ : C}
           (s : Γ --> Δ) (A : comp_cat_ty Δ)
  : comp_cat_ty Γ
  := cleaving_ob (cleaving_of_types C) s A.

Notation "A '[[' s ']]'" := (comp_cat_subst_ty s A) (at level 20) : comp_cat.

(** * Comprehension Structure and Substitution of Terms*)

Definition comprehension_functor_mor
  {C : category}
  (CC : comprehension_cat_structure C)
  {Γ₁ Γ₂ : C}
  {A : pr1 CC Γ₁}
  {B : pr1 CC Γ₂}
  (s : Γ₂ --> Γ₁)
  (ff : B -->[ s ] A)
  : pr1 (comprehension CC _ B) --> pr1 (comprehension CC _ A)
  := pr1 (♯ (comprehension CC) ff).

Definition comp_cat_comprehension (C : comp_cat)
  : comprehension_cat_structure C
  := pr2 C.

Definition comprehension_functor_mor_comp
  {C : category}
  (CC : comprehension_cat_structure C)
  {Γ₁ Γ₂ Γ₃ : C}
  {A : pr1 CC Γ₁}
  {B : pr1 CC Γ₂}
  {D : pr1 CC Γ₃}
  (s : Γ₂ --> Γ₁)
  (t : Γ₃ --> Γ₂)
  (ff : B -->[ s ] A)
  (gg : D -->[ t ] B)
  : comprehension_functor_mor CC (t · s) (gg ;; ff)%mor_disp
    =
    comprehension_functor_mor CC t gg · comprehension_functor_mor CC s ff.
Proof.
  refine (maponpaths pr1 (disp_functor_comp (comprehension CC) gg ff) @ _).
  cbn.
  apply idpath.
Qed.

Proposition comprehension_functor_mor_id
  {C : category}
  (CC : comprehension_cat_structure C)
  {Γ : C}
  {A : pr1 CC Γ}
  : comprehension_functor_mor CC (identity Γ) (id_disp A) = identity _.
Proof.
  refine (maponpaths pr1 (disp_functor_id (comprehension CC) A) @ _).
  cbn.
  apply idpath.
Qed.

Definition comprehension_functor_mor_comm
  {C : category}
  (CC : comprehension_cat_structure C)
  {Γ₁ Γ₂ : C}
  {A : pr1 CC Γ₁}
  {B : pr1 CC Γ₂}
  (s : Γ₂ --> Γ₁)
  (ff : B -->[ s ] A)
  : comprehension_functor_mor CC s ff · pr2 (comprehension CC _ A)
    = pr2 (comprehension CC _ B) · s
  := pr2 (♯ (comprehension CC) ff).

Lemma comprehension_functor_mor_transportf
  {C : category}
  (CC : comprehension_cat_structure C)
  {Γ₁ Γ₂ : C}
  {A : pr1 CC Γ₂}
  {B : pr1 CC Γ₁}
  {s s' : Γ₁ --> Γ₂}
  (p : s = s')
  (ff : B -->[ s ] A)
  : comprehension_functor_mor CC s' (transportf (mor_disp B A) p ff)
    =
    comprehension_functor_mor CC s ff.
Proof.
  unfold comprehension_functor_mor.
  etrans.
  {
    apply maponpaths.
    exact (disp_functor_transportf (functor_identity C) (comprehension CC) _ _ _ _ p _ _ ff).
  }
  cbn.
  rewrite transportf_cod_disp.
  apply idpath.
Qed.

Definition comp_cat_cartesian_comprehension
  (C : comp_cat)
  : ∑ F : disp_functor (functor_identity C)
          (disp_cat_of_types C)
          (disp_codomain C),
      is_cartesian_disp_functor F
  := pr22 (comp_cat_comprehension C).

Definition comp_cat_is_pullback
  {C : comp_cat}
  {Γ₁ Γ₂ : C}
  (A : comp_cat_ty Γ₁)
  (s : Γ₂ --> Γ₁)
  : isPullback
      (comprehension_functor_mor_comm
         (comp_cat_comprehension C)
         s
         (mor_disp_of_cartesian_lift _ _ (cleaving_of_types C _ _ s A))).
Proof.
  set (CC := comp_cat_comprehension C).
  set (χ  := comprehension CC).
  set (mapstocartesian := pr222 CC).
  set (lift := cleaving_of_types C _ _ s A).
  set (iscartesian := cartesian_lift_is_cartesian _ _ lift).
  exact (cartesian_isPullback_in_cod_disp _ (mapstocartesian _ _ _ _ _ lift iscartesian)).
Qed.

Definition comp_cat_pullback {C : comp_cat} {Γ₁ Γ₂ : C}
           (A : comp_cat_ty Γ₁) (s : Γ₂ --> Γ₁)
  : Pullback (π A) s
  := make_Pullback _ (comp_cat_is_pullback A s).

(* the universal term given by the universal property of pullback in C *)
Definition comp_cat_univ_pullback {C : comp_cat} {Γ Δ Ω : C} {A : comp_cat_ty Δ}
  (s : Γ --> Δ) (s' : Γ --> Ω)(s'' : Ω --> Δ & A)
  (p : s' · s'' · (π A) = s)
  : comp_cat_tm (A [[ s ]]).
Proof.
  use make_comp_cat_tm.
  - use (PullbackArrow (comp_cat_pullback A s)).
    + exact (s' · s'').
    + exact (identity Γ).
    + (* (s'·s'')·πA = id·s *)
      rewrite id_left.
      exact p.
  - (* t [[s]] · π(A[[s]]) = id *)
    abstract(apply (PullbackArrow_PullbackPr2 (comp_cat_pullback A s))).
Defined.

(* A term t substituted by s is given by the universal property of the pullback square given by s in C,
 where the outer square projections are identity and s · t
 So this is a special case of the previous function *)
Definition comp_cat_subst_tm {C : comp_cat} {Γ Δ : C} {A : comp_cat_ty Δ}
                     (s : Γ --> Δ) (t : comp_cat_tm A)
  : comp_cat_tm (A [[ s ]]).
Proof.
  apply (@comp_cat_univ_pullback _ _ _ Δ _ _ s t).
  set (th  := pr2 t : (t · (π A) = identity Δ)).
  rewrite assoc'.
  rewrite th.
  apply id_right.
Defined.

Notation "t '[[' s ']]tm'" := (comp_cat_subst_tm s t) (at level 20) : comp_cat.

Definition comp_cat_comp_mor {C : comp_cat} {Γ : C} {A B : comp_cat_ty Γ} (f : A <: B)
  : Γ & A --> Γ & B
  := comprehension_functor_mor
    (comp_cat_comprehension C)
    (identity Γ)
    f.

Definition comp_cat_comp_mor_law {C : comp_cat} {Γ : C} {A B : comp_cat_ty Γ} (f : A <: B)
  : (comp_cat_comp_mor f) · (π B) = π A.
Proof.
  etrans.
  {
    exact (comprehension_functor_mor_comm (comp_cat_comprehension C) (identity Γ) f).
  }
  rewrite id_right.
  apply idpath.
Qed.

Lemma comp_cat_comp_mor_id {C : comp_cat} {Γ : C} {A : comp_cat_ty Γ}
  : comp_cat_comp_mor (@identity (fiber_category (disp_cat_of_types C) Γ) A) = identity (Γ & A).
Proof.
  exact (maponpaths pr1 (disp_functor_id (comprehension (comp_cat_comprehension C)) A)).
Qed.

Lemma comp_cat_comp_mor_comp {C : comp_cat} {Γ : C} {A B D : comp_cat_ty Γ}
  (f : A <: B) (g : B <: D)
  : comp_cat_comp_mor (transportf (mor_disp A D) (id_right (identity Γ)) (f ;; g))
    = comp_cat_comp_mor f · comp_cat_comp_mor g.
Proof.
  set (χ := comprehension (comp_cat_comprehension C)).
  etrans.
  {
   exact (maponpaths pr1 (disp_functor_transportf (functor_identity C) χ _ _ (identity Γ · identity Γ)
                             (identity Γ) (id_right (identity Γ)) A D (f ;; g))).
  }
  induction (id_right (identity Γ)).
  etrans.
  {
    exact (maponpaths pr1 (disp_functor_comp χ f g)).
  }
  apply idpath.
Qed.


Definition comp_cat_comp_mor_comp'
  { C : comp_cat}
  {Γ : C}
  {A B D : comp_cat_ty Γ} (f : A <: B) (g : B <: D) :
  comp_cat_comp_mor (f · g) = comp_cat_comp_mor f · comp_cat_comp_mor g.
Proof.
  exact (comp_cat_comp_mor_comp f g).
Qed.

(** * Morphisms in Fibers as Coercions*)

Definition coerce_comp_cat_tm {C : comp_cat} {Γ : C} {A B : comp_cat_ty Γ}
           (f : A <: B) (t : comp_cat_tm A) : comp_cat_tm B.
Proof.
  use make_comp_cat_tm.
  - exact (t · comp_cat_comp_mor f).
  - abstract (
    rewrite assoc';
    set (h := comprehension_functor_mor_comm (comp_cat_comprehension C) (identity Γ) f);
    eapply pathscomp0;[apply cancel_precomposition, h|];
    rewrite assoc;
    eapply pathscomp0;[apply cancel_postcomposition, (pr2 t)|];
    apply id_right).
Defined.

Notation "t ↑ f" := (coerce_comp_cat_tm f t) (at level 29, left associativity).

Definition comp_cat_reindex_coercion {C : comp_cat} {Γ Δ : C} (s : Δ --> Γ) {A B : comp_cat_ty Γ} (f : A <: B)
  : A [[ s ]] <: B [[ s ]].
Proof.
  set (cl := cleaving_of_types C).
  set (liftA := cl _ _ s A).
  set (liftB := cl _ _ s B).
  set (ffA := mor_disp_of_cartesian_lift _ _ liftA).
  set (ffB := mor_disp_of_cartesian_lift _ _ liftB).
  set (HffB := cartesian_lift_is_cartesian _ _ liftB).
  set (hh := transportf (mor_disp (A [[ s ]]) B) (id_right s) (ffA ;; f)).
  set (hh_id  := transportf (mor_disp (A [[ s ]]) B) (pathsinv0 (id_left s)) hh).
  exact (cartesian_factorisation HffB (identity Δ) hh_id).
Defined.

Definition comp_cat_reindex_iso
  {C : comp_cat}
  {Γ Δ : C} (s : Δ --> Γ)
  {A B : comp_cat_ty Γ}
  (i : @z_iso (fiber_category (disp_cat_of_types C) Γ) A B)
  : @z_iso (fiber_category (disp_cat_of_types C) Δ) (A [[ s ]]) (B [[ s ]])
  := (functor_on_z_iso
            (fiber_functor_from_cleaving _ _ s) i).

(** *  Comprehension of Cartesian Lifts *)

(* gives s.A *)
Definition comp_cat_ext_subst {C : comp_cat} :
  ∏ {Γ Δ : C} (s : Δ --> Γ) (A : comp_cat_ty Γ), (Δ & (A [[ s ]])) --> (Γ & A).
Proof.
   intros Γ Δ s A.
   exact (comprehension_functor_mor (comp_cat_comprehension C) s
             (mor_disp_of_cartesian_lift _ _ (cleaving_of_types C _ _ s A))).
Defined.

Lemma comp_cat_ext_subst_commute {C : comp_cat}
  : ∏ {Γ Δ : C} (s : Δ --> Γ) (A : comp_cat_ty Γ),
    comp_cat_ext_subst s A · (π _) = (π _) · s.
Proof.
  intros Γ Δ s A.
  exact (comprehension_functor_mor_comm (comp_cat_comprehension C) s
           (mor_disp_of_cartesian_lift _ _ (cleaving_of_types C _ _ s A))).
Qed.

Lemma comp_cat_ext_subst_term_commute {C : comp_cat} {Γ Δ : C}
  (s : Γ --> Δ) (A : comp_cat_ty Δ) (t : comp_cat_tm A)
  : (t [[ s ]]tm) · comp_cat_ext_subst s A = s · t.
Proof.
  exact (PullbackArrow_PullbackPr1 (comp_cat_pullback A s) Γ (s · t) (identity Γ) _).
Qed.

(** * Isomorphisms in Fibers *)

(* if s = s', then A[s] ≅ A[s'] *)
Definition comp_cat_subst_ty_eq {C : comp_cat} {Γ Δ : C} (A : comp_cat_ty Δ)
  {s s' : Γ --> Δ} (p : s = s')
  : A [[ s ]] = A [[ s' ]]
  := (maponpaths (λ t, A [[ t ]]) p).

Definition comp_cat_subst_ty_iso {C : comp_cat} {Γ Δ : C} (A : comp_cat_ty Δ)
  {s s' : Γ --> Δ} (p : s = s')
  : @z_iso (fiber_category _ _) (A [[ s ]]) (A [[ s' ]]).
Proof.
  refine (idtoiso _).
  exact (comp_cat_subst_ty_eq A p).
Defined.

Lemma comp_cat_subst_ty_eq_idpath
    {C : comp_cat}
    {Γ Δ : C}
    (A : comp_cat_ty Δ)
    (s : Γ --> Δ)
  : comp_cat_subst_ty_eq A (idpath s) = idpath (A [[ s ]]).
Proof.
  apply idpath.
Qed.

Definition comp_cat_subst_ty_iso_comp {C : comp_cat} {Γ Δ : C} (A : comp_cat_ty Δ)
  {s s' s'': Γ --> Δ} {p : s = s'} {p' : s' = s''}
  : comp_cat_subst_ty_iso A p · comp_cat_subst_ty_iso _ p' = comp_cat_subst_ty_iso _ (p @ p').
Proof.
  unfold comp_cat_subst_ty_iso.
  unfold comp_cat_subst_ty_eq.
  refine (!_).
  etrans.
  2 : {
    apply pr1_idtoiso_concat.
  }
  do 2 apply maponpaths.
  induction p, p'.
  apply idpath.
Qed.

Definition comp_cat_subst_ty_id_iso {C : comp_cat}
  : ∏ {Γ : C} (A : comp_cat_ty Γ),
    @z_iso (fiber_category _ _) A (A [[ (identity _) ]]).
Proof.
  intros.
  exact (nat_z_iso_pointwise_z_iso
           (nat_z_iso_fiber_functor_from_cleaving_identity (cleaving_of_types C) Γ)
           A).
Defined.

Definition comp_cat_subst_ty_comp_iso {C : comp_cat} : ∏ {Δ Γ Θ : C}
      (A : comp_cat_ty Δ) (s1 : Γ --> Δ) (s2 : Θ --> Γ),
    @z_iso (fiber_category _ _) ((A [[ s1 ]]) [[ s2 ]]) (A [[ s2 · s1 ]]).
Proof.
    intros Γ Δ Θ A s1 s2.
    exact (nat_z_iso_pointwise_z_iso
           (fiber_functor_from_cleaving_comp_nat_z_iso (cleaving_of_types C) s1 s2)
           A).
Defined.

Definition comp_cat_subst_ty_eq_comp_iso
           {C : comp_cat}
           {Δ Γ1 Γ2 Θ : C}
           (A : comp_cat_ty Δ)
           {s1 : Γ1 --> Δ} {s2 : Θ --> Γ1}
           {s3 : Γ2 --> Δ} {s4 : Θ --> Γ2}
           (p : (s2 · s1) = (s4 · s3))
  : @z_iso (fiber_category _ _) ((A [[ s1 ]]) [[ s2 ]]) ((A [[ s3 ]]) [[ s4 ]]).
Proof.
  refine (z_iso_comp (comp_cat_subst_ty_comp_iso A s1 s2) _).
  refine (z_iso_comp (comp_cat_subst_ty_iso A p) _).
  exact (z_iso_inv (comp_cat_subst_ty_comp_iso A s3 s4)).
Defined.

Lemma comp_cat_comp_iso_natural
    {C : comp_cat} {Γ₁ Γ₂ Γ₃ : C}
    (A : comp_cat_ty Γ₁) (s₁ : Γ₂ --> Γ₁)
    {s₂ s₂' : Γ₃ --> Γ₂} (p : s₂ = s₂')
  : comp_cat_subst_ty_iso (A [[s₁]]) p
    · comp_cat_subst_ty_comp_iso A s₁ s₂'
    = comp_cat_subst_ty_comp_iso A s₁ s₂
    · comp_cat_subst_ty_iso A (maponpaths (fun z => z · s₁) p).
Proof.
  induction p.
  rewrite id_left.
  rewrite id_right.
  apply idpath.
Qed.

(* Each isomorphism in the fiber gives two coercion witnesses. *)
Definition coe_from_z_iso
           {C : comp_cat}
           {Γ : C}
           {A B : comp_cat_ty Γ}
           (i : z_iso (C := fiber_category _ _) A B)
  : A <: B
  := (morphism_from_z_iso _ _ i : _ --> _).

Definition coe_inv_from_z_iso
           {C : comp_cat}
           {Γ : C}
           {A B : comp_cat_ty Γ}
           (i : z_iso (C := fiber_category _ _) A B)
  : B <: A
  := (inv_from_z_iso i : _ --> _).

Notation "⌈ i ⌉" := (coe_from_z_iso i) (at level 10).
Notation "⌈ i ⌉⁻¹" := (coe_inv_from_z_iso i) (at level 10).

Lemma comp_cat_comp_mor_z_iso_after_z_iso_inv
  {C : comp_cat} {Γ : C} {A B : comp_cat_ty Γ}
  (i : z_iso (C := fiber_category _ _) A B)
  : comp_cat_comp_mor (⌈ i ⌉⁻¹) · comp_cat_comp_mor (⌈ i ⌉)
    = identity (Γ & B).
Proof.
  rewrite <- (comp_cat_comp_mor_comp (⌈ i ⌉⁻¹) (⌈ i ⌉)).
  eapply pathscomp0.
  - apply maponpaths. exact (z_iso_after_z_iso_inv i).
  - apply comp_cat_comp_mor_id.
Qed.

Lemma comp_cat_comp_mor_z_iso_inv_after_z_iso
  {C : comp_cat} {Γ : C} {A B : comp_cat_ty Γ}
  (i : z_iso (C := fiber_category _ _) A B)
  : comp_cat_comp_mor (⌈ i ⌉) · comp_cat_comp_mor (⌈ i ⌉⁻¹)
    = identity (Γ & A).
Proof.
  rewrite <- (comp_cat_comp_mor_comp (⌈ i ⌉) (⌈ i ⌉⁻¹)).
  unfold coe_from_z_iso.
  unfold coe_inv_from_z_iso.
  eapply pathscomp0.
  - apply maponpaths. exact (z_iso_inv_after_z_iso i).
  - apply comp_cat_comp_mor_id.
Qed.

Definition comp_cat_comp_iso {C : comp_cat} {Γ : C} {A B : comp_cat_ty Γ}
  (i : @z_iso (fiber_category _ _) A B)
  : z_iso (Γ & A) (Γ & B).
Proof.
  use make_z_iso.
  - exact (comp_cat_comp_mor ( ⌈ i ⌉ )).
  - exact (comp_cat_comp_mor ( ⌈ i ⌉⁻¹ )).
  - abstract (split ;
      [apply comp_cat_comp_mor_z_iso_inv_after_z_iso |
        apply comp_cat_comp_mor_z_iso_after_z_iso_inv]).
Defined.

Lemma comp_cat_reindex_coercion_iso_eq {C : comp_cat} {Γ Δ : C} (s : Δ --> Γ)
  {A B : comp_cat_ty Γ}
  (i : @z_iso (fiber_category (disp_cat_of_types C) Γ) A B)
  : comp_cat_reindex_coercion s ( ⌈ i ⌉ ) = ⌈ comp_cat_reindex_iso s i⌉ .
Proof.
   set (cl := cleaving_of_types C).
   set (liftB := cl _ _ s B).
   set (HffB := cartesian_lift_is_cartesian _ _ liftB).
   apply (cartesian_factorisation_unique HffB).
   unfold cartesian_factorisation_commutes.
   etrans.
   { apply (cartesian_factorisation_commutes HffB). }
   unfold fiber_functor_from_cleaving.
   cbn.
   rewrite transport_f_f.
   refine (_ @ cartesian_factorisation_commutes HffB _ _ ).
    etrans.
    2: {
    apply maponpaths_2.
    etrans.
    2: { apply maponpaths.
         apply (cartesian_factorisation_commutes (cartesian_lift_is_cartesian _ _ liftB)).
    }
    refine (!_).
    do 2 rewrite (cartesian_factorisation_commutes liftB).
    apply idpath.
    }
    rewrite cartesian_factorisation_commutes.
    apply idpath.
Qed.

(* Lemmas about how coercing interacts with the isos and the reindexing *)

Lemma comp_cat_reindex_coercion_id {C : comp_cat} {Γ Δ : C}
    (s : Δ --> Γ) (A : comp_cat_ty Γ)
  : comp_cat_reindex_coercion s (identity (C := fiber_category _ _) A)
    = identity _.
Proof.
  unfold comp_cat_reindex_coercion.
  cbn.
  unfold transportb.
  rewrite transport_f_f.
  use (cartesian_factorisation_unique (cleaving_of_types C _ _ s A)).
  rewrite cartesian_factorisation_commutes.
  rewrite id_right_disp.
  rewrite id_left_disp.
  unfold transportb.
  rewrite transport_f_f.
  apply transportf_paths.
  apply homset_property.
Qed.

Definition comp_cat_reindex_coercion_comp
  {C : comp_cat}
  {Γ Δ Θ : C} (s₁ : Δ --> Γ)(s₂ : Θ --> Δ)
  {A B: comp_cat_ty Γ}
  (f : A <: B )
  : comp_cat_reindex_coercion s₂ (comp_cat_reindex_coercion s₁ f)
    = ⌈comp_cat_subst_ty_comp_iso _ _ _⌉ ·
        comp_cat_reindex_coercion (s₂ · s₁) f
        ·⌈comp_cat_subst_ty_comp_iso _ _ _⌉⁻¹ .
Proof.
  unfold comp_cat_reindex_coercion.
  cbn.
  unfold transportb.
  repeat rewrite transport_f_f.
  eapply (cartesian_factorisation_unique).
  - exact (pr2 (pr2 (cleaving_of_types C Δ Θ s₂ (B [[ s₁ ]])))).
  - etrans.
    {
      exact (cartesian_factorisation_commutes _ (identity Θ) _).
    }
    rewrite !mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    unfold fiber_functor_from_cleaving_comp_inv.
    rewrite assoc_disp_var.
    rewrite cartesian_factorisation_commutes.
    apply (cartesian_factorisation_unique (cleaving_of_types C Γ Δ s₁ B)).
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !assoc_disp_var.
    rewrite !transport_f_f.
    rewrite !cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    rewrite !assoc_disp.
    unfold transportb.
    rewrite !transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    apply  maponpaths_2.
    apply homset_property.
Qed.

Definition comp_cat_reindex_coercion_comp'
  {C : comp_cat}
  {Γ Δ Θ : C} (s₁ : Δ --> Γ)(s₂ : Θ --> Δ)
  {A B: comp_cat_ty Γ}
  (f : A <: B )
  : ⌈comp_cat_subst_ty_comp_iso _ _ _⌉⁻¹
      · comp_cat_reindex_coercion s₂ (comp_cat_reindex_coercion s₁ f)
      · ⌈comp_cat_subst_ty_comp_iso _ _ _⌉
    = comp_cat_reindex_coercion (s₂ · s₁) f.
Proof.
  rewrite (comp_cat_reindex_coercion_comp (s₁) (s₂) (f)).
  repeat rewrite assoc.
  repeat rewrite assoc'.
  etrans.
  {
    do 3 apply maponpaths.
    apply (z_iso_after_z_iso_inv ).
  }
  rewrite assoc.
  rewrite id_right.
  etrans.
  { apply cancel_postcomposition.
    apply (z_iso_after_z_iso_inv ).
  }
  rewrite (id_left).
  apply idpath.
Qed.

Definition comp_cat_reindex_coercion_comp_witness
  {C : comp_cat}
  {Γ Δ : C} (s : Δ --> Γ)
  {A B D: comp_cat_ty Γ}
  (f : A <: B ) (g : B <: D)
  : comp_cat_reindex_coercion s (f · g)
    =  comp_cat_reindex_coercion s f · comp_cat_reindex_coercion s g.
Proof.
  unfold comp_cat_reindex_coercion.
  unfold comp_cat_reindex_coercion.
  cbn.
  unfold transportb.
  repeat rewrite transport_f_f.
  apply (cartesian_factorisation_unique (cleaving_of_types C Γ Δ s D)).
  rewrite (cartesian_factorisation_commutes).
  rewrite !mor_disp_transportf_postwhisker.
  rewrite assoc_disp_var.
  rewrite cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  rewrite !assoc_disp.
  unfold transportb.
  rewrite !transport_f_f.
  rewrite !cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !transport_f_f.
  apply  maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_reindex_coercion_subst_ty_iso
  {C : comp_cat}
  {Γ₁ Γ₂ Γ₃ : C}
  {s₁ : Γ₁ --> Γ₂}
  {s₂ s₂' : Γ₂ --> Γ₃}
  (p : s₂' = s₂)
  (A : comp_cat_ty Γ₃)
  : comp_cat_reindex_coercion s₁ (⌈comp_cat_subst_ty_iso A p⌉)
    · ⌈comp_cat_subst_ty_comp_iso A s₂ s₁⌉
    =
    ⌈comp_cat_subst_ty_comp_iso A s₂' s₁⌉
    · ⌈comp_cat_subst_ty_iso A (maponpaths (λ z, s₁ · z) p)⌉.
Proof.
  induction p.
  cbn.
  apply maponpaths.
  unfold comp_cat_reindex_coercion.
  rewrite !transport_f_f.
  unfold transportb.
  rewrite !id_right_disp.
  unfold transportb.
  rewrite !transport_f_f.
  use (cartesian_factorisation_unique (cleaving_of_types C Γ₃ Γ₁ (s₁ · s₂') A) ).
  rewrite assoc_disp_var.
  rewrite !cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !cartesian_factorisation_commutes.
  rewrite assoc_disp.
  unfold transportb.
  rewrite !transport_f_f.
  rewrite !cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.


(** * Lemmas for coercing terms  *)

Lemma coerce_tm_after_inv
  {C : comp_cat} {Γ : C} {A B : comp_cat_ty Γ}
  (i : z_iso (C := fiber_category _ _) A B)
  (t : comp_cat_tm B)
  : (t ↑ ⌈ i ⌉⁻¹) ↑ ⌈ i ⌉ = t.
Proof.
  apply comp_cat_tm_eq.
  cbn.
  rewrite <- assoc.
  rewrite comp_cat_comp_mor_z_iso_after_z_iso_inv.
  rewrite id_right.
  apply idpath.
Qed.

Lemma coerce_tm_inv_after
  {C : comp_cat} {Γ : C} {A B : comp_cat_ty Γ}
  (i : z_iso (C := fiber_category _ _) A B)
  (t : comp_cat_tm A)
  : (t ↑ ⌈ i ⌉) ↑ ⌈ i ⌉⁻¹ = t.
Proof.
  apply comp_cat_tm_eq.
  cbn.
  rewrite <- assoc.
  rewrite comp_cat_comp_mor_z_iso_inv_after_z_iso.
  rewrite id_right.
  apply idpath.
Qed.

Definition comp_cat_subst_tm_id {C : comp_cat} {Γ : C} {A : comp_cat_ty Γ} (t : comp_cat_tm A) :
  t [[ identity _ ]]tm = t ↑ ⌈comp_cat_subst_ty_id_iso _⌉.
Proof.
  use comp_cat_tm_eq ; cbn.
  refine (!_).
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback _ _))).
  - cbn.
    rewrite !assoc'.
    rewrite id_left.
    refine (_ @ id_right _).
    apply maponpaths.
    unfold comp_cat_comp_mor.
    etrans.
    {
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    rewrite cartesian_factorisation_commutes.
    refine (_ @ comprehension_functor_mor_id _ ).
    unfold comprehension_functor_mor, transportb.
    rewrite disp_functor_transportf, transportf_cod_disp.
    apply idpath.
  - cbn.
    rewrite !assoc'.
     etrans.
    {
      apply cancel_precomposition.
      set (f := cartesian_factorisation (cleaving_of_types C Γ Γ (identity Γ) A) (identity Γ)
                  (transportb (λ z : C ⟦ Γ, Γ ⟧, A -->[ z] A)
                     (fiber_functor_from_cleaving_identity_data_subproof Γ)
                     (id_disp A))).
      exact (comp_cat_comp_mor_law f).
    }
    exact (pr2 t).
Qed.

Definition comp_cat_subst_tm_comp {C : comp_cat} {Γ Δ Θ : C} {A : comp_cat_ty Γ}
  (f : Δ --> Γ) (g : Θ --> Δ) (t : comp_cat_tm A)
  : t [[ g · f ]]tm = ((t [[ f ]]tm) [[ g ]]tm) ↑ ⌈ comp_cat_subst_ty_comp_iso A f g ⌉.
Proof.
  use comp_cat_tm_eq ; cbn.
  refine (!_).
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback A _))).
  - cbn.
    unfold comp_cat_comp_mor.
    rewrite <- assoc.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    rewrite cartesian_factorisation_commutes.
    unfold comprehension_functor_mor, transportb.
    rewrite disp_functor_transportf, transportf_cod_disp.
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_comp.
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply (PullbackArrow_PullbackPr1 (comp_cat_pullback _ _)).
    }
    do 2 rewrite <- assoc.
    apply cancel_precomposition.
    apply (PullbackArrow_PullbackPr1 (comp_cat_pullback _ _ )).
  - cbn.
    rewrite <- assoc.
    etrans.
    {
      apply maponpaths.
      apply comp_cat_comp_mor_law.
    }
    apply (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _)).
Qed.

Definition comp_cat_subst_tm_comp' {C : comp_cat} {Γ Δ Θ : C} {A : comp_cat_ty Γ}
  (f : Δ --> Γ) (g : Θ --> Δ) (t : comp_cat_tm A)
  : t [[ g · f ]]tm ↑ ⌈ comp_cat_subst_ty_comp_iso A f g ⌉⁻¹ = ((t [[ f ]]tm) [[ g ]]tm) .
Proof.
  rewrite comp_cat_subst_tm_comp.
  apply coerce_tm_inv_after.
Qed.

Proposition comp_cat_comp_coerce_tm {C : comp_cat} {Γ : C} {A₁ A₂ A₃ : comp_cat_ty Γ}
  (f : A₁ <: A₂) (g : A₂ <: A₃) (t : comp_cat_tm A₁)
  : t ↑ f ↑ g = t ↑ (f · g).
Proof.
  use comp_cat_tm_eq ; cbn.
  rewrite assoc'.
  apply maponpaths.
  refine (!_).
  apply comp_cat_comp_mor_comp.
Qed.

Proposition comp_cat_id_coerce_tm {C : comp_cat} {Γ : C} {A : comp_cat_ty Γ} (t : comp_cat_tm A)
  : t ↑ id_disp _ = t.
Proof.
  use comp_cat_tm_eq ; cbn.
  change (t · comp_cat_comp_mor (@identity (fiber_category (disp_cat_of_types C) Γ) A) = pr1 t).
  rewrite comp_cat_comp_mor_id.
  apply id_right.
Qed.

Proposition comp_cat_coerce_eq {C : comp_cat} {Γ : C} {A B : comp_cat_ty Γ}
  {t : comp_cat_tm A} { f f' : A <: B}
  (p : f = f')
  : t ↑ f = t ↑ f'.
Proof.
  use comp_cat_tm_eq.
  apply cancel_precomposition.
  apply maponpaths.
  exact p.
Qed.

Proposition comp_cat_subst_coerce_tm
            {C : comp_cat}
            {Γ₁ Γ₂ : C}
            {A₁ A₂ : comp_cat_ty Γ₂}
            (s : Γ₁ --> Γ₂)
            (f : A₁ <: A₂)
            (t : comp_cat_tm A₁)
  : (t ↑ f) [[ s ]]tm
    =
    t [[ s ]]tm ↑ comp_cat_reindex_coercion s f.
Proof.
  use comp_cat_tm_eq.
  refine (!_).
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback A₂ s))).
  - unfold comp_cat_comp_mor.
    cbn.
    rewrite <- assoc.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    rewrite comprehension_functor_mor_transportf.
    etrans.
    {
      apply maponpaths.
      rewrite comprehension_functor_mor_transportf.
      apply comprehension_functor_mor_comp.
    }
    rewrite !assoc.
    apply maponpaths_2.
    apply (PullbackArrow_PullbackPr1 (comp_cat_pullback A₁ s)).
  - cbn.
    rewrite <- assoc.
    etrans.
    {
      apply maponpaths.
      apply comp_cat_comp_mor_law.
    }
    apply (PullbackArrow_PullbackPr2 (comp_cat_pullback A₁ s)).
Qed.

Proposition comp_cat_id_right_subst_ty
  {C : comp_cat}
  {Γ₁ Γ₂ : C}
  (s : Γ₁ --> Γ₂)
  (A : comp_cat_ty Γ₂)
  : comp_cat_reindex_coercion (s) (⌈ comp_cat_subst_ty_id_iso A ⌉)
    · ⌈ comp_cat_subst_ty_comp_iso A (identity _) s ⌉
    · ⌈ comp_cat_subst_ty_iso A (id_right s) ⌉
    =
    identity _.
Proof.
  refine (_ @ !(disp_cat_cleaving_id_left (cleaving_of_types C) s A)).
  do 2 apply maponpaths_2.
  unfold comp_cat_reindex_coercion.
  simpl.
  rewrite transport_f_f.
  apply idpath.
Qed.

Proposition comp_cat_id_left_subst_ty
  {C : comp_cat}
  {Γ₁ Γ₂ : C}
  (s : Γ₁ --> Γ₂)
  (A : comp_cat_ty Γ₂)
  : ⌈ comp_cat_subst_ty_id_iso (A [[ s ]]) ⌉
    · ⌈ comp_cat_subst_ty_comp_iso A s (identity _) ⌉
    · ⌈ comp_cat_subst_ty_iso A (id_left s) ⌉
    =
      identity _.
Proof.
  apply (!(disp_cat_cleaving_id_right (cleaving_of_types C) s A)).
Qed.

Proposition comp_cat_assoc'_subst_ty
  {C : comp_cat}
  {Γ₁ Γ₂ Γ₃ Γ₄ : C}
  (s₁ : Γ₁ --> Γ₂)
  (s₂ : Γ₂ --> Γ₃)
  (s₃ : Γ₃ --> Γ₄)
  (A : comp_cat_ty Γ₄)
  : comp_cat_subst_ty_comp_iso (A [[ s₃ ]]) s₂ s₁
      · comp_cat_subst_ty_comp_iso A s₃ (s₁ · s₂)
      · (⌈ comp_cat_subst_ty_iso (A) ( assoc' s₁ s₂ s₃) ⌉)
    = comp_cat_reindex_coercion s₁
        (⌈ comp_cat_subst_ty_comp_iso A s₃ s₂ ⌉)
        · ⌈ comp_cat_subst_ty_comp_iso A (s₂ · s₃) s₁ ⌉.
Proof.
  refine (!_).
  unfold comp_cat_reindex_coercion.
  refine (_ @ !disp_cat_cleaving_assoc (cleaving_of_types C) _ _ _ _).
  - rewrite transport_f_f.
    apply idpath.
  Qed.


Proposition comp_cat_assoc_subst_ty
            {C : comp_cat}
  {Γ₁ Γ₂ Γ₃ Γ₄ : C}
  (s₁ : Γ₁ --> Γ₂)
  (s₂ : Γ₂ --> Γ₃)
  (s₃ : Γ₃ --> Γ₄)
  (A : comp_cat_ty Γ₄)
  :
  ⌈ comp_cat_subst_ty_comp_iso (C:=C) (A [[ s₃ ]]) s₂ s₁ ⌉
  · ⌈ comp_cat_subst_ty_comp_iso (C:=C) A s₃ (s₁ · s₂) ⌉
  =
  comp_cat_reindex_coercion s₁
    (⌈ comp_cat_subst_ty_comp_iso A s₃ s₂ ⌉)
  · ⌈ comp_cat_subst_ty_comp_iso A (s₂ · s₃) s₁ ⌉
  · ⌈ comp_cat_subst_ty_iso A (assoc s₁ s₂ s₃) ⌉.
Proof.
  rewrite <- comp_cat_assoc'_subst_ty.
  refine (!(id_right _) @ _ @ assoc _ _ _).
  apply maponpaths.
  assert (assoc' s₁ s₂ s₃ @ assoc s₁ s₂ s₃ = idpath _) as p.
  { apply homset_property. }
  set (F := fiber_category (disp_cat_of_types C) Γ₁).
  change (identity _  = ⌈ idtoiso (C:=F)
                          (comp_cat_subst_ty_eq A (assoc' s₁ s₂ s₃)) ⌉
                          · ⌈ idtoiso (C:=F) (comp_cat_subst_ty_eq A (assoc  s₁ s₂ s₃)) ⌉).
   etrans.
   2: { apply pr1_idtoiso_concat. }
   Check comp_cat_subst_ty_eq.
   etrans.
   2: {
     do 2 apply maponpaths.
     unfold comp_cat_subst_ty_eq.
     rewrite <- (maponpathscomp0 (λ t : C ⟦ Γ₁, Γ₄ ⟧, A [[t]])).
     rewrite p.
     apply idpath.
   }
   apply idpath.
Qed.

Definition comp_cat_subst_tm_eq {C : comp_cat} {Γ Δ : C} {A : comp_cat_ty Δ}
  (t : comp_cat_tm A) { s s' : Γ --> Δ } (p : s = s')
  : t [[ s ]]tm ↑ (⌈ (comp_cat_subst_ty_iso _ p) ⌉) = t [[ s' ]]tm.
Proof.
  induction p.
  apply comp_cat_id_coerce_tm.
Qed.

Definition comp_cat_ext_subst_eq
  {C : comp_cat}
  {Γ Δ : C}
  { s s' : Γ --> Δ}
  (A : comp_cat_ty Δ)
  (p : s = s')
  : comp_cat_ext_subst s A = comp_cat_comp_mor ( ⌈ comp_cat_subst_ty_iso _ p ⌉) · comp_cat_ext_subst s' A.
Proof.
  induction p.
  change (comp_cat_subst_ty_iso A (idpath s)) with
    (idtoiso (C := fiber_category _ _) (idpath (A [[s]]))).
  cbn.
  etrans.
  2 :{
    refine (!_).
    apply maponpaths_2.
    apply comp_cat_comp_mor_id.
  }
  exact (!id_left _).
Qed.

(** * Comprehension Structure ctd.  *)

(** Pullbacks composed with isos  *)

Definition comp_cat_pullback_compose_iso
  {C : comp_cat} {Γ₁ Γ₂ : C}
  {A : comp_cat_ty Γ₁} (s : Γ₂ --> Γ₁)
  {P' : C}
  (i : z_iso P' (PullbackObject (comp_cat_pullback A s)))
  : Pullback (π A) s.
Proof.
  (* From a comp_cat_pullbak and an isomorphism of the apex, build a new pullback by composition. *)
  set (PB := comp_cat_pullback A s).
  use make_Pullback.
  - (* object *)
    exact P'.
  - (* pr1 : P' --> Γ₂ *)
    exact (i · PullbackPr1 PB).
  - (* pr2 : P' --> (Γ₁ & A) *)
    exact (i · PullbackPr2 PB).
  - (* commutativity *)
    abstract (
        repeat rewrite <- assoc;
        apply (cancel_precomposition);
        exact (PullbackSqrCommutes PB)
      ).
  - (* universal property: using invariance of isPullback under z_iso *)
    refine (isPullback_z_iso (PullbackSqrCommutes PB) (_) (isPullback_Pullback PB) (z_iso_inv i) _ _).
    + abstract (
        cbn;
        rewrite !assoc;
        rewrite z_iso_after_z_iso_inv;
        rewrite id_left;
        apply idpath
        ).
    + abstract (
        cbn ;
        rewrite !assoc ;
        rewrite z_iso_after_z_iso_inv ;
        rewrite id_left ;
        apply idpath
        ).
Defined.

(* the universal term from pullback where the apex has been changed with an iso *)
Definition comp_cat_univ_pullback_compose_iso
  {C : comp_cat} {Γ Δ Ω : C}
  {A : comp_cat_ty Δ}
  {s : Γ --> Δ}
  {A' : comp_cat_ty Γ}
  (i : @z_iso (fiber_category _ _) A' (A [[ s ]]))
  {s' : Γ --> Ω} {s'' : Ω --> Δ & A}
  (p : s' · s'' · (π A) = s)
  : comp_cat_tm A'.
Proof.
  set (PB' := comp_cat_pullback_compose_iso s (comp_cat_comp_iso i)).
  set (PB := comp_cat_pullback A s).

  use make_comp_cat_tm.
  - (* Γ -> Γ.A'  *)
    refine (PullbackArrow PB' _ (s' · s'') (identity Γ) _).
    rewrite id_left.
    exact p.
  - abstract (
    cbn;
    set (pr2 := PullbackPr2 PB');
    assert (p' : π A' = PullbackPr2 PB')
      by (unfold PB; cbn;
          change (π A' = comp_cat_comp_mor (⌈ i ⌉) · π (A [[ s ]] ));
          rewrite comp_cat_comp_mor_law;
          apply idpath);
    rewrite p';
    apply (PullbackArrow_PullbackPr2 PB')).
Defined.

(** * Variable Rule *)

Definition comp_cat_var
           {C : comp_cat}
           {Γ : C}
           (A : comp_cat_ty Γ)
  : comp_cat_tm (A [[ π A ]]).
Proof.
  use make_comp_cat_tm.
  - use (PullbackArrow (comp_cat_pullback _ _)).
    + apply identity.
    + apply identity.
    + abstract
        (rewrite !id_left ;
         apply idpath).
  - abstract
      (apply (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _))).
Defined.

Definition comp_cat_var_subst_coerce
           {C : comp_cat}
           {Γ Δ : C}
           {A : comp_cat_ty Γ}
           (s : Δ --> Γ)
           (t : comp_cat_tm (A [[ s ]]))
  : A [[s]] <: (A [[ π A ]]) [[ t · comp_cat_ext_subst s _ ]].
Proof.
  refine (⌈comp_cat_subst_ty_iso _ _⌉· ⌈comp_cat_subst_ty_comp_iso _ _ _⌉⁻¹).
  rewrite assoc'.
  rewrite comp_cat_ext_subst_commute.
  rewrite assoc.
  etrans.
  2: {
    refine (!_).
    apply maponpaths_2.
    apply (pr2 t).
  }
  refine (!_).
  apply id_left.
Defined.

Lemma cleaving_of_types_eq
      {C : comp_cat} {Γ Δ : C} {s s' : Δ --> Γ} (p : s = s') (A : comp_cat_ty Γ)
  : (pr1 (idtoiso (C := fiber_category _ _)
            (maponpaths (λ z, pr1 (cleaving_of_types _ _ _ z _)) p))
    ;; cleaving_of_types C Γ Δ s' A
    = transportf (λ z, _ -->[ z ] _) (p @ !(id_left _))
        (cleaving_of_types C Γ Δ s A))%mor_disp.
Proof.
  induction p ; cbn.
  rewrite id_left_disp.
  apply idpath.
Qed.

Proposition comp_cat_var_subst
            {C : comp_cat}
            {Γ Δ : C}
            {A : comp_cat_ty Γ}
            (s : Δ --> Γ)
            (t : comp_cat_tm (A [[ s ]]))
  : comp_cat_var A [[ t · comp_cat_ext_subst s _ ]]tm
    =
    t ↑ comp_cat_var_subst_coerce s t.
Proof.
  use comp_cat_tm_eq.
  refine (!_).
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback _ _))).
  - use (MorphismsIntoPullbackEqual (isPullback_Pullback (comp_cat_pullback A (π A)))).
    + rewrite !assoc'.
      refine (!_).
      etrans.
      { do 2 apply maponpaths.
        apply (PullbackArrow_PullbackPr1 (comp_cat_pullback A (π A))). }
      rewrite id_right.
      refine (!_).
      etrans.
      { apply maponpaths. refine (!_). apply comprehension_functor_mor_comp. }
      rewrite comprehension_functor_mor_comp.
      unfold "↑".
      cbn -[comp_cat_var_subst_coerce].
      rewrite assoc'.
      apply maponpaths.
      etrans.
      {apply maponpaths.
       refine (!_).
       apply comprehension_functor_mor_comp.
      }
      unfold comp_cat_comp_mor.
      etrans.
      { refine (!_).
        apply comprehension_functor_mor_comp.
      }
      etrans.
      { apply maponpaths.
        rewrite assoc_disp.
        apply maponpaths.
        cbn.
        unfold fiber_functor_from_cleaving_comp_inv.
        rewrite !mor_disp_transportf_postwhisker.
        apply maponpaths.
        etrans.
        { apply maponpaths_2.
          rewrite assoc_disp_var.
          rewrite cartesian_factorisation_commutes.
          apply idpath. }
        rewrite mor_disp_transportf_postwhisker.
        apply maponpaths.
        rewrite assoc_disp_var.
        apply maponpaths.
        rewrite cartesian_factorisation_commutes.
        rewrite mor_disp_transportf_prewhisker.
        apply idpath. }
      unfold transportb.
      rewrite !comprehension_functor_mor_transportf.
      etrans.
      { apply maponpaths.
        apply cleaving_of_types_eq. }
      rewrite comprehension_functor_mor_transportf.
      apply idpath.
    + rewrite !assoc'.
      etrans.
      { apply maponpaths. apply comprehension_functor_mor_comm. }
      etrans.
      { unfold "↑". cbn -[comp_cat_var_subst_coerce]. rewrite assoc'.
        apply maponpaths. rewrite !assoc. do 2 apply maponpaths_2.
        apply comp_cat_comp_mor_law. }
      rewrite !assoc.
      etrans.
      { do 2 apply maponpaths_2. apply (pr2 t). }
      rewrite id_left.
      refine (!_).
      etrans.
      { rewrite !assoc'. do 2 apply maponpaths.
        apply (PullbackArrow_PullbackPr2 (comp_cat_pullback A (π A))). }
      apply maponpaths.
      apply id_right.
  - unfold "↑". cbn -[comp_cat_var_subst_coerce].
    rewrite !assoc'.
    etrans.
    { apply maponpaths. apply comp_cat_comp_mor_law. }
    apply (pr2 t).
Qed.

(** * Extension of Substitution with Term   *)

(*
  This section covers the rules sub-ext, sub-proj, sub-beta and sub-eta from
   From Semantics to Syntax: A Type Theory for Comprehension Categories
 *)

Definition comp_cat_extend_subst
  {C : comp_cat} {Γ Δ : C} {A : comp_cat_ty Γ}
  (s : Δ --> Γ) (t : comp_cat_tm (A [[ s ]]))
  : Δ --> Γ & A
  := t · (comp_cat_ext_subst s A).

Definition comp_cat_tm_from_extend_subst
  {C : comp_cat} {Γ Δ : C} {A : comp_cat_ty Γ} (s : Δ --> Γ & A)
  : comp_cat_tm (A [[ s · π A ]])
  := (((comp_cat_var A ) [[ s  ]]tm) ↑ ⌈comp_cat_subst_ty_comp_iso _ _ _ ⌉ ).

Definition comp_cat_extend_subst_beta_1
  {C : comp_cat} {Γ Δ : C} {A : comp_cat_ty Γ}
  (s : Δ --> Γ) (t : comp_cat_tm (A [[ s ]]))
  : comp_cat_extend_subst s t · π _ = s.
Proof.
  unfold comp_cat_extend_subst.
  rewrite assoc'.
  rewrite comp_cat_ext_subst_commute.
  rewrite assoc.
  rewrite <- id_left.
  apply cancel_postcomposition.
  apply (pr2 t).
Qed.

Definition comp_cat_extend_subst_beta_2
  {C : comp_cat} {Γ Δ : C} {A : comp_cat_ty Γ}
  (s : Δ --> Γ) (t : comp_cat_tm (A [[ s ]]))
  : comp_cat_tm_from_extend_subst (comp_cat_extend_subst s t) = t ↑ ⌈comp_cat_subst_ty_iso _ (!comp_cat_extend_subst_beta_1 _ _)⌉.
Proof.
  unfold comp_cat_tm_from_extend_subst, comp_cat_extend_subst.
  rewrite comp_cat_var_subst.
  rewrite comp_cat_comp_coerce_tm.
  apply comp_cat_coerce_eq.
  unfold comp_cat_var_subst_coerce.
  etrans.
  { refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply z_iso_after_z_iso_inv.
  }
  rewrite id_right.
  do 2 apply maponpaths.
  apply homset_property.
Qed.

Definition comp_cat_extend_subst_eta
  {C : comp_cat} {Γ Δ : C} {A : comp_cat_ty Γ} (s : Δ --> Γ & A)
  : comp_cat_extend_subst (s · π _) (comp_cat_tm_from_extend_subst s) = s.
Proof.
  unfold comp_cat_extend_subst, comp_cat_tm_from_extend_subst.
  assert (H : comp_cat_comp_mor ( ⌈comp_cat_subst_ty_comp_iso A (π A) s⌉ )
                  · comp_cat_ext_subst (s · π A) A
                  = comp_cat_ext_subst s (A [[ π A ]]) · comp_cat_ext_subst (π A) A).
  { unfold comp_cat_comp_mor, comp_cat_ext_subst.
    etrans.
    { refine (!_).
      apply (comprehension_functor_mor_comp (comp_cat_comprehension C)). }
    etrans.
    { apply maponpaths.
      apply cartesian_factorisation_commutes. }
    unfold transportb.
    rewrite comprehension_functor_mor_transportf.
    apply (comprehension_functor_mor_comp (comp_cat_comprehension C)). }
  etrans.
  { refine (assoc' _ _ _ @ _).
    rewrite H.
    rewrite assoc.
    rewrite (comp_cat_ext_subst_term_commute s (A [[ π A ]]) (comp_cat_var A)).
    rewrite assoc'.
    apply maponpaths.
    apply (PullbackArrow_PullbackPr1 (comp_cat_pullback A (π A))). }
  apply id_right.
Qed.
