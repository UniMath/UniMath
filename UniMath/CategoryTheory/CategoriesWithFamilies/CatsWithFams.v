
(*  Categories with Families


  A category with families (CwF) consists of:
  1. A category C with a terminal object. Objects are contexts, morphisms are substitutions.
  2. A functor T : C^op ➔ Fam. T(Γ) is the family of terms Tm indexed by types Ty(Γ).
    For s : Γ ➜ Δ in CC, the two components of T(s) gives the
    substitution of types and terms and the substitution is the
    application of components of s.
  3. A context extension operation which assigns to each Γ ∈ C and A ∈ Ty(Γ),
      a Γ.A ∈ C, a morphism p: Γ.A → Γ, and
      a term q ∈ Tm(A[p]) satisfying the following universal property:
      for any Δ ∈ C, s : Δ ➜ Γ and t ∈ Tm(A[s]),
      there exists a unique u : Δ ➜ Gamma.A such that p ∘ u = s and t = q[u].


  References
  - "Internal Type Theory" by Peter Dybjer
  - "Categories with Families: Unityped, Simply Typed, and Dependently Typed" by Simon Castellan,
      Pierre Clairambault, and Peter Dybjer

  Contents
  1. Definition of the category Fam
  2. Definition of the data and properties of CwFs
  3. Useful computation tools for CwFs
  4. Type Formers in CwFs : Unit, Π, Σ
  5. Definition of democracy in CwFs


*)



Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Export UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Core.Setcategories.


Local Open Scope cat.

(** The category Fam *)

Definition fam_ob : UU := ∑ X : hSet, X -> hSet.

Definition fam_base (f : fam_ob) : hSet := pr1 f.

Definition fam_el {f : fam_ob} (b : fam_base f) : hSet := pr2 f b.

Definition fam_mor : fam_ob -> fam_ob -> UU
  := λ f1 f2, ∑ (f : fam_base f1 -> fam_base f2),
    (∏ (x : fam_base f1), fam_el x -> fam_el (f x)).

Definition fam_mor_eq' {f1 f2 : fam_ob} (g h : fam_mor f1 f2) (p : pr1 g = pr1 h)
  (q : transportf (λ f : fam_base f1 → fam_base f2,
             ∏ x : fam_base f1, fam_el (f:=f1) x → fam_el (f:=f2) (f x)) p (pr2 g)
       = pr2 h)
  : g = h
  := (total2_paths_f p q).

Definition transport_pr2_eq
  {a b : fam_ob}
  (f : fam_mor a b)
  (p : (λ x : fam_base a, pr1 f x) = pr1 f)
  : transportf (λ f : fam_base a → fam_base b,
          ∏ x : fam_base a, fam_el x → fam_el (f x)) p
      (λ (x : fam_base a) (y : fam_el x), pr2 f x y) = pr2 f.
Proof.
  apply funextsec ; intro x.
  apply funextfun ; intro y.
  set (E := transport_functions
              (Z:= λ (x2 : fam_base a) (y : fam_base b), fam_el x2 → fam_el  y) p
              (λ x1 : fam_base a, pr2 f x1) x).
  etrans.
  {
    exact (maponpaths (λ h : fam_el x → fam_el (pr1 f x), h y) E).
  }
  set (q := toforallpaths (λ _ : fam_base a, fam_base b) (λ x1 : fam_base a, pr1 f x1) (pr1 f) p x).
  etrans.
  {
    exact (maponpaths (λ h : fam_el x → fam_el (pr1 f x), h y)
             (transportf_set (λ y : fam_base b, fam_el x → fam_el y) q (pr2 f x) (pr2 (fam_base b)))).
  }
  apply idpath.
Defined.

Definition fam_id (f : fam_ob) : fam_mor f f.
Proof.
  use tpair.
  - exact (λ x, x).
  - intro x.
    exact (λ a, a).
Defined.

Definition fam_comp (f1 f2 f3 : fam_ob) (g : fam_mor f1 f2) (h : fam_mor f2 f3) : fam_mor f1 f3.
Proof.
  use tpair.
  - exact (λ x, pr1 h (pr1 g x)).
  - intros x a.
    exact (pr2 h (pr1 g x) (pr2 g x a)).
Defined.

Definition fam_data : precategory_data := make_precategory_data (make_precategory_ob_mor fam_ob fam_mor) fam_id fam_comp.

Definition is_precategory_fam : is_precategory fam_data.
Proof.
  do 2 split ; intros;  use fam_mor_eq'; try (apply transport_pr2_eq);
    apply funextfun; intro; cbn; apply idpath.
Defined.

Definition fam_precategory : precategory := make_precategory fam_data is_precategory_fam.

Definition has_homsets_fam : has_homsets fam_precategory.
Proof.
 intros f1 f2.
 unfold fam_precategory, fam_mor; cbn.
 use isaset_total2.
 - apply funspace_isaset.
   apply setproperty.
 - intro f.
   apply impred_isaset; intro x.
   apply funspace_isaset.
   apply setproperty.
Qed.

Definition Fam : category := make_category fam_precategory has_homsets_fam.

Definition make_fam (X : hSet) (Y : X → hSet) : ob Fam := X ,, Y.

Definition make_fam_mor {X X' : hSet} {Y : X → hSet} {Y' : X' → hSet} (f : X → X') (g : ∏ x : X, Y x → Y' (f x))
  : make_fam X Y --> make_fam X' Y' := (f ,, g).

(* in practice we use the pointwise equality of functions, not equality of functions
 so p should be pointwise equality in a lemma here.
 This will make fun_ext not appear in the functoriality proof below.
 *)
Definition fam_mor_eq {X X' : hSet} {Y : X → hSet} {Y' : X' → hSet}
  {f f' : X → X'}
  {g  : ∏ x : X, Y x → Y' (f x)}
  {g' : ∏ x : X, Y x → Y' (f' x)}
  (p : f = f')
  (q : ∏ x (y : Y x), transportf (λ h : X → X', Y' (h x)) p (g x y) = g' x y)
  : make_fam_mor f g = make_fam_mor f' g'.
Proof.
  induction p.
  apply maponpaths.
  repeat (apply funextsec;intro).
  apply q.
Qed.


(** CwF *)

Declare Scope cwf.
Local Open Scope cwf.

Definition cwf_ty_term_subst (C : category) : UU := functor (C ^opp) Fam.

Definition cwf_ty {C : category} (T : cwf_ty_term_subst C) (Γ : C) : hSet := fam_base (pr11 T Γ).

Definition cwf_tm {C : category} {Γ : C}  (T : cwf_ty_term_subst C) (A : cwf_ty T Γ) : hSet := fam_el A.

Definition cwf_subst_ty {C : category} {Γ Δ : C} (T : cwf_ty_term_subst C) (s : Γ --> Δ) (A : cwf_ty T Δ)
  : cwf_ty T Γ := (pr1 (pr21 T _ _ s) A).

Notation "A '[[' s ']]'" := (cwf_subst_ty _ s A) (at level 20) : cwf.

Definition cwf_subst_tm {C : category} {Γ Δ : C} {T : cwf_ty_term_subst C} {A : cwf_ty T Δ} (s : Γ --> Δ) (t : cwf_tm T A)
  : cwf_tm T (A [[ s ]]) := (pr2 (pr21 T _ _ s) A t).

Notation "t '[[' s ']]tm'" := (cwf_subst_tm s t) (at level 20) : cwf.

Definition make_cwf_ty_term_subst
           {C : category}
           (ty : C → hSet)
           (tm : ∏ Γ : C, ty Γ → hSet)
           (ty_subst : ∏ Γ Δ (f : Δ --> Γ), ty Γ → ty Δ)
           (tm_subst : ∏ Γ Δ (f : Δ --> Γ) (A : ty Γ), tm Γ A → tm Δ (ty_subst Γ Δ f A))
           (ty_subst_id : ∏ Γ (A : ty Γ), ty_subst Γ Γ (identity Γ) A = A)
           (ty_subst_comp : ∏ Γ Δ Θ (g : Θ --> Δ) (f : Δ --> Γ) (A : ty Γ),
               ty_subst Γ Θ (g · f) A = ty_subst Δ Θ g (ty_subst Γ Δ f A))
           (tm_subst_id : ∏ Γ (A : ty Γ) (t : pr1hSet (tm Γ A)),
               transportf (λ A, pr1hSet (tm Γ A)) (ty_subst_id Γ A) (tm_subst Γ Γ (identity Γ) A t)
               = t)
           (tm_subst_comp : ∏ Γ Δ Θ (g : Θ --> Δ) (f : Δ --> Γ) (A : ty Γ) (t : pr1hSet (tm Γ A)),
               transportf (λ A, pr1hSet (tm Θ A)) (ty_subst_comp Γ Δ Θ g f A) (tm_subst Γ Θ (g · f) A t)
               = tm_subst Δ Θ g (ty_subst Γ Δ f A) (tm_subst Γ Δ f A t))
  : cwf_ty_term_subst C.
Proof.
  use make_functor.
  - (* functor data *)
    use make_functor_data.
    + (* on objects *)
      intro Γ.
      exact (make_fam (ty Γ) (tm Γ)).
    + (* on morphisms *)
      intros Γ Δ f.
      use make_fam_mor.
      * exact (ty_subst Γ Δ f).
      * intro A.
        exact (tm_subst Γ Δ f A).
  - (* functor laws *)
    split.
    + (* identity *)
      intro Γ.
      use fam_mor_eq.
      * cbn.
        apply funextfun; intro A.
        apply ty_subst_id.
      * cbn.
        intros A t.
        change (transportf (λ x0 : ty Γ → ty Γ, tm Γ (x0 A))
                  (funextsec (λ _ : ty Γ, ty Γ) (ty_subst Γ Γ (identity Γ))
                     (λ x : ty Γ, x) (λ A0 : ty Γ, ty_subst_id Γ A0))
                  (tm_subst Γ Γ (identity Γ) A t) = t).
        eapply pathscomp0.
        -- exact (transportf_funextfun (λ B : ty Γ, tm Γ B) (ty_subst Γ Γ (identity Γ))
                    (λ x : ty Γ, x) (λ A0 : ty Γ, ty_subst_id Γ A0) (A) (tm_subst Γ Γ (identity Γ) A t)).
        -- exact (tm_subst_id Γ A t).
    + (* composition *)
      cbn.
      intro; intros.
      cbn.
      use fam_mor_eq.
      * cbn.
        apply funextfun; intro x.
        exact (ty_subst_comp a b c g f x).
      * cbn.
        intros A t.
        change (transportf (λ h : ty a → ty c, tm c (h A))
                  (funextsec (λ _ : ty a, ty c) (ty_subst a c (f · g))
                     (λ x : ty a, ty_subst b c g (ty_subst a b f x))
                     (λ x : ty a, ty_subst_comp a b c g f x))
                  (tm_subst a c (f · g) A t)
                = tm_subst b c g (ty_subst a b f A) (tm_subst a b f A t)).
        eapply pathscomp0.
        -- exact (transportf_funextfun (λ B : ty c, tm c B) (ty_subst a c (f · g))
                    (λ x : ty a, ty_subst b c g (ty_subst a b f x))
                    (λ x : ty a, ty_subst_comp a b c g f x)
                    (A) (tm_subst a c (f · g) A t)).
        -- exact (tm_subst_comp a b c g f A t).
Defined.

Definition cwf_exted_con {C : category} {T : cwf_ty_term_subst C} (Γ : C) (A : cwf_ty T Γ) : UU
  := ∑ (ext : C), (∑ (proj : ext --> Γ), cwf_tm T (A [[ proj ]])).

Definition cwf_ctx_ext {C : category} (T : cwf_ty_term_subst C) : UU
  := ∏ (Γ : C), (∏ (A : cwf_ty T Γ), cwf_exted_con Γ A).

Definition cwf_data : UU := ∑ (C : category),
    ∑ (empty_context : Terminal C), (∑ (T : cwf_ty_term_subst C), cwf_ctx_ext T).

Definition make_cwf_data (C : category) (empty_context : Terminal C)
  (T : cwf_ty_term_subst C) (ctx_ext : cwf_ctx_ext T) : cwf_data
  := C ,, (empty_context ,, (T ,, ctx_ext)).

Coercion cwf_contex {C : cwf_data} : category :=  pr1 C.

Definition cwf_empty {C : cwf_data} : C := TerminalObject (pr12 C).

Notation "[]" := cwf_empty : cwf.

Definition cwf_t (C : cwf_data) : cwf_ty_term_subst C := pr122 C.

Definition cwf_extended_con {C : cwf_data} (Γ : C) (A : cwf_ty _ Γ) : C := pr1 ((pr222 C) Γ A).

Notation "Γ '&' A" := (cwf_extended_con Γ A) (at level 20): cwf.

Definition cwf_projection {C : cwf_data} (Γ : C) (A : cwf_ty _ Γ) : Γ & A --> Γ := pr12 ((pr222 C) Γ A).

Notation "'p_' A" := (cwf_projection _ A) (at level 20): cwf.

Definition cwf_variable {C : cwf_data} (Γ : C) (A : cwf_ty _ Γ) : cwf_tm _ (A [[ (p_ A) ]]) := pr22 ((pr222 C) Γ A).

Notation "'q_' A" := (cwf_variable _ A) (at level 20): cwf.

Definition transportf_subst_ty {C : category} {Γ Δ : C} {T : cwf_ty_term_subst C} {A : cwf_ty T Δ}
  {s' s : Γ --> Δ } (p : s' = s) : cwf_ty T Γ
  := transportf (fun s : Γ --> Δ => cwf_ty T Δ  → cwf_ty T Γ) p (pr1 (pr21 T _ _ s)) A.

Definition cwf_subst_ty_eq {C : category} {Γ Δ : C} {T : cwf_ty_term_subst C}
  (A : cwf_ty T Δ) {s s' : Γ --> Δ} (p : s = s') : A [[ s ]] = A [[ s' ]].
Proof.
  induction p.
  apply idpath.
Qed.

Definition transportf_subst_tm {C : category} {Γ Δ : C} {T : cwf_ty_term_subst C}
  {A : cwf_ty T Δ} {s' s : Γ --> Δ} (p : s' = s)
  (t : cwf_tm T A) : cwf_tm T (A [[ s' ]])
  := transportf (fun s0 : Γ --> Δ => cwf_tm T (A [[ s0 ]]))
       (pathsinv0 p) ((pr2 (pr21 T _ _ s)) A t).

Definition cwf_subst_tm_eq {C : category} {Γ Δ : C} {T : cwf_ty_term_subst C}
  {A : cwf_ty T Δ} (t : cwf_tm T A) {s s' : Γ --> Δ} (p : s = s')
  : transportf (λ X, cwf_tm T (A [[ X ]])) p (t [[ s ]]tm) = t [[ s' ]]tm.
Proof.
  induction p.
  cbn.
  apply idpath.
Qed.

Definition transportf_subst_tm_on_s {C : cwf_data} {Γ Δ : C}
  {A : cwf_ty (cwf_t C) Γ} {s s' : Δ --> Γ} (p : s = s')
  (t : cwf_tm (cwf_t C) (A [[ s ]])) : cwf_tm (cwf_t C) (A [[ s' ]])
  := transportf (fun s0 : Δ --> Γ => cwf_tm (cwf_t C) (A [[ s0 ]])) p t.

Definition cwf_subst_ty_comp {C : cwf_data} {Γ Γ' Δ : C}
  (A : cwf_ty (cwf_t C) Γ) (s : Γ' --> Γ) (u : Δ --> Γ')
  : (A [[ s ]]) [[ u ]] = A [[ u · s ]].
Proof.
  set (T := pr21 (cwf_t C)).
  set (T_compax := pr2 (pr2 (cwf_t C))).
  cbn in *.
  specialize (T_compax Γ Γ' Δ s u).
  apply (maponpaths (fun f => pr1 f A)) in T_compax.
  symmetry.
  exact T_compax.
Defined.

Definition cwf_subst_tm_comp {C : cwf_data} {Γ Γ' Δ : C} (A : cwf_ty (cwf_t C) Γ) (s : Γ' --> Γ)
  (u : Δ --> Γ') (t : cwf_tm (cwf_t C) ((A [[ s ]]) [[ u ]]))
  : cwf_tm (cwf_t C) (A [[ u · s ]])
  := transportf (fun B : cwf_ty (cwf_t C) Δ => cwf_tm (cwf_t C) B)
       (cwf_subst_ty_comp A s u) t.

Definition cwf_subst_ty_id {C : cwf_data} {Γ : C} (A : cwf_ty (cwf_t C) Γ) : A [[ identity Γ ]] = A.
Proof.
  unfold cwf_subst_ty.
  set (id := functor_id (cwf_t C) Γ).
  set (id_base := maponpaths pr1 id).
  exact (toforallpaths _ _ _ id_base A).
Defined.

Definition cwf_subst_tm_id {C : cwf_data} {Γ : C} {A : cwf_ty (cwf_t C) Γ}
  (a : cwf_tm (cwf_t C) A) : cwf_tm (cwf_t C) (A [[ identity Γ ]])
  := transportf (λ X, cwf_tm (cwf_t C) X) (pathsinv0 (cwf_subst_ty_id (C:=C) A)) a.

Definition cwf_qA_subst {C : cwf_data} {Γ Δ : C} {A : cwf_ty (cwf_t C) Γ}
  (u : Δ --> Γ & A) : cwf_tm (cwf_t C) (A [[ u · p_ A ]])
  := cwf_subst_tm_comp A (p_ A) u ((q_ A) [[ u ]]tm).

Definition cwf_universal_property (C : cwf_data) : UU
  := ∏ (Γ Δ : C) (A : cwf_ty (cwf_t C) Γ)
       (s : Δ --> Γ) (t : cwf_tm _ (A [[ s ]])),
    ∃! u : (Δ --> (Γ & A)),
      ∑ p : (u · p_ A = s),
        transportf_subst_tm_on_s p (cwf_qA_subst (A:=A) u) = t.

Definition cwf : UU := ∑ (data : cwf_data), cwf_universal_property data.

Definition make_cwf (data : cwf_data) (p : cwf_universal_property data) := (data ,, p).

Coercion cwf_from_cwf_data {C : cwf} : cwf_data := pr1 C.


(** Extending substitution with terms and helpful lemmas  *)

(* the canonical morphism in the universal property *)
Definition cwf_subst_pair {C : cwf} {Γ Δ : C} {A : cwf_ty (cwf_t (pr1 C)) Γ}
  (s : Δ --> Γ) (t : cwf_tm (cwf_t (pr1 C)) (A [[ s ]])) : Δ --> (Γ & A)
  := pr1 (iscontrpr1 (pr2 C Γ Δ A s t)).

Notation "⟨⟨ s , t ⟩⟩" := (cwf_subst_pair s t) (at level 30, right associativity) : cwf.

Definition cwf_pair_p {C : cwf} {Γ Δ : C} {A : cwf_ty _ Γ}
  (s : Δ --> Γ) (t : cwf_tm _ (A[[s]])) : (⟨⟨ s , t ⟩⟩ · p_ A) = s
  := (pr1 (pr2 (pr1 (pr2 C Γ Δ A s t)))).

Definition cwf_pair_q {C : cwf} {Γ Δ : C} {A : cwf_ty _ Γ} (s : Δ --> Γ) (t : cwf_tm _ (A[[s]]))
  : transportf_subst_tm_on_s (cwf_pair_p s t) (cwf_qA_subst ( ⟨⟨ s , t ⟩⟩ )) = t
  := pr2 (pr2 (pr1 (pr2 C Γ Δ A s t))).

(* s.A *)
Definition cwf_lift
  {C : cwf} {Γ Δ : pr1 C}
  (s : Δ --> Γ)
  (A : cwf_ty (cwf_t (pr1 C)) Γ)
  : (Δ & (A [[ s ]])) --> (Γ & A).
Proof.
  set (A' := A [[ s ]]).
  set (u  := p_ A' : (Δ & A') --> Δ).
  set (t := cwf_subst_tm_comp A s u (q_ A')).
  exact (cwf_subst_pair (u · s) t).
Defined.


Definition cwf_lift_p_q {C : cwf} {Γ : pr1 C} (A : cwf_ty (cwf_t (pr1 C)) Γ)
  : (⟨⟨ identity (Γ & A) , cwf_subst_tm_id (q_ A) ⟩⟩ · cwf_lift (p_ A) A) = identity (Γ & A).
Proof.
  set (Δ := Γ & A).
  set (uu := ⟨⟨ identity Δ , cwf_subst_tm_id (q_ A) ⟩⟩ · cwf_lift (p_ A) A : Δ --> (Γ & A)).
  set (ctr := pr2 C Γ Δ A (p_ A) (q_ A)).
      admit.
  (* refine (maponpaths pr1 (pr2 contr ( (pairid · lift) ,, _ ))). *)
Admitted.

Lemma cwf_pair_subst_comm {C : cwf} {Γ Δ : pr1 C} (s : Δ --> Γ) (A : cwf_ty (cwf_t (pr1 C)) Γ)
  (a : cwf_tm (cwf_t (pr1 C)) A) :
  s · ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ =
    ⟨⟨ identity Δ , cwf_subst_tm_id (a [[ s ]]tm) ⟩⟩ · cwf_lift s A.
Proof.
  set (u := ⟨⟨ s , (a [[ s ]]tm) ⟩⟩).
  set (contr := pr2 C Γ Δ A s (a [[ s ]]tm)).

  assert (Hl : s · ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ = u).
  {
    refine (maponpaths pr1 (pr2 contr ( (s · ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩) ,, _))).
    use tpair.
    - assert (H : ⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩ · p_ A = identity _) by apply (cwf_pair_p (identity Γ) (cwf_subst_tm_id a)).
      rewrite assoc'.
      eapply pathscomp0.
      + apply maponpaths.
        exact H.
      + apply id_right.
    - cbn.
      set (pairid := ⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩).
      assert (Hp : (s · pairid) · p_ A = s).
      {
        rewrite assoc'.
        eapply pathscomp0.
        - apply cancel_precomposition.
          exact (cwf_pair_p (identity Γ) (cwf_subst_tm_id a)).
        - apply id_right.
      }
      set (bigterm := internal_paths_rew_r (pr1 C ⟦ Δ, Γ ⟧) ((s · pairid) · p_ A) (s · (pairid · p_ A))
                        (λ p : pr1 C ⟦ Δ, Γ ⟧, p = s)
                        (maponpaths (compose s) (cwf_pair_p (identity Γ) (cwf_subst_tm_id a)) @ id_right s)
                        (assoc' s pairid (p_ A))).
      assert (p : bigterm = Hp) by (apply proofirrelevance ; apply homset_property).
      eapply pathscomp0.
      +  exact (maponpaths (λ r, transportf_subst_tm_on_s r (cwf_qA_subst (s · pairid))) p).
      +  set (qpair := maponpaths (λ z, z [[ s ]]tm) (cwf_pair_q (identity Γ) (cwf_subst_tm_id a))).
         cbn in qpair.
         (* using cwf_pair_q *)
         admit.
  }

  assert (Hr : ⟨⟨ identity Δ , cwf_subst_tm_id (a [[ s ]]tm) ⟩⟩ · cwf_lift s A = u).
  {
    refine (maponpaths pr1 (pr2 contr ( (⟨⟨ identity Δ , cwf_subst_tm_id (a [[ s ]]tm) ⟩⟩ · cwf_lift s A) ,, _))).
    use tpair.
    - unfold cwf_lift.
      rewrite assoc'.
      assert (H  : (⟨⟨ p_ (A [[s]]) · s, cwf_subst_tm_comp A s (p_ (A [[s]])) (q_ (A [[s]])) ⟩⟩ · p_ A) = p_ (A [[s]]) · s) by
        apply (cwf_pair_p).
      eapply pathscomp0.
      + exact (maponpaths (λ k, ⟨⟨ identity Δ, cwf_subst_tm_id (a [[ s ]]tm) ⟩⟩ · k) H).
      + rewrite assoc.
        eapply pathscomp0.
        * apply cancel_postcomposition.
          exact ((cwf_pair_p (identity Δ) (cwf_subst_tm_id (a [[ s ]]tm)))).
        * apply id_left.
    - cbn.
      admit.
  }
  rewrite Hl.
  exact (!Hr).
Admitted.

Lemma cwf_pair_subst_ty_comm {C : cwf} {Γ Δ : pr1 C} (s : Δ --> Γ) (A : cwf_ty (cwf_t (pr1 C)) Γ)
  (B : cwf_ty (cwf_t (pr1 C)) (Γ & A)) (a : cwf_tm (cwf_t (pr1 C)) A)
  : (B [[ ⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩ ]]) [[ s ]] =
      (B [[ cwf_lift s A ]]) [[ ⟨⟨ identity Δ, cwf_subst_tm_id (a [[ s ]]tm) ⟩⟩ ]].
Proof.
  refine (cwf_subst_ty_comp B (⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩) s @ _).
  refine (_ @ pathsinv0 (cwf_subst_ty_comp B (cwf_lift s A)
                             (⟨⟨ identity Δ, cwf_subst_tm_id (a [[ s ]]tm) ⟩⟩))).
  apply cwf_subst_ty_eq.
  exact (cwf_pair_subst_comm s A a).
Qed.

(** Type Formers  *)

(** Unit Type in CwF  *)

Section Unit_For_CwF.
  Context (C : cwf).
  Let CC : cwf_data := pr1 C.
  Let T := cwf_t CC.

  Definition cwf_unit_form : UU :=
    ∏ Γ : CC, cwf_ty T Γ.

  Definition cwf_unit_intro (One : cwf_unit_form) : UU :=
    ∏ Γ : CC, cwf_tm T (One Γ).

  Definition cwf_unit_unique
    (One : cwf_unit_form) (tt : cwf_unit_intro One) : UU :=
    ∏ (Γ : CC) (t : cwf_tm T (One Γ)), t = tt Γ.

  Definition cwf_unit_subst (One : cwf_unit_form) : UU :=
    ∏ (Γ Δ : CC) (s : Γ --> Δ),
      One Δ [[ s ]] = One Γ.

  Definition cwf_unit_subst_tt
    (One : cwf_unit_form) (tt : cwf_unit_intro One)
    (us : cwf_unit_subst One) : UU :=
    ∏ (Γ Δ : CC) (s : Γ --> Δ),
      transportf (λ A, cwf_tm T A) (us Γ Δ s) (tt Δ [[ s ]]tm) = tt Γ.

  Definition cwf_unit : UU :=
    ∑ One : cwf_unit_form,
        ∑ tt  : cwf_unit_intro One,
          ∑ uniq : cwf_unit_unique One tt,
            ∑ us : cwf_unit_subst One,
              cwf_unit_subst_tt One tt us.

End Unit_For_CwF.


(** Pi Type in CwF  *)

Section Pi_For_CwF.
  Context (C : cwf).
  Let CC : cwf_data := pr1 C.
  Let T := cwf_t CC.

  Definition cwf_pi_form : UU :=
    ∏ (Γ : CC) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A)),
      cwf_ty T Γ.

  Definition cwf_pi_lam (Pi : cwf_pi_form) : UU :=
    ∏ (Γ : CC) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A)),
      cwf_tm T B -> cwf_tm T (Pi Γ A B).

  Definition cwf_pi_app (Pi : cwf_pi_form) : UU :=
    ∏ (Γ : CC) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A)),
      cwf_tm T (Pi Γ A B)
      -> ∏ a : cwf_tm T A,
        cwf_tm T (B [[ ( ⟨⟨(identity Γ) , (cwf_subst_tm_id a) ⟩⟩) ]] ).


  Definition cwf_pi_beta (Pi : cwf_pi_form)
    (lam : cwf_pi_lam Pi) (app : cwf_pi_app Pi) : UU :=
    ∏ (Γ : CC) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A))
      (b : cwf_tm T B) (a : cwf_tm T A),
      app Γ A B (lam Γ A B b) a =
        b [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]]tm.

  Definition cwf_pi_subst (Pi : cwf_pi_form) : UU :=
    ∏ (Γ Δ : CC) (s : Δ --> Γ) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A)),
      (Pi Γ A B) [[ s ]] = Pi Δ (A [[ s ]]) (B [[ cwf_lift s A ]]).

  Lemma cwf_pi_uncurry_ty_eq {Γ : pr1 C}
    (Pi  : cwf_pi_form)
    (lam : cwf_pi_lam Pi)
    (app : cwf_pi_app Pi)
    (Pi_subst : cwf_pi_subst Pi)
    (A : cwf_ty (cwf_t (pr1 C)) Γ)
    (B : cwf_ty (cwf_t (pr1 C)) (Γ & A))
    (lift_pq : (⟨⟨identity (Γ & A) , cwf_subst_tm_id (q_ A)⟩⟩ · cwf_lift (p_ A) A)
               = identity (Γ & A))
    : (B [[ cwf_lift (p_ A) A ]]) [[ ⟨⟨identity (Γ & A) , cwf_subst_tm_id (q_ A)⟩⟩ ]] = B.
  Proof.
    set (u := ⟨⟨ identity (Γ & A), cwf_subst_tm_id (q_ A) ⟩⟩).
    refine (cwf_subst_ty_comp (C:=pr1 C) B (cwf_lift (p_ A) A) u @ _).
    refine (maponpaths (λ k, B [[ k ]]) lift_pq @ _).
    exact (cwf_subst_ty_id B).
  Qed.

  Definition cwf_pi_uncurry {Γ : CC}
    (Pi  : cwf_pi_form) (lam : cwf_pi_lam Pi) (app : cwf_pi_app Pi)
    (Pi_subst : cwf_pi_subst Pi) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A))
    (f : cwf_tm T (Pi Γ A B)) : cwf_tm T B.
  Proof.
    set (f_pb := f [[ p_ A ]]tm).
    set (eqPi := Pi_subst Γ (Γ & A) (p_ A) A B).
    set (f_pb' := transportf (λ X, cwf_tm T X) eqPi f_pb).
    set (t := app (Γ & A) (A [[ p_ A ]]) (B [[ cwf_lift (p_ A) A ]]) f_pb' (q_ A)).
    refine (transportf (λ X, cwf_tm T X) (cwf_pi_uncurry_ty_eq Pi lam app Pi_subst A B _ ) t).
    exact (cwf_lift_p_q _).
  Defined.

  Definition cwf_pi_eta (Pi  : cwf_pi_form) (lam : cwf_pi_lam Pi) (app : cwf_pi_app Pi)
    (Pi_subst : cwf_pi_subst Pi) : UU :=
    ∏ (Γ : pr1 C) (A : cwf_ty (cwf_t (pr1 C)) Γ)
      (B : cwf_ty (cwf_t (pr1 C)) (Γ & A)) (f : cwf_tm (cwf_t (pr1 C)) (Pi Γ A B)),
      lam Γ A B (cwf_pi_uncurry Pi lam app Pi_subst A B f) = f.

  Definition cwf_pi_subst_lam (Pi : cwf_pi_form) (lam : cwf_pi_lam Pi)
    (Pi_subst : cwf_pi_subst Pi) : UU :=
    ∏ (Γ Δ : CC) (s : Δ --> Γ) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A))
      (b : cwf_tm T B),
      (lam Γ A B b) [[ s ]]tm = transportf (λ X, cwf_tm T X)
                                  (pathsinv0 (Pi_subst Γ Δ s A B))
                                  (lam Δ (A [[ s ]]) (B [[ cwf_lift s A ]])
                                     (b [[ cwf_lift s A ]]tm)).

  Definition cwf_pi_subst_app (Pi : cwf_pi_form) (app : cwf_pi_app Pi)
    (Pi_subst : cwf_pi_subst Pi) : UU :=
    ∏ Γ Δ s A B f a, (app Γ A B f a) [[ s ]]tm =
                       transportf (λ X, cwf_tm T X)
                         (pathsinv0 (cwf_pair_subst_ty_comm s A B a))
                         (app Δ (A [[ s ]]) (B [[ cwf_lift s A ]])
                            (transportf (λ X, cwf_tm T X) (Pi_subst Γ Δ s A B)
                               (f [[ s ]]tm)) (a [[ s ]]tm)).

  Definition cwf_pi_structure : UU :=
    ∑ Pi : cwf_pi_form,
        ∑ lam : cwf_pi_lam Pi,
          ∑ app : cwf_pi_app Pi,
            cwf_pi_beta Pi lam app ×
              ∑ Pi_subst : cwf_pi_subst Pi,
              cwf_pi_eta Pi lam app Pi_subst
                × cwf_pi_subst_lam Pi lam Pi_subst
                × cwf_pi_subst_app Pi app Pi_subst.

End Pi_For_CwF.

(**  Sigma Type in CwF  *)

Section Sigma_For_CwF.
  Context (C : cwf).
  Let CC : cwf_data := pr1 C.
  Let T := cwf_t CC.

  Definition cwf_sigma_form : UU :=
    ∏ (Γ : CC) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A)),
      cwf_ty T Γ.

  Definition cwf_sigma_pi1 (Sig : cwf_sigma_form) : UU :=
    ∏ (Γ : CC) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A)),
      cwf_tm T (Sig Γ A B) -> cwf_tm T A.

  Definition cwf_sigma_pi2 (Sig : cwf_sigma_form)
  (pi1 : cwf_sigma_pi1 Sig) : UU :=
  ∏ (Γ : CC) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A))
    (p : cwf_tm T (Sig Γ A B)),
    cwf_tm T (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id (pi1 Γ A B p) ⟩⟩ ]]).

  Definition cwf_sigma_pair (Sig : cwf_sigma_form) : UU :=
    ∏ (Γ : CC) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A)),
      ∏ a : cwf_tm T A,
        cwf_tm T (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]])
        -> cwf_tm T (Sig Γ A B).

  Definition cwf_sigma_beta1 (Sig : cwf_sigma_form) (pi1 : cwf_sigma_pi1 Sig)
    (pi2 : cwf_sigma_pi2 Sig pi1) (pair : cwf_sigma_pair Sig) : UU :=
    ∏ (Γ : CC) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A))
      (a : cwf_tm T A) (b : cwf_tm T (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]])),
      pi1 Γ A B (pair Γ A B a b) = a.

  Definition cwf_sigma_beta2 (Sig : cwf_sigma_form) (pi1 : cwf_sigma_pi1 Sig)
    (pi2 : cwf_sigma_pi2 Sig pi1) (pair : cwf_sigma_pair Sig)
    (beta1 : cwf_sigma_beta1 Sig pi1 pi2 pair) : UU :=
    ∏ (Γ : CC) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A))
      (a : cwf_tm T A) (b : cwf_tm T (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]])),
      transportf (λ X, cwf_tm T X)
        (maponpaths (λ x, B [[ ⟨⟨ identity Γ , cwf_subst_tm_id x ⟩⟩ ]])
           (beta1 Γ A B a b)) (pi2 Γ A B (pair Γ A B a b)) = b.

  Definition cwf_sigma_eta (Sig : cwf_sigma_form) (pi1 : cwf_sigma_pi1 Sig)
    (pi2 : cwf_sigma_pi2 Sig pi1) (pair : cwf_sigma_pair Sig) : UU :=
    ∏ (Γ : CC) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A))
      (p : cwf_tm T (Sig Γ A B)), pair Γ A B (pi1 Γ A B p) (pi2 Γ A B p) = p.

  Definition cwf_sigma_subst (Sig : cwf_sigma_form) : UU :=
    ∏ (Γ Δ : CC) (s : Δ --> Γ) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A)),
      (Sig Γ A B) [[ s ]] = Sig Δ (A [[ s ]]) (B [[ cwf_lift s A ]]).

  Definition cwf_sigma_subst_pi1 (Sig : cwf_sigma_form) (pi1 : cwf_sigma_pi1 Sig)
    (Sig_subst : cwf_sigma_subst Sig) : UU :=
    ∏ (Γ Δ : CC) (s : Δ --> Γ) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A))
      (p : cwf_tm T (Sig Γ A B)),
      pi1 Δ (A [[ s ]]) (B [[ cwf_lift s A ]])
        (transportf (λ X, cwf_tm T X) (Sig_subst Γ Δ s A B) (p [[ s ]]tm)) =
        (pi1 Γ A B p) [[ s ]]tm.

  Definition cwf_sigma_subst_pi2 (Sig : cwf_sigma_form) (pi1 : cwf_sigma_pi1 Sig)
    (pi2 : cwf_sigma_pi2 Sig pi1) (Sig_subst : cwf_sigma_subst Sig)
    (pi1_subst : cwf_sigma_subst_pi1 Sig pi1 Sig_subst) : UU :=
    ∏ (Γ Δ : CC) (s : Δ --> Γ) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A))
      (p : cwf_tm T (Sig Γ A B)),
      let p' : cwf_tm T (Sig Δ (A [[ s ]]) (B [[ cwf_lift s A ]])) :=
        transportf (λ X, cwf_tm T X) (Sig_subst Γ Δ s A B) (p [[ s ]]tm) in
      let a  : cwf_tm T A := pi1 Γ A B p in
      let a' : cwf_tm T (A [[ s ]]) := pi1 Δ (A [[ s ]]) (B [[ cwf_lift s A ]]) p' in
      transportf (λ X, cwf_tm T X)
        (maponpaths
           (λ x, (B [[ cwf_lift s A ]]) [[ ⟨⟨ identity Δ , cwf_subst_tm_id x ⟩⟩ ]])
           (pathsinv0 (pi1_subst Γ Δ s A B p)))
        (transportf (λ X, cwf_tm T X)
           (cwf_pair_subst_ty_comm s A B a)
           ((pi2 Γ A B p) [[ s ]]tm)) = pi2 Δ (A [[ s ]]) (B [[ cwf_lift s A ]]) p'.

  Definition cwf_sigma_subst_pair (Sig : cwf_sigma_form) (pair : cwf_sigma_pair Sig)
    (Sig_subst : cwf_sigma_subst Sig) : UU :=
    ∏ (Γ Δ : CC) (s : Δ --> Γ) (A : cwf_ty T Γ) (B : cwf_ty T (Γ & A))
      (a : cwf_tm T A) (b : cwf_tm T (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]])),
      transportf (λ X, cwf_tm T X) (Sig_subst Γ Δ s A B)
        ((pair Γ A B a b) [[ s ]]tm) =
        pair Δ (A [[ s ]]) (B [[ cwf_lift s A ]]) (a [[ s ]]tm)
          (transportf (λ X, cwf_tm T X) (cwf_pair_subst_ty_comm (C:=C) s A B a)
             (b [[ s ]]tm)).

  Definition cwf_sigma_structure : UU :=
  ∑ Sig : cwf_sigma_form,
    ∑ pi1 : cwf_sigma_pi1 Sig,
      ∑ pi2 : cwf_sigma_pi2 Sig pi1,
        ∑ pair : cwf_sigma_pair Sig,
          (∑ beta1 : cwf_sigma_beta1 Sig pi1 pi2 pair,
             ∑ beta2 : cwf_sigma_beta2 Sig pi1 pi2 pair beta1,
               cwf_sigma_eta Sig pi1 pi2 pair) ×
          ∑ Sig_subst : cwf_sigma_subst Sig,
            ∑ pi1_subst : cwf_sigma_subst_pi1 Sig pi1 Sig_subst,
              cwf_sigma_subst_pi2 Sig pi1 pi2 Sig_subst pi1_subst
              × cwf_sigma_subst_pair Sig pair Sig_subst.

End Sigma_For_CwF.

(** Democracy in CwFs  *)

Definition cwf_democracy_data (C : cwf) : UU :=
  ∏ Γ : pr1  C, ∑ Γ' : cwf_ty (cwf_t C) [], z_iso Γ ([] & Γ').


Close Scope cwf.
