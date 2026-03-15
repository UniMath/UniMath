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

Definition fam_mor_eq
  {f1 f2 : fam_ob}
  (g h : fam_mor f1 f2)
  (p : ∏ (x : fam_base f1), pr1 g x = pr1 h x)
  (q : ∏ (x : fam_base f1) (y : fam_el x),
       transportf fam_el (p x) (pr2 g x y)
       =
       pr2 h x y)
  : g = h.
Proof.
  use fam_mor_eq'.
  - use funextsec.
    exact p.
  - use funextsec ; intro x.
    use funextfun ; intro y.
    refine (_ @ q x y).
    pose (E := transport_functions
                 (Z:= λ x2 y, fam_el x2 → fam_el y)
                 (funextsec _ _ _ p)).
    etrans.
    {
      exact (maponpaths (λ h : fam_el x → fam_el _, h y) (E _ _)).
    }
    rewrite toforallpaths_funextsec.
    rewrite transportf_sec_constant.
    apply idpath.
Qed.

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

Proposition fam_mor_eq_pr1
            {a b : fam_ob}
            {f f' : fam_mor a b}
            (p : f = f')
            (x : fam_base a)
  : pr1 f x = pr1 f' x.
Proof.
  induction p.
  apply idpath.
Defined.

Proposition fam_mor_eq_pr2
            {a b : fam_ob}
            {f f' : fam_mor a b}
            (p : f = f')
            (x : fam_base a)
            (y : fam_el x)
  : transportf fam_el (fam_mor_eq_pr1 p x) (pr2 f x y) = pr2 f' x y.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

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
  do 2 split ; intros ; apply idpath.
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


(** CwF *)

Declare Scope cwf.
Delimit Scope cwf with cwf.
Local Open Scope cwf.

Definition cwf_ty_term_subst (C : category) : UU := functor (C ^opp) Fam.

Definition cwf_ty_from_ty_term_subst {C : category} (T : cwf_ty_term_subst C) (Γ : C) : hSet := fam_base (pr11 T Γ).

Definition cwf_tm_from_ty_term_subst {C : category} {Γ : C}  (T : cwf_ty_term_subst C) (A : cwf_ty_from_ty_term_subst T Γ) : hSet := fam_el A.

Definition cwf_subst_ty_from_ty_term_subst {C : category} {Γ Δ : C} (T : cwf_ty_term_subst C) (s : Γ --> Δ) (A : cwf_ty_from_ty_term_subst T Δ)
  : cwf_ty_from_ty_term_subst T Γ := (pr1 (pr21 T _ _ s) A).

Notation "A '[[' s ']]'" := (cwf_subst_ty_from_ty_term_subst _ s A) (at level 20) : cwf.

Definition cwf_subst_tm_from_ty_term_subst {C : category} {Γ Δ : C} {T : cwf_ty_term_subst C} {A : cwf_ty_from_ty_term_subst T Δ} (s : Γ --> Δ) (t : cwf_tm_from_ty_term_subst T A)
  : cwf_tm_from_ty_term_subst T (A [[ s ]]) := (pr2 (pr21 T _ _ s) A t).

Notation "t '[[' s ']]tm'" := (cwf_subst_tm_from_ty_term_subst s t) (at level 20) : cwf.

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
      use fam_mor_eq ; cbn.
      * intro A.
        apply ty_subst_id.
      * intros A t.
        apply tm_subst_id.
    + (* composition *)
      cbn.
      intro; intros.
      use fam_mor_eq ; cbn.
      * intros.
        apply ty_subst_comp.
      * intros.
        apply tm_subst_comp.
Defined.

Definition cwf_exted_con {C : category} {T : cwf_ty_term_subst C} (Γ : C) (A : cwf_ty_from_ty_term_subst T Γ) : UU
  := ∑ (ext : C), (∑ (proj : ext --> Γ), cwf_tm_from_ty_term_subst T (A [[ proj ]])).

Definition cwf_ctx_ext {C : category} (T : cwf_ty_term_subst C) : UU
  := ∏ (Γ : C), (∏ (A : cwf_ty_from_ty_term_subst T Γ), cwf_exted_con Γ A).

Definition cwf_data : UU := ∑ (C : category),
    ∑ (empty_context : Terminal C), (∑ (T : cwf_ty_term_subst C), cwf_ctx_ext T).

Definition make_cwf_data (C : category) (empty_context : Terminal C)
  (T : cwf_ty_term_subst C) (ctx_ext : cwf_ctx_ext T) : cwf_data
  := C ,, (empty_context ,, (T ,, ctx_ext)).

Coercion cwf_contex {C : cwf_data} : category :=  pr1 C.

Definition cwf_empty {C : cwf_data} : C := TerminalObject (pr12 C).

Notation "[]" := cwf_empty : cwf.

Definition cwf_t (C : cwf_data) : cwf_ty_term_subst C := pr122 C.

Definition cwf_ty {C : cwf_data} (Γ : C) : hSet := fam_base (pr11 (cwf_t C) Γ).

Definition cwf_tm {C : cwf_data} {Γ : C} (A : cwf_ty_from_ty_term_subst (cwf_t C) Γ) : hSet := fam_el A.

Definition cwf_subst_ty {C : cwf_data} {Γ Δ : C} (s : Γ --> Δ) (A : cwf_ty Δ) : cwf_ty Γ := (pr1 (pr21 (cwf_t C) _ _ s) A).

Definition cwf_subst_tm {C : cwf_data} {Γ Δ : C} {A : cwf_ty Δ} (s : Γ --> Δ) (t : cwf_tm A)
  : cwf_tm (A [[ s ]]) := (pr2 (pr21 (cwf_t C) _ _ s) A t).

Definition cwf_extended_con {C : cwf_data} (Γ : C) (A : cwf_ty Γ) : C := pr1 ((pr222 C) Γ A).

Notation "Γ '&' A" := (cwf_extended_con Γ A) (at level 20): cwf.

Definition cwf_projection {C : cwf_data} (Γ : C) (A : cwf_ty Γ) : Γ & A --> Γ := pr12 ((pr222 C) Γ A).

Notation "'p_' A" := (cwf_projection _ A) (at level 20): cwf.

Definition cwf_variable {C : cwf_data} (Γ : C) (A : cwf_ty Γ) : cwf_tm (A [[ (p_ A) ]]) := pr22 ((pr222 C) Γ A).

Notation "'q_' A" := (cwf_variable _ A) (at level 20): cwf.

Definition transportf_subst_ty {C : cwf_data} {Γ Δ : C} {A : cwf_ty Δ}
  {s' s : Γ --> Δ } (p : s' = s) : cwf_ty Γ
  := transportf (fun s : Γ --> Δ => cwf_ty Δ  → cwf_ty Γ) p (pr1 (pr21 (cwf_t C) _ _ s)) A.

Definition cwf_subst_ty_eq {C : cwf_data} {Γ Δ : C}
  (A : cwf_ty Δ) {s s' : Γ --> Δ} (p : s = s') : A [[ s ]] = A [[ s' ]].
Proof.
  induction p.
  apply idpath.
Qed.

Definition transportf_subst_tm {C : cwf_data} {Γ Δ : C}
  {A : cwf_ty Δ} {s' s : Γ --> Δ} (p : s' = s)
  (t : cwf_tm A) : cwf_tm (A [[ s' ]])
  := transportf (fun s0 : Γ --> Δ => cwf_tm (A [[ s0 ]]))
       (pathsinv0 p) ((pr2 (pr21 (cwf_t C) _ _ s)) A t).

Definition cwf_subst_tm_eq {C : cwf_data} {Γ Δ : C}
  {A : cwf_ty Δ} (t : cwf_tm A) {s s' : Γ --> Δ} (p : s = s')
  : transportf (λ X, cwf_tm (A [[ X ]])) p (t [[ s ]]tm) = t [[ s' ]]tm.
Proof.
  induction p.
  cbn.
  apply idpath.
Qed.

Definition cwf_subst_tm_eq' {C : cwf_data} {Γ Δ : C}
  {A : cwf_ty Δ} (t : cwf_tm  A) {s s' : Γ --> Δ} (p : s = s')
  : transportf (cwf_tm) (maponpaths (λ z, _ [[ z ]]) p) (t [[ s ]]tm) = t [[ s' ]]tm.
Proof.
  induction p.
  cbn.
  apply idpath.
Qed.

Proposition transportf_cwf_subst_tm
  {C : cwf_data}
  {Γ Δ : C}
  {A A' : cwf_ty Δ}
  (p : A = A')
  (s : Γ --> Δ)
  (t : cwf_tm A)
  : (transportf (cwf_tm ) p t) [[ s ]]tm
    =
    transportf (cwf_tm ) (maponpaths (λ z, z [[ s ]]) p) (t [[ s ]]tm).
Proof.
  induction p.
  apply idpath.
Qed.

Definition transportf_subst_tm_on_s {C : cwf_data} {Γ Δ : C}
  {A : cwf_ty  Γ} {s s' : Δ --> Γ} (p : s = s')
  (t : cwf_tm  (A [[ s ]])) : cwf_tm  (A [[ s' ]])
  := transportf (fun s0 : Δ --> Γ => cwf_tm  (A [[ s0 ]])) p t.

Lemma transportf_subst_tm_on_s_eq
      {C : cwf_data} {Γ Δ : C}
      {A : cwf_ty  Γ} {s s' : Δ --> Γ} (p : s = s')
      (t : cwf_tm  (A [[ s ]]))
  : transportf_subst_tm_on_s p t
    =
    transportf (cwf_tm ) (maponpaths (λ z, A [[ z ]]) p) t.
Proof.
  induction p.
  apply idpath.
Qed.

Definition cwf_subst_ty_comp {C : cwf_data} {Γ Γ' Δ : C}
  (A : cwf_ty  Γ) (s : Γ' --> Γ) (u : Δ --> Γ')
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

Definition cwf_subst_tm_comp {C : cwf_data} {Γ Γ' Δ : C} (A : cwf_ty  Γ) (s : Γ' --> Γ)
  (u : Δ --> Γ') (t : cwf_tm  ((A [[ s ]]) [[ u ]]))
  : cwf_tm  (A [[ u · s ]])
  := transportf (fun B : cwf_ty  Δ => cwf_tm  B)
       (cwf_subst_ty_comp A s u) t.

Definition cwf_subst_ty_id {C : cwf_data} {Γ : C} (A : cwf_ty  Γ)
  : A [[ identity Γ ]] = A.
Proof.
  unfold cwf_subst_ty.
  set (id := functor_id (cwf_t C) Γ).
  exact (fam_mor_eq_pr1 id A).
Defined.

Proposition cwf_subst_tm_on_id
            {C : cwf_data}
            {Γ : C}
            {A : cwf_ty  Γ}
            (t : cwf_tm  A)
  : t [[ identity _ ]]tm
    =
    transportf (cwf_tm ) (!(cwf_subst_ty_id A)) t.
Proof.
  set (id := functor_id (cwf_t C) Γ).
  pose proof (fam_mor_eq_pr2 id A t) as p.
  cbn in p.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    exact (!p).
  }
  rewrite transport_f_f.
  apply (transportf_set fam_el).
  apply setproperty.
Qed.

Proposition cwf_subst_tm_on_comp
            {C : cwf_data}
            {Γ₁ Γ₂ Γ₃ : C}
            {A : cwf_ty Γ₃}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (t : cwf_tm A)
  : t [[ s₁ · s₂ ]]tm
    =
    transportf (cwf_tm ) (cwf_subst_ty_comp _ _ _) (t [[ s₂ ]]tm [[ s₁ ]]tm).
Proof.
  set (id := functor_comp (cwf_t C) s₂ s₁).
  pose proof (fam_mor_eq_pr2 id A t) as p.
  cbn in p.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    exact (!p).
  }
  rewrite transport_f_f.
  apply (transportf_set fam_el).
  apply setproperty.
Qed.

Definition cwf_subst_tm_id {C : cwf_data} {Γ : C} {A : cwf_ty Γ}
  (a : cwf_tm  A) : cwf_tm (A [[ identity Γ ]])
  := transportf (λ X, cwf_tm  X) (pathsinv0 (cwf_subst_ty_id (C:=C) A)) a.

Definition cwf_qA_subst {C : cwf_data} {Γ Δ : C} {A : cwf_ty  Γ}
  (u : Δ --> Γ & A) : cwf_tm (A [[ u · p_ A ]])
  := cwf_subst_tm_comp A (p_ A) u ((q_ A) [[ u ]]tm).

Definition cwf_universal_property (C : cwf_data) : UU
  := ∏ (Γ Δ : C) (A : cwf_ty Γ)
       (s : Δ --> Γ) (t : cwf_tm (A [[ s ]])),
    ∃! u : (Δ --> (Γ & A)),
      ∑ p : (u · p_ A = s),
        transportf_subst_tm_on_s p (cwf_qA_subst (A:=A) u) = t.

Definition cwf : UU := ∑ (data : cwf_data), cwf_universal_property data.

Definition make_cwf (data : cwf_data) (p : cwf_universal_property data) := (data ,, p).

Coercion cwf_from_cwf_data {C : cwf} : cwf_data := pr1 C.

Definition make_cwf_universal_property_β_η
           {C : cwf_data}
           (ext : ∏ {Γ Δ : C}
                    {A : cwf_ty Γ}
                    (s : Δ --> Γ)
                    (t : cwf_tm (A [[ s ]])),
                  Δ --> Γ & A)
           (ext_pr : ∏ {Γ Δ : C}
                       {A : cwf_ty Γ}
                       (s : Δ --> Γ)
                       (t : cwf_tm (A [[ s ]])),
                     ext s t · p_ A = s)
           (ext_tm : ∏ {Γ Δ : C}
                       {A : cwf_ty Γ}
                       (s : Δ --> Γ)
                       (t : cwf_tm (A [[ s ]])),
                     transportf_subst_tm_on_s (ext_pr s t) (cwf_qA_subst (ext s t)) = t)
           (ext_eta : ∏ (Γ Δ : C)
                        (A : cwf_ty Γ)
                        (s : Δ --> Γ & A),
                      s
                      =
                      ext (s · p_ A) (cwf_subst_tm_comp _ _ _ (q_ A [[ s ]]tm)))
  : cwf_universal_property C.
Proof.
  intros Γ Δ A s t.
  use make_iscontr.
  - exact (ext Γ Δ A s t ,, ext_pr Γ Δ A s t ,, ext_tm Γ Δ A s t).
  - abstract
      (intros (s' & p_s & q_s) ;
       use subtypePath ;
       [ intro ;
         use isaproptotal2 ;
         [ intro ; apply setproperty
         | intros ; apply homset_property ]
       |
       ] ;
       refine (ext_eta Γ Δ A s' @ _) ; cbn ;
       induction p_s, q_s ;
       apply idpath).
Defined.

(** Extending substitution with terms and helpful lemmas  *)

(* the canonical morphism in the universal property *)
Definition cwf_subst_pair {C : cwf} {Γ Δ : C} {A : cwf_ty Γ}
  (s : Δ --> Γ) (t : cwf_tm (A [[ s ]])) : Δ --> (Γ & A)
  := pr1 (iscontrpr1 (pr2 C Γ Δ A s t)).

Notation "⟨⟨ s , t ⟩⟩" := (cwf_subst_pair s t) (at level 30, right associativity) : cwf.

Definition cwf_pair_p {C : cwf} {Γ Δ : C} {A : cwf_ty Γ}
  (s : Δ --> Γ) (t : cwf_tm (A[[s]])) : (⟨⟨ s , t ⟩⟩ · p_ A) = s
  := (pr1 (pr2 (pr1 (pr2 C Γ Δ A s t)))).

Definition cwf_pair_q {C : cwf} {Γ Δ : C} {A : cwf_ty Γ} (s : Δ --> Γ) (t : cwf_tm (A[[s]]))
  : transportf_subst_tm_on_s (cwf_pair_p s t) (cwf_qA_subst ( ⟨⟨ s , t ⟩⟩ )) = t
  := pr2 (pr2 (pr1 (pr2 C Γ Δ A s t))).

Proposition cwf_pair_q_subst_eq
  {C : cwf} {Γ Δ : C} {A : cwf_ty Γ} (s : Δ --> Γ) (t : cwf_tm (A[[s]]))
  : A [[s]] = (A [[p_ A]]) [[⟨⟨ s , t ⟩⟩]].
Proof.
  rewrite cwf_subst_ty_comp.
  rewrite cwf_pair_p.
  apply idpath.
Qed.

Proposition cwf_pair_q_subst
  {C : cwf} {Γ Δ : C} {A : cwf_ty Γ} (s : Δ --> Γ) (t : cwf_tm (A[[s]]))
  : (q_ A) [[ ⟨⟨ s , t ⟩⟩ ]]tm
    =
    transportf (cwf_tm ) (cwf_pair_q_subst_eq s t) t.
Proof.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    exact (!(cwf_pair_q s t)).
  }
  etrans.
  {
    apply maponpaths.
    apply transportf_subst_tm_on_s_eq.
  }
  rewrite transport_f_f.
  unfold cwf_qA_subst, cwf_subst_tm_comp.
  rewrite transport_f_f.
  use (transportf_set (cwf_tm )).
  apply setproperty.
Qed.

Proposition cwf_pair_q_subst'
  {C : cwf} {Γ Δ : C} {A : cwf_ty Γ} (s : Δ --> Γ) (t : cwf_tm (A[[s]]))
  : t
    =
    transportb (cwf_tm ) (cwf_pair_q_subst_eq s t) (q_ A [[ ⟨⟨ s , t ⟩⟩ ]]tm).
Proof.
  rewrite cwf_pair_q_subst.
  rewrite transportbfinv.
  apply idpath.
Qed.

Proposition cwf_subst_pair_eq_subst
  {C : cwf}
  {Γ Δ : C}
  {A : cwf_ty Γ}
  {s s' : Δ --> Γ}
  (p : s = s')
  (t : cwf_tm (A [[ s ]]))
  : ⟨⟨ s , t ⟩⟩ = ⟨⟨ s' , transportf_subst_tm_on_s p t ⟩⟩.
Proof.
  induction p.
  apply idpath.
Qed.

Proposition cwf_pair_unique
            {C : cwf}
            {Γ Δ : C}
            {A : cwf_ty Γ}
            (s : Δ --> Γ)
            (t : cwf_tm (A [[ s ]]))
            {u₁ u₂ : Δ --> Γ & A}
            (p₁ : u₁ · p_ A = s)
            (p₂ : u₂ · p_ A = s)
            (q₁ : transportf_subst_tm_on_s p₁ (cwf_qA_subst u₁) = t)
            (q₂ : transportf_subst_tm_on_s p₂ (cwf_qA_subst u₂) = t)
  : u₁ = u₂.
Proof.
  exact (maponpaths
           pr1
           (proofirrelevance
              _
              (isapropifcontr (pr2 C Γ Δ A s t))
              (u₁ ,, p₁ ,, q₁)
              (u₂ ,, p₂ ,, q₂))).
Qed.

Proposition cwf_subst_pair_precomp
            {C : cwf}
            {Γ₁ Γ₂ Γ₃ : C}
            {A : cwf_ty Γ₃}
            (s : Γ₁ --> Γ₂)
            (s' : Γ₂ --> Γ₃)
            (t : cwf_tm (A [[ s' ]]))
  : s · ⟨⟨ s' , t ⟩⟩
    =
    ⟨⟨ s · s' , transportf (cwf_tm ) (cwf_subst_ty_comp _ _ _) (t [[ s ]]tm) ⟩⟩.
Proof.
  use (cwf_pair_unique
         (s · s')
         (transportf (cwf_tm) (cwf_subst_ty_comp _ _ _) (t [[ s ]]tm))).
  - abstract
      (rewrite !assoc' ;
       apply maponpaths ;
       apply cwf_pair_p).
  - apply cwf_pair_p.
  - unfold cwf_qA_subst, cwf_subst_tm_comp.
    rewrite transportf_subst_tm_on_s_eq.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply cwf_subst_tm_on_comp.
    }
    rewrite transport_f_f.
    etrans.
    {
      do 2 apply maponpaths.
      apply cwf_pair_q_subst.
    }
    rewrite transportf_cwf_subst_tm.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply setproperty.
  - apply cwf_pair_q.
Qed.

Proposition cwf_pair_eta
            {C : cwf}
            {Γ Δ : C}
            {A : cwf_ty Γ}
            (s : Δ --> Γ & A)
  : s
    =
    ⟨⟨ s · p_ A , cwf_subst_tm_comp _ _ _ (q_ A [[ s ]]tm) ⟩⟩.
Proof.
  use cwf_pair_unique.
  - exact (s · p_ A).
  - exact (cwf_qA_subst s).
  - apply idpath.
  - apply cwf_pair_p.
  - apply idpath.
  - rewrite cwf_pair_q.
    apply idpath.
Qed.

(* s.A *)
Definition cwf_lift
  {C : cwf} {Γ Δ : pr1 C}
  (s : Δ --> Γ)
  (A : cwf_ty Γ)
  : (Δ & (A [[ s ]])) --> (Γ & A).
Proof.
  set (A' := A [[ s ]]).
  set (u  := p_ A' : (Δ & A') --> Δ).
  set (t := cwf_subst_tm_comp A s u (q_ A')).
  exact (cwf_subst_pair (u · s) t).
Defined.


Definition cwf_lift_p_q {C : cwf} {Γ : pr1 C} (A : cwf_ty Γ)
  : (⟨⟨ identity (Γ & A) , cwf_subst_tm_id (q_ A) ⟩⟩ · cwf_lift (p_ A) A) = identity (Γ & A).
Proof.
  set (Δ := Γ & A).
  set (uu := ⟨⟨ identity Δ , cwf_subst_tm_id (q_ A) ⟩⟩ · cwf_lift (p_ A) A : Δ --> (Γ & A)).
  set (ctr := pr2 C Γ Δ A (p_ A) (q_ A)).
  unfold cwf_lift.
  use (cwf_pair_unique (p_ A) (q_ A)).
  - abstract
      (rewrite !assoc' ;
       etrans ; [ apply maponpaths ; apply cwf_pair_p | ] ;
       rewrite !assoc ;
       etrans ; [ apply maponpaths_2 ; apply cwf_pair_p | ] ;
       apply id_left).
  - apply id_left.
  - unfold cwf_qA_subst, cwf_subst_tm_comp.
    rewrite transportf_subst_tm_on_s_eq.
    rewrite transport_f_f.
    refine (_ @ !(cwf_pair_q_subst' _ _)).
    use (transportf_transpose_left (P := cwf_tm)).
    rewrite transport_b_b.
    simple refine (!(cwf_subst_tm_eq' (s := ⟨⟨ p_ A, q_ A ⟩⟩) _ _) @ _).
    2: unfold transportb ; apply maponpaths_2 ; apply setproperty.
    refine (!_).
    etrans.
    {
      apply cwf_subst_pair_precomp.
    }
    etrans.
    {
      use cwf_subst_pair_eq_subst.
      {
        exact (p_ A).
      }
      abstract
        (rewrite !assoc ;
         etrans ; [ apply maponpaths_2 ; apply cwf_pair_p | ] ;
         apply id_left).
    }
    apply maponpaths.
    rewrite transportf_subst_tm_on_s_eq.
    rewrite transport_f_f.
    etrans. {
        apply maponpaths.
        apply transportf_cwf_subst_tm.
    }
    rewrite !transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply cwf_pair_q_subst.
    }
    rewrite transport_f_f.
    unfold cwf_subst_tm_id.
    rewrite transport_f_f.
    use (transportf_set (cwf_tm)).
    apply setproperty.
  - unfold cwf_qA_subst, cwf_subst_tm_comp.
    rewrite transportf_subst_tm_on_s_eq.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply cwf_subst_tm_on_id.
    }
    rewrite transport_f_f.
    use (transportf_set (cwf_tm)).
    apply setproperty.
Qed.

Lemma cwf_pair_subst_comm {C : cwf} {Γ Δ : C} (s : Δ --> Γ) (A : cwf_ty Γ)
  (a : cwf_tm A) :
  s · ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ =
    ⟨⟨ identity Δ , cwf_subst_tm_id (a [[ s ]]tm) ⟩⟩ · cwf_lift s A.
Proof.
  use (cwf_pair_unique s (a [[ s ]]tm)).
  - abstract
      (rewrite assoc' ;
       etrans ; [ apply maponpaths ; apply cwf_pair_p | ] ;
       apply id_right).
  - abstract
      (unfold cwf_lift ;
       rewrite !assoc' ;
       etrans ; [ apply maponpaths ; apply cwf_pair_p | ] ;
       rewrite assoc ;
       etrans ; [ apply maponpaths_2 ; apply cwf_pair_p | ] ;
       apply id_left).
  - rewrite transportf_subst_tm_on_s_eq.
    unfold cwf_qA_subst, cwf_subst_tm_comp.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply cwf_subst_tm_on_comp.
    }
    rewrite transport_f_f.
    etrans.
    {
      do 2 apply maponpaths.
      apply cwf_pair_q_subst.
    }
    unfold cwf_subst_tm_id.
    rewrite !transportf_cwf_subst_tm.
    rewrite !transport_f_f.
    use (transportf_set (cwf_tm)).
    apply setproperty.
  - rewrite transportf_subst_tm_on_s_eq.
    unfold cwf_qA_subst, cwf_subst_tm_comp.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply cwf_subst_tm_on_comp.
    }
    rewrite transport_f_f.
    etrans.
    {
      do 2 apply maponpaths.
      apply cwf_pair_q_subst.
    }
    unfold cwf_subst_tm_comp.
    rewrite !transportf_cwf_subst_tm.
    rewrite !transport_f_f.
    Admitted.
    (* etrans. *)
    (* { *)
    (*   do 2 apply maponpaths. *)
    (*   Check cwf_pair_q_subst s (a [[ s ]]tm). *)
    (* } *)
    (* rewrite transport_f_f. *)
    (* unfold cwf_subst_tm_id. *)
    (* rewrite transport_f_f. *)
    (* use (transportf_set (cwf_tm (cwf_t C))). *)
    (* apply setproperty. *)


Lemma cwf_pair_subst_ty_comm {C : cwf} {Γ Δ : C} (s : Δ --> Γ) (A : cwf_ty Γ)
  (B : cwf_ty (Γ & A)) (a : cwf_tm A)
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
  Context (CC : cwf).

  Definition unit_form : UU :=
    ∏ Γ : CC, cwf_ty Γ.

  Definition unit_intro (One : unit_form) : UU :=
    ∏ Γ : CC, cwf_tm (One Γ).

  Definition unit_unique
    (One : unit_form) (tt : unit_intro One) : UU :=
    ∏ (Γ : CC) (t : cwf_tm (One Γ)), t = tt Γ.

  Definition unit_subst (One : unit_form) : UU :=
    ∏ (Γ Δ : CC) (s : Γ --> Δ),
      One Δ [[ s ]] = One Γ.

  Definition unit_subst_tt
    (One : unit_form) (tt : unit_intro One)
    (us : unit_subst One) : UU :=
    ∏ (Γ Δ : CC) (s : Γ --> Δ),
      transportf (λ A, cwf_tm A) (us Γ Δ s) (tt Δ [[ s ]]tm) = tt Γ.

  Definition cwf_unit : UU :=
    ∑ One : unit_form,
        ∑ tt  : unit_intro One,
          ∑ uniq : unit_unique One tt,
            ∑ us : unit_subst One,
              unit_subst_tt One tt us.

End Unit_For_CwF.

(** Accessors for cwf_unit *)

Section cwf_unit_accessors.

Coercion cwf_unit_One (C : cwf) (u : cwf_unit C)
  : ∏ (Γ : C), cwf_ty Γ
  := pr1 u.

Definition cwf_unit_tt {C : cwf} {u : cwf_unit C} (Γ : C)
  : cwf_tm ((pr1 u) Γ)
  := pr12 u Γ.

Definition cwf_unit_uniq {C : cwf} {u : cwf_unit C}
  {Γ :  C} (t : cwf_tm ((pr1 u) Γ))
  : t = cwf_unit_tt Γ
  := pr122 u Γ t.

Definition cwf_unit_subst_eq {C : cwf} {u : cwf_unit C}
  {Γ Δ : C} (s : Γ --> Δ)
  : (pr1 u) Δ [[ s ]] = (pr1 u) Γ
  := pr1 (pr222 u) Γ Δ s.

Definition cwf_unit_subst_tt {C : cwf} {u : cwf_unit C}
  {Γ Δ : C} (s : Γ --> Δ)
  : transportf (λ A, cwf_tm A) (cwf_unit_subst_eq s)
      (cwf_unit_tt Δ [[ s ]]tm)
    = cwf_unit_tt Γ
  := pr2 (pr222 u) Γ Δ s.

End cwf_unit_accessors.


(** Pi Type in CwF  *)

Section Pi_For_CwF.
  Context (CC : cwf).

  Definition pi_form : UU :=
    ∏ (Γ : CC) (A : cwf_ty Γ) (B : cwf_ty (Γ & A)),
      cwf_ty Γ.

  Definition pi_lam (Pi : pi_form) : UU :=
    ∏ (Γ : CC) (A : cwf_ty Γ) (B : cwf_ty (Γ & A)),
      cwf_tm B -> cwf_tm (Pi Γ A B).

  Definition pi_app (Pi : pi_form) : UU :=
    ∏ (Γ : CC) (A : cwf_ty Γ) (B : cwf_ty (Γ & A)),
      cwf_tm (Pi Γ A B)
      -> ∏ a : cwf_tm A,
        cwf_tm (B [[ ( ⟨⟨(identity Γ) , (cwf_subst_tm_id a) ⟩⟩) ]] ).

  Definition pi_beta (Pi : pi_form)
    (lam : pi_lam Pi) (app : pi_app Pi) : UU :=
    ∏ (Γ : CC) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
      (b : cwf_tm B) (a : cwf_tm A),
      app Γ A B (lam Γ A B b) a =
        b [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]]tm.

  Definition pi_subst (Pi : pi_form) : UU :=
    ∏ (Γ Δ : CC) (s : Δ --> Γ) (A : cwf_ty Γ) (B : cwf_ty (Γ & A)),
      (Pi Γ A B) [[ s ]] = Pi Δ (A [[ s ]]) (B [[ cwf_lift s A ]]).

  Lemma pi_uncurry_ty_eq {Γ : CC}
    (Pi  : pi_form)
    (lam : pi_lam Pi)
    (app : pi_app Pi)
    (Pi_subst : pi_subst Pi)
    (A : cwf_ty Γ)
    (B : cwf_ty (Γ & A))
    (lift_pq : (⟨⟨identity (Γ & A) , cwf_subst_tm_id (q_ A)⟩⟩ · cwf_lift (p_ A) A)
               = identity (Γ & A))
    : (B [[ cwf_lift (p_ A) A ]]) [[ ⟨⟨identity (Γ & A) , cwf_subst_tm_id (q_ A)⟩⟩ ]] = B.
  Proof.
    set (u := ⟨⟨ identity (Γ & A), cwf_subst_tm_id (q_ A) ⟩⟩).
    refine (cwf_subst_ty_comp (C:=CC) B (cwf_lift (p_ A) A) u @ _).
    refine (maponpaths (λ k, B [[ k ]]) lift_pq @ _).
    exact (cwf_subst_ty_id B).
  Qed.

  Definition pi_uncurry {Γ : CC}
    (Pi  : pi_form) (lam : pi_lam Pi) (app : pi_app Pi)
    (Pi_subst : pi_subst Pi) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
    (f : cwf_tm (Pi Γ A B)) : cwf_tm B.
  Proof.
    set (f_pb := f [[ p_ A ]]tm).
    set (eqPi := Pi_subst Γ (Γ & A) (p_ A) A B).
    set (f_pb' := transportf (λ X, cwf_tm X) eqPi f_pb).
    set (t := app (Γ & A) (A [[ p_ A ]]) (B [[ cwf_lift (p_ A) A ]]) f_pb' (q_ A)).
    refine (transportf (λ X, cwf_tm X) (pi_uncurry_ty_eq Pi lam app Pi_subst A B _ ) t).
    exact (cwf_lift_p_q _).
  Defined.

  Definition pi_eta (Pi  : pi_form) (lam : pi_lam Pi) (app : pi_app Pi)
    (Pi_subst : pi_subst Pi) : UU :=
    ∏ (Γ : CC) (A : cwf_ty Γ)
      (B : cwf_ty (Γ & A)) (f : cwf_tm (Pi Γ A B)),
      lam Γ A B (pi_uncurry Pi lam app Pi_subst A B f) = f.

  Definition pi_subst_lam (Pi : pi_form) (lam : pi_lam Pi)
    (Pi_subst : pi_subst Pi) : UU :=
    ∏ (Γ Δ : CC) (s : Δ --> Γ) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
      (b : cwf_tm B),
      (lam Γ A B b) [[ s ]]tm = transportf (λ X, cwf_tm X)
                                  (pathsinv0 (Pi_subst Γ Δ s A B))
                                  (lam Δ (A [[ s ]]) (B [[ cwf_lift s A ]])
                                     (b [[ cwf_lift s A ]]tm)).

  Definition pi_subst_app (Pi : pi_form) (app : pi_app Pi)
    (Pi_subst : pi_subst Pi) : UU :=
    ∏ Γ Δ s A B f a, (app Γ A B f a) [[ s ]]tm =
                       transportf (λ X, cwf_tm X)
                         (pathsinv0 (cwf_pair_subst_ty_comm s A B a))
                         (app Δ (A [[ s ]]) (B [[ cwf_lift s A ]])
                            (transportf (λ X, cwf_tm X) (Pi_subst Γ Δ s A B)
                               (f [[ s ]]tm)) (a [[ s ]]tm)).

  Definition cwf_pi_structure : UU :=
    ∑ Pi : pi_form,
        ∑ lam : pi_lam Pi,
          ∑ app : pi_app Pi,
            pi_beta Pi lam app ×
              ∑ Pi_subst : pi_subst Pi,
              pi_eta Pi lam app Pi_subst
                × pi_subst_lam Pi lam Pi_subst
                × pi_subst_app Pi app Pi_subst.

End Pi_For_CwF.

(** Accessors for cwf_pi_structure *)

Section cwf_pi_accessors.

Coercion cwf_pi_Pi (C : cwf) (π : cwf_pi_structure C)
  : ∏ (Γ : pr1 C) (A : cwf_ty Γ) (B : cwf_ty (Γ & A)),
      cwf_ty Γ
  := pr1 π.

Definition cwf_pi_lam_map {C : cwf} {π : cwf_pi_structure C}
  {Γ : pr1 C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (b : cwf_tm B)
  : cwf_tm ((pr1 π) Γ A B)
  := pr12 π Γ A B b.

Definition cwf_pi_app_map {C : cwf} {π : cwf_pi_structure C}
  {Γ : pr1 C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (f : cwf_tm ((pr1 π) Γ A B))
  (a : cwf_tm A)
  : cwf_tm (B [[ ⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩ ]])
  := pr122 π Γ A B f a.

Definition cwf_pi_beta {C : cwf} {π : cwf_pi_structure C}
  {Γ : pr1 C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (b : cwf_tm B) (a : cwf_tm A)
  : cwf_pi_app_map (cwf_pi_lam_map b) a = b [[ ⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩ ]]tm
  := pr1 (pr222 π) Γ A B b a.

Definition cwf_pi_subst_eq {C : cwf} {π : cwf_pi_structure C}
  {Γ Δ : pr1 C} (s : Δ --> Γ)
  (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
  : ((pr1 π) Γ A B) [[ s ]] = (pr1 π) Δ (A [[ s ]]) (B [[ cwf_lift s A ]])
  := pr1 (pr2 (pr222 π)) Γ Δ s A B.

(** Uncurrying using the bundled structure *)
Definition cwf_pi_uncurry_map {C : cwf} {π : cwf_pi_structure C}
  {Γ : pr1 C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (f : cwf_tm ((pr1 π) Γ A B))
  : cwf_tm B
  := pi_uncurry C (pr1 π) (pr12 π) (pr122 π) (pr1 (pr2 (pr222 π))) A B f.

Definition cwf_pi_eta {C : cwf} {π : cwf_pi_structure C}
  {Γ : pr1 C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (f : cwf_tm ((pr1 π) Γ A B))
  : cwf_pi_lam_map (cwf_pi_uncurry_map f) = f
  := pr1 (pr2 (pr2 (pr222 π))) Γ A B f.

Definition cwf_pi_subst_lam {C : cwf} {π : cwf_pi_structure C}
  {Γ Δ : pr1 C} (s : Δ --> Γ)
  {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (b : cwf_tm B)
  : cwf_pi_lam_map b [[ s ]]tm =
      transportf (λ X, cwf_tm X)
        (pathsinv0 (cwf_pi_subst_eq s A B))
        (cwf_pi_lam_map (b [[ cwf_lift s A ]]tm))
  := pr1 (pr2 (pr2 (pr2 (pr222 π)))) Γ Δ s A B b.

Definition cwf_pi_subst_app {C : cwf} {π : cwf_pi_structure C}
  {Γ Δ : pr1 C} (s : Δ --> Γ)
  {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (f : cwf_tm ((pr1 π) Γ A B)) (a : cwf_tm A)
  : cwf_pi_app_map f a [[ s ]]tm =
      transportf (λ X, cwf_tm  X)
        (pathsinv0 (cwf_pair_subst_ty_comm s A B a))
        (cwf_pi_app_map
          (transportf (λ X, cwf_tm X) (cwf_pi_subst_eq s A B) (f [[ s ]]tm))
          (a [[ s ]]tm))
  := pr2 (pr2 (pr2 (pr2 (pr222 π)))) Γ Δ s A B f a.

End cwf_pi_accessors.


(**  Sigma Type in CwF  *)

Section Sigma_For_CwF.
  Context (CC : cwf).

  Definition sigma_form : UU :=
    ∏ (Γ : CC) (A : cwf_ty Γ) (B : cwf_ty (Γ & A)),
      cwf_ty Γ.

  Definition sigma_pi1 (Sig : sigma_form) : UU :=
    ∏ (Γ : CC) (A : cwf_ty Γ) (B : cwf_ty (Γ & A)),
      cwf_tm (Sig Γ A B) -> cwf_tm A.

  Definition sigma_pi2 (Sig : sigma_form)
  (pi1 : sigma_pi1 Sig) : UU :=
  ∏ (Γ : CC) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
    (p : cwf_tm (Sig Γ A B)),
    cwf_tm (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id (pi1 Γ A B p) ⟩⟩ ]]).

  Definition sigma_pair (Sig : sigma_form) : UU :=
    ∏ (Γ : CC) (A : cwf_ty Γ) (B : cwf_ty (Γ & A)),
      ∏ a : cwf_tm A,
        cwf_tm (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]])
        -> cwf_tm (Sig Γ A B).

  Definition sigma_beta1 (Sig : sigma_form) (pi1 : sigma_pi1 Sig)
    (pi2 : sigma_pi2 Sig pi1) (pair : sigma_pair Sig) : UU :=
    ∏ (Γ : CC) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
      (a : cwf_tm A) (b : cwf_tm (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]])),
      pi1 Γ A B (pair Γ A B a b) = a.

  Definition sigma_beta2 (Sig : sigma_form) (pi1 : sigma_pi1 Sig)
    (pi2 : sigma_pi2 Sig pi1) (pair : sigma_pair Sig)
    (beta1 : sigma_beta1 Sig pi1 pi2 pair) : UU :=
    ∏ (Γ : CC) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
      (a : cwf_tm A) (b : cwf_tm (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]])),
      transportf (λ X, cwf_tm X)
        (maponpaths (λ x, B [[ ⟨⟨ identity Γ , cwf_subst_tm_id x ⟩⟩ ]])
           (beta1 Γ A B a b)) (pi2 Γ A B (pair Γ A B a b)) = b.

  Definition sigma_eta (Sig : sigma_form) (pi1 : sigma_pi1 Sig)
    (pi2 : sigma_pi2 Sig pi1) (pair : sigma_pair Sig) : UU :=
    ∏ (Γ : CC) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
      (p : cwf_tm (Sig Γ A B)), pair Γ A B (pi1 Γ A B p) (pi2 Γ A B p) = p.

  Definition sigma_subst (Sig : sigma_form) : UU :=
    ∏ (Γ Δ : CC) (s : Δ --> Γ) (A : cwf_ty Γ) (B : cwf_ty (Γ & A)),
      (Sig Γ A B) [[ s ]] = Sig Δ (A [[ s ]]) (B [[ cwf_lift s A ]]).

  Definition sigma_subst_pi1 (Sig : sigma_form) (pi1 : sigma_pi1 Sig)
    (Sig_subst : sigma_subst Sig) : UU :=
    ∏ (Γ Δ : CC) (s : Δ --> Γ) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
      (p : cwf_tm (Sig Γ A B)),
      pi1 Δ (A [[ s ]]) (B [[ cwf_lift s A ]])
        (transportf (λ X, cwf_tm X) (Sig_subst Γ Δ s A B) (p [[ s ]]tm)) =
        (pi1 Γ A B p) [[ s ]]tm.

  Definition sigma_subst_pi2 (Sig : sigma_form) (pi1 : sigma_pi1 Sig)
    (pi2 : sigma_pi2 Sig pi1) (Sig_subst : sigma_subst Sig)
    (pi1_subst : sigma_subst_pi1 Sig pi1 Sig_subst) : UU :=
    ∏ (Γ Δ : CC) (s : Δ --> Γ) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
      (p : cwf_tm (Sig Γ A B)),
      let p' : cwf_tm (Sig Δ (A [[ s ]]) (B [[ cwf_lift s A ]])) :=
        transportf (λ X, cwf_tm X) (Sig_subst Γ Δ s A B) (p [[ s ]]tm) in
      let a  : cwf_tm A := pi1 Γ A B p in
      let a' : cwf_tm (A [[ s ]]) := pi1 Δ (A [[ s ]]) (B [[ cwf_lift s A ]]) p' in
      transportf (λ X, cwf_tm X)
        (maponpaths
           (λ x, (B [[ cwf_lift s A ]]) [[ ⟨⟨ identity Δ , cwf_subst_tm_id x ⟩⟩ ]])
           (pathsinv0 (pi1_subst Γ Δ s A B p)))
        (transportf (λ X, cwf_tm X)
           (cwf_pair_subst_ty_comm s A B a)
           ((pi2 Γ A B p) [[ s ]]tm)) = pi2 Δ (A [[ s ]]) (B [[ cwf_lift s A ]]) p'.

  Definition sigma_subst_pair (Sig : sigma_form) (pair : sigma_pair Sig)
    (Sig_subst : sigma_subst Sig) : UU :=
    ∏ (Γ Δ : CC) (s : Δ --> Γ) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
      (a : cwf_tm A) (b : cwf_tm (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]])),
      transportf (λ X, cwf_tm X) (Sig_subst Γ Δ s A B)
        ((pair Γ A B a b) [[ s ]]tm) =
        pair Δ (A [[ s ]]) (B [[ cwf_lift s A ]]) (a [[ s ]]tm)
          (transportf (λ X, cwf_tm X) (cwf_pair_subst_ty_comm s A B a)
             (b [[ s ]]tm)).

  Definition cwf_sigma_structure : UU :=
  ∑ Sig : sigma_form,
    ∑ pi1 : sigma_pi1 Sig,
      ∑ pi2 : sigma_pi2 Sig pi1,
        ∑ pair : sigma_pair Sig,
          (∑ beta1 : sigma_beta1 Sig pi1 pi2 pair,
             ∑ beta2 : sigma_beta2 Sig pi1 pi2 pair beta1,
               sigma_eta Sig pi1 pi2 pair) ×
          ∑ Sig_subst : sigma_subst Sig,
            ∑ pi1_subst : sigma_subst_pi1 Sig pi1 Sig_subst,
              sigma_subst_pi2 Sig pi1 pi2 Sig_subst pi1_subst
              × sigma_subst_pair Sig pair Sig_subst.

End Sigma_For_CwF.

(** Accessors for cwf_sigma_structure *)

Section cwf_sigma_accessors.

Coercion cwf_sigma_Sig (C : cwf) (σ : cwf_sigma_structure C)
  : ∏ (Γ : pr1 C) (A : cwf_ty Γ) (B : cwf_ty (Γ & A)),
      cwf_ty Γ
  := pr1 σ.

Definition cwf_sigma_pi1_map {C : cwf} {σ : cwf_sigma_structure C}
  {Γ : pr1 C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (p : cwf_tm ((pr1 σ) Γ A B))
  : cwf_tm A
  := pr12 σ Γ A B p.

Definition cwf_sigma_pi2_map {C : cwf} {σ : cwf_sigma_structure C}
  {Γ : pr1 C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (p : cwf_tm ((pr1 σ) Γ A B))
  : cwf_tm (B [[ ⟨⟨ identity Γ, cwf_subst_tm_id (cwf_sigma_pi1_map p) ⟩⟩ ]])
  := pr122 σ Γ A B p.

Definition cwf_sigma_pair_map {C : cwf} {σ : cwf_sigma_structure C}
  {Γ : pr1 C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (a : cwf_tm  A)
  (b : cwf_tm (B [[ ⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩ ]]))
  : cwf_tm ((pr1 σ) Γ A B)
  := pr1 (pr222 σ) Γ A B a b.

Definition cwf_sigma_beta1 {C : cwf} {σ : cwf_sigma_structure C}
  {Γ : pr1 C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (a : cwf_tm A)
  (b : cwf_tm  (B [[ ⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩ ]]))
  : cwf_sigma_pi1_map (cwf_sigma_pair_map a b) = a
  := pr1 (pr1 (pr2 (pr222 σ))) Γ A B a b.

Definition cwf_sigma_beta2 {C : cwf} {σ : cwf_sigma_structure C}
  {Γ : pr1 C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (a : cwf_tm A)
  (b : cwf_tm (B [[ ⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩ ]]))
  : transportf (λ X, cwf_tm X)
      (maponpaths (λ x, B [[ ⟨⟨ identity Γ, cwf_subst_tm_id x ⟩⟩ ]])
        (cwf_sigma_beta1 a b))
      (cwf_sigma_pi2_map (cwf_sigma_pair_map a b))
    = b
  := pr1 (pr2 (pr1 (pr2 (pr222 σ)))) Γ A B a b.

Definition cwf_sigma_eta {C : cwf} {σ : cwf_sigma_structure C}
  {Γ : pr1 C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (p : cwf_tm ((pr1 σ) Γ A B))
  : cwf_sigma_pair_map (cwf_sigma_pi1_map p) (cwf_sigma_pi2_map p) = p
  := pr2 (pr2 (pr1 (pr2 (pr222 σ)))) Γ A B p.

Definition cwf_sigma_subst_eq {C : cwf} {σ : cwf_sigma_structure C}
  {Γ Δ : pr1 C} (s : Δ --> Γ)
  (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
  : ((pr1 σ) Γ A B) [[ s ]] = (pr1 σ) Δ (A [[ s ]]) (B [[ cwf_lift s A ]])
  := pr1 (pr2 (pr2 (pr222 σ))) Γ Δ s A B.

Definition cwf_sigma_subst_pi1 {C : cwf} {σ : cwf_sigma_structure C}
  {Γ Δ : pr1 C} (s : Δ --> Γ)
  {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (p : cwf_tm ((pr1 σ) Γ A B))
  : cwf_sigma_pi1_map
      (transportf (λ X, cwf_tm X) (cwf_sigma_subst_eq s A B) (p [[ s ]]tm))
    = cwf_sigma_pi1_map p [[ s ]]tm
  := pr1 (pr2 (pr2 (pr2 (pr222 σ)))) Γ Δ s A B p.

Definition cwf_sigma_subst_pi2 {C : cwf} {σ : cwf_sigma_structure C}
  {Γ Δ : pr1 C} (s : Δ --> Γ)
  {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (p : cwf_tm ((pr1 σ) Γ A B))
  : let T   := cwf_t (pr1 C) in
    let p'  := transportf (λ X, cwf_tm X) (cwf_sigma_subst_eq s A B) (p [[ s ]]tm) in
    transportf (λ X, cwf_tm X)
      (maponpaths
         (λ x, (B [[ cwf_lift s A ]]) [[ ⟨⟨ identity Δ, cwf_subst_tm_id x ⟩⟩ ]])
         (pathsinv0 (cwf_sigma_subst_pi1 s p)))
      (transportf (λ X, cwf_tm X)
         (cwf_pair_subst_ty_comm s A B (cwf_sigma_pi1_map p))
         (cwf_sigma_pi2_map p [[ s ]]tm))
    = cwf_sigma_pi2_map p'
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr222 σ))))) Γ Δ s A B p.

Definition cwf_sigma_subst_pair {C : cwf} {σ : cwf_sigma_structure C}
  {Γ Δ : pr1 C} (s : Δ --> Γ)
  {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
  (a : cwf_tm A)
  (b : cwf_tm (B [[ ⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩ ]]))
  : transportf (λ X, cwf_tm X)
      (cwf_sigma_subst_eq s A B)
      (cwf_sigma_pair_map a b [[ s ]]tm)
    = cwf_sigma_pair_map
        (a [[ s ]]tm)
        (transportf (λ X, cwf_tm X)
           (cwf_pair_subst_ty_comm s A B a)
           (b [[ s ]]tm))
  := pr2 (pr2 (pr2 (pr2 (pr2 (pr222 σ))))) Γ Δ s A B a b.

End cwf_sigma_accessors.


(** Democracy in CwFs  *)

Definition cwf_democracy_data (C : cwf) : UU :=
  ∏ Γ : pr1  C, ∑ Γ' : cwf_ty [], z_iso Γ ([] & Γ').

Close Scope cwf.
