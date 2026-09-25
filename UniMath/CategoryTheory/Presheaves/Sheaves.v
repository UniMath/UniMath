(**

 Sheaves and dependent sheaves

 In this file, we define two of the key ingredients for the sheaf model of dependent
 type theory. Specifically, we define when a presheaf is a sheaf, and when a dependent
 presheaf is a dependent sheaf. The first notion is standard and we follow the usual
 definition in the literature. The second notion (dependent sheaf) is less standard. The
 key idea is that a dependent sheaf over a sheaf `Γ` corresponds to a sheaf over the
 category of elements for `Γ`. In the sheaf model of type theory, contexts are interpreted
 as sheaves and types as dependent sheaves.

 Content
 1. Matching families
 2. Amalgamations of matching families
 3. Sheaves
 4. Dependent matching families
 5. Amalgamations for dependent matching families
 6. Dependent sheaves
 7. The category of sheaves
 8. The displayed category of dependent sheaves

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.FullSubDispCat.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.Sites.

Local Open Scope cat.

(** * 1. Matching families *)
Definition matching_family
           {C : site}
           (F : C^op ⟶ HSET)
           {x : C}
           (ω : sieve x)
  : UU
  := ∑ (z : ∏ (y : C) (f : y --> x), ω y f → (F y : hSet)),
     ∏ (y₁ y₂ : C)
       (f₁ : y₁ --> x)
       (f₂ : y₂ --> x)
       (g : y₁ --> y₂)
       (p : g · f₂ = f₁)
       (q₁ : ω y₁ f₁)
       (q₂ : ω y₂ f₂),
     #F g (z y₂ f₂ q₂) = z y₁ f₁ q₁.

Definition make_matching_family
           {C : site}
           {F : C^op ⟶ HSET}
           {x : C}
           {ω : sieve x}
           (z : ∏ (y : C) (f : y --> x), ω y f → (F y : hSet))
           (Hz : ∏ (y₁ y₂ : C)
                   (f₁ : y₁ --> x)
                   (f₂ : y₂ --> x)
                   (g : y₁ --> y₂)
                   (p : g · f₂ = f₁)
                   (q₁ : ω y₁ f₁)
                   (q₂ : ω y₂ f₂),
                 #F g (z y₂ f₂ q₂) = z y₁ f₁ q₁)
  : matching_family F ω
  := z ,, Hz.

Definition matching_family_fam
           {C : site}
           {F : C^op ⟶ HSET}
           {x : C}
           {ω : sieve x}
           (z : matching_family F ω)
           (y : C)
           (f : y --> x)
           (p : ω y f)
  : (F y : hSet)
  := pr1 z y f p.

Coercion matching_family_fam : matching_family >-> Funclass.

Proposition matching_family_restr
            {C : site}
            {F : C^op ⟶ HSET}
            {x : C}
            {ω : sieve x}
            (z : matching_family F ω)
            {y₁ y₂ : C}
            {f₁ : y₁ --> x}
            {f₂ : y₂ --> x}
            {g : y₁ --> y₂}
            (p : g · f₂ = f₁)
            (q₁ : ω y₁ f₁)
            (q₂ : ω y₂ f₂)
  : #F g (z y₂ f₂ q₂) = z y₁ f₁ q₁.
Proof.
  exact (pr2 z y₁ y₂ f₁ f₂ g p q₁ q₂).
Defined.

Proposition matching_family_fam_fun_eq
            {C : site}
            {Γ : C^op ⟶ HSET}
            {x : C}
            {ω : sieve x}
            {z : matching_family Γ ω}
            {y : C}
            {f₁ f₂ : y --> x}
            (p : f₁ = f₂)
            (q : ω y f₁)
            (q' : ω y f₂)
  : z y f₁ q = z y f₂ q'.
Proof.
  induction p.
  apply maponpaths.
  apply propproperty.
Qed.

Definition nat_trans_matching_family
           {C : site}
           {Γ Δ : C^op ⟶ HSET}
           (s : Γ ⟹ Δ)
           {x : C}
           {ω : sieve x}
           (z : matching_family Γ ω)
  : matching_family Δ ω.
Proof.
  use make_matching_family.
  - exact (λ y f p, s y (z y f p)).
  - abstract
      (intros y₁ y₂ f₁ f₂ g p q₁ q₂ ;
       induction p ; cbn ;
       refine (eqtohomot (!(nat_trans_ax s _ _ g)) _ @ _) ;
       cbn ;
       apply maponpaths ;
       apply matching_family_restr ;
       apply idpath).
Defined.

(** * 2. Amalgamations of matching families *)
Definition amalgamation_law
           {C : site}
           {F : C^op ⟶ HSET}
           {x : C}
           {ω : sieve x}
           (z : matching_family F ω)
           (a : (F x : hSet))
  : UU
  := ∏ (y : C) (f : y --> x) (p : ω y f), #F f a = z y f p.

Definition amalgamation
           {C : site}
           {F : C^op ⟶ HSET}
           {x : C}
           {ω : sieve x}
           (z : matching_family F ω)
  : UU
  := ∑ (a : (F x : hSet)), amalgamation_law z a.

Definition make_amalgamation
           {C : site}
           {F : C^op ⟶ HSET}
           {x : C}
           {ω : sieve x}
           {z : matching_family F ω}
           (a : (F x : hSet))
           (H : amalgamation_law z a)
  : amalgamation z
  := a ,, H.

Coercion amalgamation_el
         {C : site}
         {F : C^op ⟶ HSET}
         {x : C}
         {ω : sieve x}
         {z : matching_family F ω}
         (a : amalgamation z)
  : (F x : hSet)
  := pr1 a.

Proposition amalgamation_restr
            {C : site}
            {F : C^op ⟶ HSET}
            {x : C}
            {ω : sieve x}
            {z : matching_family F ω}
            (a : amalgamation z)
            {y : C}
            (f : y --> x)
            (p : ω y f)
  : #F f a = pr1 z y f p.
Proof.
  exact (pr2 a y f p).
Defined.

Proposition amalgamation_eq
            {C : site}
            {F : C^op ⟶ HSET}
            {x : C}
            {ω : sieve x}
            {z : matching_family F ω}
            {a₁ a₂ : amalgamation z}
            (p : pr1 a₁ = a₂)
  : a₁ = a₂.
Proof.
  use subtypePath.
  {
    intro.
    repeat (use impred ; intro).
    apply setproperty.
  }
  exact p.
Qed.

(** * 3. Sheaves *)
Definition is_sheaf
           {C : site}
           (Γ : C^op ⟶ HSET)
  : UU
  := ∏ (x : C) (ω : sieve x) (H : C x ω) (z : matching_family Γ ω),
     iscontr (amalgamation z).

Proposition isaprop_is_sheaf
            {C : site}
            (Γ : C^op ⟶ HSET)
  : isaprop (is_sheaf Γ).
Proof.
  repeat (use impred ; intro).
  apply isapropiscontr.
Qed.

Definition sheaf_amalgamation
           {C : site}
           {Γ : C^op ⟶ HSET}
           (HΓ : is_sheaf Γ)
           {x : C}
           {ω : sieve x}
           (H : C x ω)
           (z : matching_family Γ ω)
  : amalgamation z
  := pr1 (HΓ x ω H z).

Definition sheaf_amalgamation_unique
           {C : site}
           {Γ : C^op ⟶ HSET}
           (HΓ : is_sheaf Γ)
           {x : C}
           {ω : sieve x}
           (H : C x ω)
           {z : matching_family Γ ω}
           {a₁ a₂ : (Γ x : hSet)}
           (H₁ : ∏ (y : C) (f : y --> x) (p : ω y f), #Γ f a₁ = pr1 z y f p)
           (H₂ : ∏ (y : C) (f : y --> x) (p : ω y f), #Γ f a₂ = pr1 z y f p)
  : a₁ = a₂.
Proof.
  exact (maponpaths
           pr1
           (proofirrelevance _ (isapropifcontr (HΓ x ω H z)) (a₁ ,, H₁) (a₂ ,, H₂))).
Qed.

(** * 4. Dependent matching families *)
Definition matching_family_dep
           {C : site}
           {Γ : C^op ⟶ HSET}
           (A : dep_psh Γ)
           {x : C}
           {ω : sieve x}
           (z : matching_family Γ ω)
  : UU
  := ∑ (zz : ∏ (y : C) (f : y --> x) (p : ω y f), A y (z y f p)),
     ∏ (y₁ y₂ : C)
       (f₁ : y₁ --> x)
       (f₂ : y₂ --> x)
       (g : y₁ --> y₂)
       (p : g · f₂ = f₁)
       (q₁ : ω y₁ f₁)
       (q₂ : ω y₂ f₂),
     #d A g (matching_family_restr z p q₁ q₂) (zz y₂ f₂ q₂)
     =
     zz y₁ f₁ q₁.

Definition make_matching_family_dep
           {C : site}
           {Γ : C^op ⟶ HSET}
           (A : dep_psh Γ)
           {x : C}
           {ω : sieve x}
           (z : matching_family Γ ω)
           (zz : ∏ (y : C) (f : y --> x) (p : ω y f), A y (z y f p))
           (Hzz : ∏ (y₁ y₂ : C)
                    (f₁ : y₁ --> x)
                    (f₂ : y₂ --> x)
                    (g : y₁ --> y₂)
                    (p : g · f₂ = f₁)
                    (q₁ : ω y₁ f₁)
                    (q₂ : ω y₂ f₂),
                  #d A g (matching_family_restr z p q₁ q₂) (zz y₂ f₂ q₂)
                  =
                  zz y₁ f₁ q₁)
  : matching_family_dep A z
  := zz ,, Hzz.

Definition matching_family_dep_fam
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ ω}
           (zz : matching_family_dep A z)
           (y : C)
           (f : y --> x)
           (p : ω y f)
  : A y (z y f p)
  := pr1 zz y f p.

Coercion matching_family_dep_fam : matching_family_dep >-> Funclass.

Proposition matching_family_dep_restr
            {C : site}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            {x : C}
            {ω : sieve x}
            {z : matching_family Γ ω}
            (zz : matching_family_dep A z)
            {y₁ y₂ : C}
            {f₁ : y₁ --> x}
            {f₂ : y₂ --> x}
            {g : y₁ --> y₂}
            (p : g · f₂ = f₁)
            (q₁ : ω y₁ f₁)
            (q₂ : ω y₂ f₂)
  : #d A g (matching_family_restr z p q₁ q₂) (zz y₂ f₂ q₂)
    =
    zz y₁ f₁ q₁.
Proof.
  exact (pr2 zz y₁ y₂ f₁ f₂ g p q₁ q₂).
Defined.

Lemma matching_family_dep_el_eq_lem
      {C : site}
      {Γ : C^op ⟶ HSET}
      {x : C}
      {ω : sieve x}
      (z : matching_family Γ ω)
      (y : C)
      (f : y --> x)
      (p p' : ω y f)
  : #Γ (identity y) (z y f p') = z y f p.
Proof.
  assert (p = p') as ->.
  {
    apply propproperty.
  }
  exact (eqtohomot (functor_id Γ _) _).
Qed.

Proposition matching_family_dep_el_eq
            {C : site}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            {x : C}
            {ω : sieve x}
            {z : matching_family Γ ω}
            (zz : matching_family_dep A z)
            (y : C)
            (f : y --> x)
            (p p' : ω y f)
  : zz y f p
    =
    #d A (identity _) (matching_family_dep_el_eq_lem z y f p p') (zz y f p').
Proof.
  assert (p = p') as ->.
  {
    apply propproperty.
  }
  refine (!_).
  apply dep_psh_mor_id.
Qed.

Lemma matching_family_dep_fam_fun_eq_lem
      {C : site}
      {Γ : C^op ⟶ HSET}
      {x : C}
      {ω : sieve x}
      {z : matching_family Γ ω}
      {y : C}
      {f₁ f₂ : y --> x}
      (p : f₁ = f₂)
      (q : ω y f₁)
  : #Γ (identity y) (z y f₂ (#ω ω (identity y) (id_left f₁ @ p) q)) = z y f₁ q.
Proof.
  induction p.
  refine (eqtohomot (functor_id Γ _) _ @ _).
  cbn.
  apply maponpaths.
  apply propproperty.
Qed.

Proposition matching_family_dep_fam_fun_eq
            {C : site}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            {x : C}
            {ω : sieve x}
            {z : matching_family Γ ω}
            (zz : matching_family_dep A z)
            {y : C}
            {f₁ f₂ : y --> x}
            (p : f₁ = f₂)
            (q : ω y f₁)
  : zz y f₁ q
    =
    #d A (identity _)
         (matching_family_dep_fam_fun_eq_lem p q)
         (zz y f₂ (#ω ω (identity _) (id_left _ @ p) q)).
Proof.
  induction p.
  etrans.
  {
    use matching_family_dep_el_eq.
    exact (#ω ω (identity y) (id_left f₁ @ idpath f₁) q).
  }
  apply dep_psh_mor_path_eq.
  apply idpath.
Qed.

Definition dep_psh_nat_trans_on_matching_family
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A B : dep_psh Γ}
           (τ : dep_psh_nat_trans A B (nat_trans_id Γ))
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ ω}
           (zz : matching_family_dep A z)
  : matching_family_dep B z.
Proof.
  use make_matching_family_dep.
  - exact (λ y f p, τ _ _ (zz y f p)).
  - abstract
      (cbn ;
       intros y₁ y₂ f₁ f₂ g p q₁ q₂ ;
       refine (!(dep_psh_nat_trans_ax τ _ (matching_family_restr z p _ _) _ _) @ _) ;
       apply maponpaths ;
       apply matching_family_dep_restr).
Defined.

(** * 5. Amalgamations for dependent matching families *)
Definition amalgamation_dep_law
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ ω}
           {a : amalgamation z}
           (zz : matching_family_dep A z)
           (aa : A x a)
  : UU
  := ∏ (y : C) (f : y --> x) (p : ω y f),
     #d A f (amalgamation_restr a f p) aa
     =
     zz y f p.

Definition amalgamation_dep
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ ω}
           (a : amalgamation z)
           (zz : matching_family_dep A z)
  : UU
  := ∑ (aa : A x a), amalgamation_dep_law zz aa.

Definition make_amalgamation_dep
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ ω}
           {a : amalgamation z}
           {zz : matching_family_dep A z}
           (aa : A x a)
           (H : amalgamation_dep_law zz aa)
  : amalgamation_dep a zz
  := aa ,, H.

Coercion amalgamation_dep_el
         {C : site}
         {Γ : C^op ⟶ HSET}
         {A : dep_psh Γ}
         {x : C}
         {ω : sieve x}
         {z : matching_family Γ ω}
         {a : amalgamation z}
         {zz : matching_family_dep A z}
         (aa : amalgamation_dep a zz)
  : A x a
  := pr1 aa.

Proposition amalgamation_dep_restr
            {C : site}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            {x : C}
            {ω : sieve x}
            {z : matching_family Γ ω}
            {a : amalgamation z}
            {zz : matching_family_dep A z}
            (aa : amalgamation_dep a zz)
            {y : C}
            (f : y --> x)
            (p : ω y f)
  : #d A f (amalgamation_restr a f p) aa
    =
    zz y f p.
Proof.
  exact (pr2 aa y f p).
Defined.

Proposition amalgamation_dep_eq
            {C : site}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            {x : C}
            {ω : sieve x}
            {z : matching_family Γ ω}
            {a : amalgamation z}
            {zz : matching_family_dep A z}
            {aa₁ aa₂ : amalgamation_dep a zz}
            (p : pr1 aa₁ = aa₂)
  : aa₁ = aa₂.
Proof.
  use subtypePath.
  {
    intro.
    repeat (use impred ; intro).
    apply setproperty.
  }
  exact p.
Qed.

(** * 6. Dependent sheaves *)
Definition is_dep_sheaf
           {C : site}
           {Γ : C^op ⟶ HSET}
           (A : dep_psh Γ)
  : UU
  := ∏ (x : C)
       (ω : sieve x)
       (H : C x ω)
       (z : matching_family Γ ω)
       (a : amalgamation z)
       (zz : matching_family_dep A z),
     iscontr (amalgamation_dep a zz).

Proposition isaprop_is_dep_sheaf
            {C : site}
            {Γ : C^op ⟶ HSET}
            (A : dep_psh Γ)
  : isaprop (is_dep_sheaf A).
Proof.
  repeat (use impred ; intro).
  apply isapropiscontr.
Qed.

Definition dep_sheaf_amalgamation_dep
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           (HA : is_dep_sheaf A)
           {x : C}
           {ω : sieve x}
           (H : C x ω)
           (z : matching_family Γ ω)
           (a : amalgamation z)
           (zz : matching_family_dep A z)
  : amalgamation_dep a zz
  := pr1 (HA x ω H z a zz).

Definition dep_sheaf_amalgamation
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           (HA : is_dep_sheaf A)
           {x : C}
           {ω : sieve x}
           (H : C x ω)
           (z : matching_family Γ ω)
           (a : amalgamation z)
           (zz : matching_family_dep A z)
  : A x a
  := pr1 (HA x ω H z a zz).

Proposition dep_sheaf_amalgamation_restr
            {C : site}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            (HA : is_dep_sheaf A)
            {x : C}
            {ω : sieve x}
            (H : C x ω)
            (z : matching_family Γ ω)
            (a : amalgamation z)
            (zz : matching_family_dep A z)
            {y : C}
            {f : y --> x}
            (p : ω y f)
  : #d A f (amalgamation_restr a f p) (dep_sheaf_amalgamation HA H z a zz)
    =
    zz y f p.
Proof.
  exact (pr21 (HA x ω H z a zz) y f p).
Defined.

Proposition dep_sheaf_amalgamation_restr'
            {C : site}
            {Γ : C^op ⟶ HSET}
            {A : dep_psh Γ}
            (HA : is_dep_sheaf A)
            {x : C}
            {ω : sieve x}
            (H : C x ω)
            (z : matching_family Γ ω)
            (a : amalgamation z)
            (zz : matching_family_dep A z)
            {y : C}
            {f : y --> x}
            (p : ω y f)
            (q : #Γ f a = z y f p)
  : #d A f q (dep_sheaf_amalgamation HA H z a zz)
    =
    zz y f p.
Proof.
  refine (_ @ dep_sheaf_amalgamation_restr HA H z a zz p).
  use dep_psh_mor_path_eq.
  apply idpath.
Qed.

Definition dep_sheaf_amalgamation_unique
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           (HA : is_dep_sheaf A)
           {x : C}
           {ω : sieve x}
           (H : C x ω)
           {z : matching_family Γ ω}
           {a : amalgamation z}
           {zz : matching_family_dep A z}
           {aa₁ aa₂ : A x a}
           (H₁ : ∏ (y : C) (f : y --> x) (p : ω y f),
                 #d A f (amalgamation_restr a f p) aa₁
                 =
                 zz y f p)
           (H₂ : ∏ (y : C) (f : y --> x) (p : ω y f),
                 #d A f (amalgamation_restr a f p) aa₂
                 =
                 zz y f p)
  : aa₁ = aa₂.
Proof.
  exact (maponpaths
           pr1
           (proofirrelevance
              _
              (isapropifcontr (HA x ω H z a zz))
              (aa₁ ,, H₁)
              (aa₂ ,, H₂))).
Qed.

Definition dep_sheaf_amalgamation_unique'
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           (HA : is_dep_sheaf A)
           {x : C}
           {ω : sieve x}
           (H : C x ω)
           {z : matching_family Γ ω}
           {a : amalgamation z}
           {zz : matching_family_dep A z}
           {aa : A x a}
           (H₁ : ∏ (y : C) (f : y --> x) (p : ω y f),
                 #d A f (amalgamation_restr a f p) aa
                 =
                 zz y f p)
  : aa = dep_sheaf_amalgamation HA H z a zz.
Proof.
  use (dep_sheaf_amalgamation_unique HA H).
  - exact zz.
  - exact H₁.
  - intros y f p.
    exact (dep_sheaf_amalgamation_restr HA H z a zz p).
Qed.

(** * 7. The category of sheaves *)
Definition cat_of_sheaves
           (C : site)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (full_subcat (PreShv C) is_sheaf).
  - abstract
      (use is_univalent_full_subcat ;
       [ | intro ; apply isaprop_is_sheaf ] ;
    use is_univalent_functor_category ;
       exact is_univalent_HSET).
Defined.

Definition sheaf
           (C : site)
  : UU
  := cat_of_sheaves C.

Coercion sheaf_to_presheaf
         {C : site}
         (Γ : sheaf C)
  : C^op ⟶ HSET
  := pr1 Γ.

Proposition is_sheaf_sheaf
            {C : site}
            (Γ : sheaf C)
  : is_sheaf Γ.
Proof.
  exact (pr2 Γ).
Defined.

Definition make_sheaf
           {C : site}
           (Γ : C^op ⟶ HSET)
           (HΓ : is_sheaf Γ)
  : sheaf C
  := Γ ,, HΓ.

Definition sheaf_nat_trans
           {C : site}
           (Γ₁ Γ₂ : sheaf C)
  := Γ₁ --> Γ₂.

Coercion nat_trans_of_sheaf_nat_trans
         {C : site}
         {Γ₁ Γ₂ : sheaf C}
         (τ : sheaf_nat_trans Γ₁ Γ₂)
  : Γ₁ ⟹ Γ₂
  := pr1 τ.

Definition make_sheaf_nat_trans
           {C : site}
           {Γ₁ Γ₂ : sheaf C}
           (τ : Γ₁ ⟹ Γ₂)
  : sheaf_nat_trans Γ₁ Γ₂
  := τ ,, tt.

Proposition sheaf_nat_trans_eq
            {C : site}
            {Γ₁ Γ₂ : sheaf C}
            {τ₁ τ₂ : sheaf_nat_trans Γ₁ Γ₂}
            (p : (τ₁ : _ ⟹ _) = τ₂)
  : τ₁ = τ₂.
Proof.
  use subtypePath.
  {
    intro.
    apply isapropunit.
  }
  exact p.
Qed.

Proposition from_sheaf_nat_trans_eq
            {C : site}
            {Γ₁ Γ₂ : sheaf C}
            {τ₁ τ₂ : sheaf_nat_trans Γ₁ Γ₂}
            (p : τ₁ = τ₂)
            {x : C}
            (xx : (Γ₁ x : hSet))
  : τ₁ x xx = τ₂ x xx.
Proof.
  induction p.
  apply idpath.
Qed.

Definition sheaf_incl
           (C : site)
  : cat_of_sheaves C ⟶ PreShv C
  := pr1_category _.

(** * 8. The displayed category of dependent sheaves *)
Definition disp_cat_of_dep_sheaves
           (C : site)
  : disp_univalent_category (cat_of_sheaves C).
Proof.
  use make_disp_univalent_category.
  - use full_sub_disp_cat.
    + exact (disp_cat_dep_psh C).
    + exact (λ Γ HΓ A, is_dep_sheaf A).
  - abstract
      (use is_univalent_full_sub_disp_cat ;
       [ apply is_univalent_disp_disp_cat_dep_psh | ] ;
       intros ;
       apply isaprop_is_dep_sheaf).
Defined.

Definition dep_sheaf
           {C : site}
           (Γ : sheaf C)
  : UU
  := disp_cat_of_dep_sheaves C Γ.

Coercion dep_sheaf_to_dep_psh
         {C : site}
         {Γ : sheaf C}
         (A : dep_sheaf Γ)
  : dep_psh Γ
  := pr1 A.

Proposition is_dep_sheaf_dep_sheaf
            {C : site}
            {Γ : sheaf C}
            (A : dep_sheaf Γ)
  : is_dep_sheaf A.
Proof.
  exact (pr2 A).
Defined.

Definition make_dep_sheaf
           {C : site}
           {Γ : sheaf C}
           (A : dep_psh Γ)
           (HA : is_dep_sheaf A)
  : dep_sheaf Γ
  := A ,, HA.

Definition dep_sheaf_nat_trans
           {C : site}
           {Γ₁ Γ₂ : sheaf C}
           (A₁ : dep_sheaf Γ₁)
           (A₂ : dep_sheaf Γ₂)
           (s : sheaf_nat_trans Γ₁ Γ₂)
  : UU
  := A₁ -->[ s ] A₂.

Coercion dep_sheaf_nat_trans_to_dep_psh_nat_trans
         {C : site}
         {Γ₁ Γ₂ : sheaf C}
         {A₁ : dep_sheaf Γ₁}
         {A₂ : dep_sheaf Γ₂}
         {s : sheaf_nat_trans Γ₁ Γ₂}
         (τ : dep_sheaf_nat_trans A₁ A₂ s)
  : dep_psh_nat_trans A₁ A₂ s
  := τ.

Definition make_dep_sheaf_nat_trans
           {C : site}
           {Γ₁ Γ₂ : sheaf C}
           {A₁ : dep_sheaf Γ₁}
           {A₂ : dep_sheaf Γ₂}
           {s : sheaf_nat_trans Γ₁ Γ₂}
           (τ : dep_psh_nat_trans A₁ A₂ s)
  : dep_sheaf_nat_trans A₁ A₂ s
  := τ.

Proposition dep_sheaf_nat_trans_eq
            {C : site}
            {Γ₁ Γ₂ : sheaf C}
            {A₁ : dep_sheaf Γ₁}
            {A₂ : dep_sheaf Γ₂}
            {s : sheaf_nat_trans Γ₁ Γ₂}
            {τ₁ τ₂ : dep_sheaf_nat_trans A₁ A₂ s}
            (p : ∏ (x : C)
                   (xx : (Γ₁ x : hSet))
                   (a : A₁ x xx),
                 τ₁ x xx a = τ₂ x xx a)
  : τ₁ = τ₂.
Proof.
  use dep_psh_nat_trans_eq.
  exact p.
Qed.

Proposition dep_sheaf_fiber_comp
            {C : site}
            {Γ : sheaf C}
            {A₁ A₂ A₃ : dep_sheaf Γ}
            (τ₁ : (disp_cat_of_dep_sheaves C)[{ Γ }] ⟦ A₁ , A₂ ⟧)
            (τ₂ : (disp_cat_of_dep_sheaves C)[{ Γ }] ⟦ A₂ , A₃ ⟧)
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
  etrans.
  {
    exact (maponpaths
             (λ (ζ : dep_psh_nat_trans _ _ _), ζ x xx a)
             (transportf_full_sub_disp_cat
                (disp_cat_dep_psh C)
                is_sheaf
                (λ Γ HΓ A, is_dep_sheaf A)
                (id_right _)
                (dep_psh_comp_nat_trans τ₁ τ₂))).
  }
  etrans.
  {
    exact (transportf_dep_psh_nat_trans
             C
             (maponpaths pr1 (id_right (identity Γ)))
             (dep_psh_comp_nat_trans τ₁ τ₂)
             x
             xx
             a).
  }
  apply (transportf_set (A₃ x)).
  apply setproperty.
Qed.

Definition dep_sheaf_incl
           (C : site)
  : disp_functor
      (sheaf_incl C)
      (disp_cat_of_dep_sheaves C)
      (disp_cat_dep_psh C)
  := full_sub_disp_cat_incl _ _ _.

Proposition fiber_functor_dep_sheaf_incl
            {C : site}
            {Γ : sheaf C}
            {A B : dep_sheaf Γ}
            (τ : dep_psh_nat_trans A B (nat_trans_id _))
  : #(fiber_functor (dep_sheaf_incl C) Γ) τ = τ.
Proof.
  use dep_psh_nat_trans_eq ; cbn.
  intros x xx a.
  rewrite transportf_dep_psh_nat_trans.
  apply (transportf_set (B x)).
  apply setproperty.
Qed.

Proposition fiber_functor_dep_sheaf_incl_pt
            {C : site}
            {Γ : sheaf C}
            {A B : dep_sheaf Γ}
            (τ : dep_psh_nat_trans A B (nat_trans_id _))
            {x : C}
            {xx : (Γ x : hSet)}
            (a : A x xx)
  : (#(fiber_functor (dep_sheaf_incl C) Γ) τ : dep_psh_nat_trans _ _ _) x xx a
    =
    τ x xx a.
Proof.
  cbn.
  rewrite transportf_dep_psh_nat_trans.
  apply (transportf_set (B x)).
  apply setproperty.
Qed.
