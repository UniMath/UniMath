(**

 Dependent presheaves

 If we have a category `C`, then the presheaves over `C` form a model of extensional
 Martin-Löf type theory. Contexts are presheaves and there are two equivalent ways
 to describe types in this model
 1. A type in a context `Γ` is a presheaf `A` over `C` with a natural transformation
    `τ : A ⟹ Γ`.
 2. Types in a context `Γ` are presheaves over the category of elements for `Γ`.

 The first method is an instance of a general construction: if we have a category `C`
 with finite limits, then the arrow category for `C` gives a comprehension category
 where the comprehension functor is the identity. However, often the presheaf model
 is presented in a different way, namely the second, because it is more convenient
 to use. The equivalence of these two presentation is shown in `elems_slice_equiv.v`.

 in this file, we provide an interface for using dependent presheaves by providing
 convenient builders and accessors. We do the same for natural transformations
 between them.

 Content
 1. Dependent presheaves
 2. Accessors for dependent presheaves
 3. Substitution for dependent presheaves
 4. Natural transformations between dependent presheaves
 5. Accessors for natural transformations between dependent presheaves
 6. Examples of natural transformations between dependent presheaves

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Categories.CategoryOfElementsPsh.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.

Local Open Scope cat.

(** * 1. Dependent presheaves *)
Definition dep_psh
           {C : category}
           (Γ : C^op ⟶ HSET)
  : UU
  := (∫ Γ)^op ⟶ HSET.

(** * 2. Accessors for dependent presheaves *)
Definition dep_psh_ob
           {C : category}
           {Γ : C^op ⟶ HSET}
           (A : dep_psh Γ)
           (x : C)
           (xx : (Γ x : hSet))
  : hSet
  := (A : _ ⟶ _) (x ,, xx).

Coercion dep_psh_ob : dep_psh >-> Funclass.

Definition dep_psh_mor
           {C : category}
           {Γ : C^op ⟶ HSET}
           (A : dep_psh Γ)
           {x y : C}
           {xx : (Γ x : hSet)}
           {yy : (Γ y : hSet)}
           (s : y --> x)
           (p : #Γ s xx = yy)
  : A x xx → A y yy.
Proof.
  simple refine (#(A : _ ⟶ _) (_ ,, _)).
  - exact s.
  - exact p.
Defined.

Notation "#d" := (dep_psh_mor).

Proposition dep_psh_mor_path_eq
            {C : category}
            {Γ : C^op ⟶ HSET}
            (A : dep_psh Γ)
            {x y : C}
            {xx : (Γ x : hSet)}
            {yy : (Γ y : hSet)}
            {s₁ s₂ : y --> x}
            (p : #Γ s₁ xx = yy)
            (q : #Γ s₂ xx = yy)
            (r : s₁ = s₂)
            (a : A x xx)
  : #d A s₁ p a = #d A s₂ q a.
Proof.
  induction r.
  enough (p = q) as ->.
  {
    apply idpath.
  }
  apply setproperty.
Qed.

Proposition dep_psh_mor_path_eq_pt
            {C : category}
            {Γ : C^op ⟶ HSET}
            (A : dep_psh Γ)
            {x y : C}
            {xx : (Γ x : hSet)}
            {yy : (Γ y : hSet)}
            {s₁ s₂ : y --> x}
            (p : #Γ s₁ xx = yy)
            (q : #Γ s₂ xx = yy)
            (r : s₁ = s₂)
            {a a' : A x xx}
            (r' : a = a')
  : #d A s₁ p a = #d A s₂ q a'.
Proof.
  induction r, r'.
  enough (p = q) as ->.
  {
    apply idpath.
  }
  apply setproperty.
Qed.

Proposition dep_psh_mor_id
            {C : category}
            {Γ : C^op ⟶ HSET}
            (A : dep_psh Γ)
            {x : C}
            {xx : (Γ x : hSet)}
            (p : #Γ (identity x) xx = xx)
            (a : A x xx)
  : #d A (identity x) p a = a.
Proof.
  refine (_ @ eqtohomot (functor_id A _) _).
  apply dep_psh_mor_path_eq.
  apply idpath.
Qed.

Proposition dep_psh_mor_id'
            {C : category}
            {Γ : C^op ⟶ HSET}
            (A : dep_psh Γ)
            {x : C}
            (f : x --> x)
            {xx : (Γ x : hSet)}
            (p : #Γ f xx = xx)
            (q : identity _ = f)
            (a : A x xx)
  : #d A f p a = a.
Proof.
  induction q.
  apply dep_psh_mor_id.
Qed.

Proposition dep_psh_mor_comp
            {C : category}
            {Γ : C^op ⟶ HSET}
            (A : dep_psh Γ)
            {x y z : C}
            {xx : (Γ x : hSet)}
            {yy : (Γ y : hSet)}
            {zz : (Γ z : hSet)}
            (s₁ : y --> x)
            (s₂ : z --> y)
            (p : #Γ s₁ xx = yy)
            (q : #Γ s₂ yy = zz)
            (r : #Γ (s₂ · s₁) xx = zz)
            (a : A x xx)
  : #d A (s₂ · s₁) r a = #d A s₂ q (#d A s₁ p a).
Proof.
  refine (_ @ eqtohomot (functor_comp A _ _) _).
  apply dep_psh_mor_path_eq.
  apply idpath.
Qed.

Proposition dep_psh_mor_comp_path
            {C : category}
            {Γ : C^op ⟶ HSET}
            {x y z : C}
            {xx : (Γ x : hSet)}
            {yy : (Γ y : hSet)}
            {zz : (Γ z : hSet)}
            {s₁ : y --> x}
            {s₂ : z --> y}
            (p : #Γ s₁ xx = yy)
            (q : #Γ s₂ yy = zz)
  : #Γ (s₂ · s₁) xx = zz.
Proof.
  exact(eqtohomot (functor_comp Γ _ _) _ @ maponpaths (#Γ s₂) p @ q).
Qed.

Proposition dep_psh_mor_comp'
            {C : category}
            {Γ : C^op ⟶ HSET}
            (A : dep_psh Γ)
            {x y z : C}
            {xx : (Γ x : hSet)}
            {yy : (Γ y : hSet)}
            {zz : (Γ z : hSet)}
            (s₁ : y --> x)
            (s₂ : z --> y)
            (p : #Γ s₁ xx = yy)
            (q : #Γ s₂ yy = zz)
            (a : A x xx)
  : #d A s₂ q (#d A s₁ p a) = #d A (s₂ · s₁) (dep_psh_mor_comp_path p q) a.
Proof.
  refine (!_).
  apply dep_psh_mor_comp.
Qed.

Proposition transport_dep_psh_mor
            {C : category}
            {Γ : C^op ⟶ HSET}
            (A : dep_psh Γ)
            {x : C}
            {xx₁ xx₂ : (Γ x : hSet)}
            (p : xx₁ = xx₂)
            (a : A x xx₁)
  : transportf (A x) p a
    =
    #d A (identity _) (eqtohomot (functor_id Γ _) _ @ p) a.
Proof.
  induction p ; cbn.
  refine (!_).
  apply dep_psh_mor_id.
Qed.

Definition make_dep_psh
           {C : category}
           {Γ : C^op ⟶ HSET}
           (Ao : ∏ (x : C), (Γ x : hSet) → hSet)
           (Am : ∏ (x y : C)
                   (xx : (Γ x : hSet))
                   (yy : (Γ y : hSet))
                   (s : y --> x)
                   (p : #Γ s xx = yy),
                 Ao x xx → Ao y yy)
           (Ai : ∏ (x : C)
                   (xx : (Γ x : hSet))
                   (p : #Γ (identity x) xx = xx)
                   (a : Ao x xx),
                 Am _ _ _ _ (identity x) p a
                 =
                 a)
           (Ac : ∏ (x y z : C)
                   (xx : (Γ x : hSet))
                   (yy : (Γ y : hSet))
                   (zz : (Γ z : hSet))
                   (s₁ : y --> x)
                   (s₂ : z --> y)
                   (p : #Γ s₁ xx = yy)
                   (q : #Γ s₂ yy = zz)
                   (r : #Γ (s₂ · s₁) xx = zz)
                   (a : Ao x xx),
                 Am _ _ _ _ (s₂ · s₁) r a
                 =
                 Am _ _ _ _ s₂ q (Am _ _ _ _ s₁ p a))
  : dep_psh Γ.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (λ x, Ao (pr1 x) (pr2 x)).
    + exact (λ x y f, Am _ _ _ _ (pr1 f) (pr2 f)).
  - split.
    + abstract
        (intro x ;
         use funextsec ;
         intro a ;
         apply Ai).
    + abstract
        (intros x y z f g ;
         use funextsec ;
         intro a ;
         apply Ac).
Defined.

(** * 3. Substitution for dependent presheaves *)
Definition dep_psh_subst
           {C : category}
           {Γ₁ Γ₂ : C^op ⟶ HSET}
           (s : Γ₁ ⟹ Γ₂)
           (A : dep_psh Γ₂)
  : dep_psh Γ₁.
Proof.
  use make_dep_psh.
  - exact (λ x xx, A x (s x xx)).
  - refine (λ x y xx yy f p a, #d A f _ a).
    abstract
      (rewrite <- p ;
       exact (!(eqtohomot (nat_trans_ax s _ _ f) xx))).
  - abstract
      (intros x xx p a ; cbn ;
       apply dep_psh_mor_id).
  - abstract
      (intros x y z xx yy zz s₁ s₂ p q r a ; cbn ;
       apply dep_psh_mor_comp).
Defined.

(** * 4. Natural transformations between dependent presheaves *)
Definition dep_psh_nat_trans
           {C : category}
           {Γ₁ Γ₂ : C^op ⟶ HSET}
           (A : dep_psh Γ₁)
           (B : dep_psh Γ₂)
           (s : Γ₁ ⟹ Γ₂)
  : UU
  := (A : _ ⟶ _) ⟹ functor_opp (cat_of_elems_psh_nat_trans s) ∙ B.

(** * 5. Accessors for natural transformations between dependent presheaves *)
Definition dep_psh_nat_trans_ob
           {C : category}
           {Γ₁ Γ₂ : C^op ⟶ HSET}
           {A : dep_psh Γ₁}
           {B : dep_psh Γ₂}
           {s : Γ₁ ⟹ Γ₂}
           (τ : dep_psh_nat_trans A B s)
           (x : C)
           (xx : (Γ₁ x : hSet))
           (a : A x xx)
  : B x (s x xx)
  := pr1 τ (x ,, xx) a.

Coercion dep_psh_nat_trans_ob : dep_psh_nat_trans >-> Funclass.

Proposition dep_psh_nat_trans_ax
            {C : category}
            {Γ₁ Γ₂ : C^op ⟶ HSET}
            {A : dep_psh Γ₁}
            {B : dep_psh Γ₂}
            {s : Γ₁ ⟹ Γ₂}
            (τ : dep_psh_nat_trans A B s)
            {x y : C}
            {xx : (Γ₁ x : hSet)}
            {yy : (Γ₁ y : hSet)}
            (f : y --> x)
            (p : #Γ₁ f xx = yy)
            (q : #Γ₂ f (s x xx) = s y yy)
            (a : A x xx)
  : τ y yy (#d A f p a) = #d B f q (τ x xx a).
Proof.
  refine (eqtohomot (pr2 τ (x ,, xx) (y ,, yy) (f ,, p)) a @ _) ; cbn.
  apply dep_psh_mor_path_eq.
  apply idpath.
Qed.

Proposition dep_psh_nat_trans_ax_path
            {C : category}
            {Γ₁ Γ₂ : C^op ⟶ HSET}
            {A : dep_psh Γ₁}
            {B : dep_psh Γ₂}
            {s : Γ₁ ⟹ Γ₂}
            (τ : dep_psh_nat_trans A B s)
            {x y : C}
            {xx : (Γ₁ x : hSet)}
            {yy : (Γ₁ y : hSet)}
            (f : y --> x)
            (p : #Γ₁ f xx = yy)
  : #Γ₂ f (s x xx) = s y yy.
Proof.
  rewrite <- p.
  exact (!(eqtohomot (nat_trans_ax s x y f) xx)).
Qed.

Proposition dep_psh_nat_trans_ax'
            {C : category}
            {Γ₁ Γ₂ : C^op ⟶ HSET}
            {A : dep_psh Γ₁}
            {B : dep_psh Γ₂}
            {s : Γ₁ ⟹ Γ₂}
            (τ : dep_psh_nat_trans A B s)
            {x y : C}
            {xx : (Γ₁ x : hSet)}
            {yy : (Γ₁ y : hSet)}
            (f : y --> x)
            (p : #Γ₁ f xx = yy)
            (a : A x xx)
  : τ y yy (#d A f p a) = #d B f (dep_psh_nat_trans_ax_path τ f p) (τ x xx a).
Proof.
  apply dep_psh_nat_trans_ax.
Qed.

Definition dep_psh_nat_trans_naturality
           {C : category}
           {Γ₁ Γ₂ : C^op ⟶ HSET}
           {A : dep_psh Γ₁}
           {B : dep_psh Γ₂}
           {s : Γ₁ ⟹ Γ₂}
           (τo : ∏ (x : C)
                   (xx : (Γ₁ x : hSet)),
                 A x xx → B x (s x xx))
  : UU
  := ∏ (x y : C)
       (xx : (Γ₁ x : hSet))
       (yy : (Γ₁ y : hSet))
       (f : y --> x)
       (p : #Γ₁ f xx = yy)
       (q : #Γ₂ f (s x xx) = s y yy)
       (a : A x xx),
     τo y yy (#d A f p a) = #d B f q (τo x xx a).

Arguments dep_psh_nat_trans_naturality /.

Definition make_dep_psh_nat_trans
           {C : category}
           {Γ₁ Γ₂ : C^op ⟶ HSET}
           (A : dep_psh Γ₁)
           (B : dep_psh Γ₂)
           (s : Γ₁ ⟹ Γ₂)
           (τo : ∏ (x : C)
                   (xx : (Γ₁ x : hSet)),
                 A x xx → B x (s x xx))
           (τm : dep_psh_nat_trans_naturality τo)
  : dep_psh_nat_trans A B s.
Proof.
  use make_nat_trans.
  - exact (λ x a, τo (pr1 x) (pr2 x) a).
  - abstract
      (intros x y f ;
       use funextsec ;
       intro a ;
       exact (τm (pr1 x) (pr1 y) (pr2 x) (pr2 y) (pr1 f) (pr2 f) _ a)).
Defined.

Proposition dep_psh_nat_trans_eq
            {C : category}
            {Γ₁ Γ₂ : C^op ⟶ HSET}
            {A : dep_psh Γ₁}
            {B : dep_psh Γ₂}
            {s : Γ₁ ⟹ Γ₂}
            {τ₁ τ₂ : dep_psh_nat_trans A B s}
            (p : ∏ (x : C) (xx : (Γ₁ x : hSet)) (a : A x xx),
                 τ₁ x xx a = τ₂ x xx a)
  : τ₁ = τ₂.
Proof.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intros x.
  use funextsec.
  intro a.
  apply p.
Qed.

Proposition dep_psh_nat_trans_eq_pt
            {C : category}
            {Γ₁ Γ₂ : C^op ⟶ HSET}
            {A : dep_psh Γ₁}
            {B : dep_psh Γ₂}
            {s : Γ₁ ⟹ Γ₂}
            {τ₁ τ₂ : dep_psh_nat_trans A B s}
            (p : τ₁ = τ₂)
            {x : C}
            (xx : (Γ₁ x : hSet))
            (a : A x xx)
  : τ₁ x xx a = τ₂ x xx a.
Proof.
  induction p.
  apply idpath.
Qed.

(** * 6. Examples of natural transformations between dependent presheaves *)
Definition dep_psh_id_nat_trans
           {C : category}
           {Γ : C^op ⟶ HSET}
           (A : dep_psh Γ)
  : dep_psh_nat_trans A A (nat_trans_id Γ).
Proof.
  use make_dep_psh_nat_trans.
  - exact (λ x xx a, a).
  - abstract
      (intro ; intros ; cbn ;
       apply dep_psh_mor_path_eq ;
       apply idpath).
Defined.

Definition dep_psh_comp_nat_trans
           {C : category}
           {Γ₁ Γ₂ Γ₃ : C^op ⟶ HSET}
           {A₁ : dep_psh Γ₁}
           {A₂ : dep_psh Γ₂}
           {A₃ : dep_psh Γ₃}
           {s₁ : Γ₁ ⟹ Γ₂}
           {s₂ : Γ₂ ⟹ Γ₃}
           (τ₁ : dep_psh_nat_trans A₁ A₂ s₁)
           (τ₂ : dep_psh_nat_trans A₂ A₃ s₂)
  : dep_psh_nat_trans A₁ A₃ (nat_trans_comp _ _ _ s₁ s₂).
Proof.
  use make_dep_psh_nat_trans.
  - exact (λ x xx a, τ₂ x _ (τ₁ x xx a)).
  - abstract
      (intro ; intros ; cbn ;
       rewrite dep_psh_nat_trans_ax' ;
       apply dep_psh_nat_trans_ax).
Defined.

Definition dep_psh_subst_nat_trans
           {C : category}
           {Γ₁ Γ₂ : C^op ⟶ HSET}
           (s : Γ₁ ⟹ Γ₂)
           (A : dep_psh Γ₂)
  : dep_psh_nat_trans (dep_psh_subst s A) A s.
Proof.
  use make_dep_psh_nat_trans.
  - exact (λ x xx a, a).
  - abstract
      (intros x y xx yy f p q a ; cbn ;
       apply dep_psh_mor_path_eq ;
       apply idpath).
Defined.

Definition dep_psh_factor_nat_trans
           {C : category}
           {Γ₁ Γ₂ Γ₃ : C^op ⟶ HSET}
           {s₁ : Γ₁ ⟹ Γ₂}
           {s₂ : Γ₂ ⟹ Γ₃}
           {A : dep_psh Γ₁}
           {B : dep_psh Γ₃}
           (τ : dep_psh_nat_trans A B (nat_trans_comp _ _ _ s₁ s₂))
  : dep_psh_nat_trans A (dep_psh_subst s₂ B) s₁.
Proof.
  use make_dep_psh_nat_trans.
  - exact (λ x xx a, τ x xx a).
  - abstract
      (intros x y xx yy f p q a ; cbn ;
       exact (dep_psh_nat_trans_ax τ f p _ a)).
Defined.
