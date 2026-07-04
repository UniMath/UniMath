(**

 Sites

 We define Grothendieck topologies and sites. Note that Grothendieck topologies are defined
 in terms of sieves and that there are multiple equivalent definitions of the notion of
 sieve. Here we use the following definition: a sieve on `x` is the same as a functor from
 the slice category `C / x` to the category `hProp` (objects are propositions, and the type
 of morphisms is given by impliciation).

 Content
 1. Grothendieck topologies
 2. Sites

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.

Local Open Scope cat.

(** * 1. Grothendieck topologies *)
Definition grothendieck_topology
           (C : category)
  : UU
  := ∑ (P : ∏ (x : C), sieve x → hProp),
     (∏ (x : C),
      P x (truth_sieve x))
     ×
     (∏ (x y : C)
        (f : x --> y)
        (ω : sieve y),
      P y ω
      → P x (f^* ω))
     ×
     (∏ (y : C)
        (ω₁ ω₂ : sieve y),
      P y ω₁
      → (∏ (x : C) (h : x --> y), ω₁ _ h → P x (h^* ω₂))
      → P y ω₂).

Definition make_grothendieck_topology
           {C : category}
           (P : ∏ (x : C), sieve x → hProp)
           (Pt : ∏ (x : C), P x (truth_sieve x))
           (Pp : ∏ (x y : C)
                  (f : x --> y)
                  (ω : sieve y),
                P y ω
                → P x (f^* ω))
           (PT : ∏ (y : C)
                   (ω₁ ω₂ : sieve y),
                 P y ω₁
                 → (∏ (x : C) (h : x --> y), ω₁ _ h → P x (h^* ω₂))
                 → P y ω₂)
  : grothendieck_topology C
  := P ,, Pt ,, Pp ,, PT.

(** * 2. Sites *)
Definition site
  : UU
  := ∑ (C : category), grothendieck_topology C.

Definition make_site
           (C : category)
           (G : grothendieck_topology C)
  : site
  := C ,, G.

Coercion site_to_cat
         (C : site)
  : category
  := pr1 C.

Definition site_to_sieve_pred
           (C : site)
           (x : C)
           (ω : sieve x)
  : hProp
  := pr12 C x ω.

Coercion site_to_sieve_pred : site >-> Funclass.

Proposition site_truth_sieve
            {C : site}
            (x : C)
  : C x (truth_sieve x).
Proof.
  exact (pr122 C x).
Defined.

Proposition site_sieve_stable
            {C : site}
            {x y : C}
            (f : x --> y)
            {ω : sieve y}
            (p : C y ω)
  : C x (f^* ω).
Proof.
  exact (pr1 (pr222 C) x y f ω p).
Defined.

Proposition site_trans_sieve
            {C : site}
            {y : C}
            {ω₁ ω₂ : sieve y}
            (p : C y ω₁)
            (H : ∏ (x : C) (h : x --> y), ω₁ x h → C x (h^* ω₂))
  : C y ω₂.
Proof.
  exact (pr2 (pr222 C) y ω₁ ω₂ p H).
Defined.
