(**

 Each universe induces a category

 We show that each set universe induces a category whose objects form a set.

 Content
 1. The category coming from a universe
 2. It is a setcategory
 3. Equality of functors to this category

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.SetUniverses.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.

Local Open Scope cat.

(** * 1. The category coming from a universe *)
Definition set_universe_to_precategory_ob_mor
           (u : set_universe)
  : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact u.
  - exact (λ X Y, set_universe_el X → set_universe_el Y).
Defined.

Definition set_universe_to_precategory_data
           (u : set_universe)
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact (set_universe_to_precategory_ob_mor u).
  - exact (λ X x, x).
  - exact (λ X Y Z f g x, g(f x)).
Defined.

Definition set_universe_to_precategory
           (u : set_universe)
  : precategory.
Proof.
  use make_precategory.
  - exact (set_universe_to_precategory_data u).
  - abstract (repeat split).
Defined.

Definition set_universe_to_category
           (u : set_universe)
  : category.
Proof.
  use make_category.
  - exact (set_universe_to_precategory u).
  - abstract
      (intros X Y ;
       use impred_isaset ;
       intro x ;
       apply setproperty).
Defined.

Proposition idtoiso_set_universe_to_category
            {u : set_universe}
            {x y : set_universe_to_category u}
            (p : x = y)
  : pr1 (idtoiso p) = set_universe_eq p.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition idtoiso_set_universe_to_category_inv
            {u : set_universe}
            {x y : set_universe_to_category u}
            (p : x = y)
  : inv_from_z_iso (idtoiso p) = set_universe_eq (!p).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

(** * 2. It is a setcategory *)
Definition set_universe_to_setcategory
           (u : set_universe)
  : setcategory.
Proof.
  use make_setcategory.
  - exact (set_universe_to_category u).
  - apply setproperty.
Defined.

(** * 3. Equality of functors to this category *)
Proposition path_functor_to_set_universe
            {C : category}
            {u : set_universe}
            {F G : C ⟶ set_universe_to_category u}
            (p : ∏ (x : C), F x = G x)
            (q : ∏ (x y : C)
                   (f : x --> y)
                   (a : set_universe_el (G x)),
                 set_universe_eq
                   (p y)
                   (#F f (set_universe_eq (!(p x)) a))
                 =
                 #G f a)
  : F = G.
Proof.
  use functor_eq.
  {
    apply homset_property.
  }
  use functor_data_eq.
  - exact p.
  - intros x y f.
    rewrite double_transport_idtoiso.
    etrans.
    {
      apply maponpaths.
      apply idtoiso_set_universe_to_category.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply idtoiso_set_universe_to_category_inv.
    }
    use funextsec.
    intro a.
    cbn.
    apply q.
Qed.
