(* Binary product categories *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.

Local Open Scope cat.

Notation "'id' X" := (identity X) (at level 30).

Section Binary_Product_Precat.

Definition binprod_precat (C D : precategory) : precategory
:= (product_precategory (λ (x : bool), if x then C else D)).

Local Notation "C ⊠ D" := (binprod_precat C D) (at level 38).

Definition binprod_ob {C D : precategory} (c : C) (d : D) : C ⊠ D.
Proof.
  intro x.
  induction x.
  exact c.
  exact d.
Defined.

Local Notation "( c , d )" := (binprod_ob c d).

Definition binprod_mor {C D : precategory} {c c' : C} {d d' : D} (f : c --> c') (g : d --> d') : (c, d) --> (c', d').
  intro x.
  induction x.
  - exact f.
  - exact g.
Defined.

Local Notation "( f #, g )" := (binprod_mor f g).

Definition binprod_id {C D : precategory} (c : C) (d : D) : (id c #, id d) = id (c, d).
Proof.
  apply funextsec.
  intro x.
  induction x; reflexivity.
Defined.

Definition binprod_proj_id {C D : precategory} (cd : C ⊠ D) (b : bool) : (id cd) b = id cd b.
Proof.
  reflexivity.
Defined.

Definition binprod_comp {C D : precategory} (c c' c'' : C) (d d' d'' : D) (f : c --> c') (f' : c' --> c'') (g : d --> d') (g' : d' --> d'') : (f · f' #, g · g') = (f #, g) · (f' #, g').
Proof.
  apply funextsec.
  intro x.
  induction x; reflexivity.
Defined.

Definition binprod_proj_comp {C D : precategory} {cd cd' cd'' : C ⊠ D} (f : cd --> cd') (g : cd' --> cd'') (b : bool) : (f · g) b = f b · g b.
Proof.
  reflexivity.
Defined.

Definition is_iso_binprod_iso {C D : precategory} {c c' : C} {d d' : D} {f : c --> c'} {g : d --> d'} (f_is_iso : is_iso f)
  (g_is_iso : is_iso g) : is_iso (f #, g).
Proof.
  apply (is_iso_qinv (f #, g) (inv_from_iso (isopair f f_is_iso) #, inv_from_iso (isopair g g_is_iso))).
  apply dirprodpair.
  - transitivity ((isopair f f_is_iso) · (inv_from_iso (isopair f f_is_iso)) #, (isopair g g_is_iso) · (inv_from_iso (isopair g g_is_iso))).
    + symmetry.
      apply binprod_comp.
    + rewrite 2 iso_inv_after_iso.
      apply binprod_id.
  - transitivity ((inv_from_iso (isopair f f_is_iso)) · (isopair f f_is_iso) #, (inv_from_iso (isopair g g_is_iso)) · (isopair g g_is_iso)).
    + symmetry.
      apply binprod_comp.
    + rewrite 2 iso_after_iso_inv.
      apply binprod_id.
Defined.

End Binary_Product_Precat.
