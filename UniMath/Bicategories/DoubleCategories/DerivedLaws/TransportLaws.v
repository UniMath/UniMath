(********************************************************************************

 Transport laws for double categories

 This file collects a bunch of laws involving transporting squares in double
 categories.  There also is the module `TransportSquare`. Importing this
 module gives nicer notations for transporting squares, so that the goals look
 simpler, and it makes the map from `paths` to globular iso squares opaque, which
 makes the computational behavior a bit nicer. The reason for that is that `cbn`
 would unfold `path_to_globular_iso` to `id_two_disp`, even though it is nicer to
 have `id_v_square`.

 ********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.

Local Open Scope cat.
Local Open Scope double_cat.

Proposition transportf_f_square
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ v₁' v₁'' : x₁ -->v y₁}
            {v₂ v₂' v₂'' : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (p₁ : v₁ = v₁') (p₂ : v₁' = v₁'')
            (q₁ : v₂ = v₂') (q₂ : v₂' = v₂'')
            (s : square v₁ v₂ h₁ h₂)
  : transportf_square p₂ q₂ (transportf_square p₁ q₁ s)
    =
    transportf_square (p₁ @ p₂) (q₁ @ q₂) s.
Proof.
  induction p₁, p₂, q₁, q₂.
  apply idpath.
Qed.

Proposition transportb_b_square
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ v₁' v₁'' : x₁ -->v y₁}
            {v₂ v₂' v₂'' : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (p₁ : v₁ = v₁') (p₂ : v₁' = v₁'')
            (q₁ : v₂ = v₂') (q₂ : v₂' = v₂'')
            (s : square v₁'' v₂'' h₁ h₂)
  : transportb_square p₁ q₁ (transportb_square p₂ q₂ s)
    =
    transportb_square (p₁ @ p₂) (q₁ @ q₂) s.
Proof.
  induction p₁, p₂, q₁, q₂.
  apply idpath.
Qed.

Proposition transportf_square_prewhisker
            {C : double_cat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ v₁' : x₁ -->v y₁}
            {v₂ v₂' : x₂ -->v y₂}
            {w₁ : y₁ -->v z₁}
            {w₂ : y₂ -->v z₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            {k : z₁ -->h z₂}
            (p : v₁ = v₁')
            (q : v₂ = v₂')
            (s : square v₁ v₂ h₁ h₂)
            (s' : square w₁ w₂ h₂ k)
  : transportf_square p q s ⋆v s'
    =
    transportf_square (maponpaths (λ z, z ·v _) p) (maponpaths (λ z, z ·v _) q) (s ⋆v s').
Proof.
  induction p, q ; cbn.
  apply idpath.
Qed.

Proposition transportb_square_prewhisker
            {C : double_cat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ v₁' : x₁ -->v y₁}
            {v₂ v₂' : x₂ -->v y₂}
            {w₁ : y₁ -->v z₁}
            {w₂ : y₂ -->v z₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            {k : z₁ -->h z₂}
            (p : v₁ = v₁')
            (q : v₂ = v₂')
            (s : square v₁' v₂' h₁ h₂)
            (s' : square w₁ w₂ h₂ k)
  : transportb_square p q s ⋆v s'
    =
    transportb_square (maponpaths (λ z, z ·v _) p) (maponpaths (λ z, z ·v _) q) (s ⋆v s').
Proof.
  induction p, q ; cbn.
  apply idpath.
Qed.

Proposition transportf_square_postwhisker
            {C : double_cat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {w₁ w₁' : y₁ -->v z₁}
            {w₂ w₂' : y₂ -->v z₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            {k : z₁ -->h z₂}
            (p : w₁ = w₁')
            (q : w₂ = w₂')
            (s : square v₁ v₂ h₁ h₂)
            (s' : square w₁ w₂ h₂ k)
  : s ⋆v transportf_square p q s'
    =
    transportf_square (maponpaths (λ z, _ ·v z) p) (maponpaths (λ z, _ ·v z) q) (s ⋆v s').
Proof.
  induction p, q ; cbn.
  apply idpath.
Qed.

Proposition transportb_square_postwhisker
            {C : double_cat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {w₁ w₁' : y₁ -->v z₁}
            {w₂ w₂' : y₂ -->v z₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            {k : z₁ -->h z₂}
            (p : w₁ = w₁')
            (q : w₂ = w₂')
            (s : square v₁ v₂ h₁ h₂)
            (s' : square w₁' w₂' h₂ k)
  : s ⋆v transportb_square p q s'
    =
    transportb_square (maponpaths (λ z, _ ·v z) p) (maponpaths (λ z, _ ·v z) q) (s ⋆v s').
Proof.
  induction p, q ; cbn.
  apply idpath.
Qed.

Proposition transportf_square_id
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (p : v₁ = v₁)
            (q : v₂ = v₂)
            (s : square v₁ v₂ h₁ h₂)
  : transportf_square p q s = s.
Proof.
  assert (r : p = idpath _) by apply isaset_ver_mor.
  rewrite r ; clear r.
  assert (r : q = idpath _) by apply isaset_ver_mor.
  rewrite r ; clear r.
  apply idpath.
Qed.

Proposition transportb_square_id
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (p : v₁ = v₁)
            (q : v₂ = v₂)
            (s : square v₁ v₂ h₁ h₂)
  : transportb_square p q s = s.
Proof.
  assert (r : p = idpath _) by apply isaset_ver_mor.
  rewrite r ; clear r.
  assert (r : q = idpath _) by apply isaset_ver_mor.
  rewrite r ; clear r.
  apply idpath.
Qed.

Proposition transportf_square_eq
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ v₁' : x₁ -->v y₁}
            {v₂ v₂' : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (p p' : v₁ = v₁')
            (q q' : v₂ = v₂')
            {s s' : square v₁ v₂ h₁ h₂}
            (r : s = s')
  : transportf_square p q s = transportf_square p' q' s'.
Proof.
  assert (t : p = p') by apply isaset_ver_mor.
  rewrite t ; clear t.
  assert (t : q = q') by apply isaset_ver_mor.
  rewrite t ; clear t.
  apply maponpaths.
  exact r.
Qed.

Proposition transportb_square_eq
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ v₁' : x₁ -->v y₁}
            {v₂ v₂' : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (p p' : v₁ = v₁')
            (q q' : v₂ = v₂')
            {s s' : square v₁' v₂' h₁ h₂}
            (r : s = s')
  : transportb_square p q s = transportb_square p' q' s'.
Proof.
  assert (t : p = p') by apply isaset_ver_mor.
  rewrite t ; clear t.
  assert (t : q = q') by apply isaset_ver_mor.
  rewrite t ; clear t.
  apply maponpaths.
  exact r.
Qed.

Proposition transportf_hcomp_l
            {C : double_cat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ v₁' : x₁ -->v x₂}
            {v₂ v₂' : y₁ -->v y₂}
            {v₃ : z₁ -->v z₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : y₁ -->h z₁}
            {k₁ : x₂ -->h y₂}
            {k₂ : y₂ -->h z₂}
            (p : v₁ = v₁')
            (q : v₂ = v₂')
            (s₁ : square v₁ v₂ h₁ k₁)
            (s₂ : square v₂' v₃ h₂ k₂)
  : transportf_square p q s₁ ⋆h s₂
    =
    transportf_square p (idpath _) (s₁ ⋆h transportf_square (!q) (idpath _) s₂).
Proof.
  induction p, q ; cbn.
  apply idpath.
Qed.

Proposition transportf_hcomp_r
            {C : double_cat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ v₂' : y₁ -->v y₂}
            {v₃ v₃' : z₁ -->v z₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : y₁ -->h z₁}
            {k₁ : x₂ -->h y₂}
            {k₂ : y₂ -->h z₂}
            (p : v₂ = v₂')
            (q : v₃ = v₃')
            (s₁ : square v₁ v₂' h₁ k₁)
            (s₂ : square v₂ v₃ h₂ k₂)
  : s₁ ⋆h transportf_square p q s₂
    =
    transportf_square (idpath _) q (transportf_square (idpath _) (!p) s₁ ⋆h s₂).
Proof.
  induction p, q ; cbn.
  apply idpath.
Qed.

Proposition transportf_square_id_h_square_eq
            {C : double_cat}
            {x y : C}
            {v₁ v₂ w₁ w₂ : x -->v y}
            (p₁ : v₁ = w₁) (p₂ : v₂ = w₁)
            (q₁ : v₁ = w₂) (q₂ : v₂ = w₂)
  : transportf_square
      p₁
      q₁
      (id_h_square v₁)
    =
    transportf_square
      p₂
      q₂
      (id_h_square v₂).
Proof.
  induction p₁, p₂, q₁.
  assert (idpath _ = q₂) as r.
  {
    apply isaset_ver_mor.
  }
  induction r.
  apply idpath.
Qed.

Proposition transportf_square_id_h_square_eq'
            {C : double_cat}
            {x y : C}
            {v v' v'' : x -->v y}
            (p : v = v')
            (q : v = v'')
  : transportf_square
      p
      q
      (id_h_square v)
    =
    transportf_square
      (idpath _)
      (!p @ q)
      (id_h_square v').
Proof.
  induction p, q ; cbn.
  apply idpath.
Qed.

Proposition eq_hcomp_square
            {C : double_cat}
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ v₂' : y₁ -->v y₂}
            {v₃ : z₁ -->v z₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : y₁ -->h z₁}
            {k₁ : x₂ -->h y₂}
            {k₂ : y₂ -->h z₂}
            {s₁ : square v₁ v₂ h₁ k₁}
            {s₁' : square v₁ v₂' h₁ k₁}
            {s₂ : square v₂ v₃ h₂ k₂}
            {s₂' : square v₂' v₃ h₂ k₂}
            (p : v₂ = v₂')
            (q₁ : s₁ = transportf_square (idpath _) (!p) s₁')
            (q₂ : s₂ = transportf_square (!p) (idpath _) s₂')
  : s₁ ⋆h s₂ = s₁' ⋆h s₂'.
Proof.
  induction p.
  cbn in q₁, q₂.
  induction q₁, q₂.
  apply idpath.
Qed.

Module TransportSquare.
  Notation "'trfs' fg" := (transportf_square _ _ fg) (at level 50, only printing).
  Notation "'trbs' fg" := (transportb_square _ _ fg) (at level 50, only printing).

  Global Opaque path_to_globular_iso_square.
End TransportSquare.
