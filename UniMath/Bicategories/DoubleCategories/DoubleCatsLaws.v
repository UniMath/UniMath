(********************************************************************************

 Derived laws for double categories

 This file is a random collection of derived laws for double categories, because
 they are useful. There also is the module `TransportSquare`. Importing this
 module gives nicer notations for transporting squares, so that the goals look
 simpler, and it makes the map from `paths` to globular iso squares opaque, which
 makes the computational behavior a bit nicer. The reason for that, is that `cbn`
 would unfold `path_to_globular_iso` to `id_two_disp`, even though it is nicer to
 have `id_v_square`.

 Contents
 1. Variations of the double category laws
 2. Laws involving identities and globular iso squares
 3. Transport laws for squares

 ********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCats.

Local Open Scope cat.
Local Open Scope double_cat.

(** * 1. Variations of the double category laws *)
Proposition square_id_left_v'
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : transportf_square (id_left _) (id_left _) (id_v_square h₁ ⋆v s)
    =
    s.
Proof.
  rewrite square_id_left_v.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition square_id_right_v'
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : transportf_square (id_right _) (id_right _) (s ⋆v id_v_square h₂)
    =
    s.
Proof.
  rewrite square_id_right_v.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition square_assoc_v'
            {C : double_cat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ : w₁ -->v x₁} {v₁' : x₁ -->v y₁} {v₁'' : y₁ -->v z₁}
            {v₂ : w₂ -->v x₂} {v₂' : x₂ -->v y₂} {v₂'' : y₂ -->v z₂}
            {h₁ : w₁ -->h w₂}
            {h₂ : x₁ -->h x₂}
            {h₃ : y₁ -->h y₂}
            {h₄ : z₁ -->h z₂}
            (s₁ : square v₁ v₂ h₁ h₂)
            (s₂ : square v₁' v₂' h₂ h₃)
            (s₃ : square v₁'' v₂'' h₃ h₄)
  : transportf_square (assoc _ _ _) (assoc _ _ _) (s₁ ⋆v (s₂ ⋆v s₃))
    =
    ((s₁ ⋆v s₂) ⋆v s₃).
Proof.
  rewrite square_assoc_v.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition lunitor_linvunitor_h'
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : transportf_square (id_v_left _) (id_v_left _) (lunitor_h f ⋆v linvunitor_h f)
    =
    id_v_square _.
Proof.
  rewrite lunitor_linvunitor_h.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition linvunitor_lunitor_h'
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : transportf_square (id_v_left _) (id_v_left _) (linvunitor_h f ⋆v lunitor_h f)
    =
    id_v_square _.
Proof.
  rewrite linvunitor_lunitor_h.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition lunitor_square'
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : x₂ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : transportf_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      ((id_h_square _ ⋆h s) ⋆v lunitor_h h₂)
    =
    lunitor_h h₁ ⋆v s.
Proof.
  rewrite lunitor_square.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition runitor_rinvunitor_h'
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : transportf_square (id_v_left _) (id_v_left _) (runitor_h f ⋆v rinvunitor_h f)
    =
    id_v_square _.
Proof.
  rewrite runitor_rinvunitor_h.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition rinvunitor_runitor_h'
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : transportf_square (id_v_left _) (id_v_left _) (rinvunitor_h f ⋆v runitor_h f)
    =
    id_v_square _.
Proof.
  rewrite rinvunitor_runitor_h.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition runitor_square'
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : x₂ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : transportf_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      ((s ⋆h id_h_square _) ⋆v runitor_h h₂)
    =
    runitor_h h₁ ⋆v s.
Proof.
  rewrite runitor_square.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition lassociator_rassociator_h'
            {C : double_cat}
            {w x y z : C}
            (f : w -->h x)
            (g : x -->h y)
            (h : y -->h z)
  : transportf_square (id_v_left _) (id_v_left _) (lassociator_h f g h ⋆v rassociator_h f g h)
    =
    id_v_square _.
Proof.
  rewrite lassociator_rassociator_h.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition rassociator_lassociator_h'
            {C : double_cat}
            {w x y z : C}
            (f : w -->h x)
            (g : x -->h y)
            (h : y -->h z)
  : transportf_square (id_v_left _) (id_v_left _) (rassociator_h f g h ⋆v lassociator_h f g h)
    =
    id_v_square _.
Proof.
  rewrite rassociator_lassociator_h.
  rewrite transportfb_square.
  apply idpath.
Qed.

(** * 2. Laws involving identities and globular iso squares *)
Proposition path_to_globular_iso_square_id
            {C : double_cat}
            {x y : C}
            {h : x -->h y}
  : id_v_square h
    =
    path_to_globular_iso_square (idpath h).
Proof.
  apply idpath.
Qed.

Proposition path_to_globular_iso_square_inv
            {C : double_cat}
            {x y : C}
            {h₁ h₂ : x -->h y}
            (p : h₁ = h₂)
  : globular_iso_square_inv (path_to_globular_iso_square p)
    =
    path_to_globular_iso_square (!p).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition path_to_globular_iso_square_comp
            {C : double_cat}
            {x y : C}
            {h₁ h₂ h₃ : x -->h y}
            (p : h₁ = h₂)
            (q : h₂ = h₃)
  : transportf_square
      (id_v_left _)
      (id_v_left _)
      (path_to_globular_iso_square p ⋆v path_to_globular_iso_square q)
    =
    path_to_globular_iso_square (p @ q).
Proof.
  induction p, q.
  rewrite <- !path_to_globular_iso_square_id.
  rewrite square_id_left_v.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition path_to_globular_iso_to_path
            {C : double_cat}
            {x y : C}
            {h₁ h₂ : x -->h y}
            (p : h₁ = h₂)
  : globular_iso_square_to_path (path_to_globular_iso_square p) = p.
Proof.
  exact (idtoisotoid_twosided_disp
           (is_univalent_twosided_disp_cat_hor_mor C)
           (idpath _) (idpath _)
           p).
Qed.

Proposition globular_iso_to_path_to_iso
            {C : double_cat}
            {x y : C}
            {h₁ h₂ : x -->h y}
            (p : globular_iso_square h₁ h₂)
  : path_to_globular_iso_square (globular_iso_square_to_path p) = p.
Proof.
  exact (isotoidtoiso_twosided_disp
           (is_univalent_twosided_disp_cat_hor_mor C)
           (idpath _) (idpath _)
           p).
Qed.

(** * 3. Transport laws for squares *)
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
