(********************************************************************************

 Laws governing the unitors

 In this file, we derive laws that dictate how the unitors act on the identity.

 Content
 1. Derived laws regarding horizontal composition
 2. Derived laws for the pentagon and triangle
 3. Derived laws for the unitors on the identity

 ********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.DerivedLaws.TransportLaws.
Require Import UniMath.Bicategories.DoubleCategories.DerivedLaws.Variations.
Import TransportSquare.

Local Open Scope cat.
Local Open Scope double_cat.

(** * 1. Derived laws regarding horizontal composition *)
Proposition hcomp_split_globular
            {C : double_cat}
            {x y z : C}
            {v₁ : x -->v x}
            {v₂ : y -->v y}
            {v₃ : z -->v z}
            (p₁ : identity_v x = v₁)
            (p₂ : identity_v y = v₂)
            (p₃ : identity_v z = v₃)
            {h₁ : x -->h y}
            {k₁ : y -->h z}
            {h₂ : x -->h y}
            {k₂ : y -->h z}
            (s₁ : square v₁ v₂ h₁ h₂)
            (s₂ : square v₂ v₃ k₁ k₂)
  : s₁ ⋆h s₂
    =
    transportf_square
      (id_v_left _ @ p₁)
      (id_v_left _ @ p₃)
      (transportf_square (!p₁) (!p₂) s₁ ⋆h id_v_square k₁
       ⋆v
       id_v_square h₂ ⋆h transportf_square (!p₂) (!p₃) s₂).
Proof.
  induction p₁, p₂, p₃ ; cbn.
  rewrite <- comp_h_square_comp.
  rewrite square_id_left_v.
  rewrite square_id_right_v.
  unfold transportb_square.
  rewrite transportf_hcomp_l.
  rewrite !transportf_f_square.
  rewrite transportf_hcomp_r.
  rewrite transportf_f_square.
  rewrite !transportf_square_id.
  apply idpath.
Qed.

Proposition hcomp_split_globular_l_path
            {C : double_cat}
            {x : C}
            {v₁ v₂ : x -->v x}
            (q₁ : identity_v x = v₁)
            (q₂ : identity_v x = v₂)
  : v₁ ·v v₂ = v₂.
Proof.
  induction q₁, q₂.
  apply id_v_left.
Qed.

Proposition hcomp_split_globular_l
            {C : double_cat}
            {x y z : C}
            {u₁ u₂ : x -->v x}
            {v₁ v₂ : y -->v y}
            {w : z -->v z}
            (q₁ : identity_v y = v₁)
            (q₂ : identity_v y = v₂)
            (r : identity_v z = w)
            {h₁ h₂ h₃ : x -->h y}
            {k₁ k₂ : y -->h z}
            (s₁ : square u₁ v₁ h₁ h₂)
            (s₂ : square u₂ v₂ h₂ h₃)
            (s₃ : square (v₁ ·v v₂) w k₁ k₂)
  : (s₁ ⋆v s₂) ⋆h s₃
    =
    transportf_square
      (idpath _)
      (id_v_left _ @ r)
      ((s₁ ⋆h transportf_square q₁ (idpath _) (id_v_square _))
       ⋆v
       (s₂ ⋆h transportf_square (hcomp_split_globular_l_path q₁ q₂) (!r) s₃)).
Proof.
  induction q₁, q₂, r.
  rewrite <- comp_h_square_comp.
  rewrite transportf_square_postwhisker.
  rewrite transportf_square_prewhisker.
  rewrite transportf_f_square.
  rewrite square_id_left_v.
  unfold transportb_square.
  rewrite transportf_f_square.
  rewrite transportf_hcomp_r.
  rewrite transportf_f_square.
  rewrite !transportf_square_id.
  apply idpath.
Qed.

Proposition hcomp_split_globular_l'
            {C : double_cat}
            {x y z : C}
            {u₁ u₂ : x -->v x}
            {v₁ v₂ : y -->v y}
            {w : z -->v z}
            (q₁ : identity_v y = v₁)
            (q₂ : identity_v y = v₂)
            (r : identity_v z = w)
            {h₁ h₂ h₃ : x -->h y}
            {k₁ k₂ : y -->h z}
            (s₁ : square u₁ v₁ h₁ h₂)
            (s₂ : square u₂ v₂ h₂ h₃)
            (s₃ : square (v₁ ·v v₂) w k₁ k₂)
  : (s₁ ⋆h transportf_square q₁ (idpath _) (id_v_square _))
    ⋆v
    (s₂ ⋆h transportf_square (hcomp_split_globular_l_path q₁ q₂) (!r) s₃)
    =
    transportb_square
      (idpath _)
      (id_v_left _ @ r)
      ((s₁ ⋆v s₂) ⋆h s₃).
Proof.
  rewrite (hcomp_split_globular_l q₁ q₂ r).
  rewrite transportbf_square.
  apply idpath.
Qed.

Proposition hcomp_split_globular_l'_idpath
            {C : double_cat}
            {x y z : C}
            {u₁ u₂ : x -->v x}
            (q : identity_v y ·v identity_v y = identity_v y)
            {h₁ h₂ h₃ : x -->h y}
            {k₁ k₂ : y -->h z}
            (s₁ : square u₁ (identity_v y) h₁ h₂)
            (s₂ : square u₂ (identity_v y) h₂ h₃)
            (s₃ : square (identity_v y ·v identity_v y) (identity_v z) k₁ k₂)
  : (s₁ ⋆h id_v_square _)
    ⋆v
    (s₂ ⋆h transportf_square q (idpath _) s₃)
    =
    transportb_square
      (idpath _)
      (id_v_left _)
      ((s₁ ⋆v s₂) ⋆h s₃).
Proof.
  refine (_ @ hcomp_split_globular_l' (idpath _) (idpath _) (idpath _) s₁ s₂ s₃ @ _).
  - do 2 apply maponpaths.
    use transportf_square_eq.
    apply idpath.
  - use transportf_square_eq.
    apply idpath.
Qed.

Proposition hcomp_split_globular_l_id
            {C : double_cat}
            {x y z : C}
            {v₁ v₂ : z -->v z}
            (q₁ : identity_v z = v₁)
            (q₂ : identity_v z = v₂)
            {h₁ h₂ h₃ : y -->h z}
            {k : x -->h y}
            (s₁ : square (identity_v y) v₁ h₁ h₂)
            (s₂ : square (identity_v y) v₂ h₂ h₃)
  : id_v_square k ⋆h s₁
    ⋆v
    id_v_square k ⋆h s₂
    =
    transportf_square
      (!(id_v_left _))
      (idpath _)
      (id_v_square k ⋆h transportf_square (id_v_left _) (idpath _) (s₁ ⋆v s₂)).
Proof.
  induction q₁, q₂ ; cbn.
  rewrite <- comp_h_square_comp.
  rewrite square_id_left_v.
  unfold transportb_square.
  rewrite transportf_hcomp_r.
  rewrite transportf_f_square.
  rewrite transportf_hcomp_l.
  use transportf_square_eq.
  rewrite transportf_hcomp_r.
  refine (maponpaths (λ z, z ⋆h _) _).
  use transportf_square_eq.
  apply idpath.
Qed.

Proposition hcomp_split_globular_l_id'
            {C : double_cat}
            {x y z : C}
            {v₁ v₂ v₃ : z -->v z}
            (p₁ : identity_v y ·v identity_v y = identity_v y)
            (p₂ : v₁ ·v v₂ = v₃)
            (q₁ : identity_v z = v₁)
            (q₂ : identity_v z = v₂)
            {h₁ h₂ h₃ : y -->h z}
            {k : x -->h y}
            (s₁ : square (identity_v y) v₁ h₁ h₂)
            (s₂ : square (identity_v y) v₂ h₂ h₃)
  : id_v_square k ⋆h (transportf_square p₁ p₂ (s₁ ⋆v s₂))
    =
    transportf_square
      (id_v_left _)
      p₂
      (id_v_square k ⋆h s₁
       ⋆v
       id_v_square k ⋆h s₂).
Proof.
  rewrite (hcomp_split_globular_l_id q₁ q₂).
  rewrite transportf_f_square.
  rewrite !transportf_hcomp_r.
  rewrite !transportf_f_square.
  use transportf_square_eq.
  apply maponpaths_2.
  use transportf_square_eq.
  apply idpath.
Qed.

Proposition hcomp_split_globular_r_path
            {C : double_cat}
            {x : C}
            {v₁ v₂ : x -->v x}
            (q₁ : identity_v x = v₁)
            (q₂ : identity_v x = v₂)
  : v₁ = v₁ ·v v₂.
Proof.
  induction q₁, q₂.
  refine (!_).
  apply id_v_left.
Qed.

Proposition hcomp_split_globular_r
            {C : double_cat}
            {x y z : C}
            {w : x -->v x}
            {u₁ u₂ : y -->v y}
            {v₁ v₂ : z -->v z}
            (p₁ : identity_v y = u₁)
            (p₂ : identity_v y = u₂)
            {h₁ h₂ h₃ : y -->h z}
            {k₁ k₂ : x -->h y}
            (s₁ : square u₁ v₁ h₁ h₂)
            (s₂ : square u₂ v₂ h₂ h₃)
            (s₃ : square w (u₁ ·v u₂) k₁ k₂)
  : s₃ ⋆h (s₁ ⋆v s₂)
    =
    transportf_square
      (id_v_right _)
      (idpath _)
      ((s₃ ⋆h transportf_square (hcomp_split_globular_r_path p₁ p₂) (idpath _) s₁)
       ⋆v
       (id_v_square _ ⋆h transportf_square (!p₂) (idpath _) s₂)).
Proof.
  induction p₁, p₂.
  rewrite <- comp_h_square_comp.
  rewrite transportf_square_postwhisker.
  rewrite transportf_square_prewhisker.
  rewrite transportf_f_square.
  rewrite square_id_right_v.
  unfold transportb_square.
  rewrite transportf_hcomp_l.
  rewrite !transportf_f_square.
  rewrite !transportf_square_id.
  apply idpath.
Qed.

Proposition hcomp_split_globular_r'
            {C : double_cat}
            {x y z : C}
            {w : x -->v x}
            {u₁ u₂ : y -->v y}
            {v₁ v₂ : z -->v z}
            (p₁ : identity_v y = u₁)
            (p₂ : identity_v y = u₂)
            {h₁ h₂ h₃ : y -->h z}
            {k₁ k₂ : x -->h y}
            (s₁ : square u₁ v₁ h₁ h₂)
            (s₂ : square u₂ v₂ h₂ h₃)
            (s₃ : square w (u₁ ·v u₂) k₁ k₂)
  : (s₃ ⋆h transportf_square (hcomp_split_globular_r_path p₁ p₂) (idpath _) s₁)
    ⋆v
    (id_v_square _ ⋆h transportf_square (!p₂) (idpath _) s₂)
    =
    transportb_square
      (id_v_right _)
      (idpath _)
      (s₃ ⋆h (s₁ ⋆v s₂)).
Proof.
  rewrite (hcomp_split_globular_r p₁ p₂).
  rewrite transportbf_square.
  apply idpath.
Qed.

Proposition hcomp_split_globular_r'_idpath
            {C : double_cat}
            {x y z : C}
            {w : x -->v x}
            {v₁ v₂ : z -->v z}
            (q₁ : identity_v z = v₁)
            (q₂ : identity_v z = v₂)
            (r : identity_v y = identity_v y ·v identity_v y)
            {h₁ h₂ h₃ : y -->h z}
            {k₁ k₂ : x -->h y}
            (s₁ : square (identity_v y) v₁ h₁ h₂)
            (s₂ : square (identity_v y) v₂ h₂ h₃)
            (s₃ : square w (identity_v y ·v identity_v y) k₁ k₂)
  : (s₃ ⋆h transportf_square r (idpath _) s₁)
    ⋆v
    (id_v_square _ ⋆h s₂)
    =
    transportb_square
      (id_v_right _)
      (idpath _)
      (s₃ ⋆h (s₁ ⋆v s₂)).
Proof.
  refine (_ @ hcomp_split_globular_r' (idpath _) (idpath _) s₁ s₂ s₃ @ _).
  - apply maponpaths_2.
    apply maponpaths.
    use transportf_square_eq.
    apply idpath.
  - use transportf_square_eq.
    apply idpath.
Qed.

Proposition hcomp_split_globular_r_id
            {C : double_cat}
            {x y z : C}
            {v₁ v₂ : x -->v x}
            (q₁ : identity_v x = v₁)
            (q₂ : identity_v x = v₂)
            {h₁ h₂ h₃ : x -->h y}
            {k : y -->h z}
            (s₁ : square v₁ (identity_v y) h₁ h₂)
            (s₂ : square v₂ (identity_v y) h₂ h₃)
  : s₁ ⋆h id_v_square k ⋆v s₂ ⋆h id_v_square k
    =
    transportf_square
      (idpath _)
      (!(id_v_left _))
      (transportf_square (idpath _) (id_v_left _) (s₁ ⋆v s₂) ⋆h id_v_square k).
Proof.
  induction q₁, q₂ ; cbn -[transportf_square].
  rewrite <- comp_h_square_comp.
  rewrite square_id_left_v.
  unfold transportb_square.
  rewrite transportf_hcomp_l.
  rewrite transportf_f_square.
  rewrite transportf_hcomp_r.
  use transportf_square_eq.
  rewrite transportf_hcomp_r.
  refine (maponpaths (λ z, z ⋆h _) _).
  use transportf_square_eq.
  apply idpath.
Qed.

Proposition hcomp_r_inj
            {C : double_cat}
            {x y z : C}
            {f : x -->v y}
            {g : x -->h z}
            {h : y -->h z}
            {k : z -->v z}
            (p : identity_v z = k)
            {s s' : square f k g h}
            (q : transportf_square (idpath _) (!p) s ⋆h id_v_square (identity_h _)
                 =
                 transportf_square (idpath _) (!p) s' ⋆h id_v_square (identity_h _))
  : s = s'.
Proof.
  induction p ; cbn in q.
  refine (!(square_id_left_v' _) @ _ @ square_id_left_v' _).
  apply maponpaths.
  rewrite <- rinvunitor_runitor_h'.
  rewrite !transportf_square_prewhisker.
  apply maponpaths.
  refine (!(square_assoc_v' _ _ _) @ _ @ square_assoc_v' _ _ _).
  do 2 apply maponpaths.
  rewrite <- !runitor_square'.
  apply maponpaths.
  apply maponpaths_2.
  rewrite !id_h_square_id.
  exact q.
Qed.

Proposition hcomp_l_inj
            {C : double_cat}
            {x y z : C}
            {g : x -->h y}
            {h : x -->h z}
            {v : y -->v z}
            {v' : x -->v x}
            {s s' : square v' v g h}
            (p : identity_v x = v')
            (q : id_v_square (identity_h _) ⋆h (transportf_square (!p) (idpath _) s)
                 =
                 id_v_square (identity_h x) ⋆h (transportf_square (!p) (idpath _) s'))
  : s = s'.
Proof.
  induction p ; cbn in q.
  refine (!(square_id_left_v' _) @ _ @ square_id_left_v' _).
  apply maponpaths.
  rewrite <- linvunitor_lunitor_h'.
  rewrite !transportf_square_prewhisker.
  apply maponpaths.
  refine (!(square_assoc_v' _ _ _) @ _ @ square_assoc_v' _ _ _).
  do 2 apply maponpaths.
  rewrite <- !lunitor_square'.
  apply maponpaths.
  apply maponpaths_2.
  rewrite !id_h_square_id.
  exact q.
Qed.

(** * 2. Derived laws for the pentagon and triangle *)
Proposition double_inverse_pentagon
            {C : double_cat}
            {v w x y z : C}
            (h₁ : v -->h w)
            (h₂ : w -->h x)
            (h₃ : x -->h y)
            (h₄ : y -->h z)
  : rassociator_h (h₁ ·h h₂) h₃ h₄ ⋆v rassociator_h h₁ h₂ (h₃ ·h h₄)
    =
    transportf_square
      (id_v_right _)
      (id_v_right _)
      ((rassociator_h h₁ h₂ h₃ ⋆h id_v_square h₄)
       ⋆v
       rassociator_h h₁ (h₂ ·h h₃) h₄
       ⋆v
       (id_v_square h₁ ⋆h rassociator_h h₂ h₃ h₄)).
Proof.
  refine (!(square_id_right_v' _) @ _ @ square_id_right_v' _).
  apply maponpaths.
  rewrite <- !lassociator_rassociator_h'.
  rewrite !transportf_square_postwhisker.
  apply maponpaths.
  refine (square_assoc_v _ _ _ @ _ @ !(square_assoc_v _ _ _)).
  apply maponpaths.
  apply maponpaths_2.
  etrans.
  {
    refine (!(square_assoc_v' _ _ _) @ _).
    rewrite rassociator_lassociator_h.
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_id_right_v.
    unfold transportb_square.
    rewrite transportf_f_square.
    apply idpath.
  }
  refine (!(square_id_right_v' _) @ _ @ square_id_right_v' _).
  apply maponpaths.
  rewrite <- !lassociator_rassociator_h'.
  rewrite !transportf_square_postwhisker.
  apply maponpaths.
  refine (square_assoc_v _ _ _ @ _ @ !(square_assoc_v _ _ _)).
  apply maponpaths.
  apply maponpaths_2.
  rewrite transportf_square_prewhisker.
  rewrite rassociator_lassociator_h.
  unfold transportb_square.
  rewrite transportf_f_square.
  refine (!_).
  etrans.
  {
    refine (!(square_assoc_v' _ _ _) @ _).
    rewrite double_pentagon'.
    rewrite transportf_square_postwhisker.
    rewrite transportf_square_prewhisker.
    rewrite !transportf_f_square.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    rewrite <- square_assoc_v'.
    rewrite !transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 3 apply maponpaths.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite !transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 3 apply maponpaths.
      apply maponpaths_2.
      apply hcomp_split_globular_l_id ; apply idpath.
    }
    rewrite transportf_square_prewhisker.
    rewrite !transportf_square_postwhisker.
    rewrite rassociator_lassociator_h.
    unfold transportb_square.
    rewrite !transportf_f_square.
    etrans.
    {
      do 3 apply maponpaths.
      apply maponpaths_2.
      rewrite transportf_hcomp_r.
      rewrite transportf_square_id.
      rewrite comp_h_square_id.
      apply idpath.
    }
    rewrite transportf_square_prewhisker.
    rewrite !transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_id_left_v.
    unfold transportb_square.
    rewrite !transportf_square_postwhisker.
    rewrite transportf_f_square.
    etrans.
    {
      do 2 apply maponpaths.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite !transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite rassociator_lassociator_h.
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite transportf_f_square.
    rewrite square_id_left_v.
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite !transportf_f_square.
    rewrite (hcomp_split_globular_r_id (idpath _) (idpath _)).
    rewrite !transportf_f_square.
    rewrite rassociator_lassociator_h.
    unfold transportb_square.
    rewrite !transportf_f_square.
    rewrite transportf_hcomp_l.
    rewrite transportf_square_id.
    rewrite comp_h_square_id.
    rewrite transportf_f_square.
    apply idpath.
  }
  use transportf_square_eq.
  apply idpath.
Qed.

Proposition double_triangle_alt
            {C : double_cat}
            {x y z : C}
            (h : x -->h y)
            (k : y -->h z)
  : rassociator_h h _ k ⋆v (id_v_square h ⋆h lunitor_h k)
    =
    transportb_square
      (id_v_left _)
      (id_v_left _)
      (runitor_h h ⋆h id_v_square _).
Proof.
  rewrite <- double_triangle'.
  unfold transportb_square.
  rewrite transportf_square_postwhisker.
  etrans.
  {
    apply maponpaths.
    apply square_assoc_v.
  }
  unfold transportb_square.
  rewrite transportf_f_square.
  rewrite rassociator_lassociator_h.
  unfold transportb_square.
  rewrite transportf_square_prewhisker.
  rewrite transportf_f_square.
  rewrite square_id_left_v.
  unfold transportb_square.
  rewrite transportf_f_square.
  apply transportf_square_eq.
  apply idpath.
Qed.

Proposition double_triangle_alt'
            {C : double_cat}
            {x y z : C}
            (h : x -->h y)
            (k : y -->h z)
  : transportf_square
      (id_v_left _)
      (id_v_left _)
      (rassociator_h h _ k ⋆v (id_v_square h ⋆h lunitor_h k))
    =
    runitor_h h ⋆h id_v_square _.
Proof.
  rewrite double_triangle_alt.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition double_triangle_alt_inv
            {C : double_cat}
            {x y z : C}
            (h : x -->h y)
            (k : y -->h z)
  : (id_v_square h ⋆h linvunitor_h k) ⋆v lassociator_h _ _ _
    =
    transportb_square
      (id_v_left _)
      (id_v_left _)
      (rinvunitor_h _ ⋆h id_v_square _).
Proof.
  refine (!(square_id_right_v' _) @ _ @ square_id_right_v' _).
  apply maponpaths.
  rewrite <- rassociator_lassociator_h'.
  rewrite !transportf_square_postwhisker.
  apply maponpaths.
  refine (square_assoc_v _ _ _ @ _ @ !(square_assoc_v _ _ _)).
  apply maponpaths.
  apply maponpaths_2.
  rewrite <- !square_assoc_v'.
  rewrite lassociator_rassociator_h.
  unfold transportb_square.
  rewrite transportf_square_postwhisker.
  rewrite transportf_f_square.
  rewrite square_id_right_v.
  unfold transportb_square.
  rewrite transportf_f_square.
  refine (!(square_id_right_v' _) @ _ @ square_id_right_v' _).
  apply maponpaths.
  rewrite <- comp_h_square_id.
  rewrite <- lunitor_linvunitor_h'.
  etrans.
  {
    apply maponpaths.
    use hcomp_split_globular_l_id' ; apply idpath.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths.
    use hcomp_split_globular_l_id' ; apply idpath.
  }
  rewrite !transportf_square_postwhisker.
  apply maponpaths.
  refine (square_assoc_v _ _ _ @ _ @ !(square_assoc_v _ _ _)).
  apply maponpaths.
  apply maponpaths_2.
  refine (!(square_assoc_v' _ _ _) @ _).
  rewrite double_triangle_alt.
  unfold transportb_square.
  rewrite transportf_square_postwhisker.
  rewrite !transportf_square_prewhisker.
  rewrite !transportf_f_square.
  rewrite (hcomp_split_globular_l_id (idpath _) (idpath _)).
  rewrite (hcomp_split_globular_r_id (idpath _) (idpath _)).
  rewrite !transportf_f_square.
  rewrite rinvunitor_runitor_h.
  rewrite linvunitor_lunitor_h.
  unfold transportb_square.
  rewrite !transportf_f_square.
  rewrite transportf_hcomp_l.
  rewrite transportf_f_square.
  rewrite transportf_hcomp_r.
  rewrite !transportf_square_id.
  rewrite transportf_hcomp_r.
  rewrite transportf_f_square.
  rewrite transportf_hcomp_l.
  rewrite !transportf_square_id.
  use transportf_square_eq.
  apply idpath.
Qed.


Proposition runitor_h_triangle
            {C : double_cat}
            {x y z : C}
            (f : x -->h y)
            (g : y -->h z)
  : rassociator_h f g (identity_h z) ⋆v (id_v_square f ⋆h runitor_h g)
    =
    transportb_square
      (id_v_left _)
      (id_v_left _)
      (runitor_h _).
Proof.
  use hcomp_r_inj.
  - exact (!(id_v_left _)).
  - refine (!_).
    unfold transportb_square.
    rewrite transportf_f_square.
    rewrite transportf_hcomp_l.
    rewrite transportf_square_id.
    rewrite <- double_triangle_alt'.
    rewrite transportf_f_square.
    refine (!(square_id_right_v' _) @ _ @ square_id_right_v' _).
    apply maponpaths.
    rewrite <- !rassociator_lassociator_h'.
    rewrite !transportf_square_postwhisker.
    apply maponpaths.
    refine (square_assoc_v _ _ _ @ _ @ !(square_assoc_v _ _ _)).
    apply maponpaths.
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      rewrite transportf_hcomp_l.
      rewrite transportf_square_prewhisker.
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        use hcomp_split_globular_l ; apply idpath.
      }
      rewrite transportf_square_prewhisker.
      rewrite transportf_f_square.
      apply maponpaths.
      etrans.
      {
        refine (!_).
        apply square_assoc_v'.
      }
      rewrite <- rassociator_square'.
      apply idpath.
    }
    unfold transportb_square.
    rewrite transportf_square_prewhisker.
    rewrite transportf_square_postwhisker.
    rewrite !transportf_f_square.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite <- comp_h_square_id.
      etrans.
      {
        refine (!_).
        apply square_assoc_v'.
      }
      rewrite <- rassociator_square'.
      apply idpath.
    }
    unfold transportb_square.
    rewrite transportf_square_postwhisker.
    rewrite !transportf_f_square.
    rewrite <- double_triangle'.
    etrans.
    {
      apply maponpaths.
      apply square_assoc_v.
    }
    unfold transportb_square.
    rewrite !transportf_f_square.
    rewrite double_inverse_pentagon.
    rewrite transportf_square_prewhisker.
    rewrite transportf_f_square.
    rewrite !transportf_square_id.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    rewrite <- square_assoc_v'.
    rewrite transportf_f_square.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite (hcomp_split_globular_l_id (idpath _) (idpath _)).
      rewrite transportf_square_postwhisker.
      rewrite transportf_f_square.
      etrans.
      {
        do 3 apply maponpaths.
        apply square_assoc_v.
      }
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite rassociator_lassociator_h.
      unfold transportb_square.
      rewrite transportf_square_prewhisker.
      rewrite transportf_f_square.
      rewrite square_id_left_v.
      unfold transportb_square.
      rewrite transportf_f_square.
      rewrite transportf_hcomp_r.
      rewrite transportf_square_id.
      rewrite transportf_f_square.
      apply idpath.
    }
    rewrite !transportf_square_postwhisker.
    rewrite transportf_f_square.
    use transportf_square_eq.
    apply idpath.
Qed.

Proposition lunitor_id_id_h
            {C : double_cat}
            (x : C)
  : lunitor_h (identity_h x ·h identity_h x)
    =
    id_h_square (identity_v x) ⋆h lunitor_h (identity_h x).
Proof.
  refine (!(square_id_right_v' _) @ _ @ square_id_right_v' _).
  apply maponpaths.
  rewrite <- !lunitor_linvunitor_h'.
  rewrite !transportf_square_postwhisker.
  apply maponpaths.
  refine (square_assoc_v _ _ _ @ _ @ !(square_assoc_v _ _ _)).
  apply maponpaths.
  apply maponpaths_2.
  etrans.
  {
    rewrite <- lunitor_square'.
    apply idpath.
  }
  rewrite transportf_square_id.
  apply idpath.
Qed.

Proposition runitor_id_id_h
            {C : double_cat}
            (x : C)
  : runitor_h (identity_h x ·h identity_h x)
    =
    runitor_h (identity_h x) ⋆h id_h_square (identity_v x).
Proof.
  refine (!(square_id_right_v' _) @ _ @ square_id_right_v' _).
  apply maponpaths.
  rewrite <- !runitor_rinvunitor_h'.
  rewrite !transportf_square_postwhisker.
  apply maponpaths.
  refine (square_assoc_v _ _ _ @ _ @ !(square_assoc_v _ _ _)).
  apply maponpaths.
  apply maponpaths_2.
  etrans.
  {
    rewrite <- runitor_square'.
    apply idpath.
  }
  rewrite transportf_square_id.
  apply idpath.
Qed.

Proposition hcomp_runitor_lunitor
            {C : double_cat}
            (x : C)
  : id_h_square (identity_v x) ⋆h runitor_h (identity_h x)
    =
    id_h_square (identity_v x) ⋆h lunitor_h (identity_h x).
Proof.
  refine (!(square_id_left_v' _) @ _ @ square_id_left_v' _).
  apply maponpaths.
  rewrite <- lassociator_rassociator_h'.
  rewrite !transportf_square_prewhisker.
  apply maponpaths.
  refine (!(square_assoc_v' _ _ _) @ _ @ square_assoc_v' _ _ _).
  do 2 apply maponpaths.
  rewrite id_h_square_id.
  refine (_ @ !(double_triangle_alt _ _)).
  refine (!_).
  etrans.
  {
    apply maponpaths.
    refine (!_).
    rewrite <- id_h_square_id.
    apply runitor_id_id_h.
  }
  rewrite runitor_h_triangle.
  apply idpath.
Qed.

(** * 3. Derived laws for the unitors on the identity *)
Proposition lunitor_h_runitor_h
            {C : double_cat}
            (x : C)
  : lunitor_h (identity_h x)
    =
    runitor_h (identity_h x).
Proof.
  refine (!(square_id_left_v' _) @ _ @ square_id_left_v' _).
  apply maponpaths.
  rewrite <- linvunitor_lunitor_h'.
  rewrite !transportf_square_prewhisker.
  apply maponpaths.
  refine (!(square_assoc_v' _ _ _) @ _ @ square_assoc_v' _ _ _).
  do 2 apply maponpaths.
  refine (!_).
  rewrite <- lunitor_square'.
  rewrite transportf_square_id.
  apply maponpaths_2.
  rewrite hcomp_runitor_lunitor.
  rewrite lunitor_id_id_h.
  apply idpath.
Qed.

Proposition runitor_h_lunitor_h
            {C : double_cat}
            (x : C)
  : runitor_h (identity_h x)
    =
    lunitor_h (identity_h x).
Proof.
  rewrite lunitor_h_runitor_h.
  apply idpath.
Qed.

Proposition linvunitor_h_rinvunitor_h
            {C : double_cat}
            (x : C)
  : linvunitor_h (identity_h x)
    =
    rinvunitor_h (identity_h x).
Proof.
  refine (!(square_id_right_v' _) @ _ @ square_id_right_v' _).
  apply maponpaths.
  rewrite <- !lunitor_linvunitor_h'.
  rewrite !transportf_square_postwhisker.
  apply maponpaths.
  refine (square_assoc_v _ _ _ @ _ @ !(square_assoc_v _ _ _)).
  apply maponpaths.
  apply maponpaths_2.
  rewrite linvunitor_lunitor_h.
  rewrite lunitor_h_runitor_h.
  rewrite rinvunitor_runitor_h.
  apply idpath.
Qed.

Proposition rinvunitor_h_linvunitor_h
            {C : double_cat}
            (x : C)
  : linvunitor_h (identity_h x)
    =
    rinvunitor_h (identity_h x).
Proof.
  rewrite linvunitor_h_rinvunitor_h.
  apply idpath.
Qed.
