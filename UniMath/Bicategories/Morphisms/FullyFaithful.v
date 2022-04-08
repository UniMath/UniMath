(**
 Faithful and fully faithful 1-cells in bicategories

 Contents:
 1. Definition of faithful 1-cells
 2. Characterization of faithful 1-cells
 3. Fully faithful 1-cells
 4. Characterization of fully faithful 1-cells
 5. Pseudomonic 1-cells
 6. Characterization of pseudomonic 1-cells
 7. Pseudomonic 1-cells in locally groupoidal bicategories
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.

Local Open Scope cat.

(**
 1. Definition of faithful 1-cells
 *)
Definition faithful_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : UU
  := ∏ (z : B)
       (g₁ g₂ : z --> a)
       (α₁ α₂ : g₁ ==> g₂),
     α₁ ▹ f = α₂ ▹ f
     →
     α₁ = α₂.

Definition faithful_1cell_eq_cell
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : faithful_1cell f)
           {z : B}
           {g₁ g₂ : z --> a}
           {α₁ α₂ : g₁ ==> g₂}
           (p : α₁ ▹ f = α₂ ▹ f)
  : α₁ = α₂
  := Hf _ _ _ _ _ p.

Definition isaprop_faithful_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : isaprop (faithful_1cell f).
Proof.
  repeat (use impred ; intro).
  apply cellset_property.
Qed.

(**
 2. Characterization of faithful 1-cells
 *)
Definition faithful_1cell_to_faithful
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : faithful_1cell f → ∏ (z : B), faithful (post_comp z f).
Proof.
  intros Hf z g₁ g₂ α ; cbn in *.
  use invproofirrelevance.
  intros φ₁ φ₂ ; cbn in *.
  use subtypePath.
  {
    intro ; apply cellset_property.
  }
  apply (faithful_1cell_eq_cell Hf).
  exact (pr2 φ₁ @ !(pr2 φ₂)).
Qed.

Definition faithful_to_faithful_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : (∏ (z : B), faithful (post_comp z f)) → faithful_1cell f.
Proof.
  intros Hf z g₁ g₂ α₁ α₂ p.
  pose (proofirrelevance _ (Hf z g₁ g₂ (α₂ ▹ f)) (α₁ ,, p) (α₂ ,, idpath _)) as q.
  exact (maponpaths pr1 q).
Qed.

Definition faithful_1cell_weq_faithful
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : (faithful_1cell f) ≃ (∏ (z : B), faithful (post_comp z f)).
Proof.
  use weqimplimpl.
  - exact (faithful_1cell_to_faithful f).
  - exact (faithful_to_faithful_1cell f).
  - exact (isaprop_faithful_1cell f).
  - use impred ; intro.
    apply isaprop_faithful.
Defined.

(**
 3. Fully faithful 1-cells
 *)
Definition fully_faithful_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : UU
  := (∏ (z : B)
        (g₁ g₂ : z --> a)
        (α₁ α₂ : g₁ ==> g₂),
      α₁ ▹ f = α₂ ▹ f
      →
      α₁ = α₂)
     ×
     (∏ (z : B)
        (g₁ g₂ : z --> a)
        (αf : g₁ · f ==> g₂ · f),
      ∑ (α : g₁ ==> g₂), α ▹ f = αf).

Definition fully_faithful_1cell_faithful
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : fully_faithful_1cell f)
  : faithful_1cell f
  := pr1 Hf.

Definition fully_faithful_1cell_eq
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : fully_faithful_1cell f)
           {z : B}
           {g₁ g₂ : z --> a}
           {α₁ α₂ : g₁ ==> g₂}
           (p : α₁ ▹ f = α₂ ▹ f)
  : α₁ = α₂
  := pr1 Hf _ _ _ _ _ p.

Definition fully_faithful_1cell_inv_map
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : fully_faithful_1cell f)
           {z : B}
           {g₁ g₂ : z --> a}
           (αf : g₁ · f ==> g₂ · f)
  : g₁ ==> g₂
  := pr1 (pr2 Hf _ _ _ αf).

Definition fully_faithful_1cell_inv_map_eq
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : fully_faithful_1cell f)
           {z : B}
           {g₁ g₂ : z --> a}
           (αf : g₁ · f ==> g₂ · f)
  : fully_faithful_1cell_inv_map Hf αf ▹ f = αf
  := pr2 (pr2 Hf _ _ _ αf).

Definition make_fully_faithful
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf₁ : faithful_1cell f)
           (Hf₂ : ∏ (z : B)
                    (g₁ g₂ : z --> a)
                    (αf : g₁ · f ==> g₂ · f),
                  ∑ (α : g₁ ==> g₂), α ▹ f = αf)
  : fully_faithful_1cell f
  := (Hf₁ ,, Hf₂).

Definition isaprop_fully_faithful_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : isaprop (fully_faithful_1cell f).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use pathsdirprod.
  - apply isaprop_faithful_1cell.
  - use funextsec ; intro z.
    use funextsec ; intro g₁.
    use funextsec ; intro g₂.
    use funextsec ; intro αf.
    use subtypePath.
    {
      intro ; apply cellset_property.
    }
    pose (ψ₁ := pr2 φ₁ z g₁ g₂ αf).
    pose (ψ₂ := pr2 φ₂ z g₁ g₂ αf).
    enough (pr1 ψ₁ = pr1 ψ₂) as X.
    {
      exact X.
    }
    use (fully_faithful_1cell_eq φ₁).
    exact (pr2 ψ₁ @ !(pr2 ψ₂)).
Qed.

(**
 4. Characterizations of fully faithful 1-cells
 *)
Definition fully_faithful_1cell_to_fully_faithful
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : fully_faithful_1cell f → ∏ (z : B), fully_faithful (post_comp z f).
Proof.
  intros Hf z g₁ g₂ α ; cbn in *.
  use iscontraprop1.
  - use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath ; [ intro ; apply cellset_property | ].
    cbn in *.
    apply (pr1 Hf).
    exact (pr2 φ₁ @ !(pr2 φ₂)).
  - exact (pr2 Hf z _ _ α).
Qed.

Definition fully_faithful_to_fully_faithful_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : (∏ (z : B), fully_faithful (post_comp z f)) → fully_faithful_1cell f.
Proof.
  intros Hf.
  use make_fully_faithful.
  - use faithful_to_faithful_1cell.
    intro z.
    apply fully_faithful_implies_full_and_faithful.
    apply Hf.
  - intros z g₁ g₂ αf.
    simple refine (_ ,, _).
    + exact (invmap (make_weq _ (Hf z g₁ g₂)) αf).
    + apply (homotweqinvweq (make_weq _ (Hf z g₁ g₂))).
Qed.

Definition fully_faithful_1cell_weq_fully_faithful
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : (fully_faithful_1cell f)
    ≃
    (∏ (z : B), fully_faithful (post_comp z f)).
Proof.
  use weqimplimpl.
  - exact (fully_faithful_1cell_to_fully_faithful f).
  - exact (fully_faithful_to_fully_faithful_1cell f).
  - exact (isaprop_fully_faithful_1cell f).
  - use impred ; intro.
    apply isaprop_fully_faithful.
Defined.

(**
 5. Pseudomonic 1-cells
 *)
Definition pseudomonic_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : UU
  := (∏ (z : B)
        (g₁ g₂ : z --> a)
        (α₁ α₂ : g₁ ==> g₂),
      α₁ ▹ f = α₂ ▹ f
      →
      α₁ = α₂)
     ×
     (∏ (z : B)
        (g₁ g₂ : z --> a)
        (αf : g₁ · f ==> g₂ · f)
        (Hαf : is_invertible_2cell αf),
      ∑ (α : g₁ ==> g₂), is_invertible_2cell α × α ▹ f = αf).


Definition pseudomonic_1cell_faithful
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : pseudomonic_1cell f)
  : faithful_1cell f
  := pr1 Hf.

Definition pseudomonic_1cell_eq
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : pseudomonic_1cell f)
           {z : B}
           {g₁ g₂ : z --> a}
           {α₁ α₂ : g₁ ==> g₂}
           (p : α₁ ▹ f = α₂ ▹ f)
  : α₁ = α₂
  := pr1 Hf _ _ _ _ _ p.

Definition pseudomonic_1cell_inv_map
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : pseudomonic_1cell f)
           {z : B}
           {g₁ g₂ : z --> a}
           (αf : g₁ · f ==> g₂ · f)
           (Hαf : is_invertible_2cell αf)
  : g₁ ==> g₂
  := pr1 (pr2 Hf _ _ _ αf Hαf).

Definition is_invertible_2cell_pseudomonic_1cell_inv_map
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : pseudomonic_1cell f)
           {z : B}
           {g₁ g₂ : z --> a}
           (αf : g₁ · f ==> g₂ · f)
           (Hαf : is_invertible_2cell αf)
  : is_invertible_2cell (pseudomonic_1cell_inv_map Hf αf Hαf)
  := pr12 (pr2 Hf _ _ _ αf Hαf).

Definition pseudomonic_1cell_inv_map_eq
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : pseudomonic_1cell f)
           {z : B}
           {g₁ g₂ : z --> a}
           (αf : g₁ · f ==> g₂ · f)
           (Hαf : is_invertible_2cell αf)
  : pseudomonic_1cell_inv_map Hf αf Hαf ▹ f = αf
  := pr22 (pr2 Hf _ _ _ αf Hαf).

Definition make_pseudomonic
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf₁ : faithful_1cell f)
           (Hf₂ : ∏ (z : B)
                    (g₁ g₂ : z --> a)
                    (αf : g₁ · f ==> g₂ · f)
                    (Hαf : is_invertible_2cell αf),
                  ∑ (α : g₁ ==> g₂),
                  is_invertible_2cell α × α ▹ f = αf)
  : pseudomonic_1cell f
  := (Hf₁ ,, Hf₂).

Definition isaprop_pseudomonic_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : isaprop (pseudomonic_1cell f).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use pathsdirprod.
  - apply isaprop_faithful_1cell.
  - use funextsec ; intro z.
    use funextsec ; intro g₁.
    use funextsec ; intro g₂.
    use funextsec ; intro αf.
    use funextsec ; intro Hαf.
    use subtypePath.
    {
      intro.
      apply isapropdirprod.
      + apply isaprop_is_invertible_2cell.
      + apply cellset_property.
    }
    pose (ψ₁ := pr2 φ₁ z g₁ g₂ αf Hαf).
    pose (ψ₂ := pr2 φ₂ z g₁ g₂ αf Hαf).
    enough (pr1 ψ₁ = pr1 ψ₂) as X.
    {
      exact X.
    }
    use (pseudomonic_1cell_eq φ₁).
    exact (pr22 ψ₁ @ !(pr22 ψ₂)).
Qed.

(**
  6. Characterization of pseudomonic 1-cells
 *)
Definition pseudomonic_1cell_to_pseudomonic
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : pseudomonic_1cell f → ∏ (z : B), pseudomonic (post_comp z f).
Proof.
  intros Hf z.
  split.
  - apply faithful_1cell_to_faithful.
    exact (pr1 Hf).
  - intros g₁ g₂ α.
    apply hinhpr.
    simple refine (_ ,, _) ; cbn.
    + apply inv2cell_to_iso.
      use make_invertible_2cell.
      * use (pseudomonic_1cell_inv_map Hf (iso_to_inv2cell α)).
        apply property_from_invertible_2cell.
      * apply is_invertible_2cell_pseudomonic_1cell_inv_map.
    + use subtypePath ; [ intro ; apply isaprop_is_iso | ].
      cbn.
      apply pseudomonic_1cell_inv_map_eq.
Qed.

Definition pseudomonic_to_pseudomonic_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : (∏ (z : B), pseudomonic (post_comp z f)) → pseudomonic_1cell f.
Proof.
  intro H.
  use make_pseudomonic.
  - apply faithful_to_faithful_1cell.
    intro z.
    apply H.
  - intros z g₁ g₂ αf Hαf.
    pose (w := make_weq _ (isweq_functor_on_iso_pseudomonic (H z) g₁ g₂)).
    simple refine (_ ,, _ ,, _).
    + apply (invweq w).
      use inv2cell_to_iso.
      exact (αf ,, Hαf).
    + cbn.
      apply is_iso_to_is_inv2cell.
      apply (pr2 (invmap w (inv2cell_to_iso (αf,, Hαf)))).
    + exact (maponpaths
               pr1
               (homotweqinvweq w (inv2cell_to_iso (αf,, Hαf)))).
Qed.

Definition pseudomonic_1cell_weq_pseudomonic
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : (pseudomonic_1cell f)
    ≃
    (∏ (z : B), pseudomonic (post_comp z f)).
Proof.
  use weqimplimpl.
  - exact (pseudomonic_1cell_to_pseudomonic f).
  - exact (pseudomonic_to_pseudomonic_1cell f).
  - exact (isaprop_pseudomonic_1cell f).
  - use impred ; intro.
    apply isaprop_pseudomonic.
Defined.

(**
 7. Pseudomonic 1-cells in locally groupoidal bicategories
 *)
Definition fully_faithful_is_pseudomonic
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : fully_faithful_1cell f)
  : pseudomonic_1cell f.
Proof.
  use make_pseudomonic.
  - exact (fully_faithful_1cell_faithful Hf).
  - intros z g₁ g₂ αf ?.
    refine (fully_faithful_1cell_inv_map Hf αf ,, _ ,, _).
    + use make_is_invertible_2cell.
      * exact (fully_faithful_1cell_inv_map Hf (Hαf^-1)).
      * abstract
          (use (fully_faithful_1cell_faithful Hf) ;
           rewrite <- rwhisker_vcomp ;
           rewrite !fully_faithful_1cell_inv_map_eq ;
           rewrite id2_rwhisker ;
           apply vcomp_rinv).
      * abstract
          (use (fully_faithful_1cell_faithful Hf) ;
           rewrite <- rwhisker_vcomp ;
           rewrite !fully_faithful_1cell_inv_map_eq ;
           rewrite id2_rwhisker ;
           apply vcomp_linv).
    + exact (fully_faithful_1cell_inv_map_eq Hf αf).
Defined.

Definition pseudomonic_is_fully_faithful_locally_grpd
           {B : bicat}
           (inv_B : locally_groupoid B)
           {a b : B}
           {f : a --> b}
           (Hf : pseudomonic_1cell f)
  : fully_faithful_1cell f.
Proof.
  use make_fully_faithful.
  - exact (pr1 Hf).
  - intros z g₁ g₂ αf.
    simple refine (_ ,, _).
    + use (pseudomonic_1cell_inv_map Hf αf).
      apply inv_B.
    + apply (pseudomonic_1cell_inv_map_eq Hf).
Defined.

Definition pseudomonic_weq_fully_faithful_locally_grpd
           {B : bicat}
           (inv_B : locally_groupoid B)
           {a b : B}
           (f : a --> b)
  : pseudomonic_1cell f ≃ fully_faithful_1cell f.
Proof.
  use weqimplimpl.
  - exact (pseudomonic_is_fully_faithful_locally_grpd inv_B).
  - exact fully_faithful_is_pseudomonic.
  - apply isaprop_pseudomonic_1cell.
  - apply isaprop_fully_faithful_1cell.
Defined.
