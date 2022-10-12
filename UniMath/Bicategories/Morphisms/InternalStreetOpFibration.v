(********************************************************

 Internal Street opfibrations

 In this file, we define the notion of Street opfibration
 internal to a bicategory.

 1. Definition of an internal Street opfibration
 2. Street opfibrations in [B] are the same as Street fibrations in [op2_bicat B]
 3. Properties of opcartesian cells
 4. Morphisms of internal Street opfibrations
 5. Cells of internal Street opfibrations
 6. Equivalences preserve cartesian cells
 7. Pullbacks of Street opfibrations

 ********************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.

Local Open Scope cat.

(**
 1. Definition of an internal Street opfibration
 *)
Section InternalStreetOpFibration.
  Context {B : bicat}
          {e b : B}
          (p : e --> b).

  Definition is_opcartesian_2cell_sopfib
             {x : B}
             {f g : x --> e}
             (γ : f ==> g)
    : UU
    := ∏ (h : x --> e)
         (α : f ==> h)
         (δp : g · p ==> h · p)
         (q : α ▹ p = (γ ▹ p) • δp),
       ∃! (δ : g ==> h),
       δ ▹ p = δp
       ×
       γ • δ = α.

  Definition is_opcartesian_2cell_sopfib_factor
             {x : B}
             {f g : x --> e}
             {γ : f ==> g}
             (Hγ : is_opcartesian_2cell_sopfib γ)
             {h : x --> e}
             (α : f ==> h)
             (δp : g · p ==> h · p)
             (q : α ▹ p = (γ ▹ p) • δp)
    : g ==> h
    := pr11 (Hγ h α δp q).

  Definition is_opcartesian_2cell_sopfib_factor_over
             {x : B}
             {f g : x --> e}
             {γ : f ==> g}
             (Hγ : is_opcartesian_2cell_sopfib γ)
             {h : x --> e}
             (α : f ==> h)
             (δp : g · p ==> h · p)
             (q : α ▹ p = (γ ▹ p) • δp)
    : (is_opcartesian_2cell_sopfib_factor Hγ _ _ q) ▹ p = δp
    := pr121 (Hγ h α δp q).

  Definition is_opcartesian_2cell_sopfib_factor_comm
             {x : B}
             {f g : x --> e}
             {γ : f ==> g}
             (Hγ : is_opcartesian_2cell_sopfib γ)
             {h : x --> e}
             (α : f ==> h)
             (δp : g · p ==> h · p)
             (q : α ▹ p = (γ ▹ p) • δp)
    : γ • is_opcartesian_2cell_sopfib_factor Hγ _ _ q = α
    := pr221 (Hγ h α δp q).

  Definition is_opcartesian_2cell_sopfib_factor_unique
             {x : B}
             {f g : x --> e}
             {γ : f ==> g}
             (Hγ : is_opcartesian_2cell_sopfib γ)
             (h : x --> e)
             (α : f ==> h)
             (δp : g · p ==> h · p)
             (q : α ▹ p = (γ ▹ p) • δp)
             (δ₁ δ₂ : g ==> h)
             (pδ₁ : δ₁ ▹ p = δp)
             (pδ₂ : δ₂ ▹ p = δp)
             (δγ₁ : γ • δ₁ = α)
             (δγ₂ : γ • δ₂ = α)
    : δ₁ = δ₂.
  Proof.
    pose (proofirrelevance
            _
            (isapropifcontr (Hγ h α δp q))
            (δ₁ ,, pδ₁ ,, δγ₁)
            (δ₂ ,, pδ₂ ,, δγ₂))
      as H.
    exact (maponpaths pr1 H).
  Qed.

  Definition isaprop_is_opcartesian_2cell_sopfib
             {x : B}
             {f : x --> e}
             {g : x --> e}
             (γ : f ==> g)
    : isaprop (is_opcartesian_2cell_sopfib γ).
  Proof.
    do 4 (use impred ; intro).
    apply isapropiscontr.
  Qed.

  Definition internal_sopfib_opcleaving
    : UU
    := ∏ (x : B)
         (f : x --> e)
         (g : x --> b)
         (α : f · p ==> g),
       ∑ (h : x --> e)
         (γ : f ==> h)
         (β : invertible_2cell g (h · p)),
       is_opcartesian_2cell_sopfib γ
       ×
       γ ▹ p = α • β.

  Definition internal_sopfib_opcleaving_lift_mor
             (H : internal_sopfib_opcleaving)
             {x : B}
             {f : x --> e}
             {g : x --> b}
             (α : f · p ==> g)
    : x --> e
    := pr1 (H _ _ _ α).

  Definition internal_sopfib_opcleaving_lift_cell
             (H : internal_sopfib_opcleaving)
             {x : B}
             {f : x --> e}
             {g : x --> b}
             (α : f · p ==> g)
    : f ==> internal_sopfib_opcleaving_lift_mor H α
    := pr12 (H _ _ _ α).

  Definition internal_sopfib_opcleaving_com
             (H : internal_sopfib_opcleaving)
             {x : B}
             {f : x --> e}
             {g : x --> b}
             (α : f · p ==> g)
    : invertible_2cell g (internal_sopfib_opcleaving_lift_mor H α · p)
    := pr122 (H _ _ _ α).

  Definition internal_sopfib_opcleaving_is_opcartesian
             (H : internal_sopfib_opcleaving)
             {x : B}
             {f : x --> e}
             {g : x --> b}
             (α : f · p ==> g)
    : is_opcartesian_2cell_sopfib (internal_sopfib_opcleaving_lift_cell H α)
    := pr1 (pr222 (H _ _ _ α)).

  Definition internal_sopfib_opcleaving_over
             (H : internal_sopfib_opcleaving)
             {x : B}
             {f : x --> e}
             {g : x --> b}
             (α : f · p ==> g)
    : internal_sopfib_opcleaving_lift_cell H α ▹ p
      =
      α • internal_sopfib_opcleaving_com H α
    := pr2 (pr222 (H _ _ _ α)).

  Definition lwhisker_is_opcartesian
    : UU
    := ∏ (x y : B)
         (h : y --> x)
         (f g : x --> e)
         (γ : f ==> g)
         (Hγ : is_opcartesian_2cell_sopfib γ),
       is_opcartesian_2cell_sopfib (h ◃ γ).

  Definition internal_sopfib
    : UU
    := internal_sopfib_opcleaving × lwhisker_is_opcartesian.

  Coercion internal_sopfib_to_opcleaving
           (H : internal_sopfib)
    : internal_sopfib_opcleaving
    := pr1 H.
End InternalStreetOpFibration.

(**
 2. Street opfibrations in [B] are the same as Street fibrations in [op2_bicat B]
 *)
Definition is_cartesian_to_is_opcartesian_sfib
           {B : bicat}
           {e b : B}
           {p : e --> b}
           {x : B}
           {f g : x --> e}
           {α : f ==> g}
           (Hα : @is_cartesian_2cell_sfib (op2_bicat B) e b p x g f α)
  : is_opcartesian_2cell_sopfib p α.
Proof.
  intros h γ δp q.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros δ₁ δ₂ ;
       use subtypePath ;
       [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
       exact (is_cartesian_2cell_sfib_factor_unique
                _
                Hα
                _
                γ
                δp
                q
                _ _
                (pr12 δ₁)
                (pr12 δ₂)
                (pr22 δ₁)
                (pr22 δ₂))).
  - exact (is_cartesian_2cell_sfib_factor _ Hα γ δp q
           ,,
           is_cartesian_2cell_sfib_factor_over _ Hα q
           ,,
           is_cartesian_2cell_sfib_factor_comm _ Hα q).
Defined.

Definition is_opcartesian_to_is_cartesian_sfib
           {B : bicat}
           {e b : B}
           {p : e --> b}
           {x : B}
           {f g : x --> e}
           {α : f ==> g}
           (Hα : is_opcartesian_2cell_sopfib p α)
  : @is_cartesian_2cell_sfib (op2_bicat B) e b p x g f α.
Proof.
  intros h γ δp q.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros δ₁ δ₂ ;
       use subtypePath ;
       [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
       exact (is_opcartesian_2cell_sopfib_factor_unique
                _
                Hα
                _
                γ
                δp
                q
                _ _
                (pr12 δ₁)
                (pr12 δ₂)
                (pr22 δ₁)
                (pr22 δ₂))).
  - exact (is_opcartesian_2cell_sopfib_factor _ Hα γ δp q
           ,,
           is_opcartesian_2cell_sopfib_factor_over _ Hα _ _ q
           ,,
           is_opcartesian_2cell_sopfib_factor_comm _ Hα _ _ q).
Defined.

Definition is_cartesian_weq_is_opcartesian_sfib
           {B : bicat}
           {e b : B}
           {p : e --> b}
           {x : B}
           {f g : x --> e}
           (α : f ==> g)
  : @is_cartesian_2cell_sfib (op2_bicat B) e b p x g f α
    ≃
    is_opcartesian_2cell_sopfib p α.
Proof.
  use weqimplimpl.
  - exact is_cartesian_to_is_opcartesian_sfib.
  - exact is_opcartesian_to_is_cartesian_sfib.
  - apply isaprop_is_cartesian_2cell_sfib.
  - apply isaprop_is_opcartesian_2cell_sopfib.
Defined.

Definition internal_sfib_is_internal_sopfib
           {B : bicat}
           {e b : B}
           {p : e --> b}
           (Hp : @internal_sfib (op2_bicat B) e b p)
  : internal_sopfib p.
Proof.
  split.
  - intros x f g α.
    refine (internal_sfib_cleaving_lift_mor _ Hp α
            ,,
            internal_sfib_cleaving_lift_cell _ Hp α
            ,,
            weq_op2_invertible_2cell
              _ _
              (internal_sfib_cleaving_com _ Hp α)
            ,,
            _
            ,,
            internal_sfib_cleaving_over _ Hp α).
    apply is_cartesian_to_is_opcartesian_sfib.
    exact (internal_sfib_cleaving_is_cartesian _ Hp α).
  - intros x y h f g γ Hγ.
    apply is_cartesian_to_is_opcartesian_sfib.
    apply (pr2 Hp).
    apply is_opcartesian_to_is_cartesian_sfib.
    exact Hγ.
Defined.

Definition internal_sopfib_is_internal_sfib
           {B : bicat}
           {e b : B}
           {p : e --> b}
           (Hp : internal_sopfib p)
  : @internal_sfib (op2_bicat B) e b p.
Proof.
  split.
  - intros x f g α.
    refine (internal_sopfib_opcleaving_lift_mor _ Hp α
            ,,
            internal_sopfib_opcleaving_lift_cell _ Hp α
            ,,
            weq_op2_invertible_2cell
              _ _
              (internal_sopfib_opcleaving_com _  Hp α)
            ,,
            _
            ,,
            internal_sopfib_opcleaving_over _ Hp α).
    apply is_opcartesian_to_is_cartesian_sfib.
    exact (internal_sopfib_opcleaving_is_opcartesian _ Hp α).
  - intros x y h f g γ Hγ.
    apply is_opcartesian_to_is_cartesian_sfib.
    apply (pr2 Hp).
    apply is_cartesian_to_is_opcartesian_sfib.
    exact Hγ.
Defined.

Definition internal_sopfib_weq_internal_sfib_inv_left
           {B : bicat}
           {e b : B}
           {p : e --> b}
           (Hp : @internal_sfib (op2_bicat B) e b p)
  : internal_sopfib_is_internal_sfib
      (internal_sfib_is_internal_sopfib Hp)
    =
    Hp.
Proof.
  use pathsdirprod ;
    repeat (use funextsec ; intro) ;
    repeat (refine (maponpaths (λ z, _ ,, z) _)).
  - use pathsdirprod.
    + apply isaprop_is_cartesian_2cell_sfib.
    + apply idpath.
  - apply isapropiscontr.
Qed.

Definition internal_sopfib_weq_internal_sfib_inv_right
           {B : bicat}
           {e b : B}
           {p : e --> b}
           (Hp : internal_sopfib p)
  : internal_sfib_is_internal_sopfib
      (internal_sopfib_is_internal_sfib Hp)
    =
    Hp.
Proof.
  use pathsdirprod ;
    repeat (use funextsec ; intro) ;
    repeat (refine (maponpaths (λ z, _ ,, z) _)).
  - use pathsdirprod.
    + apply isaprop_is_opcartesian_2cell_sopfib.
    + apply idpath.
  - apply isapropiscontr.
Qed.

Definition internal_sopfib_weq_internal_sfib
           {B : bicat}
           {e b : B}
           (p : e --> b)
  : @internal_sfib (op2_bicat B) e b p ≃ internal_sopfib p.
Proof.
  use make_weq.
  - exact internal_sfib_is_internal_sopfib.
  - use isweq_iso.
    + exact internal_sopfib_is_internal_sfib.
    + exact internal_sopfib_weq_internal_sfib_inv_left.
    + exact internal_sopfib_weq_internal_sfib_inv_right.
Defined.

Definition isaprop_internal_sopfib
           {B : bicat}
           (HB_2_1 : is_univalent_2_1 B)
           {e b : B}
           (p : e --> b)
  : isaprop (internal_sopfib p).
Proof.
  use (isofhlevelweqf _ (internal_sopfib_weq_internal_sfib p)).
  apply isaprop_internal_sfib.
  apply op2_bicat_is_univalent_2_1.
  exact HB_2_1.
Qed.

(**
 3. Properties of opcartesian cells
 *)
Definition id_is_opcartesian_2cell_sopfib
           {B : bicat}
           {e b : B}
           (p : e --> b)
           {x : B}
           (f : x --> e)
  : is_opcartesian_2cell_sopfib p (id2 f).
Proof.
  apply is_cartesian_to_is_opcartesian_sfib.
  apply (@id_is_cartesian_2cell_sfib (op2_bicat B)).
Defined.

Definition vcomp_is_opcartesian_2cell_sopfib
           {B : bicat}
           {e b : B}
           (p : e --> b)
           {x : B}
           {f g h : x --> e}
           {α : f ==> g}
           {β : g ==> h}
           (Hα : is_opcartesian_2cell_sopfib p α)
           (Hβ : is_opcartesian_2cell_sopfib p β)
  : is_opcartesian_2cell_sopfib p (α • β).
Proof.
  apply is_cartesian_to_is_opcartesian_sfib.
  use vcomp_is_cartesian_2cell_sfib.
  - apply is_opcartesian_to_is_cartesian_sfib.
    exact Hβ.
  - apply is_opcartesian_to_is_cartesian_sfib.
    exact Hα.
Defined.

Definition invertible_is_opcartesian_2cell_sopfib
           {B : bicat}
           {e b : B}
           (p : e --> b)
           {x : B}
           {f g : x --> e}
           (α : f ==> g)
           (Hα : is_invertible_2cell α)
  : is_opcartesian_2cell_sopfib p α.
Proof.
  apply is_cartesian_to_is_opcartesian_sfib.
  apply invertible_is_cartesian_2cell_sfib.
  apply to_op2_is_invertible_2cell.
  exact Hα.
Defined.

Definition locally_grpd_opcartesian
           {B : bicat}
           (HB : locally_groupoid B)
           {e b : B}
           (p : e --> b)
           {x : B}
           {f g : x --> e}
           (γ : f ==> g)
  : is_opcartesian_2cell_sopfib p γ.
Proof.
  apply invertible_is_opcartesian_2cell_sopfib.
  apply HB.
Defined.

Definition is_opcartesian_2cell_sopfib_precomp
           {B : bicat}
           {e b : B}
           (p : e --> b)
           {x : B}
           {f g h : x --> e}
           (α : f ==> g) {β : g ==> h}
           {γ : f ==> h}
           (Hα : is_opcartesian_2cell_sopfib p α)
           (Hγ : is_opcartesian_2cell_sopfib p γ)
           (q : α • β = γ)
  : is_opcartesian_2cell_sopfib p β.
Proof.
  apply is_cartesian_to_is_opcartesian_sfib.
  refine (@is_cartesian_2cell_sfib_postcomp
           (op2_bicat B)
           _ _ _ _ _ _ _
           β α γ
           _ _ _).
  - apply is_opcartesian_to_is_cartesian_sfib.
    exact Hα.
  - apply is_opcartesian_to_is_cartesian_sfib.
    exact Hγ.
  - exact q.
Defined.

Definition invertible_between_opcartesians
           {B : bicat}
           {x e b : B}
           {p : e --> b}
           {g₀ g₁ g₂ : x --> e}
           {α : g₀ ==> g₁}
           (Hα : is_opcartesian_2cell_sopfib p α)
           {β : g₀ ==> g₂}
           (Hβ : is_opcartesian_2cell_sopfib p β)
           (δ : invertible_2cell (g₂ · p) (g₁ · p))
           (q : α ▹ p = (β ▹ p) • pr1 δ)
  : invertible_2cell g₂ g₁.
Proof.
  use (make_invertible_2cell
           (weq_op2_invertible_2cell
              _ _
              (@invertible_between_cartesians
                 (op2_bicat B)
                 x e b
                 p
                 _ _ _
                 α
                 (is_opcartesian_to_is_cartesian_sfib Hα)
                 β
                 (is_opcartesian_to_is_cartesian_sfib Hβ)
                 _
                 _))).
  - exact (weq_op2_invertible_2cell _ _ δ).
  - exact q.
Defined.

Definition locally_grpd_internal_sopfib
           {B : bicat}
           (HB : locally_groupoid B)
           {e b : B}
           (p : e --> b)
  : internal_sopfib p.
Proof.
  split.
  - intros x f g α.
    refine (f
            ,,
            id2 _
            ,,
            inv_of_invertible_2cell (make_invertible_2cell (HB _ _ _ _ α))
            ,,
            locally_grpd_opcartesian HB _ _
            ,,
            _).
    abstract
      (cbn ;
       rewrite id2_rwhisker ;
       rewrite vcomp_rinv ;
       apply idpath).
  - intro ; intros.
    apply (locally_grpd_opcartesian HB).
Defined.

(**
 4. Morphisms of internal Street opfibrations
 *)
Definition mor_preserves_opcartesian
           {B : bicat}
           {e₁ b₁ : B}
           (p₁ : e₁ --> b₁)
           {e₂ b₂ : B}
           (p₂ : e₂ --> b₂)
           (fe : e₁ --> e₂)
  : UU
  := ∏ (x : B)
       (f g : x --> e₁)
       (γ : f ==> g)
       (Hγ : is_opcartesian_2cell_sopfib p₁ γ),
     is_opcartesian_2cell_sopfib p₂ (γ ▹ fe).

Definition mor_preserves_cartesian_to_mor_preserves_opcartesian
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           (H : @mor_preserves_cartesian
                  (op2_bicat B)
                  e₁ b₁ p₁
                  e₂ b₂ p₂
                  fe)
  : mor_preserves_opcartesian p₁ p₂ fe.
Proof.
  intros x f g γ Hγ.
  apply is_cartesian_to_is_opcartesian_sfib.
  apply H.
  apply is_opcartesian_to_is_cartesian_sfib.
  exact Hγ.
Defined.

Definition mor_preserves_opcartesian_to_mor_preserves_cartesian
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           (H : mor_preserves_opcartesian p₁ p₂ fe)
  : @mor_preserves_cartesian
      (op2_bicat B)
      e₁ b₁ p₁
      e₂ b₂ p₂
      fe.
Proof.
  intros x f g γ Hγ.
  apply is_opcartesian_to_is_cartesian_sfib.
  apply H.
  apply is_cartesian_to_is_opcartesian_sfib.
  exact Hγ.
Defined.

Definition id_mor_preserves_opcartesian
           {B : bicat}
           {e b : B}
           (p : e --> b)
  : mor_preserves_opcartesian p p (id₁ e).
Proof.
  intros ? ? ? ? H.
  assert (γ ▹ id₁ e = runitor _ • γ • rinvunitor _) as q.
  {
    use vcomp_move_L_Mp ; [ is_iso | ].
    cbn.
    rewrite !vcomp_runitor.
    apply idpath.
  }
  rewrite q.
  use vcomp_is_opcartesian_2cell_sopfib.
  - use vcomp_is_opcartesian_2cell_sopfib.
    + use invertible_is_opcartesian_2cell_sopfib.
      is_iso.
    + exact H.
  - use invertible_is_opcartesian_2cell_sopfib.
    is_iso.
Qed.

Definition comp_preserves_opcartesian
           {B : bicat}
           {e₁ b₁ e₂ b₂ e₃ b₃ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {p₃ : e₃ --> b₃}
           {fe₁ : e₁ --> e₂}
           {fe₂ : e₂ --> e₃}
           (H₁ : mor_preserves_opcartesian p₁ p₂ fe₁)
           (H₂ : mor_preserves_opcartesian p₂ p₃ fe₂)
  : mor_preserves_opcartesian p₁ p₃ (fe₁ · fe₂).
Proof.
  intros x f g γ Hγ.
  specialize (H₁ x _ _ γ Hγ).
  specialize (H₂ x _ _ _ H₁).
  assert (γ ▹ fe₁ · fe₂
          =
          lassociator _ _ _
          • ((γ ▹ fe₁) ▹ fe₂)
          • rassociator _ _ _)
    as q.
  {
    use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
    rewrite rwhisker_rwhisker.
    apply idpath.
  }
  rewrite q.
  use vcomp_is_opcartesian_2cell_sopfib.
  - use vcomp_is_opcartesian_2cell_sopfib.
    + use invertible_is_opcartesian_2cell_sopfib.
      is_iso.
    + exact H₂.
  - use invertible_is_opcartesian_2cell_sopfib.
    is_iso.
Qed.

Definition is_opcartesian_2cell_sopfib_inv2cell
           {B : bicat}
           {x e b : B}
           {p p' : e --> b}
           (α : invertible_2cell p p')
           {f g : x --> e}
           {β : f ==> g}
           (Hβ : is_opcartesian_2cell_sopfib p β)
  : is_opcartesian_2cell_sopfib p' β.
Proof.
  apply is_cartesian_to_is_opcartesian_sfib.
  use (is_cartesian_2cell_sfib_inv2cell
         (inv_of_invertible_2cell
            (weq_op2_invertible_2cell _ _ α))).
  apply is_opcartesian_to_is_cartesian_sfib.
  exact Hβ.
Defined.

Definition invertible_2cell_mor_between_preserves_opcartesian
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe₁ fe₂ : e₁ --> e₂}
           (α : invertible_2cell fe₁ fe₂)
           (H : mor_preserves_opcartesian p₁ p₂ fe₁)
  : mor_preserves_opcartesian p₁ p₂ fe₂.
Proof.
  intros x f g γ Hγ.
  assert ((_ ◃ α) • (γ ▹ fe₂) = (γ ▹ fe₁) • (_ ◃ α)) as p.
  {
    rewrite vcomp_whisker.
    apply idpath.
  }
  use (is_opcartesian_2cell_sopfib_precomp _ _ _ _ p).
  - use invertible_is_opcartesian_2cell_sopfib.
    is_iso.
    apply property_from_invertible_2cell.
  - use vcomp_is_opcartesian_2cell_sopfib.
    + exact (H x f g γ Hγ).
    + use invertible_is_opcartesian_2cell_sopfib.
      is_iso.
      apply property_from_invertible_2cell.
Defined.

Definition invertible_2cell_between_preserves_opcartesian
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ p₁' : e₁ --> b₁}
           {p₂ p₂' : e₂ --> b₂}
           {fe fe' : e₁ --> e₂}
           (α : invertible_2cell p₁ p₁')
           (β : invertible_2cell p₂ p₂')
           (γ : invertible_2cell fe fe')
           (H : mor_preserves_opcartesian p₁ p₂ fe)
  : mor_preserves_opcartesian p₁' p₂' fe'.
Proof.
  intros w h₁ h₂ ζ Hζ.
  use (is_opcartesian_2cell_sopfib_inv2cell β).
  use (invertible_2cell_mor_between_preserves_opcartesian γ H).
  use (is_opcartesian_2cell_sopfib_inv2cell (inv_of_invertible_2cell α)).
  exact Hζ.
Defined.

Definition locally_grpd_preserves_opcartesian
           {B : bicat}
           (HB : locally_groupoid B)
           {e₁ b₁ e₂ b₂ : B}
           (p₁ : e₁ --> b₁)
           (p₂ : e₂ --> b₂)
           (fe : e₁ --> e₂)
  : mor_preserves_opcartesian p₁ p₂ fe.
Proof.
  intro ; intros.
  apply (locally_grpd_opcartesian HB).
Defined.

Definition isaprop_mor_preserves_opcartesian
           {B : bicat}
           {e₁ b₁ : B}
           (p₁ : e₁ --> b₁)
           {e₂ b₂ : B}
           (p₂ : e₂ --> b₂)
           (fe : e₁ --> e₂)
  : isaprop (mor_preserves_opcartesian p₁ p₂ fe).
Proof.
  do 5 (use impred ; intro).
  exact (isaprop_is_opcartesian_2cell_sopfib _ _).
Qed.

Definition mor_of_internal_sopfib_over
           {B : bicat}
           {e₁ b₁ : B}
           (p₁ : e₁ --> b₁)
           {e₂ b₂ : B}
           (p₂ : e₂ --> b₂)
           (fb : b₁ --> b₂)
  : UU
  := ∑ (fe : e₁ --> e₂),
     mor_preserves_opcartesian p₁ p₂ fe
     ×
     invertible_2cell (p₁ · fb) (fe · p₂).

Definition make_mor_of_internal_sopfib_over
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fb : b₁ --> b₂}
           (fe : e₁ --> e₂)
           (fc : mor_preserves_opcartesian p₁ p₂ fe)
           (f_com : invertible_2cell (p₁ · fb) (fe · p₂))
  : mor_of_internal_sopfib_over p₁ p₂ fb
  := (fe ,, fc ,, f_com).

Coercion mor_of_internal_sopfib_over_to_mor
         {B : bicat}
         {e₁ b₁ : B}
         {p₁ : e₁ --> b₁}
         {e₂ b₂ : B}
         {p₂ : e₂ --> b₂}
         {fb : b₁ --> b₂}
         (fe : mor_of_internal_sopfib_over p₁ p₂ fb)
  : e₁ --> e₂
  := pr1 fe.

Definition mor_of_internal_sopfib_over_preserves
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fb : b₁ --> b₂}
           (fe : mor_of_internal_sopfib_over p₁ p₂ fb)
  : mor_preserves_opcartesian p₁ p₂ fe
  := pr12 fe.

Definition mor_of_internal_sopfib_over_com
           {B : bicat}
           {e₁ b₁ : B}
           {p₁ : e₁ --> b₁}
           {e₂ b₂ : B}
           {p₂ : e₂ --> b₂}
           {fb : b₁ --> b₂}
           (fe : mor_of_internal_sopfib_over p₁ p₂ fb)
  : invertible_2cell (p₁ · fb) (fe · p₂)
  := pr22 fe.

Definition id_mor_of_internal_sopfib_over
           {B : bicat}
           {e b : B}
           (p : e --> b)
  : mor_of_internal_sopfib_over p p (id₁ _).
Proof.
  use make_mor_of_internal_sopfib_over.
  - exact (id₁ e).
  - apply id_mor_preserves_opcartesian.
  - use make_invertible_2cell.
    + refine (runitor _ • linvunitor _).
    + is_iso.
Defined.

Definition comp_mor_of_internal_sopfib_over
           {B : bicat}
           {e₁ e₂ e₃ b₁ b₂ b₃ : B}
           {fb₁ : b₁ --> b₂}
           {fb₂ : b₂ --> b₃}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {p₃ : e₃ --> b₃}
           (fe₁ : mor_of_internal_sopfib_over p₁ p₂ fb₁)
           (fe₂ : mor_of_internal_sopfib_over p₂ p₃ fb₂)
  : mor_of_internal_sopfib_over p₁ p₃ (fb₁ · fb₂).
Proof.
  use make_mor_of_internal_sopfib_over.
  - exact (fe₁ · fe₂).
  - exact (comp_preserves_opcartesian
             (mor_of_internal_sopfib_over_preserves fe₁)
             (mor_of_internal_sopfib_over_preserves fe₂)).
  - use make_invertible_2cell.
    + exact (lassociator _ _ _
             • (mor_of_internal_sopfib_over_com fe₁ ▹ _)
             • rassociator _ _ _
             • (_ ◃ mor_of_internal_sopfib_over_com fe₂)
             • lassociator _ _ _).
    + is_iso.
      * apply property_from_invertible_2cell.
      * apply property_from_invertible_2cell.
Defined.

(**
 5. Cells of internal Street opfibrations
 *)
Definition cell_of_internal_sopfib_over_homot
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           (γ : fb ==> gb)
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : mor_of_internal_sopfib_over p₁ p₂ fb}
           {ge : mor_of_internal_sopfib_over p₁ p₂ gb}
           (γe : fe ==> ge)
  : UU
  := mor_of_internal_sopfib_over_com fe • (γe ▹ _)
     =
     (_ ◃ γ) • mor_of_internal_sopfib_over_com ge.


Definition cell_of_internal_sopfib_over
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           (γ : fb ==> gb)
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           (fe : mor_of_internal_sopfib_over p₁ p₂ fb)
           (ge : mor_of_internal_sopfib_over p₁ p₂ gb)
  : UU
  := ∑ (γe : fe ==> ge), cell_of_internal_sopfib_over_homot γ γe.

Definition make_cell_of_internal_sopfib_over
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           {γ : fb ==> gb}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : mor_of_internal_sopfib_over p₁ p₂ fb}
           {ge : mor_of_internal_sopfib_over p₁ p₂ gb}
           (γe : fe ==> ge)
           (p : cell_of_internal_sopfib_over_homot γ γe)
  : cell_of_internal_sopfib_over γ fe ge
  := (γe ,, p).

Coercion cell_of_cell_of_internal_sopfib_over
         {B : bicat}
         {b₁ b₂ e₁ e₂ : B}
         {fb gb : b₁ --> b₂}
         {γ : fb ==> gb}
         {p₁ : e₁ --> b₁}
         {p₂ : e₂ --> b₂}
         {fe : mor_of_internal_sopfib_over p₁ p₂ fb}
         {ge : mor_of_internal_sopfib_over p₁ p₂ gb}
         (γe : cell_of_internal_sopfib_over γ fe ge)
  : fe ==> ge
  := pr1 γe.

Definition cell_of_internal_sopfib_over_eq
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           {γ : fb ==> gb}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : mor_of_internal_sopfib_over p₁ p₂ fb}
           {ge : mor_of_internal_sopfib_over p₁ p₂ gb}
           (γe : cell_of_internal_sopfib_over γ fe ge)
  : mor_of_internal_sopfib_over_com fe • (γe ▹ _)
     =
     (_ ◃ γ) • mor_of_internal_sopfib_over_com ge
  := pr2 γe.

Definition eq_cell_of_internal_sopfib_over
           {B : bicat}
           {b₁ b₂ e₁ e₂ : B}
           {fb gb : b₁ --> b₂}
           {γ : fb ==> gb}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : mor_of_internal_sopfib_over p₁ p₂ fb}
           {ge : mor_of_internal_sopfib_over p₁ p₂ gb}
           (γe₁ γe₂ : cell_of_internal_sopfib_over γ fe ge)
           (p : pr1 γe₁ = γe₂)
  : γe₁ = γe₂.
Proof.
  use subtypePath.
  {
    intro.
    apply cellset_property.
  }
  exact p.
Qed.
