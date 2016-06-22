(* direct implementation of kernels *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.zero.

Section def_kernels.

  Context {C : precategory}.
  Hypothesis Z : Zero C.

  (** This rewrite is used to rewrite an equality f ;; g = ZeroArrow to
     f ;; g = f ;; ZeroArrow. This is because Equalizers need the latter
     equality. *)
  Lemma KernelEqRw {x y z : C} {g : y --> z} {f : x --> y}
        (H : f ;; g = ZeroArrow _ Z x z) :
    f ;; g = f ;; ZeroArrow _ Z y z.
  Proof.
    pathvia (ZeroArrow _ Z x z).
    apply H. apply pathsinv0. apply ZeroArrow_comp_right.
  Defined.

  (** Definition and construction of Kernels *)
  Definition Kernel {y z : C} (g : y --> z) :
    UU := Equalizer g (ZeroArrow _ Z y z).
  Definition mk_Kernel {x y z : C} (f : x --> y) (g : y --> z)
             (H : f ;; g = (ZeroArrow _ Z x z))
             (isE : isEqualizer g (ZeroArrow _ Z y z) f (KernelEqRw H))
    : Kernel g.
  Proof.
    use (mk_Equalizer g (ZeroArrow _ Z y z) f (KernelEqRw H)).
    apply isE.
  Defined.
  Definition Kernels := forall (y z : C) (g : y --> z), Kernel g.
  Definition hasKernels := forall (y z : C) (g : y --> z), ishinh (Kernel g).
  Definition KernelOb {y z : C} {g : y --> z} (K : Kernel g) :
    C := EqualizerObject K.
  Coercion KernelOb : Kernel >-> ob.
  Definition KernelArrow {y z : C} {g : y --> z} (K : Kernel g) :
    C⟦K, y⟧:= EqualizerArrow K.
  Definition KernelEqAr {y z : C} {g : y --> z} (K : Kernel g) :=
    EqualizerEqAr K.
  Definition KernelIn {y z : C} {g : y --> z} (K : Kernel g)
             (w : C) (h : w --> y) (H : h ;; g = ZeroArrow _ Z w z) :
    C⟦w, K⟧ := EqualizerIn K _ h (KernelEqRw H).

  (** Commutativity of Kernels. *)
  Lemma KernelCommutes {y z : C} {g : y --> z} (K : Kernel g)
        (w : C) (h : w --> y) (H : h ;; g = ZeroArrow _ Z w z) :
    (KernelIn K w h H) ;; (KernelArrow K) = h.
  Proof.
    apply (EqualizerCommutes K).
  Defined.

  (** Two arrows to Kernel, such that the compositions with KernelArrow
    are equal, are equal. *)
  Lemma KernelInsEq {y z: C} {g : y --> z} (K : Kernel g)
        {w : C} (φ1 φ2: C⟦w, K⟧)
        (H' : φ1 ;; (KernelArrow K) = φ2 ;; (KernelArrow K)) : φ1 = φ2.
  Proof.
    apply (isEqualizerInsEq (isEqualizer_Equalizer K) _ _ H').
  Defined.

  (** Results on morphisms between Kernels. *)
  Definition identity_is_KernelIn {y z : C} {g : y --> z}
             (K : Kernel g) :
    Σ φ : C⟦K, K⟧, φ ;; (KernelArrow K) = (KernelArrow K).
  Proof.
    exists (identity K).
    apply id_left.
  Defined.

  Lemma KernelEndo_is_identity {y z : C} {g : y --> z} {K : Kernel g}
        (φ : C⟦K, K⟧) (H : φ ;; (KernelArrow K) = KernelArrow K) :
    identity K = φ.
  Proof.
    set (H1 := tpair ((fun φ' : C⟦K, K⟧ => φ' ;; _ = _)) φ H).
    assert (H2 : identity_is_KernelIn K = H1).
    - apply proofirrelevance.
      apply isapropifcontr.
      apply (isEqualizer_Equalizer K).
      apply KernelEqAr.
    - apply (base_paths _ _ H2).
  Defined.

  Definition from_Kernel_to_Kernel {y z : C} {g : y --> z}
             (K K': Kernel g) : C⟦K, K'⟧.
  Proof.
    apply (KernelIn K' K (KernelArrow K)).
    pathvia (KernelArrow K ;; ZeroArrow _ Z y z).
    apply KernelEqAr.
    apply ZeroArrow_comp_right.
  Defined.

  Lemma are_inverses_from_Kernel_to_Kernel {y z : C} {g : y --> z}
        {K K': Kernel g} :
    is_inverse_in_precat (from_Kernel_to_Kernel K K')
                         (from_Kernel_to_Kernel K' K).
  Proof.
    split; apply pathsinv0; use KernelEndo_is_identity;
    rewrite <- assoc; unfold from_Kernel_to_Kernel;
      repeat rewrite KernelCommutes; apply idpath.
  Defined.

  Lemma isiso_from_Kernel_to_Kernel {y z : C} {g : y --> z}
        (K K' : Kernel g) :
    is_isomorphism (from_Kernel_to_Kernel K K').
  Proof.
    apply (is_iso_qinv _ (from_Kernel_to_Kernel K' K)).
    apply are_inverses_from_Kernel_to_Kernel.
  Defined.

  Definition iso_from_Kernel_to_Kernel {y z : C} {g : y --> z}
             (K K' : Kernel g) : iso K K' :=
    tpair _ _ (isiso_from_Kernel_to_Kernel K K').

  (** It follows that KernelArrow is monic. *)
  Lemma KernelArrowisMonic {y z : C} {g : y --> z} (K : Kernel g ) :
    isMonic _ (KernelArrow K).
  Proof.
    apply EqualizerArrowisMonic.
  Defined.
End def_kernels.