(**
   Preservation And Reflection Of Parameterized Natural Numbers Objects, by Weak Equivalences.

   In this file, we show that any weak equivalence F : C -> D preserves a parameterized natural numbers object.

   Contents
   1. Image of a PNNO, under F, is a PNNO [weak_equiv_preserves_parameterized_NNO]
   2. Weak equivalences preserve PNNNO's, up to isomorphism [weak_equiv_preserves_parameterized_NNO']
   3. Weak Equivalences reflect PNNNO's [weak_equiv_reflects_parameterized_NNO]
   4. Preservation of PNNO lift along weak equivalences [weak_equiv_lifts_preserves_parameterized_NNO]

   Remark: Observe that no univalence conditions are needed
 *)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Arithmetic.NNO.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Binproducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Creation.BinProducts.

Local Open Scope cat.

(* To be moved *)

Lemma parameterized_NNO_independent_of_terminal
  {C : category} {T : Terminal C} {P : BinProducts C} (N : parameterized_NNO T P) (T' : Terminal C)
  : parameterized_NNO T' P.
Proof.
  use make_parameterized_NNO.
  - exact N.
  - refine (_ · parameterized_NNO_Z N).
    apply z_iso_Terminals.
  - exact (parameterized_NNO_S N).
  - intros b y z s.
    use (iscontrweqb' (pr222 N b y z s)).
    use weqfibtototal.
    intro f.
    simpl.
    use weqdirprodf.
    + rewrite assoc.
      assert (pf : TerminalArrow T' b · TerminalArrow T T' = TerminalArrow T b).
      { use TerminalArrowUnique. }
      rewrite pf.
      apply idweq.
    + apply idweq.
Defined.

Lemma parameterized_NNO_unique_up_to_iso
  {C : category} {T : Terminal C} {P : BinProducts C} (N M : parameterized_NNO T P)
  : z_iso N M.
Proof.
  exact (iso_between_NNO (parameterized_NNO_to_NNO N) (parameterized_NNO_to_NNO M)).
Defined.

Lemma parameterized_NNO_unique_up_to_iso'
  {C : category} {T : Terminal C} {P : BinProducts C} (N M : parameterized_NNO T P)
  : z_iso N M.
Proof.
  use make_z_iso.
  - apply is_NNO_parameterized_NNO_mor ; apply M.
  - apply is_NNO_parameterized_NNO_mor ; apply N.
  - split.
    + simpl ; use is_NNO_parameterized_NNO_unique ; (try apply N).
      * simpl ; rewrite assoc.
        now do 2 rewrite is_NNO_parameterized_NNO_mor_Z.
      * simpl ; rewrite assoc.
        rewrite is_NNO_parameterized_NNO_mor_S.
        rewrite assoc'.
        rewrite is_NNO_parameterized_NNO_mor_S.
        now rewrite assoc.
      * apply id_right.
      * exact (id_right _ @ ! id_left _).
    + simpl ; use is_NNO_parameterized_NNO_unique ; (try apply M).
      * simpl ; rewrite assoc.
        now do 2 rewrite is_NNO_parameterized_NNO_mor_Z.
      * simpl ; rewrite assoc.
        rewrite is_NNO_parameterized_NNO_mor_S.
        rewrite assoc'.
        rewrite is_NNO_parameterized_NNO_mor_S.
        now rewrite assoc.
      * apply id_right.
      * exact (id_right _ @ ! id_left _).
Defined.

Lemma BinProductOfIsIsos {C : category} {x x' y y' : C} (i : C⟦x, x'⟧) (j : C⟦y,y'⟧)
                       (p : BinProduct _ x y) (p' : BinProduct _ x' y')
  : is_z_isomorphism i → is_z_isomorphism j → is_z_isomorphism (BinProductOfArrows _ p' p i j).
Proof.
  intros ii jj.
  use make_is_z_isomorphism.
  - exact (BinProductOfArrows _ p p' (pr1 ii) (pr1 jj)).
  - exact (binproduct_of_z_iso_inv p p' (_,,ii) (_,,jj)).
Defined.

(** * 1. Image of a PNNO is a PNNO *)
Section WeakEquivalencesPreserveNNOs.

  Context {C D : category}
    {F : C ⟶ D} (F_weq : is_weak_equiv F)
    {T_C : Terminal C} {P_C : BinProducts C} (N_C : parameterized_NNO T_C P_C)
    (P_D : BinProducts D).

  Let T_D : Terminal D
      := weak_equiv_creates_terminal F_weq T_C.

  Definition weak_equiv_preserves_parameterized_NNO_Z
    : D⟦T_D, F N_C⟧
    := #F (parameterized_NNO_Z N_C).
  Let F_Z := weak_equiv_preserves_parameterized_NNO_Z.

  Definition weak_equiv_preserves_parameterized_NNO_S
    : D⟦F N_C, F N_C⟧
    := #F (parameterized_NNO_S N_C).
  Let F_S := weak_equiv_preserves_parameterized_NNO_S.

  Context {b' y' : D}
    (z' : D⟦b', y'⟧) (s' : D⟦y', y'⟧)
    {b y : C}
    (i_b : z_iso (F b) b')
    (i_y : z_iso (F y) y').

  Let bp (f : D⟦b', F N_C⟧)
      := BinProductArrow D (P_D b' (F N_C)) (identity b') f.
  Let bp' (f : D⟦F N_C, F N_C⟧)
      := BinProductOfArrows D (P_D b' (F N_C)) (P_D b' (F N_C)) (identity b') f.

  Let A
      := ∑ f : D ⟦ P_D b' (F N_C), y'⟧,
          bp (TerminalArrow T_D b' · F_Z) · f = z' × bp' F_S · f = f · s'.

  Let P_D' (x y : C) : BinProduct _ (F x) (F y)
      := make_BinProduct _ _ _ _ _ _ (weak_equiv_preserves_chosen_binproducts F_weq P_C x y).

  Let bp''
    : z_iso (F (P_C b N_C)) (P_D b' (F N_C)).
  Proof.
    exists (BinProductOfArrows D (P_D _ _) (P_D' _ _) i_b (identity _)).
    apply (BinProductOfIsIsos _ _ (P_D' _ _) (P_D _ _) (pr2 i_b) (identity_is_z_iso _)).
  Defined.

  Let z : C⟦b, y⟧
      := fully_faithful_inv_hom (pr2 F_weq) _ _ (i_b · z' · inv_from_z_iso i_y).
  Local Lemma z_vs_z'
    : z' = z_iso_inv i_b · #F z · i_y.
  Proof.
    unfold z.
    rewrite functor_on_fully_faithful_inv_hom.
    rewrite ! assoc'.
    rewrite z_iso_after_z_iso_inv.
    rewrite id_right.
    rewrite assoc.
    simpl ; rewrite z_iso_after_z_iso_inv.
    now rewrite id_left.
  Qed.

  Let s : C⟦y, y⟧
      := fully_faithful_inv_hom (pr2 F_weq) _ _ (i_y · s' · inv_from_z_iso i_y).
  Lemma s_vs_s'
    : s' = inv_from_z_iso i_y · (# F s · i_y).
  Proof.
    refine (idpath (s') @ _).
    unfold s.
    rewrite functor_on_fully_faithful_inv_hom.
    rewrite assoc'.
    rewrite z_iso_after_z_iso_inv.
    rewrite id_right.
    rewrite assoc.
    rewrite (z_iso_after_z_iso_inv i_y).
    now rewrite id_left.
  Qed.

  Let e : C⟦P_C b N_C, y⟧
      := parameterized_NNO_mor N_C b y z s.

  Let ϕ_mod (ϕ : A)
    : D⟦F(P_C b N_C), F y⟧
      := bp'' · (pr1 ϕ · inv_from_z_iso i_y).

  Let inv_F (ϕ : A) : C⟦P_C b N_C, y⟧
      := fully_faithful_inv_hom (pr2 F_weq) _ _ (ϕ_mod ϕ).

  Local Lemma reflection_parameterized_NNO_helper
    : inv_from_z_iso i_b
        · # F (BinProductArrow C (P_C b N_C) (identity b) (TerminalArrow T_C b · parameterized_NNO_Z N_C))
        · BinProductOfArrows D (P_D b' (F N_C)) (P_D' b N_C) i_b (identity (F N_C))
      = BinProductArrow D (P_D b' (F N_C)) (identity b') (TerminalArrow T_D b' · F_Z).
  Proof.
    use BinProductArrowUnique.
    - cbn.
      rewrite ! assoc'.
      etrans. {
        do 2 apply maponpaths.
        apply (BinProductOfArrowsPr1 _ (P_D _ _) (P_D' _ _)).
      }
      etrans. {
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        cbn.
        rewrite <- functor_comp.
        apply maponpaths, BinProductPr1Commutes.
      }
      rewrite functor_id, id_left.
      apply z_iso_after_z_iso_inv.
    - cbn.
      rewrite ! assoc'.
      etrans. {
        do 2 apply maponpaths.
        apply (BinProductOfArrowsPr2 _ (P_D _ _) (P_D' _ _)).
      }
      etrans. {
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        cbn.
        rewrite <- functor_comp.
        apply maponpaths, BinProductPr2Commutes.
      }
      rewrite id_right.
      unfold F_Z, weak_equiv_preserves_parameterized_NNO_Z.
      rewrite functor_comp, assoc.
      apply maponpaths_2.
      apply (TerminalArrowUnique T_D).
  Qed.

  Lemma reflection_parameterized_NNO_mor_Z (ϕ : A)
    : BinProductArrow C (P_C b N_C) (identity b) (TerminalArrow T_C b · parameterized_NNO_Z N_C)
        · inv_F ϕ = z.
  Proof.
    apply (faithful_reflects_morphism_equality _ (pr2 F_weq)).
      unfold inv_F, ϕ_mod.

      rewrite assoc.
      rewrite functor_comp.
      rewrite functor_on_fully_faithful_inv_hom.

      etrans.
      2: {
        apply pathsinv0, functor_on_fully_faithful_inv_hom.
      }

      use (cancel_z_iso' (z_iso_inv i_b)).

      rewrite ! assoc.
      etrans. {
        apply maponpaths_2.
        refine (_ @ pr12 ϕ).
        apply maponpaths_2.
        exact reflection_parameterized_NNO_helper.
      }
      apply maponpaths_2.
      apply pathsinv0.
      etrans. { apply maponpaths_2, z_iso_after_z_iso_inv. }
      apply id_left.
  Qed.

  Local Lemma reflection_parameterized_NNO_helper'
    : # F (BinProductOfArrows C (P_C b N_C) (P_C b N_C) (identity b) (parameterized_NNO_S N_C))
        · BinProductOfArrows D (P_D b' (F N_C)) (P_D' b N_C) i_b (identity (F N_C))
      = BinProductOfArrows D (P_D b' (F N_C)) (P_D' b N_C) i_b (identity (F N_C))
          · BinProductOfArrows D (P_D b' (F N_C)) (P_D b' (F N_C)) (identity b') F_S.
  Proof.
    etrans.
    2: {
      apply pathsinv0, postcompWithBinProductArrow.
    }
    do 2 rewrite id_right.

    apply BinProductArrowUnique.
    - etrans. {
        rewrite assoc'.
        apply maponpaths.
        apply (BinProductOfArrowsPr1 _ (P_D _ _) (P_D' _ _)).
      }
      rewrite assoc.
      apply maponpaths_2.
      etrans. {
        cbn.
        rewrite <- functor_comp.
        apply maponpaths, BinProductPr1Commutes.
      }
      cbn.
      apply maponpaths, id_right.
    - etrans. {
        rewrite assoc'.
        apply maponpaths.
        apply (BinProductOfArrowsPr2 _ (P_D _ _) (P_D' _ _)).
      }
      rewrite id_right.
      etrans. {
        cbn.
        rewrite <- functor_comp.
        apply maponpaths, BinProductPr2Commutes.
      }
      apply functor_comp.
  Qed.

  Lemma reflection_parameterized_NNO_mor_S (ϕ : A)
    : BinProductOfArrows C (P_C b N_C) (P_C b N_C) (identity b) (parameterized_NNO_S N_C)
        · inv_F ϕ = inv_F ϕ · s.
  Proof.
    apply (faithful_reflects_morphism_equality _ (pr2 F_weq)).
    unfold inv_F, ϕ_mod.
    rewrite assoc.
    rewrite functor_comp.
    etrans. {
      apply maponpaths.
      apply functor_on_fully_faithful_inv_hom.
    }
    rewrite functor_comp.
    etrans.
    2: {
      apply maponpaths_2.
      apply pathsinv0, functor_on_fully_faithful_inv_hom.
    }

    use (cancel_z_iso _ _ i_y).
    rewrite ! assoc'.
    simpl ; rewrite z_iso_after_z_iso_inv.
    rewrite id_right.
    etrans.
    2: {
      do 2 apply maponpaths.
      apply s_vs_s'.
    }
    rewrite <- (pr22 ϕ).
    rewrite ! assoc.
    apply maponpaths_2.
    apply reflection_parameterized_NNO_helper'.
  Qed.

  Lemma inv_of_ϕ_is_parameterized_NNO_mor (ϕ : A)
    : inv_F ϕ = parameterized_NNO_mor N_C b y z s.
  Proof.
    use parameterized_NNO_mor_unique.
    - exact z.
    - exact s.
    - apply reflection_parameterized_NNO_mor_Z.
    - apply reflection_parameterized_NNO_mor_S.
    - apply parameterized_NNO_mor_Z.
    - apply parameterized_NNO_mor_S.
  Qed.

  Lemma img_of_nno_uvp_uniqueness
    : isaprop A.
  Proof.
    use invproofirrelevance.
    intros ϕ ψ.
    use subtypePath.
    { intro ; apply isapropdirprod ; apply homset_property. }

    use (cancel_z_iso _ _ (z_iso_inv i_y)).
    use (cancel_z_iso' bp'').
    refine (! homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ F_weq) _ _) _ @ _).
    refine (_ @ homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ F_weq) _ _) _).

    apply maponpaths.
    exact (inv_of_ϕ_is_parameterized_NNO_mor ϕ @ ! inv_of_ϕ_is_parameterized_NNO_mor ψ).
  Qed.

  Definition weak_equiv_preserves_parameterized_NNO_mor
    : D⟦P_D b' (F N_C), y'⟧
    := inv_from_z_iso bp'' · #F e · i_y.

  Lemma weak_equiv_preserves_parameterized_NNO_mor_Z
    : bp (TerminalArrow T_D b' · F_Z) · weak_equiv_preserves_parameterized_NNO_mor = z'.
  Proof.
    unfold weak_equiv_preserves_parameterized_NNO_mor.
    rewrite ! assoc.
    rewrite z_vs_z'.

    set (pf := maponpaths #F (parameterized_NNO_mor_Z N_C b y z s)).
    rewrite <- pf.
    unfold e.
    rewrite functor_comp.
    rewrite ! assoc.
    do 2 apply maponpaths_2.

    etrans. {
      apply (postcompWithBinProductArrow _ (P_D' _ _) (P_D _ _)).
    }
    apply pathsinv0.
    simpl.
    rewrite id_left, id_right.
    apply (BinProductArrowUnique _ _ _ (P_D' _ _)).
    - rewrite assoc'.
      cbn.
      rewrite <- functor_comp.
      rewrite BinProductPr1Commutes.
      rewrite functor_id.
      apply id_right.
    - rewrite assoc'.
      cbn.
      rewrite <- functor_comp.
      rewrite BinProductPr2Commutes.
      rewrite functor_comp.
      rewrite assoc.
      apply maponpaths_2.
      apply (TerminalArrowUnique T_D).
  Qed.

  Lemma weak_equiv_preserves_parameterized_NNO_mor_S
    : bp' F_S · weak_equiv_preserves_parameterized_NNO_mor
      = weak_equiv_preserves_parameterized_NNO_mor · s'.
  Proof.
    unfold weak_equiv_preserves_parameterized_NNO_mor.
    set (pf := maponpaths #F (parameterized_NNO_mor_S N_C b y z s)).
    unfold F_S, weak_equiv_preserves_parameterized_NNO_S.

    rewrite assoc.
    use z_iso_inv_to_right.
    rewrite ! assoc'.
    apply pathsinv0.
    use z_iso_inv_on_right.
    unfold e.
    refine (_ @ ! pf @ _).
    - rewrite functor_comp.
      apply maponpaths.
      rewrite assoc.
      apply pathsinv0, functor_on_fully_faithful_inv_hom.
    - rewrite functor_comp.
      rewrite ! assoc.
      apply maponpaths_2.

      unfold bp'', bp'.
      cbn.
      apply pathsinv0.

      etrans. {
        apply maponpaths_2.
        exact (! reflection_parameterized_NNO_helper').
      }
      refine (_ @ id_right _).
      rewrite assoc'.
      apply maponpaths.
      etrans. {
        apply (postcompWithBinProductArrow _ (P_D' _ _) (P_D _ _)).
      }

      etrans. {
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        apply (z_iso_inv_after_z_iso i_b).
      }
      do 3 rewrite id_right.
      apply pathsinv0.
      use (BinProductArrowUnique _ _ _ (P_D' _ _)) ; apply id_left.
  Qed.

  Definition weak_equiv_preserves_parameterized_NNO_existence
    : A.
  Proof.
    exists weak_equiv_preserves_parameterized_NNO_mor.
    split.
    - exact weak_equiv_preserves_parameterized_NNO_mor_Z.
    - exact weak_equiv_preserves_parameterized_NNO_mor_S.
  Defined.

End WeakEquivalencesPreserveNNOs.

Lemma weak_equiv_preserves_parameterized_NNO
  {C D : category}
  {F : C ⟶ D} (F_weq : is_weak_equiv F)
  {T_C : Terminal C} {P_C : BinProducts C} (N_C : parameterized_NNO T_C P_C)
  (P_D : BinProducts D)
  : is_parameterized_NNO (weak_equiv_creates_terminal F_weq T_C) P_D (F N_C)
      (weak_equiv_preserves_parameterized_NNO_Z F_weq N_C)
      (weak_equiv_preserves_parameterized_NNO_S N_C).
Proof.
  intros b' y' z' s'.

  use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ F_weq b')).
  intros [b i_b].
  use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ F_weq y')).
  intros [y i_y].

  use iscontraprop1.
  - exact (img_of_nno_uvp_uniqueness F_weq N_C P_D z' s' i_b i_y).
  - apply (weak_equiv_preserves_parameterized_NNO_existence F_weq N_C P_D z' s' i_b i_y).
Defined.

Lemma weak_equiv_creates_parameterized_NNO
  {C D : category}
  {F : C ⟶ D} (F_weq : is_weak_equiv F)
  {T_C : Terminal C} {P_C : BinProducts C} (N_C : parameterized_NNO T_C P_C)
  (T_D : Terminal D) (P_D : BinProducts D)
  : parameterized_NNO T_D P_D.
Proof.
  set (is_M_D := weak_equiv_preserves_parameterized_NNO F_weq N_C P_D).
  set (M_D := make_parameterized_NNO _ _ _ is_M_D).
  exact (parameterized_NNO_independent_of_terminal M_D T_D).
Defined.


(** * 2. Weak equivalences preserve PNNNO's *)
Proposition weak_equiv_preserves_parameterized_NNO'
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F)
  {T_C : Terminal C} {P_C : BinProducts C}
  (N_C : parameterized_NNO T_C P_C)
  {T_D : Terminal D} {P_D : BinProducts D}
  (N_D : parameterized_NNO T_D P_D)
  : preserves_parameterized_NNO N_C N_D _ (weak_equiv_preserves_terminal _ Fw).
Proof.
  set (M_D' := weak_equiv_creates_parameterized_NNO Fw N_C T_D P_D).
  set (i := (parameterized_NNO_unique_up_to_iso' N_D M_D')).
  exact (is_z_isomorphism_path (idpath _) (pr2 i)).
Defined.

(** * 3. Weak Equivalences reflect PNNNO's *)
Section WeakEquivalencesReflectPNNO.

  Context  {C D : category} {F : C ⟶ D} (F_weq : is_weak_equiv F)
    {T_C : Terminal C} {P_C : BinProducts C}
    {P_D : BinProducts D}.

  Context (N_C : C) (z_C : C⟦T_C, N_C⟧) (s_C : C⟦N_C, N_C⟧).

  Let T_D : Terminal D
      := weak_equiv_creates_terminal F_weq T_C.

  Let N_D : D := F N_C.
  Let z_D : D⟦T_D, N_D⟧ := #F z_C.
  Let s_D : D⟦N_D, N_D⟧ := #F s_C.

  Context (N_D_p : is_parameterized_NNO T_D P_D N_D z_D s_D).

  Local Lemma equiv_on_zero_mor
    {b y : C} {z' : C ⟦ b, y ⟧}
    (f : C⟦P_C b N_C, y⟧)
    : BinProductArrow C (P_C b N_C) (identity b) (TerminalArrow T_C b · z_C) · f = z'
      <-> BinProductArrow D (P_D (F b) N_D) (identity (F b)) (TerminalArrow T_D (F b) · z_D)
          · (BinProductArrow D
               (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P_C b N_C)) (BinProductPr1 D (P_D (F b) N_D)) (BinProductPr2 D (P_D (F b) N_D)) · # F f) =
          # F z'.
  Proof.
    split ; intro pf.
    - etrans.
      2: { apply maponpaths, pf. }
      rewrite functor_comp.
      rewrite assoc.
      apply maponpaths_2.
      etrans.
      2: {
        apply pathsinv0.
        use (preserves_binproduct_to_preserves_arrow _ _ (P_C _ _) (P_D _ _)).
      }
      cbn.
      apply maponpaths_2.
      apply maponpaths_12.
      + apply pathsinv0, functor_id.
      + rewrite functor_comp.
        apply maponpaths_2.
        apply pathsinv0, (TerminalArrowUnique T_D).
    - use (faithful_reflects_morphism_equality _ (pr2 F_weq)).
      refine (_ @ pf).
      rewrite functor_comp.
      rewrite assoc.
      apply maponpaths_2.
      rewrite (preserves_binproduct_to_preserves_arrow _ (weak_equiv_preserves_binproducts F_weq) (P_C _ _) (P_D _ _)).
      cbn.
      apply maponpaths_2.
      rewrite functor_id.
      apply maponpaths.
      rewrite functor_comp.
      apply maponpaths_2.
      apply (TerminalArrowUnique T_D).
  Qed.

  Local Lemma equiv_on_succ_mor
    {b y : C} {s' : C⟦y, y⟧}
    (f : C⟦P_C b N_C, y⟧)
    : (BinProductOfArrows C (P_C b N_C) (P_C b N_C) (identity b) s_C · f = f · s')
      <->
        BinProductOfArrows D (P_D (F b) N_D) (P_D (F b) N_D) (identity (F b)) s_D
          · (BinProductArrow D
               (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P_C b N_C)) (BinProductPr1 D (P_D (F b) N_D)) (BinProductPr2 D (P_D (F b) N_D)) · # F f)
        = BinProductArrow D (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P_C b N_C))
            (BinProductPr1 D (P_D (F b) N_D)) (BinProductPr2 D (P_D (F b) N_D)) · # F f · # F s'.
  Proof.
    split.
    - intro p_l.
      set (q_r := maponpaths #F p_l).
      do 2 rewrite functor_comp in q_r.
      use cancel_z_iso'.
      2: { apply (preserves_binproduct_to_z_iso _ (weak_equiv_preserves_binproducts F_weq)). }
      refine (_ @ q_r @ _).
      + rewrite ! assoc.
        apply maponpaths_2.
        etrans.
        2: {
          apply pathsinv0.
          apply (preserves_binproduct_to_preserves_arrow _ _ (P_C _ _) (P_D _ _)).
        }
        cbn.
        apply maponpaths_2.
        rewrite postcompWithBinProductArrow.
        apply maponpaths_12.
        * now rewrite functor_comp, functor_id.
        * now rewrite functor_comp.
      + refine (! id_left _ @ _).
        rewrite ! assoc.
        do 2 apply maponpaths_2.
        cbn.
        set (p := preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P_C b N_C)).
        apply (BinProductArrowsEq _ _ _ p) ; rewrite assoc'.
        * etrans.
          2: {
            apply maponpaths, pathsinv0.
            apply (BinProductPr1Commutes _ _ _ p).
          }
          rewrite BinProductPr1Commutes.
          apply id_left.
        * etrans.
          2: {
            apply maponpaths, pathsinv0.
            apply (BinProductPr2Commutes _ _ _ p).
          }
          rewrite BinProductPr2Commutes.
          apply id_left.
    - intro q_r.
      use (faithful_reflects_morphism_equality _ (pr2 F_weq)).
      do 2 rewrite functor_comp.
      use cancel_z_iso'.
      2: { apply z_iso_inv, (preserves_binproduct_to_z_iso _ (weak_equiv_preserves_binproducts F_weq) (P_C _ _) (P_D _ _)). }

      cbn.
      rewrite ! assoc.
      refine (_ @ q_r).
      rewrite ! assoc.
      apply maponpaths_2.
      set (p := preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P_C b N_C)).
      apply (BinProductArrowsEq _ _ _ p) ; cbn ; rewrite assoc', <- functor_comp.
      + etrans. {
          do 2 apply maponpaths.
          apply BinProductOfArrowsPr1.
        }
        rewrite id_right.
        rewrite assoc'.
        etrans.
        2: {
          apply maponpaths, pathsinv0.
          apply (BinProductPr1Commutes _ _ _ p).
        }
        etrans. {
          apply (BinProductPr1Commutes _ _ _ p).
        }
        rewrite BinProductOfArrowsPr1.
        apply pathsinv0, id_right.
      + etrans. {
          do 2 apply maponpaths.
          apply BinProductOfArrowsPr2.
        }
        rewrite assoc'.
        etrans.
        2: {
          apply maponpaths, pathsinv0.
          apply (BinProductPr2Commutes _ _ _ p).
        }
        rewrite BinProductOfArrowsPr2.
        rewrite functor_comp, assoc.
        apply maponpaths_2.
        apply (BinProductPr2Commutes _ _ _ p).
  Qed.

  Proposition weak_equiv_reflects_parameterized_NNO
    : is_parameterized_NNO T_C P_C N_C z_C s_C.
  Proof.
    unfold is_parameterized_NNO.
    intros b y z' s'.

    set (q := N_D_p (F b) (F y) (#F z') (#F s')).
    use (iscontrweqb' q).

    use weq_subtypes'.
    - refine (_ ∘ weq_from_fully_faithful (pr2 F_weq) _ _)%weq.
      use z_iso_comp_right_weq.
      apply z_iso_inv.
      apply (preserves_binproduct_to_z_iso _ (weak_equiv_preserves_binproducts F_weq)).
    - intro ; apply isapropdirprod ; apply homset_property.
    - intro ; apply isapropdirprod ; apply homset_property.
    - intro f.
      split.
      + intros [p_l p_r].
        split.
        * exact (pr1 (equiv_on_zero_mor f) p_l).
        * exact (pr1 (equiv_on_succ_mor f) p_r).
      + intros [p_l p_r].
        split.
        * exact (pr2 (equiv_on_zero_mor f) p_l).
        * exact (pr2 (equiv_on_succ_mor f) p_r).
  Defined.

End WeakEquivalencesReflectPNNO.

(** * 4. Weak Equivalences Lift Preservation of PNNO. *)
Section WeakEquivalencesLiftPreservesPNNO.

  Context {C1 C2 C3 : category}
    {F : C1 ⟶ C3} {G : C1 ⟶ C2} {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (G_weq : is_weak_equiv G)
    {Fpt : preserves_terminal F}
    {T1 : Terminal C1} {T3 : Terminal C3}
    {P1 : BinProducts C1} {P2 : BinProducts C2} {P3 : BinProducts C3}.

  (* Let T2 := weak_equiv_creates_terminal G_weq T1. *)
  Context {T2 : Terminal C2}.

  Context (N1 : parameterized_NNO T1 P1) (N2 : parameterized_NNO T2 P2) (N3 : parameterized_NNO T3 P3).
  Context (Fpn : preserves_parameterized_NNO N1 N3 F Fpt).

  Let N2' : parameterized_NNO T2 P2.
  Proof.
    exact (weak_equiv_creates_parameterized_NNO G_weq N1 T2 P2).
      (* := make_parameterized_NNO _ _ _
           (weak_equiv_preserves_parameterized_NNO G_weq N1 P2). *)
  Defined.

  Let H_pt : preserves_terminal H
      := weak_equiv_lifts_preserves_terminal α G_weq Fpt.

  Let F_z := TerminalArrow (preserves_terminal_to_terminal F Fpt T1) T3 · # F (parameterized_NNO_Z N1).
  Let F_s := (# F (parameterized_NNO_S N1)).
  Let F_hn
      := nat_z_iso_pointwise_z_iso (nat_z_iso_inv α) N1
           · # H (parameterized_NNO_unique_up_to_iso' N2' N2).


  Let H_z
      := TerminalArrow (preserves_terminal_to_terminal H H_pt T2) T3 · # H (parameterized_NNO_Z N2).
  Let H_s
      := # H (parameterized_NNO_S N2).

  Let T3' : Terminal C3.
  Proof.
    exists (H (G T1)).
    apply H_pt.
    apply weak_equiv_preserves_terminal.
    - assumption.
    - apply T1.
  Defined.

  Lemma weak_equiv_lifts_preserves_parameterized_NNO_comm
    : parameterized_NNO_mor N3 T3 (F N1) F_z F_s · F_hn
      = parameterized_NNO_mor N3 T3 (H N2) H_z H_s.
  Proof.
    use (parameterized_NNO_mor_unique N3).
    - exact H_z.
    - exact H_s.
    - rewrite assoc.
      rewrite parameterized_NNO_mor_Z.
      unfold H_z, F_z, F_hn.
      rewrite assoc.
      etrans. {
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        apply nat_trans_ax.
      }
      cbn.
      rewrite ! assoc'.
      assert (tmp : # G (parameterized_NNO_Z N1)
                      · is_NNO_parameterized_NNO_mor N2' N2 (pr12 N2) (pr122 N2)
                    = TerminalArrow T2 (G T1) · parameterized_NNO_Z N2). {
        etrans.
        2: {
          apply maponpaths.
          apply (is_NNO_parameterized_NNO_mor_Z N2' N2 (pr12 N2) (pr122 N2)).
        }
        rewrite ! assoc.
        apply maponpaths_2.
        refine (_ @ assoc' _ _ _).
        cbn ; unfold weak_equiv_preserves_parameterized_NNO_Z.
        refine (! id_left _ @ _).
        apply maponpaths_2.
        use proofirrelevance.
        apply isapropifcontr.
        apply (weak_equiv_preserves_terminal _ G_weq _ (pr2 T1) _).
      }

      rewrite <- functor_comp.
      etrans. {
        do 3 apply maponpaths.
        exact tmp.
      }
      rewrite functor_comp.
      rewrite ! assoc.
      apply maponpaths_2.
      apply (TerminalArrowUnique (preserves_terminal_to_terminal _ H_pt T2)).
    - rewrite assoc.
      rewrite parameterized_NNO_mor_S.
      rewrite ! assoc'.
      apply maponpaths.
      unfold F_s, F_hn, H_s.
      rewrite assoc.
      rewrite (nat_trans_ax (nat_z_iso_inv α)).
      rewrite ! assoc'.
      apply maponpaths.
      cbn.
      rewrite <- ! functor_comp.
      apply maponpaths.
      apply (is_NNO_parameterized_NNO_mor_S N2').
    - apply parameterized_NNO_mor_Z.
    - apply parameterized_NNO_mor_S.
  Qed.

  Proposition weak_equiv_lifts_preserves_parameterized_NNO
    : preserves_parameterized_NNO N2 N3 H H_pt.
  Proof.
    use is_z_isomorphism_path.
    - refine (preserves_parameterized_NNO_mor N1 N3 F Fpt · _).
      refine (_ · #H (parameterized_NNO_unique_up_to_iso' N2' N2)).
      exact (nat_z_iso_pointwise_z_iso (nat_z_iso_inv α) N1).
    - unfold preserves_parameterized_NNO_mor, is_NNO_parameterized_NNO_mor.
      rewrite ! assoc'.
      apply maponpaths.
      apply weak_equiv_lifts_preserves_parameterized_NNO_comm.
    - use is_z_isomorphism_comp.
      { apply Fpn. }
      use is_z_isomorphism_comp.
      + apply (nat_z_iso_pointwise_z_iso (nat_z_iso_inv α) N1).
      + apply functor_on_is_z_isomorphism.
        apply parameterized_NNO_unique_up_to_iso'.
  Qed.

End WeakEquivalencesLiftPreservesPNNO.
