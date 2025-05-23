(**
   Preservation Of Parameterized Natural Numbers Objects, by Weak Equivalences.

   In this file, we show that any weak equivalence F : C -> D preserves a parameterized natural numbers object.

   Contents
   1. Image of a PNNO, under F, is a PNNO [weak_equiv_preserves_parameterized_NNO]
   2. Weak equivalences preserve PNNNO's, up to isomorphism [weak_equiv_preserves_parameterized_NNO']
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
Qed.

(** * 2. Weak equivalences preserve PNNNO's *)
Proposition weak_equiv_preserves_parameterized_NNO'
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F)
  {T_C : Terminal C} {P_C : BinProducts C}
  (N_C : parameterized_NNO T_C P_C)
  {T_D : Terminal D} {P_D : BinProducts D}
  (N_D : parameterized_NNO T_D P_D)
  : preserves_parameterized_NNO N_C N_D _ (weak_equiv_preserves_terminal _ Fw).
Proof.
  set (is_M_D := weak_equiv_preserves_parameterized_NNO Fw N_C P_D).
  set (M_D := make_parameterized_NNO _ _ _ is_M_D).
  set (M_D' := parameterized_NNO_independent_of_terminal M_D T_D).
  set (i := (parameterized_NNO_unique_up_to_iso' N_D M_D')).
  exact (is_z_isomorphism_path (idpath _) (pr2 i)).
Defined.
