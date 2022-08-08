Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Local Open Scope cat.

Section Tensor.

  Definition tensor_data (C : category) : UU :=
    ∑ T : C -> C -> C, ∏ (x1 x2 y1 y2 : C), C⟦x1,x2⟧ -> C⟦y1,y2⟧ -> C⟦T x1 y1, T x2 y2⟧.

  Definition make_tensor_data {C : category} (T : C -> C -> C)
             (h : ∏ (x1 x2 y1 y2 : C), C⟦x1,x2⟧ -> C⟦y1,y2⟧ -> C⟦T x1 y1, T x2 y2⟧)
    : tensor_data C := (T,,h).

  Definition tensor_on_ob {C : category} (T : tensor_data C) : C -> C -> C := pr1 T.
  Notation "x ⊗_{ T } y" := (tensor_on_ob T x y) (at level 31).

  Definition tensor_on_hom {C : category} (T : tensor_data C)
    : ∏ (x1 x2 y1 y2 : C), C⟦x1,x2⟧ -> C⟦y1,y2⟧ -> C⟦x1 ⊗_{T} y1, x2 ⊗_{T} y2⟧ := pr2 T.
  Notation "f ⊗^{ T } g" := (tensor_on_hom T _ _ _ _ f g) (at level 31).

  Definition tensor_idax {C : category} (T : tensor_data C)
    := ∏ (x y : C), (identity x) ⊗^{T} (identity y) = identity (x ⊗_{T} y).

  Definition tensor_compax {C : category} (T : tensor_data C)
    := ∏ (x1 x2 x3 y1 y2 y3 : C) (f1 : C⟦x1,x2⟧) (f2 : C⟦x2,x3⟧) (g1 : C⟦y1,y2⟧) (g2 : C⟦y2,y3⟧),
      (f1 · f2) ⊗^{T} (g1 · g2) = (f1 ⊗^{T} g1) · (f2 ⊗^{T} g2).

  Definition tensor_ax {C : category} (T : tensor_data C) : UU
    := tensor_idax T × tensor_compax T.

  Definition tensor (C : category) : UU :=
    ∑ T : tensor_data C, tensor_ax T.

  Definition tensor_to_data {C : category} (T : tensor C) : tensor_data C := pr1 T.
  Coercion tensor_to_data : tensor >-> tensor_data.

  Definition tensor_to_ax {C : category} (T : tensor C) : tensor_ax T := pr2 T.

  Definition tensor_id {C : category} (T : tensor C) : tensor_idax T
    := pr1 (tensor_to_ax T).

  Definition tensor_comp {C : category} (T : tensor C) : tensor_compax T
    := pr2 (tensor_to_ax T).

  Definition preserves_tensor_data {C D : category} (TC : tensor_data C) (TD : tensor_data D) (F : functor C D) : UU :=
    ∏ (x y : C), D ⟦ F x ⊗_{TD} F y, F (x ⊗_{TC} y) ⟧.

  Definition preserves_tensor_nat {C D : category} {TC : tensor C} {TD : tensor D} {F : functor C D} (ptF : preserves_tensor_data TC TD F) : UU
    := ∏ (x1 x2 y1 y2 : C) (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      (ptF x1 y1) · (functor_on_morphisms F  (f ⊗^{TC} g)) = ((functor_on_morphisms F f) ⊗^{TD} (functor_on_morphisms F g)) · ptF x2 y2.

  Definition preserves_tensor  {C D : category} (TC : tensor C) (TD : tensor D) (F : functor C D) : UU
    := ∑ (ptF : preserves_tensor_data TC TD F), preserves_tensor_nat ptF.

  Definition preservestensor_into_preservestensordata {C D : category} {TC : tensor C} {TD : tensor D} {F : functor C D} (pt : preserves_tensor TC TD F)
    : preserves_tensor_data TC TD F := pr1 pt.
  Coercion preservestensor_into_preservestensordata : preserves_tensor >-> preserves_tensor_data.

  Lemma identityfunctor_preserves_tensor_data {C : category} (T : tensor C)
    : preserves_tensor_data T T (functor_identity C).
  Proof.
    intros x y.
    apply identity.
  Defined.

  Lemma identityfunctor_preserves_tensor_nat {C : category} (T : tensor C)
    : preserves_tensor_nat (identityfunctor_preserves_tensor_data T).
  Proof.
    intros x1 x2 y1 y2 f g.
    rewrite id_left.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition identityfunctor_preserves_tensor {C : category} (T : tensor C)
    : preserves_tensor T T (functor_identity C)
    := (identityfunctor_preserves_tensor_data T,, identityfunctor_preserves_tensor_nat T).

  Lemma compositions_preserves_tensor_data
        {C D E : category}
        {TC : tensor C} {TD : tensor D} {TE : tensor E}
        {F : functor C D} {G : functor D E}
        (ptF : preserves_tensor_data TC TD F) (ptG : preserves_tensor_data TD TE G)
    : preserves_tensor_data TC TE (functor_composite F G).
  Proof.
    intros x y.
    exact ((ptG (F x) (F y)) · (functor_on_morphisms G) (ptF x y)).
  Defined.

  Lemma compositions_preserves_tensor_nat
        {C D E : category}
        {TC : tensor C} {TD : tensor D} {TE : tensor E}
        {F : functor C D} {G : functor D E}
        (ptF : preserves_tensor TC TD F) (ptG : preserves_tensor TD TE G)
    : preserves_tensor_nat (compositions_preserves_tensor_data ptF ptG).
  Proof.
    intros x1 x2 y1 y2 f g.
    unfold compositions_preserves_tensor_data.
    simpl.
    rewrite assoc'.
    etrans. {
      apply cancel_precomposition.
      apply (pathsinv0 (functor_comp G _ _)).
    }
    rewrite (pr2 ptF).
    rewrite assoc.
    rewrite functor_comp.
    rewrite assoc.
    rewrite (pr2 ptG).
    apply idpath.
  Qed.

  Definition compositions_preserves_tensor
        {C D E : category}
        {TC : tensor C} {TD : tensor D} {TE : tensor E}
        {F : functor C D} {G : functor D E}
        (ptF : preserves_tensor TC TD F) (ptG : preserves_tensor TD TE G)
    : preserves_tensor TC TE (functor_composite F G)
    := (compositions_preserves_tensor_data ptF ptG,, compositions_preserves_tensor_nat ptF ptG).

  Definition preservestensor_commutes
             {C D : category}
             {TC : tensor C}
             {TD : tensor D}
             {F G : functor C D}
             (ptF : preserves_tensor_data TC TD F)
             (ptG : preserves_tensor_data TC TD G)
             (α : nat_trans F G)
    : UU := ∏ (x y : C),
    (ptF x y) ·  α (x ⊗_{TC} y)
    = (α x) ⊗^{TD} (α y) · (ptG x y).

  Definition identitynattrans_preservestensor_commutes
             {C D : category}
             {TC : tensor C}
             {TD : tensor D}
             {F : functor C D}
             (ptF : preserves_tensor_data TC TD F)
    : preservestensor_commutes ptF ptF (nat_trans_id F).
  Proof.
    intros x y.
    simpl.
    rewrite id_right.
    rewrite tensor_id.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition isaprop_preservestensor_commutes
             {C D : category}
             {TC : tensor C}
             {TD : tensor D}
             {F G : functor C D}
             (ptF : preserves_tensor_data TC TD F)
             (ptG : preserves_tensor_data TC TD G)
             (α : nat_trans F G)
    : isaprop (preservestensor_commutes ptF ptG α).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply homset_property.
  Qed.

End Tensor.

Module TensorNotation.

  Notation "x ⊗_{ T } y" := (tensor_on_ob T x y) (at level 31).
  Notation "f ⊗^{ T } g" := (tensor_on_hom T _ _ _ _ f g) (at level 31).

End TensorNotation.

Section Unit.

  Definition preserves_unit {C D : category} (IC : C) (ID : D) (F : functor C D)
    : UU := D⟦ID, (pr1 F) IC⟧.

  Definition identityfunctor_preserves_unit {C : category} (IC : C)
    : preserves_unit IC IC (functor_identity C) := identity IC.

  Definition composition_preserves_unit {C D E : category}
             {IC : C} {ID : D} {IE : E}
             {F : functor C D} {G : functor D E}
             (puF : preserves_unit IC ID F)
             (puG : preserves_unit ID IE G)
    : preserves_unit IC IE (functor_composite F G)
    := puG · (functor_on_morphisms (pr1 G) puF).

  Definition preservesunit_commutes
             {C D : category}
             {IC : C}
             {ID : D}
             {F G : functor C D}
             (puF : preserves_unit IC ID F)
             (puG : preserves_unit IC ID G)
             (α : nat_trans F G)
    : UU := puF · (α IC) = puG.

  Definition identitynattrans_preservesunit_commutes
             {C D : category}
             {IC : C}
             {ID : D}
             {F : functor C D}
             (puF : preserves_unit IC ID F)
    : preservesunit_commutes puF puF (nat_trans_id F).
  Proof.
    apply id_right.
  Qed.

  Lemma isaprop_preservesunit_commutes
        {C D : category}
        {IC : C}
        {ID : D}
        {F G : functor C D}
        (puF : preserves_unit IC ID F)
        (puG : preserves_unit IC ID G)
        (α : nat_trans F G)
    : isaprop (preservesunit_commutes puF puG α).
  Proof.
    apply homset_property.
  Qed.

End Unit.

Section TensorUnit.

  Definition tensor_unit (C : category) : UU := tensor C × C.

  Definition tensor_unit_to_tensor {C : category} (tu : tensor_unit C)
    : tensor C := pr1 tu.
  Coercion tensor_unit_to_tensor : tensor_unit >-> tensor.

  Definition tensor_unit_to_unit {C : category} (tu : tensor_unit C)
    : ob C := pr2 tu.
  Coercion tensor_unit_to_unit : tensor_unit >-> ob.

  Definition functor_tensor_unit {C D : category}
             (tuC : tensor_unit C) (tuD : tensor_unit D)
             (F : functor C D)
    : UU
    := preserves_tensor tuC tuD F × preserves_unit tuC tuD F.

  Definition functor_tensor_unit_to_preserves_tensor
             {C D : category}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             {F : functor C D}
             (ptu : functor_tensor_unit tuC tuD F)
    : preserves_tensor tuC tuD F := pr1 ptu.
  Coercion functor_tensor_unit_to_preserves_tensor : functor_tensor_unit >-> preserves_tensor.

  Definition functor_tensor_unit_to_preserves_unit
             {C D : category}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             {F : functor C D}
             (ptu : functor_tensor_unit tuC tuD F)
    : preserves_unit tuC tuD F := pr2 ptu.
  Coercion functor_tensor_unit_to_preserves_unit : functor_tensor_unit >-> preserves_unit.

  Definition identity_functor_tensor_unit {C : category}
             (tu : tensor_unit C)
    : functor_tensor_unit tu tu (functor_identity C).
  Proof.
    use tpair.
    - apply identityfunctor_preserves_tensor.
    - apply identityfunctor_preserves_unit.
  Defined.

  Definition composite_functor_tensor_unit
             {C D E : category}
             {F : functor C D} {G : functor D E}
             {tuC : tensor_unit C}
             {tuD : tensor_unit D}
             {tuE : tensor_unit E}
             (ptuF : functor_tensor_unit tuC tuD F)
             (ptuG : functor_tensor_unit tuD tuE G)
    : functor_tensor_unit tuC tuE (functor_composite F G).
  Proof.
    use tpair.
    - apply (compositions_preserves_tensor ptuF ptuG).
    - apply (composition_preserves_unit ptuF ptuG).
  Defined.

  Definition nattrans_tensor_unit {C D : category}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             {F G : functor C D}
             (ptuF : functor_tensor_unit tuC tuD F)
             (ptuG : functor_tensor_unit tuC tuD G)
             (α : nat_trans F G)
    : UU := preservestensor_commutes ptuF ptuG α × preservesunit_commutes ptuF ptuG α.

  Lemma isaprop_nattrans_tensor_unit
        {C D : category}
        {tuC : tensor_unit C} {tuD : tensor_unit D}
        {F G : functor C D}
        (ptuF : functor_tensor_unit tuC tuD F)
        (ptuG : functor_tensor_unit tuC tuD G)
        (α : nat_trans F G)
    : isaprop (nattrans_tensor_unit ptuF ptuG α).
  Proof.
    apply isapropdirprod.
    - apply isaprop_preservestensor_commutes.
    - apply isaprop_preservesunit_commutes.
  Qed.

End TensorUnit.

Module TensorUnitNotation.

  Notation "T_{ tu }" := (tensor_unit_to_tensor tu).
  Notation "I_{ tu }" := (tensor_unit_to_unit tu).
  Notation "pt_{ ptu }" := (functor_tensor_unit_to_preserves_tensor ptu).
  Notation "pu_{ ptu }" := (functor_tensor_unit_to_preserves_unit ptu).

End TensorUnitNotation.


Section LeftUnitor.

  Import TensorNotation.
  Import TensorUnitNotation.

  Definition lunitor_data {C : category} (tu : tensor_unit C) : UU
    := ∏ x : C, C⟦I_{tu} ⊗_{tu} x, x⟧.

  Definition lunitor_nat {C : category} {tu : tensor_unit C} (lu : lunitor_data tu) : UU
    := ∏ (x y : C) (f : C⟦x,y⟧), ((identity I_{tu}) ⊗^{tu} f) · (lu y) = (lu x) · f.

  Definition lunitor {C : category} (tu : tensor_unit C) : UU
    := ∑ lu : lunitor_data tu, lunitor_nat lu.

  (* For some reason I can't just do pt_{ptuF} _ _, but I really have to
     project on the first component, however there are coercions.. *)
  Definition preserves_lunitor
             {C D : category} {F : functor C D}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             (ptuF : functor_tensor_unit tuC tuD F)
             (luC : lunitor tuC) (luD : lunitor tuD)
    : UU := ∏ x : C,
        (pu_{ptuF} ⊗^{tuD} (identity (F x))) · (pr1 pt_{ptuF} I_{tuC} x)
                                             · (functor_on_morphisms F (pr1 luC x))
        = pr1 luD (F x).

  Definition id_preserves_lunitor
             {C : category}
             {tu : tensor_unit C}
             (lu : lunitor tu)
    : preserves_lunitor (identity_functor_tensor_unit tu) lu lu.
  Proof.
    intro x.
    etrans. {
      apply cancel_postcomposition.
      apply id_right.
    }
    etrans. {
      apply cancel_postcomposition.
      apply tensor_id.
    }
    apply id_left.
  Qed.

  Definition comp_preserves_lunitor
             {C D E : category}
             {tuC : tensor_unit C}
             {tuD : tensor_unit D}
             {tuE : tensor_unit E}
             {F : functor C D}
             {G : functor D E}
             {ptuF : functor_tensor_unit tuC tuD F}
             {ptuG : functor_tensor_unit tuD tuE G}
             {luC : lunitor tuC}
             {luD : lunitor tuD}
             {luE : lunitor tuE}
             (pluF : preserves_lunitor ptuF luC luD)
             (pluG : preserves_lunitor ptuG luD luE)
    : preserves_lunitor (composite_functor_tensor_unit ptuF ptuG) luC luE.
  Proof.
    intro x.

    use pathscomp0.
    3: exact (pluG (F x)).

    etrans. {
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      apply maponpaths.
      apply (! id_right _).
    }

    etrans. {
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      apply tensor_comp.
    }

    rewrite assoc'.
    rewrite assoc'.
    use pathscomp0.
    3: {
      apply assoc.
    }
    apply cancel_precomposition.
    unfold compositions_preserves_tensor_data.
    use pathscomp0.
    3: {
      apply cancel_precomposition.
      apply maponpaths.
      exact (pluF x).
    }
    (* cbn. *)
    unfold composite_functor_tensor_unit.
    unfold compositions_preserves_tensor.
    unfold compositions_preserves_tensor_data.

    use pathscomp0.
    3: {
      apply cancel_precomposition.
      apply (! functor_comp _ _ _).
    }

    rewrite assoc.
    rewrite assoc.
    cbn.
    rewrite assoc.
    apply cancel_postcomposition.

    use pathscomp0.
    3: {
      apply cancel_precomposition.
      apply (! functor_comp _ _ _).
    }

    use pathscomp0.
    3: { apply assoc'. }
    apply cancel_postcomposition.

    use pathscomp0.
    3: {
      apply (! pr21 ptuG _ _ _ _ _ _).
    }
    apply cancel_postcomposition.
    apply maponpaths.
    apply (! functor_id _ _).
  Qed.

  Definition isaprop_preserves_lunitor
             {C D : category} {F : functor C D}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             (ptuF : functor_tensor_unit tuC tuD F)
             (luC : lunitor tuC) (luD : lunitor tuD)
    : isaprop (preserves_lunitor ptuF luC luD).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply homset_property.
  Qed.

End LeftUnitor.


Section RightUnitor.

  Import TensorNotation.
  Import TensorUnitNotation.

  Definition runitor_data {C : category} (tu : tensor_unit C) : UU
    := ∏ x : C, C⟦x ⊗_{tu} I_{tu}, x⟧.

  Definition runitor_nat {C : category} {tu : tensor_unit C} (ru : runitor_data tu) : UU
    := ∏ (x y : C) (f : C⟦x,y⟧), (f ⊗^{tu} (identity I_{tu})) · (ru y) = (ru x) · f.

  Definition runitor {C : category} (tu : tensor_unit C) : UU
    := ∑ ru : runitor_data tu, runitor_nat ru.

  (* For some reason I can't just do pt_{ptuF} _ _, but I really have to
     project on the first component, however there are coercions.. *)
  Definition preserves_runitor
             {C D : category} {F : functor C D}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             (ptuF : functor_tensor_unit tuC tuD F)
             (ruC : runitor tuC) (ruD : runitor tuD)
    : UU := ∏ x : C,
        ((identity (F x)) ⊗^{tuD} pu_{ptuF}) · (pr1 pt_{ptuF} x I_{tuC})
                                             · (functor_on_morphisms F (pr1 ruC x))
        = pr1 ruD (F x).
  Definition id_preserves_runitor
             {C : category}
             {tu : tensor_unit C}
             (ru : runitor tu)
    : preserves_runitor (identity_functor_tensor_unit tu) ru ru.
  Proof.
    intro x.
    etrans. {
      apply cancel_postcomposition.
      apply id_right.
    }
    etrans. {
      apply cancel_postcomposition.
      apply tensor_id.
    }
    apply id_left.
  Qed.

  Definition comp_preserves_runitor
             {C D E : category}
             {tuC : tensor_unit C}
             {tuD : tensor_unit D}
             {tuE : tensor_unit E}
             {F : functor C D}
             {G : functor D E}
             {ptuF : functor_tensor_unit tuC tuD F}
             {ptuG : functor_tensor_unit tuD tuE G}
             {ruC : runitor tuC}
             {ruD : runitor tuD}
             {ruE : runitor tuE}
             (pruF : preserves_runitor ptuF ruC ruD)
             (pruG : preserves_runitor ptuG ruD ruE)
    : preserves_runitor (composite_functor_tensor_unit ptuF ptuG) ruC ruE.
  Proof.
    intro x.

    use pathscomp0.
    3: exact (pruG (F x)).

    etrans. {
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      assert (pf :  (identity (G (F x))) =  (identity (G (F x)))· (identity (G (F x)))). {
        apply (! id_right _).
      }
      simpl.
      rewrite pf.
      apply tensor_comp.
    }

    rewrite assoc'.
    rewrite assoc'.
    use pathscomp0.
    3: {
      apply assoc.
    }
    apply cancel_precomposition.
    unfold compositions_preserves_tensor_data.
    use pathscomp0.
    3: {
      apply cancel_precomposition.
      apply maponpaths.
      exact (pruF x).
    }
    cbn in *.
    unfold compositions_preserves_tensor_data.

    use pathscomp0.
    3: {
      apply cancel_precomposition.
      apply (! functor_comp _ _ _).
    }

    rewrite assoc.
    rewrite assoc.
    rewrite assoc.
    apply cancel_postcomposition.

    use pathscomp0.
    3: {
      apply cancel_precomposition.
      apply (! functor_comp _ _ _).
    }

    use pathscomp0.
    3: { apply assoc'. }
    apply cancel_postcomposition.

    use pathscomp0.
    3: {
      apply (! pr21 ptuG _ _ _ _ _ _).
    }
    apply cancel_postcomposition.
    rewrite (! functor_id _ _).
    apply idpath.
  Qed.

  Definition isaprop_preserves_runitor
             {C D : category} {F : functor C D}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             (ptuF : functor_tensor_unit tuC tuD F)
             (ruC : runitor tuC) (ruD : runitor tuD)
    : isaprop (preserves_runitor ptuF ruC ruD).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply homset_property.
  Qed.

End RightUnitor.

Section Associator.

  Import TensorNotation.
  Import TensorUnitNotation.

  Definition associator_data {C : category} (tu : tensor_unit C) : UU
    := ∏ x y z : C, C⟦(x ⊗_{tu} y) ⊗_{tu} z, x ⊗_{tu} (y ⊗_{tu} z)⟧.

  Definition associator_nat {C : category} {tu : tensor_unit C} (α : associator_data tu) : UU
    := ∏ (x x' y y' z z' : C), ∏ (f : C⟦x,x'⟧) (g : C⟦y,y'⟧) (h : C⟦z,z'⟧),
       (α x y z)· (f ⊗^{tu} (g ⊗^{tu} h)) = ((f ⊗^{tu} g) ⊗^{tu} h) · (α x' y' z').

  Definition associator {C : category} (tu : tensor_unit C) : UU
    := ∑ α : associator_data tu, associator_nat α.

  Definition preserves_associator
             {C D : category} {F : functor C D}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             (ptuF : functor_tensor_unit tuC tuD F)
             (αC : associator tuC) (αD : associator tuD)
    : UU := ∏ (x y z : C),
      ((pr1 pt_{ptuF} x y) ⊗^{tuD} (identity (F z)))
        · (pr1 pt_{ptuF} (x ⊗_{tuC} y) z)
        · (functor_on_morphisms F (pr1 αC x y z))
      = (pr1 αD (F x) (F y) (F z))
          · ((identity (F x)) ⊗^{tuD} (pr1 pt_{ptuF} y z))
          · (pr1 pt_{ptuF} x (y ⊗_{tuC} z)).

  Definition id_preserves_associator
             {C : category}
             {tu : tensor_unit C}
             (α :  associator tu)
    : preserves_associator (identity_functor_tensor_unit tu) α α.
  Proof.
    intros x y z.
      etrans. {
          apply cancel_postcomposition.
          apply id_right.
      }
      etrans. {
          apply cancel_postcomposition.
          apply tensor_id.
      }
      etrans. {
        apply id_left.
      }

      apply pathsinv0.
      etrans. {
        apply cancel_postcomposition.
        apply cancel_precomposition.
        apply tensor_id.
      }
      etrans. {
        apply cancel_postcomposition.
        apply id_right.
      }
      apply id_right.
  Qed.

  Definition comp_preserves_associator
             {C D E : category}
             {tuC : tensor_unit C}
             {tuD : tensor_unit D}
             {tuE : tensor_unit E}
             {F : functor C D}
             {G : functor D E}
             {ptuF : functor_tensor_unit tuC tuD F}
             {ptuG : functor_tensor_unit tuD tuE G}
             {assC : associator tuC}
             {assD : associator tuD}
             {assE : associator tuE}
             (paF : preserves_associator ptuF assC assD)
             (paG : preserves_associator ptuG assD assE)
    : preserves_associator (composite_functor_tensor_unit ptuF ptuG) assC assE.
  Proof.
    intros x y z.
    cbn in *.
    unfold compositions_preserves_tensor_data.

    etrans. {
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      apply maponpaths.
      apply (! id_right _).
    }
    etrans. {
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      apply tensor_comp.
    }

    etrans. {
      rewrite assoc'.
      rewrite assoc'.
      apply cancel_precomposition.
      rewrite assoc.
      apply cancel_postcomposition.
      rewrite assoc.
      apply cancel_postcomposition.
      rewrite (! functor_id _ _).
      apply (! pr21 ptuG _ _ _ _ _ _ ).
    }
    etrans. {
      apply cancel_precomposition.
      rewrite assoc'.
      rewrite (! functor_comp _ _ _).
      rewrite assoc'.
      rewrite (! functor_comp _ _ _).
      apply cancel_precomposition.
      apply maponpaths.
      rewrite assoc.
      apply (paF x y z).
    }

    simpl.
    rewrite functor_comp.
    etrans. {
      rewrite assoc.
      rewrite assoc.
      apply cancel_postcomposition.
      rewrite assoc'.
      rewrite functor_comp.
      rewrite assoc.
      rewrite assoc.
      apply cancel_postcomposition.
      apply paG.
    }
    rewrite assoc'.
    rewrite assoc'.
    rewrite assoc'.
    rewrite assoc'.
    apply cancel_precomposition.
    rewrite assoc.
    rewrite assoc.
    rewrite assoc.
    apply cancel_postcomposition.

    assert (pf : (identity (G (F x))) =  (identity (G (F x)))·  (identity (G (F x)))). {
      apply (! id_right _).
    }

    use pathscomp0.
    3: {
      rewrite pf.
      rewrite tensor_comp.
      apply assoc.
    }
    rewrite assoc'.
    apply cancel_precomposition.
    etrans. { apply (pr21 ptuG). }
    rewrite (functor_id _ _).
    apply idpath.
  Qed.

  Definition isaprop_preserves_associator
             {C D : category} {F : functor C D}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             (ptuF : functor_tensor_unit tuC tuD F)
             (assC : associator tuC) (assD : associator tuD)
    : isaprop (preserves_associator ptuF assC assD).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply homset_property.
  Qed.

End Associator.

Section UnitorsAssociator.

  Definition unitors_associator {C : category} (tu : tensor_unit C) : UU
    := lunitor tu × runitor tu × associator tu.

  Definition unitors_associator_to_lunitor {C : category}
             {tu : tensor_unit C} (ua : unitors_associator tu)
    : lunitor tu := pr1 ua.
  (* Coercion unitors_associator_to_lunitor : unitors_associator >-> lunitor. *)

  Definition unitors_associator_to_runitor {C : category}
             {tu : tensor_unit C} (ua : unitors_associator tu)
    : runitor tu := pr12 ua.
  (* Coercion unitors_associator_to_runitor : unitors_associator >-> runitor. *)

  Definition unitors_associator_to_associator {C : category}
             {tu : tensor_unit C} (ua : unitors_associator tu)
    : associator tu := pr22 ua.
  (* Coercion unitors_associator_to_associator : unitors_associator >-> associator. *)

  Definition functor_unitors_associator {C D : category}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             (uaC : unitors_associator tuC)
             (uaD : unitors_associator tuD)
             {F : functor C D}
             (ptuF : functor_tensor_unit tuC tuD F)
    : UU
    := preserves_lunitor ptuF (pr1 uaC) (pr1 uaD)
                         × preserves_runitor ptuF (pr12 uaC) (pr12 uaD)
                         × preserves_associator ptuF (pr22 uaC) (pr22 uaD).
  (* := preserves_lunitor ptuF uaC uaD
                         × preserves_runitor ptuF uaC uaD
                         × preserves_associator ptuF uaC uaD. *)

  Definition functor_unitors_associator_to_preserves_lunitor
             {C D : category}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             {uaC : unitors_associator tuC}
             {uaD : unitors_associator tuD}
             {F : functor C D}
             {ptuF : functor_tensor_unit tuC tuD F}
             (puaF : functor_unitors_associator uaC uaD ptuF)
    : preserves_lunitor ptuF (pr1 uaC) (pr1 uaD) := pr1 puaF.
    (* : preserves_lunitor ptuF (pr1 uaC) uaD := pr1 puaF. *)
  Coercion functor_unitors_associator_to_preserves_lunitor
    : functor_unitors_associator >-> preserves_lunitor.

  Definition functor_unitors_associator_to_preserves_runitor
             {C D : category}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             {uaC : unitors_associator tuC}
             {uaD : unitors_associator tuD}
             {F : functor C D}
             {ptuF : functor_tensor_unit tuC tuD F}
             (puaF : functor_unitors_associator uaC uaD ptuF)
    : preserves_runitor ptuF (pr12 uaC) (pr12 uaD) := pr12 puaF.
  Coercion functor_unitors_associator_to_preserves_runitor
    : functor_unitors_associator >-> preserves_runitor.

  Definition functor_unitors_associator_to_preserves_associator
             {C D : category}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             {uaC : unitors_associator tuC}
             {uaD : unitors_associator tuD}
             {F : functor C D}
             {ptuF : functor_tensor_unit tuC tuD F}
             (puaF : functor_unitors_associator uaC uaD ptuF)
    : preserves_associator ptuF (pr22 uaC) (pr22 uaD) := pr22 puaF.
  Coercion functor_unitors_associator_to_preserves_associator
    : functor_unitors_associator >-> preserves_associator.

  Definition identity_functor_unitors_associator {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu)
    : functor_unitors_associator ua ua (identity_functor_tensor_unit tu).
  Proof.
    repeat split.
    - apply id_preserves_lunitor.
    - apply id_preserves_runitor.
    - apply id_preserves_associator.
  Defined.

  Definition comp_functor_unitors_associator
             {C D E : category}
             {F : functor C D} {G : functor D E}
             {tuC : tensor_unit C}
             {tuD : tensor_unit D}
             {tuE : tensor_unit E}
             {ptuF : functor_tensor_unit tuC tuD F}
             {ptuG : functor_tensor_unit tuD tuE G}
             {uaC : unitors_associator tuC}
             {uaD : unitors_associator tuD}
             {uaE : unitors_associator tuE}
             (puaF : functor_unitors_associator uaC uaD ptuF)
             (puaG : functor_unitors_associator uaD uaE ptuG)
    : functor_unitors_associator uaC uaE (composite_functor_tensor_unit ptuF ptuG).
  Proof.
    repeat split.
    - apply (comp_preserves_lunitor puaF puaG).
    - apply (comp_preserves_runitor puaF puaG).
    - apply (comp_preserves_associator puaF puaG).
  Defined.

  Lemma isaprop_functor_unitors_associator
        {C D : category}
        {tuC : tensor_unit C} {tuD : tensor_unit D}
        (uaC : unitors_associator tuC)
        (uaD : unitors_associator tuD)
        {F : functor C D}
        (ptuF : functor_tensor_unit tuC tuD F)
    : isaprop (functor_unitors_associator uaC uaD ptuF).
  Proof.
    repeat (apply isapropdirprod).
    - apply isaprop_preserves_lunitor.
    - apply isaprop_preserves_runitor.
    - apply isaprop_preserves_associator.
  Qed.

End UnitorsAssociator.

Module UnitorsAssociatorNotation.

  Notation "lu^{ ua }" := (unitors_associator_to_lunitor ua).
  Notation "ru^{ ua }" := (unitors_associator_to_runitor ua).
  Notation "ass^{ ua }" := (unitors_associator_to_associator ua).

End UnitorsAssociatorNotation.

Section PentagonTriangle.

  Import TensorNotation.
  Import TensorUnitNotation.
  Import UnitorsAssociatorNotation.

  Definition triangle {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu) : UU
    := ∏ (x y : C),
      (pr1 ass^{ua} x I_{tu} y) · ((identity x) ⊗^{tu} (pr1 lu^{ua} y))
      = (pr1 ru^{ua} x) ⊗^{tu} (identity y).

  Definition pentagon {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu) : UU
    := ∏ (w x y z : C),
      ((pr1 ass^{ua} w x y) ⊗^{tu} (identity z)) · (pr1 ass^{ua} w (x⊗_{tu} y) z)
                                                 · ((identity w) ⊗^{tu} (pr1 ass^{ua} x y z))
      = (pr1 ass^{ua} (w ⊗_{tu} x) y z) · (pr1 ass^{ua} w x (y ⊗_{tu} z)).

  Definition triangle_pentagon {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu) : UU
    := triangle ua × pentagon ua.

  Lemma isaprop_triangle {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu)
    : isaprop (triangle ua).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply homset_property.
  Qed.

  Lemma isaprop_pentagon {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu)
    : isaprop (pentagon ua).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply homset_property.
  Qed.

  Lemma isaprop_triangle_pentagon {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu)
    : isaprop (triangle_pentagon ua).
  Proof.
    apply isapropdirprod.
    - apply isaprop_triangle.
    - apply isaprop_pentagon.
  Qed.

End PentagonTriangle.

Section Strong.

  Import TensorNotation.
  Import TensorUnitNotation.
  Import UnitorsAssociatorNotation.

  Definition strong_lunitor {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu) : UU
    := ∏ (x : C), is_z_isomorphism (pr1 lu^{ua} x).

  Definition strong_runitor {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu) : UU
    := ∏ (x : C), is_z_isomorphism (pr1 ru^{ua} x).

  Definition strong_associator {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu) : UU
    := ∏ (x y z : C), is_z_isomorphism (pr1 ass^{ua} x y z).

  Definition strong {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu)
             : UU
    := strong_lunitor ua × strong_runitor ua × strong_associator ua.

  Definition isaprop_strong_lunitor {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu)
    : isaprop (strong_lunitor ua).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply isaprop_is_z_isomorphism.
  Qed.

  Definition isaprop_strong_runitor {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu)
    : isaprop (strong_runitor ua).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply isaprop_is_z_isomorphism.
  Qed.

  Definition isaprop_strong_associator {C : category}
             {tu : tensor_unit C}
             (ua : unitors_associator tu)
    : isaprop (strong_associator ua).
  Proof.
    repeat (apply impred_isaprop ; intro).
    apply isaprop_is_z_isomorphism.
  Qed.

  Definition isaprop_strong {C : category}
             {tu : tensor_unit C}
             {ua : unitors_associator tu}
    : isaprop (strong ua).
  Proof.
    repeat (apply isapropdirprod).
    - apply isaprop_strong_lunitor.
    - apply isaprop_strong_runitor.
    - apply isaprop_strong_associator.
  Qed.

  Definition functor_strong
             {C D : category}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             {uaC : unitors_associator tuC}
             {uaD : unitors_associator tuD}
             {F : functor C D}
             {ptuF : functor_tensor_unit tuC tuD F}
             (puaF : functor_unitors_associator uaC uaD ptuF) : UU
    := is_z_isomorphism (pr2 ptuF) × ∏ x y : C, is_z_isomorphism (pr11 ptuF x y).

  Definition isaprop_functor_strong
             {C D : category}
             {tuC : tensor_unit C} {tuD : tensor_unit D}
             {uaC : unitors_associator tuC}
             {uaD : unitors_associator tuD}
             {F : functor C D}
             {ptuF : functor_tensor_unit tuC tuD F}
             (puaF : functor_unitors_associator uaC uaD ptuF)
    : isaprop (functor_strong puaF).
  Proof.
    apply isapropdirprod.
    - apply isaprop_is_z_isomorphism.
    - repeat (apply impred_isaprop ; intro).
      apply isaprop_is_z_isomorphism.
  Qed.

End Strong.

Section MonoidalSigmaStructure.

  Definition tensor_unit_unitors_associator (C : category) : UU
    := ∑ tu : tensor_unit C, unitors_associator tu.

  Definition tensor_unit_unitors_associator_to_tensor_unit
             {C : category} (tuua : tensor_unit_unitors_associator C)
    : tensor_unit C := pr1 tuua.
  Coercion tensor_unit_unitors_associator_to_tensor_unit
    : tensor_unit_unitors_associator >-> tensor_unit.

  Definition tensor_unit_unitors_associator_to_unitors_associator
             {C : category} (tuua : tensor_unit_unitors_associator C)
    : unitors_associator (tensor_unit_unitors_associator_to_tensor_unit tuua)
    := pr2 tuua.
  Coercion tensor_unit_unitors_associator_to_unitors_associator
    : tensor_unit_unitors_associator >-> unitors_associator.

  Definition laxmon (C : category) : UU
    := ∑ tuua : tensor_unit_unitors_associator C, triangle_pentagon tuua.

  Definition laxmon_to_tensor_unit_unitors_associator
             {C : category} (lm : laxmon C)
    : tensor_unit_unitors_associator C := pr1 lm.
  Coercion laxmon_to_tensor_unit_unitors_associator
    : laxmon >-> tensor_unit_unitors_associator.

  Definition strongmon (C : category) : UU
    := ∑ tuua : tensor_unit_unitors_associator C, triangle_pentagon tuua × strong tuua.

  Definition strongmon_to_laxmon
             {C : category} (lm : strongmon C)
    : laxmon C := (pr1 lm,, pr12 lm).
  Coercion strongmon_to_laxmon
    : strongmon >-> laxmon.

End MonoidalSigmaStructure.

Section MonoidalFunctorSigmaStructure.

  Definition functor_tensor_unit_unitors_associator
             {C D : category} (F : functor C D)
             (tuuaC : tensor_unit_unitors_associator C)
             (tuuaD : tensor_unit_unitors_associator D)
    : UU
    := ∑ ftu : functor_tensor_unit tuuaC tuuaD F, functor_unitors_associator tuuaC tuuaD ftu.

  Definition functor_tensor_unit_unitors_associator_to_tensor_unit
             {C D : category} {F : functor C D}
             {tuuaC : tensor_unit_unitors_associator C}
             {tuuaD : tensor_unit_unitors_associator D}
             (ftuua : functor_tensor_unit_unitors_associator F tuuaC tuuaD)
    : functor_tensor_unit tuuaC tuuaD F := pr1 ftuua.
  Coercion functor_tensor_unit_unitors_associator_to_tensor_unit
    : functor_tensor_unit_unitors_associator >-> functor_tensor_unit.

  Definition functor_tensor_unit_unitors_associator_to_unitors_associator
             {C D : category} {F : functor C D}
             {tuuaC : tensor_unit_unitors_associator C}
             {tuuaD : tensor_unit_unitors_associator D}
             (ftuua : functor_tensor_unit_unitors_associator F tuuaC tuuaD)
    : functor_unitors_associator tuuaC tuuaD (functor_tensor_unit_unitors_associator_to_tensor_unit ftuua)
    := pr2 ftuua.
  Coercion functor_tensor_unit_unitors_associator_to_unitors_associator
    : functor_tensor_unit_unitors_associator >-> functor_unitors_associator.

  Definition functor_lax_monoidal
             {C D : category} (F : functor C D)
             (tuuaC : tensor_unit_unitors_associator C)
             (tuuaD : tensor_unit_unitors_associator D) : UU
    := functor_tensor_unit_unitors_associator F tuuaC tuuaD.
  Identity Coercion functor_lax_monoidal_tensorunitunitorsassociator
    : functor_lax_monoidal >-> functor_tensor_unit_unitors_associator.

  Definition functor_strong_monoidal
             {C D : category} (F : functor C D)
             (tuuaC : tensor_unit_unitors_associator C)
             (tuuaD : tensor_unit_unitors_associator D) : UU
    := ∑ ftuua : functor_lax_monoidal F tuuaC tuuaD, functor_strong ftuua.

  Definition functor_strong_monoidal_to_lax_monoidal
             {C D : category} {F : functor C D}
             {tuuaC : tensor_unit_unitors_associator C}
             {tuuaD : tensor_unit_unitors_associator D}
             (ftuuas : functor_strong_monoidal F tuuaC tuuaD)
    : functor_lax_monoidal F tuuaC tuuaD := pr1 ftuuas.

End MonoidalFunctorSigmaStructure.
