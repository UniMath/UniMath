Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.

Section MonoidalStructReordered.

  Definition tensor_unit (C : category) : UU := tensor C × C.
  Definition tensor_unit_to_tensor {C : category} (tu : tensor_unit C)
    : tensor C := pr1 tu.
  Coercion tensor_unit_to_tensor : tensor_unit >-> tensor.
  Definition tensor_unit_to_unit {C : category} (tu : tensor_unit C)
    : ob C := pr2 tu.
  Coercion tensor_unit_to_unit : tensor_unit >-> ob.

  (* Unitors and associators *)
  Definition laxleftunitor {C : category} (tu : tensor_unit C) : UU
    := ∑ lu : leftunitor_data tu tu, leftunitor_nat lu.
  Definition laxleftunitor_to_lunitor_data
             {C : category} {tu : tensor_unit C} (lu : laxleftunitor tu)
    : leftunitor_data tu tu := pr1 lu.
  Coercion laxleftunitor_to_lunitor_data : laxleftunitor >-> leftunitor_data.
  Definition laxleftunitor_to_lunitor_nat
             {C : category} {tu : tensor_unit C} (lu : laxleftunitor tu)
    : leftunitor_nat lu := pr2 lu.

  Definition laxrightunitor {C : category} (tu : tensor_unit C) : UU
    := ∑ ru : rightunitor_data tu tu, rightunitor_nat ru.
  Definition laxrightunitor_to_runitor_data
             {C : category} {tu : tensor_unit C} (ru : laxrightunitor tu)
    : rightunitor_data tu tu := pr1 ru.
  Coercion laxrightunitor_to_runitor_data : laxrightunitor >-> rightunitor_data.
  Definition laxrightunitor_to_runitor_nat
             {C : category} {tu : tensor_unit C} (ru : laxrightunitor tu)
    : rightunitor_nat ru := pr2 ru.

  Definition laxassociator {C : category} (tu : tensor_unit C) : UU
    := ∑ α : associator_data tu,
        (associator_nat_leftwhisker α) × (associator_nat_rightwhisker α) ×
    (associator_nat_leftrightwhisker α).
  Definition laxassociator_to_associator_data
             {C : category} {tu : tensor_unit C} (α : laxassociator tu)
    : associator_data tu := pr1 α.
  Coercion laxassociator_to_associator_data : laxassociator >-> associator_data.
  Definition laxassociator_to_associator_nat_left
             {C : category} {tu : tensor_unit C} (α : laxassociator tu)
    : associator_nat_leftwhisker α := pr12 α.
  Definition laxassociator_to_associator_nat_right
             {C : category} {tu : tensor_unit C} (α : laxassociator tu)
    : associator_nat_rightwhisker α := pr122 α.
  Definition laxassociator_to_associator_nat_leftright
             {C : category} {tu : tensor_unit C} (α : laxassociator tu)
    : associator_nat_leftrightwhisker α := pr222 α.

  Definition tensor_unit_unitors_associator (C : category) : UU
    := ∑ tu : tensor_unit C, laxleftunitor tu × laxrightunitor tu × laxassociator tu.
  Definition tensor_unit_unitors_associator_to_tensor_unit
             {C : category} (tuua : tensor_unit_unitors_associator C)
    : tensor_unit C := pr1 tuua.
  Coercion tensor_unit_unitors_associator_to_tensor_unit
    : tensor_unit_unitors_associator >-> tensor_unit.
  Definition tensor_unit_unitors_associator_laxleftunitor
             {C : category} (tuua : tensor_unit_unitors_associator C)
    : laxleftunitor tuua := pr12 tuua.
  Definition tensor_unit_unitors_associator_laxrightunitor
             {C : category} (tuua : tensor_unit_unitors_associator C)
    : laxrightunitor tuua := pr122 tuua.
  Definition tensor_unit_unitors_associator_laxassociator
             {C : category} (tuua : tensor_unit_unitors_associator C)
    : laxassociator tuua := pr222 tuua.

  (* Triangle-pentagon identities and inverses *)
  Definition lax_monoidal_leftunitor_inverse
             {C : category} (M :  tensor_unit_unitors_associator C) : UU
    := ∑ lui : leftunitorinv_data M M,
        leftunitor_iso_law (tensor_unit_unitors_associator_laxleftunitor M) lui.
  Definition lax_monoidal_leftunitor_inverse_to_inverse_data
             {C : category} {M : tensor_unit_unitors_associator C}
             (lui : lax_monoidal_leftunitor_inverse M)
    : leftunitorinv_data M M := pr1 lui.
  Coercion lax_monoidal_leftunitor_inverse_to_inverse_data
    : lax_monoidal_leftunitor_inverse >-> leftunitorinv_data.
  Definition lax_monoidal_leftunitor_inverse_to_inverse_law
             {C : category} {M : tensor_unit_unitors_associator C}
             (lui : lax_monoidal_leftunitor_inverse M)
    : leftunitor_iso_law (tensor_unit_unitors_associator_laxleftunitor M) lui
    := pr2 lui.

  Definition lax_monoidal_rightunitor_inverse
             {C : category} (M : tensor_unit_unitors_associator C) : UU
    := ∑ lui : rightunitorinv_data M M,
        rightunitor_iso_law (tensor_unit_unitors_associator_laxrightunitor M) lui.
  Definition lax_monoidal_rightunitor_inverse_to_inverse_data
             {C : category} {M : tensor_unit_unitors_associator C}
             (lui : lax_monoidal_rightunitor_inverse M)
    : rightunitorinv_data M M := pr1 lui.
  Coercion lax_monoidal_rightunitor_inverse_to_inverse_data
    : lax_monoidal_rightunitor_inverse >-> rightunitorinv_data.
  Definition lax_monoidal_rightunitor_inverse_to_inverse_law
             {C : category} {M : tensor_unit_unitors_associator C}
             (lui : lax_monoidal_rightunitor_inverse M)
    : rightunitor_iso_law (tensor_unit_unitors_associator_laxrightunitor M) lui
    := pr2 lui.

  Definition lax_monoidal_associator_inverse
             {C : category} (M : tensor_unit_unitors_associator C) : UU
    := ∑ lui : associatorinv_data M,
        associator_iso_law (tensor_unit_unitors_associator_laxassociator M) lui.
  Definition lax_monoidal_associator_inverse_to_inverse_data
             {C : category} {M : tensor_unit_unitors_associator C}
             (lui : lax_monoidal_associator_inverse M)
    : associatorinv_data M := pr1 lui.
  Coercion lax_monoidal_associator_inverse_to_inverse_data
    : lax_monoidal_associator_inverse >-> associatorinv_data.
  Definition lax_monoidal_associator_inverse_to_inverse_law
             {C : category} {M : tensor_unit_unitors_associator C} (lui : lax_monoidal_associator_inverse M)
    : associator_iso_law (tensor_unit_unitors_associator_laxassociator M) lui
    := pr2 lui.

  Definition unitorsassociator_inverses
             {C : category} (tuua : tensor_unit_unitors_associator C) : UU
    := lax_monoidal_leftunitor_inverse tuua
                                        × lax_monoidal_rightunitor_inverse tuua
                                        × lax_monoidal_associator_inverse tuua.

  Definition unitorsassociator_inverses_to_leftunitorinverse
             {C : category} {tuua : tensor_unit_unitors_associator C}
             (ui : unitorsassociator_inverses tuua)
    : lax_monoidal_leftunitor_inverse tuua := pr1 ui.

  Definition unitorsassociator_inverses_to_rightunitorinverse
             {C : category} {tuua : tensor_unit_unitors_associator C}
             (ui : unitorsassociator_inverses tuua)
    : lax_monoidal_rightunitor_inverse tuua := pr12 ui.

  Definition unitorsassociator_inverses_to_associatorinverse
             {C : category} {tuua : tensor_unit_unitors_associator C}
             (ui : unitorsassociator_inverses tuua)
    : lax_monoidal_associator_inverse tuua := pr22 ui.

  Definition pentagontriangle
             {C : category} (tuua : tensor_unit_unitors_associator C) : UU
    := triangle_identity
        (tensor_unit_unitors_associator_laxleftunitor tuua)
        (tensor_unit_unitors_associator_laxrightunitor tuua)
        (tensor_unit_unitors_associator_laxassociator tuua)
        ×
       pentagon_identity
       (tensor_unit_unitors_associator_laxassociator tuua).

  Definition pentagontriangle_to_triangle
             {C : category} {tuua : tensor_unit_unitors_associator C}
             (pt : pentagontriangle tuua)
    : triangle_identity
        (tensor_unit_unitors_associator_laxleftunitor tuua)
        (tensor_unit_unitors_associator_laxrightunitor tuua)
        (tensor_unit_unitors_associator_laxassociator tuua)
    := pr1 pt.

  Definition pentagontriangle_to_pentagon
             {C : category} {tuua : tensor_unit_unitors_associator C}
             (pt : pentagontriangle tuua)
    : pentagon_identity
       (tensor_unit_unitors_associator_laxassociator tuua)
    := pr2 pt.

  Definition monoidal_struct (C : category) : UU
    := ∑ M : tensor_unit_unitors_associator C,
        pentagontriangle M × unitorsassociator_inverses M.

  Definition monoidal_struct_to_tensor_unit_unitors_associator
             {C : category} (M : monoidal_struct C)
    : tensor_unit_unitors_associator C := pr1 M.
  Coercion monoidal_struct_to_tensor_unit_unitors_associator
    : monoidal_struct >-> tensor_unit_unitors_associator.

  Definition monoidal_struct_to_pentagontriangle
             {C : category} (M : monoidal_struct C)
    : pentagontriangle M
    := pr12 M.

  Definition monoidal_struct_to_unitorsassociator_inverses
             {C : category} (M : monoidal_struct C)
    : unitorsassociator_inverses M := pr22 M.

End MonoidalStructReordered.

Section ReorderingMonStructEquivalence.

  Definition monoidal_to_tensor_unit {C : category} (M : monoidal C)
    : tensor_unit C := monoidal_tensor M ,, monoidal_unit M.

  Definition monoidal_to_tensor_unit_unitors_associator {C : category} (M : monoidal C)
    : tensor_unit_unitors_associator C.
  Proof.
    exists (monoidal_to_tensor_unit M).
    repeat split.
    - exists (monoidal_leftunitordata M).
      exact (monoidal_leftunitornat M).
    - exists (monoidal_rightunitordata M).
      exact (monoidal_rightunitornat M).
    - exists (monoidal_associatordata M).
      exists (monoidal_associatornatleft M).
      exists (monoidal_associatornatright M).
      exact (monoidal_associatornatleftright M).
  Defined.

  Definition monoidal_to_monoidal_struct {C : category} (M : monoidal C)
    : monoidal_struct C.
  Proof.
    exists (monoidal_to_tensor_unit_unitors_associator M).
    repeat split.
    - exact (monoidal_triangleidentity M).
    - exact (monoidal_pentagonidentity M).
    - exists (monoidal_leftunitorinvdata M).
      exact (monoidal_leftunitorisolaw M).
    - exists (monoidal_rightunitorinvdata M).
      exact (monoidal_rightunitorisolaw M).
    - exists (monoidal_associatorinvdata M).
      exact (monoidal_associatorisolaw M).
  Defined.

  Definition monoidal_struct_to_monoidal_data {C : category} (M : monoidal_struct C)
    : monoidal_data C.
  Proof.
    set (tuua := monoidal_struct_to_tensor_unit_unitors_associator M).
    set (tu := tensor_unit_unitors_associator_to_tensor_unit tuua).
    set (ui := (monoidal_struct_to_unitorsassociator_inverses M)).
    exists (tensor_unit_to_tensor tu).
    exists (tensor_unit_to_unit tu).
    exists (tensor_unit_unitors_associator_laxleftunitor tuua).
    exists (unitorsassociator_inverses_to_leftunitorinverse ui).
    exists (pr1 (tensor_unit_unitors_associator_laxrightunitor tuua)).
    exists (unitorsassociator_inverses_to_rightunitorinverse ui).
    exists (tensor_unit_unitors_associator_laxassociator tuua).
    exact (unitorsassociator_inverses_to_associatorinverse ui).
  Defined.

  Definition monoidal_struct_to_monoidal_laws {C : category} (M : monoidal_struct C)
    : monoidal_laws (monoidal_struct_to_monoidal_data M).
  Proof.
    set (tuua := monoidal_struct_to_tensor_unit_unitors_associator M).
    set (tu := tensor_unit_unitors_associator_to_tensor_unit tuua).
    set (ui := (monoidal_struct_to_unitorsassociator_inverses M)).
    exists (laxleftunitor_to_lunitor_nat _ ,, lax_monoidal_leftunitor_inverse_to_inverse_law _).
    exists (laxrightunitor_to_runitor_nat _ ,, lax_monoidal_rightunitor_inverse_to_inverse_law _).
    split.
    - exists (laxassociator_to_associator_nat_left _).
      exists (laxassociator_to_associator_nat_right _).
      exists (laxassociator_to_associator_nat_leftright _).
      do 3 intro ; apply lax_monoidal_associator_inverse_to_inverse_law.
    - apply monoidal_struct_to_pentagontriangle.
  Defined.

  Definition monoidal_struct_to_monoidal {C : category} (M : monoidal_struct C)
    : monoidal C
    := monoidal_struct_to_monoidal_data M ,, monoidal_struct_to_monoidal_laws M.

  Definition monoidal_struct_equiv_monoidal (C : category)
    : monoidal_struct C ≃ monoidal C.
  Proof.
    use weq_iso.
    - exact monoidal_struct_to_monoidal.
    - exact monoidal_to_monoidal_struct.
    - apply idpath.
    - apply idpath.
  Defined.

End ReorderingMonStructEquivalence.
