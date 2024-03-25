(** ***************************************************************

Contents:
 - Category of coalgebras over an endofunctor.
 - Dual of Lambek's lemma: if (A,α) is final coalgebra, α is an isomorphism.
 - Primitive corecursion.

******************************************************************)

Require Import UniMath.Foundations.Propositions.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.

Section Coalgebra_Definition.

  Context {C : category} (F : functor C C).

  Definition coalgebra_disp_cat_ob_mor : disp_cat_ob_mor C.
  Proof.
    use tpair.
    - exact (λ x, x --> F x).
    - exact (λ x y hx hy f, hx · #F f = f · hy).
  Defined.

  Definition coalgebra_disp_cat_id_comp
    : disp_cat_id_comp C coalgebra_disp_cat_ob_mor.
  Proof.
    split.
    - intros x hx ; cbn.
      rewrite !functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - intros x y z f g hx hy hz hf hg ; cbn in *.
      rewrite !functor_comp.
      rewrite !assoc.
      rewrite hf.
      rewrite !assoc'.
      rewrite hg.
      apply idpath.
  Qed.

  Definition coalgebra_disp_cat_data : disp_cat_data C
    := coalgebra_disp_cat_ob_mor ,, coalgebra_disp_cat_id_comp.

  Definition coalgebra_disp_cat_axioms
    : disp_cat_axioms C coalgebra_disp_cat_data.
  Proof.
    repeat split ; intros ; try (apply homset_property).
    apply isasetaprop.
    apply homset_property.
  Qed.

  Definition coalgebra_disp_cat : disp_cat C
    := coalgebra_disp_cat_data ,, coalgebra_disp_cat_axioms.

  Definition CoAlg_category : category
    := total_category coalgebra_disp_cat.

  Definition coalgebra_ob : UU := ob CoAlg_category.


  Definition coalg_carrier (X : coalgebra_ob) : C := pr1 X.
  Local Coercion coalg_carrier : coalgebra_ob >-> ob.

  Definition coalg_map (X : coalgebra_ob) : C ⟦X, F X ⟧ := pr2 X.

  (** A homomorphism of F-coalgebras (F A, α : C ⟦A, F A⟧) and (F B, β : C ⟦B, F B⟧)
    is a morphism f : C ⟦A, B⟧ s.t. the below diagram commutes.
<<
         f
     A -----> B
     |        |
     | α      | β
     |        |
     V        V
    F A ---> F B
        F f
>>
*)

  Definition is_coalgebra_mor (X Y : coalgebra_ob) (f : coalg_carrier X --> coalg_carrier Y) : UU
    := coalg_map X · #F f = f · coalg_map Y.

  Definition coalgebra_mor (X Y : coalgebra_ob) : UU := CoAlg_category⟦X,Y⟧.
  #[reversible=no] Coercion mor_from_coalgebra_mor {X Y : coalgebra_ob} (f : coalgebra_mor X Y) : C⟦X, Y⟧ := pr1 f.

  Lemma coalgebra_mor_commutes {X Y : coalgebra_ob} (f : coalgebra_mor X Y)
    : coalg_map X · #F f = pr1 f · coalg_map Y.
  Proof.
    exact (pr2 f).
  Qed.

  Definition coalgebra_homo_eq {X Y : coalgebra_ob}
             (f g : coalgebra_mor X Y) : (f : C ⟦X, Y⟧) = g ≃ f = g.
  Proof.
    apply invweq.
    apply subtypeInjectivity.
    intro. apply homset_property.
  Defined.

End Coalgebra_Definition.

Section Lambek_dual.
(** Dual of Lambeks Lemma : If (A,α) is final F-coalgebra, then α is an iso *)

Context (C : category)
        (F : functor C C)
        (X : coalgebra_ob F).

Local Notation F_CoAlg := (CoAlg_category F).

Context (isTerminalX : isTerminal F_CoAlg X).

Definition TerminalX : Terminal F_CoAlg := make_Terminal _ isTerminalX.

Local Notation α := (coalg_map F (TerminalObject TerminalX)).
Local Notation A := (coalg_carrier F (TerminalObject TerminalX)).

(** FX := (FA,Fα) is also an F-coalgebra *)
Definition FX : ob F_CoAlg := tpair _ (F A) (#F α).

(** By terminality there is an arrow α' : FA → A, s.t.:
<<
         α'
    FA ------> A
    |          |
    | Fα       | α
    V          V
   FFA ------> FA
         Fα'
>>
  commutes *)

Definition f : F_CoAlg ⟦FX, TerminalX⟧ := (@TerminalArrow F_CoAlg TerminalX FX).

Definition α' : C ⟦F A, A⟧ := mor_from_coalgebra_mor F f.

Definition αα'_mor : coalgebra_mor F X X.
Proof.
  exists (α · α').
  simpl.
  rewrite <- assoc.
  apply cancel_precomposition.
  rewrite functor_comp.
  apply (coalgebra_mor_commutes F f).
Defined.

Definition αα'_idA : α · α' = identity A
  := maponpaths pr1 (TerminalEndo_is_identity (T:=TerminalX) αα'_mor).

Lemma α'α_idFA : α' · α = identity (F A).
Proof.
  rewrite <- functor_id.
  rewrite <- αα'_idA.
  rewrite functor_comp.
  unfold α'.
  apply pathsinv0.
  apply (coalgebra_mor_commutes F f).
Defined.

Lemma finalcoalgebra_is_z_iso : is_z_isomorphism α.
Proof.
  use make_is_z_isomorphism.
  - exact α'.
  - split.
    + exact αα'_idA.
    + exact α'α_idFA.
Defined.

Definition finalcoalgebra_z_iso : z_iso A (F A) := α,, finalcoalgebra_is_z_iso.

(* Definition finalcoalgebra_iso : iso A (F A) := z_iso_to_iso finalcoalgebra_z_iso. *)

End Lambek_dual.

Section PrimitiveCorecursion.

  Context {C : category} (CP : BinCoproducts C)
          {F : functor C C} {νF : coalgebra_ob F}
          (isTerminalνF : isTerminal (CoAlg_category F) νF).

  Context {x : C} (ϕ : C⟦x, F(CP x (pr1 νF))⟧).

  Definition X_coproduct_νF_coalgebra : coalgebra_ob F.
  Proof.
    exists (CP x (pr1 νF)).
    exact (BinCoproductArrow (CP x (pr1 νF)) ϕ (pr2 νF · #F (BinCoproductIn2 (CP x (pr1 νF))))).
  Defined.

  Let h : C⟦x, pr1 νF⟧
      := (BinCoproductIn1 (CP x (pr1 νF)) · pr1 (@TerminalArrow (CoAlg_category F) (νF,,isTerminalνF) X_coproduct_νF_coalgebra)).

  Lemma X_coproduct_νF_coalgebra_morphism_into_νF_aux :
    pr2 X_coproduct_νF_coalgebra -->[ BinCoproductArrow (CP x (pr1 νF)) h (identity (pr1 νF))] pr2 νF.
  Proof.
    cbn.

    etrans.
    1: apply postcompWithBinCoproductArrow.
    etrans.
    2: apply pathsinv0, postcompWithBinCoproductArrow.

    assert (p0 : ϕ · # F (BinCoproductArrow (CP x (pr1 νF)) h (identity (pr1 νF))) = h · pr2 νF).
    {
      unfold h.
      set (t := pr2 (TerminalArrow (νF,, isTerminalνF) X_coproduct_νF_coalgebra)).
      cbn in t.

      etrans.
      2: apply assoc.
      etrans.
      2: apply maponpaths, t.
      etrans.
      2: apply assoc'.
      etrans.
      2: apply maponpaths_2, pathsinv0, BinCoproductIn1Commutes.
      do 2 apply maponpaths.

      assert (p1 : identity (pr1 νF) = BinCoproductIn2 (CP x (pr1 νF)) ·  pr1 (TerminalArrow (νF,, isTerminalνF) X_coproduct_νF_coalgebra)).
      {
        etrans.
        1: apply (base_paths _ _ (TerminalArrowUnique (νF,,isTerminalνF) νF (identity _))).

        transparent assert (f : ((CoAlg_category F)⟦νF,νF⟧)).
        {
          refine (_ · (TerminalArrow (νF,, isTerminalνF) X_coproduct_νF_coalgebra)).
          exists (BinCoproductIn2 (CP x (pr1 νF))).
          apply pathsinv0, BinCoproductIn2Commutes.
        }
        exact (! base_paths _ _ (TerminalArrowUnique (νF,,isTerminalνF) νF f)).
      }
      rewrite p1.
      apply pathsinv0, BinCoproductArrowEta.
    }

    rewrite p0.
    apply maponpaths.

    etrans.
    1: apply assoc'.
    etrans. {
      apply maponpaths.
      etrans.
      1: apply pathsinv0, functor_comp.
      apply maponpaths.
      apply BinCoproductIn2Commutes.
    }
    etrans. {
      apply maponpaths.
      apply functor_id.
    }
    exact (id_right _ @ ! id_left _).
  Qed.

  Definition X_coproduct_νF_coalgebra_morphism_into_νF : (CoAlg_category F ⟦ X_coproduct_νF_coalgebra, νF⟧).
  Proof.
    exists (BinCoproductArrow (CP x (pr1 νF)) h (identity (pr1 νF))).
    exact X_coproduct_νF_coalgebra_morphism_into_νF_aux.
  Defined.

  Definition primitive_corecursion_characteristic_formula (h :  C⟦x, pr1 νF⟧) : UU :=
    h · (pr2 νF) = ϕ · #F (BinCoproductArrow (CP _ _) h (identity _)).

  Lemma primitive_corecursion_existence : primitive_corecursion_characteristic_formula h.
  Proof.
    etrans. { apply assoc'. }
    etrans. {
      apply maponpaths.
      exact (! pr2 (@TerminalArrow (CoAlg_category F) (νF,,isTerminalνF) X_coproduct_νF_coalgebra)).
    }
    cbn.
    etrans. { apply assoc. }
    etrans. {
      apply maponpaths_2.
      apply BinCoproductIn1Commutes.
    }
    do 2 apply maponpaths.
    apply pathsinv0.
    exact (base_paths _ _ (TerminalArrowUnique (νF,, isTerminalνF) _ X_coproduct_νF_coalgebra_morphism_into_νF)).
  Qed.

  Lemma primitive_corecursion_aux (p : ∑ h : C ⟦ x, pr1 νF ⟧, primitive_corecursion_characteristic_formula h) :
    p = h,, primitive_corecursion_existence.
  Proof.
    use total2_paths_f.
    - assert (q : (pr1 p = BinCoproductIn1 (CP x (pr1 νF)) · (BinCoproductArrow (CP _ _) (pr1 p) (identity _)))).
      {
        apply pathsinv0, BinCoproductIn1Commutes.
      }

      etrans.
      1: exact q.
      simpl.
      apply maponpaths.

      transparent assert ( f : ( CoAlg_category F ⟦ X_coproduct_νF_coalgebra, νF⟧)).
      {
        exists ( BinCoproductArrow (CP x (pr1 νF)) (pr1 p) (identity (pr1 νF))).
        cbn.

        etrans.
        1: apply postcompWithBinCoproductArrow.
        etrans.
        2: apply pathsinv0, postcompWithBinCoproductArrow.

        use (BinCoproductArrowUnique _ _ _ (CP x (pr1 νF)) (F (pr1 νF))).
        - etrans.
          1: apply BinCoproductIn1Commutes.
          exact (! pr2 p).
        - etrans.
          1: apply BinCoproductIn2Commutes.
          etrans.
          1: apply assoc'.
          etrans. {
            apply maponpaths.
            etrans.
            1: apply pathsinv0, functor_comp.
            apply maponpaths.
            apply BinCoproductIn2Commutes.
          }
          etrans. {
            apply maponpaths.
            apply functor_id.
          }
          exact (id_right _ @ ! id_left _).
      }
      exact (base_paths _ _ (TerminalArrowUnique  (νF,, isTerminalνF)  X_coproduct_νF_coalgebra f)).
    - apply homset_property.
  Qed.

  Definition primitive_corecursion
    : ∃! h : C⟦x, pr1 νF⟧, primitive_corecursion_characteristic_formula h.
  Proof.
    exists (h ,, primitive_corecursion_existence).
    apply primitive_corecursion_aux.
  Defined.

  Lemma primitive_corecursion_formula_with_inverse :
    h  = ϕ · #F (BinCoproductArrow (CP _ _) h (identity _)) · (α' _ _ _ isTerminalνF).
  Proof.
    etrans.
    2: { exact (maponpaths (fun x => x · α' C F νF isTerminalνF) primitive_corecursion_existence). }
    rewrite assoc'.
    etrans.
    2: { apply maponpaths, pathsinv0, αα'_idA. }
    apply pathsinv0, id_right.
  Qed.

End PrimitiveCorecursion.
