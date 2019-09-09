(* ******************************************************************************* *)
(** * Univalence for bicategories
    Benedikt Ahrens, Marco Maggesi
    May 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Local Open Scope bicategory_scope.
Local Open Scope cat.

Section Idtoiso.
  Context {C : bicat}.

  Definition internal_adjunction_data_identity (a : C)
    : left_adjoint_data (identity a).
  Proof.
    exists (identity a).
    exact (linvunitor (identity a),, lunitor (identity a)).
  Defined.

  Definition is_internal_adjunction_identity (a : C)
    : left_adjoint_axioms (internal_adjunction_data_identity a).
  Proof.
    split.
    - etrans.
      { apply maponpaths_2.
        etrans; [apply (!vassocr _ _ _) | ].
        etrans.
        { apply maponpaths.
          etrans; [apply lunitor_lwhisker | ].
          apply maponpaths, pathsinv0, lunitor_runitor_identity.
        }
        etrans; [apply (!vassocr _ _ _) | ].
        etrans.
        { apply maponpaths.
          etrans; [apply rwhisker_vcomp | ].
          etrans; [apply maponpaths, linvunitor_lunitor | ].
          apply id2_rwhisker.
        }
        apply id2_right.
      }
      etrans; [apply maponpaths, pathsinv0, lunitor_runitor_identity | ].
      apply linvunitor_lunitor.
    - etrans.
      { apply maponpaths_2.
        etrans; [apply (!vassocr _ _ _) | ].
        etrans.
        { apply maponpaths.
          etrans.
          { apply maponpaths.
            apply maponpaths.
            apply lunitor_runitor_identity.
          }
          apply runitor_rwhisker.
        }
        etrans; [apply (!vassocr _ _ _) | ].
        apply maponpaths.
        etrans; [ apply lwhisker_vcomp | ].
        apply maponpaths.
        apply linvunitor_lunitor.
      }
      etrans; [apply (!vassocr _ _ _) | ].
      etrans.
      { apply maponpaths.
        etrans; [apply maponpaths_2, lwhisker_id2 | ].
        apply id2_left.
      }
      etrans; [apply maponpaths, lunitor_runitor_identity | ].
      apply rinvunitor_runitor.
  Qed.

  Definition internal_adjoint_equivalence_identity (a : C)
    : adjoint_equivalence a a.
  Proof.
    exists (identity a).
    use tpair.
    - apply internal_adjunction_data_identity.
    - split; [ apply is_internal_adjunction_identity |].
      split.
      + apply is_invertible_2cell_linvunitor.
      + apply is_invertible_2cell_lunitor.
  Defined.

  Definition idtoiso_2_0 (a b : C)
    : a = b -> adjoint_equivalence a b.
  Proof.
    induction 1.
    apply internal_adjoint_equivalence_identity.
  Defined.

  Definition idtoiso_2_1 {a b : C} (f g : C⟦a,b⟧)
    : f = g -> invertible_2cell f g.
  Proof.
    induction 1. apply id2_invertible_2cell.
  Defined.
End Idtoiso.

Definition is_univalent_2_1 (C : bicat) : UU
  := ∏ (a b : C) (f g : C⟦a,b⟧), isweq (idtoiso_2_1 f g).

Definition is_univalent_2_0 (C : bicat) : UU
    := ∏ (a b : C), isweq (idtoiso_2_0 a b).

Definition is_univalent_2 (C : bicat) : UU
  := is_univalent_2_0 C × is_univalent_2_1 C.

Definition isaprop_is_univalent_2_1 (C : bicat)
  : isaprop (is_univalent_2_1 C).
Proof.
  do 4 (apply impred ; intro).
  apply isapropisweq.
Defined.

Definition isaprop_is_univalent_2_0 (C : bicat)
  : isaprop (is_univalent_2_0 C).
Proof.
  do 2 (apply impred ; intro).
  apply isapropisweq.
Defined.

Definition isaprop_is_univalent_2 (C : bicat)
  : isaprop (is_univalent_2 C).
Proof.
  apply isapropdirprod.
  apply isaprop_is_univalent_2_0.
  apply isaprop_is_univalent_2_1.
Defined.

Definition isotoid_2_1
           {C : bicat}
           (HC : is_univalent_2_1 C)
           {a b : C}
           {f g : C⟦a,b⟧}
           (α : invertible_2cell f g)
  : f = g
  := invmap (idtoiso_2_1 f g ,, HC a b f g) α.

Definition isotoid_2_0
           {C : bicat}
           (HC : is_univalent_2_0 C)
           {a b : C}
           (f : adjoint_equivalence a b)
  : a = b
  := invmap (idtoiso_2_0 a b ,, HC a b) f.


(** In a univalent bicategory 0-cells are 1-types.
For the proofs that 1-cells are 2-types see AdjointUnique.v *)
Lemma univalent_bicategory_1_cell_hlevel_3
      (C : bicat) (HC : is_univalent_2_1 C) (a b : C) :
  isofhlevel 3 (C⟦a,b⟧).
Proof.
  intros f g.
  apply (isofhlevelweqb _ (idtoiso_2_1 f g,, HC _ _ f g)).
  apply isaset_invertible_2cell.
Qed.

(** Local Univalence implies the hom cats are univalent *)
Section IsoInvertible2Cells.
  Context {C : bicat}.
  Variable (C_is_univalent_2_1 : is_univalent_2_1 C).

  Definition is_inv2cell_to_is_iso {a b : C} (f g : hom a b) (η : f ==> g)
    : is_invertible_2cell η → is_iso η.
  Proof.
    intros p h.
    use isweq_iso.
    - intro ψ.
      cbn in *.
      exact (p^-1 • ψ).
    - abstract (intro ψ;
                cbn in *;
                rewrite vassocr;
                rewrite vcomp_lid;
                apply id2_left).
    - abstract (intro ψ;
                cbn in *;
                rewrite vassocr;
                rewrite vcomp_rinv;
                apply id2_left).
  Defined.

  Definition inv2cell_to_iso {a b : C} (f g : hom a b) : invertible_2cell f g → iso f g.
  Proof.
    intro i.
    use make_iso.
    - apply i.
    - apply is_inv2cell_to_is_iso.
      apply i.
  Defined.


  Definition iso_to_inv2cell {a b : C} (f g : hom a b) : iso f g → invertible_2cell f g.
  Proof.
    intro i.
    use tpair.
    + exact (morphism_from_iso i).
    + use make_is_invertible_2cell.
      * exact (inv_from_iso i).
      * exact (iso_inv_after_iso i).
      * exact (iso_after_iso_inv i).
  Defined.

  Definition inv2cell_to_iso_isweq {a b : C} (f g : hom a b) : isweq (inv2cell_to_iso f g).
  Proof.
    use isweq_iso.
    - exact (iso_to_inv2cell f g).
    - intro i.
      apply cell_from_invertible_2cell_eq.
      apply idpath.
    - intro i.
      apply eq_iso.
      apply idpath.
  Defined.

  Definition inv2cell_to_iso_weq {a b : C} (f g : hom a b) : invertible_2cell f g ≃ iso f g.
  Proof.
    use make_weq.
    - exact (inv2cell_to_iso f g).
    - exact (inv2cell_to_iso_isweq f g).
  Defined.

  Definition idtoiso_alt_weq {a b : C} (f g : hom a b) : f = g ≃ iso f g.
  Proof.
    refine (inv2cell_to_iso_weq f g ∘ _)%weq.
    use make_weq.
    - exact (idtoiso_2_1 f g).
    - apply C_is_univalent_2_1.
  Defined.

  Definition idtoiso_weq {a b : C} (f g : hom a b) : isweq (λ p : f = g, idtoiso p).
  Proof.
    use weqhomot.
    + exact (idtoiso_alt_weq f g).
    + intro p.
      apply eq_iso.
      induction p.
      apply idpath.
  Defined.
End IsoInvertible2Cells.

Definition univ_hom
           {C : bicat}
           (C_is_univalent_2_1 : is_univalent_2_1 C)
           (X Y : C)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (hom X Y).
  - split.
    + apply idtoiso_weq.
      exact C_is_univalent_2_1.
    + exact (pr2 C X Y).
Defined.

Definition idtoiso_2_1_isotoid_2_1
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {a b : B}
           {f g : a --> b}
           (α : invertible_2cell f g)
  : idtoiso_2_1 _ _ (isotoid_2_1 HB α) = α.
Proof.
  unfold isotoid_2_1.
  exact (homotweqinvweq (make_weq (idtoiso_2_1 f g) (HB _ _ f g)) α).
Defined.

Definition isotoid_2_1_idtoiso_2_1
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {a b : B}
           {f g : a --> b}
           (p : f = g)
  : isotoid_2_1 HB (idtoiso_2_1 _ _ p) = p.
Proof.
  unfold isotoid_2_1.
  exact (homotinvweqweq (make_weq (idtoiso_2_1 f g) (HB _ _ f g)) p).
Defined.

Definition idtoiso_2_0_isotoid_2_0
           {B : bicat}
           (HB : is_univalent_2_0 B)
           {a b : B}
           (f : adjoint_equivalence a b)
  : idtoiso_2_0 _ _ (isotoid_2_0 HB f) = f.
Proof.
  unfold isotoid_2_0.
  exact (homotweqinvweq (make_weq (idtoiso_2_0 a b) (HB a b)) f).
Defined.

Definition isotoid_2_0_idtoiso_2_0
           {B : bicat}
           (HB : is_univalent_2_0 B)
           {a b : B}
           (p : a = b)
  : isotoid_2_0 HB (idtoiso_2_0 _ _ p) = p.
Proof.
  unfold isotoid_2_0.
  exact (homotinvweqweq (make_weq (idtoiso_2_0 a b) (HB a b)) p).
Defined.

(* ----------------------------------------------------------------------------------- *)
(** ** J rule for locally univalent bicategories                                       *)
(* ----------------------------------------------------------------------------------- *)

Section J21.
  Context {B : bicat}.
  Variable (HB : is_univalent_2_1 B)
           (Y : ∏ (a b : B) (f g : a --> b), invertible_2cell f g → UU)
           (r : ∏ (a b : B) (f : a --> b), Y _ _ _ _ (id2_invertible_2cell f)).

  Local Definition Y'_2_1
        {a b : B}
        {f g : a --> b}
        (p : f = g) :
    UU := Y a b f g (idtoiso_2_1 f g p).

  Local Definition J'_2_1
        {a b : B}
        {f g : a --> b}
        (p : f = g)
    : Y'_2_1 p.
  Proof.
    induction p.
    exact (r a b f).
  Defined.

  Local Lemma J'_2_1_transport
        {a b : B}
        {f g : a --> b}
        (p q : f = g)
        (s : p = q)
    : transportf Y'_2_1 s (J'_2_1 p) = J'_2_1 q.
  Proof.
    induction s.
    exact (idpath _).
  Defined.

  Definition J_2_1
             {a b : B}
             {f g : a --> b}
             (α : invertible_2cell f g)
    : Y a b f g α
    := transportf (Y a b f g) (idtoiso_2_1_isotoid_2_1 HB α) (J'_2_1 (isotoid_2_1 HB α)).

  Definition J_2_1_comp
             {a b : B}
             {f : a --> b}
    : J_2_1 (id2_invertible_2cell f) = r a b f.
  Proof.
    unfold J_2_1.
    refine (! (!_ @ _)).
    + exact (J'_2_1_transport _ _ (isotoid_2_1_idtoiso_2_1 HB (idpath f))).
    + rewrite (functtransportf (idtoiso_2_1 f f) (Y a b f f)).
      apply maponpaths_2.
      exact (homotweqinvweqweq (make_weq (idtoiso_2_1 f f) (HB _ _ f f)) (idpath f)).
  Qed.
End J21.

(* ----------------------------------------------------------------------------------- *)
(** ** J rule for globally univalent bicategories                                      *)
(* ----------------------------------------------------------------------------------- *)

Section J20.
  Context {B : bicat}.
  Variable (HB : is_univalent_2_0 B)
           (Y : ∏ (a b : B), adjoint_equivalence a b → UU)
           (r : ∏ (a : B), Y _ _ (internal_adjoint_equivalence_identity a)).

  Local Definition Y'_2_0 : ∏ {a b : B}, a = b → UU
    := λ a b p,  Y a b (idtoiso_2_0 a b p).

  Local Definition J'_2_0
        {a b : B}
        (p : a = b)
    : Y'_2_0 p.
  Proof.
    induction p.
    exact (r a).
  Defined.

  Local Lemma J'_2_0_transport
        {a b : B}
        (p q : a = b)
        (s : p = q)
    : transportf Y'_2_0 s (J'_2_0 p) = J'_2_0 q.
  Proof.
    induction s.
    exact (idpath _).
  Defined.

  Definition J_2_0
             {a b : B}
             (f : adjoint_equivalence a b)
    : Y a b f
    := transportf (Y a b) (idtoiso_2_0_isotoid_2_0 HB f) (J'_2_0 (isotoid_2_0 HB f)).

  Definition J_2_0_comp
             {a : B}
    : J_2_0 (internal_adjoint_equivalence_identity a) = r a.
  Proof.
    unfold J_2_0.
    refine (! (!_ @ _)).
    + exact (J'_2_0_transport _ _ (isotoid_2_0_idtoiso_2_0 HB (idpath a))).
    + rewrite (functtransportf (idtoiso_2_0 a a) (Y a a)).
      apply maponpaths_2.
      exact (homotweqinvweqweq (make_weq (idtoiso_2_0 a a) (HB a a)) (idpath a)).
  Defined.
End J20.

(* ----------------------------------------------------------------------------------- *)
(** ** Application of J:                                                               *)
(** ** Adjoint equivalences in a globally univalent bicategory form a pregroupoid      *)
(* ----------------------------------------------------------------------------------- *)

Section AdjointEquivPregroupoid.
  Context {B : bicat}.
  Variable (HB : is_univalent_2_0 B).

  Definition comp_adjoint_equivalence
             (a b c : B)
             (f : adjoint_equivalence a b)
             (g : adjoint_equivalence b c)
    : adjoint_equivalence a c
    := J_2_0 HB (λ a b _, ∏ (c : B), adjoint_equivalence b c → adjoint_equivalence a c) (λ _ _ h, h) f c g.

  Definition inv_adjoint_equivalence
             (a b : B)
             (f : adjoint_equivalence a b)
    : adjoint_equivalence b a
    := J_2_0 HB (λ a b _, adjoint_equivalence b a) internal_adjoint_equivalence_identity f.

  Definition adjoint_equivalence_lid
             (a b : B)
             (f : adjoint_equivalence a b)
    : comp_adjoint_equivalence a a b (internal_adjoint_equivalence_identity a) f = f.
  Proof.
    apply (J_2_0 HB (λ a b f, comp_adjoint_equivalence a a b (internal_adjoint_equivalence_identity a) f = f)).
    intro c.
    unfold comp_adjoint_equivalence.
    rewrite J_2_0_comp.
    apply idpath.
  Defined.

  Definition adjoint_equivalence_rid
             (a b : B)
             (f : adjoint_equivalence a b)
    : comp_adjoint_equivalence a b b f (internal_adjoint_equivalence_identity b) = f.
  Proof.
    apply (J_2_0 HB (λ a b f, comp_adjoint_equivalence a b b f (internal_adjoint_equivalence_identity b) = f)).
    intro c.
    unfold comp_adjoint_equivalence.
    rewrite J_2_0_comp.
    apply idpath.
  Defined.

  Definition adjoint_equivalence_assoc
             (a b c d : B)
             (f : adjoint_equivalence a b)
             (g : adjoint_equivalence b c)
             (h : adjoint_equivalence c d)
    : comp_adjoint_equivalence a b d f (comp_adjoint_equivalence b c d g h) =
      comp_adjoint_equivalence a c d (comp_adjoint_equivalence a b c f g) h.
  Proof.
    apply (J_2_0 HB (λ a b f,
                     ∏ (c d : B) (g : adjoint_equivalence b c) (h : adjoint_equivalence c d),
                     comp_adjoint_equivalence a b d f (comp_adjoint_equivalence b c d g h) =
                     comp_adjoint_equivalence a c d (comp_adjoint_equivalence a b c f g) h)).
    intros.
    rewrite adjoint_equivalence_lid.
    apply maponpaths_2.
    rewrite adjoint_equivalence_lid.
    exact (idpath _).
  Defined.

  Definition adjoint_equivalence_linv
             (a b : B)
             (f : adjoint_equivalence a b)
    : comp_adjoint_equivalence b a b (inv_adjoint_equivalence a b f) f =
      internal_adjoint_equivalence_identity b.
  Proof.
    apply (J_2_0 HB (λ a b f,
                     comp_adjoint_equivalence b a b (inv_adjoint_equivalence a b f) f =
                     internal_adjoint_equivalence_identity b)).
    intro c.
    rewrite adjoint_equivalence_rid.
    unfold inv_adjoint_equivalence.
    rewrite J_2_0_comp.
    exact (idpath _).
  Defined.

  Definition adjoint_equivalence_rinv
             (a b : B)
             (f : adjoint_equivalence a b)
    : comp_adjoint_equivalence a b a f (inv_adjoint_equivalence a b f) =
      internal_adjoint_equivalence_identity a.
  Proof.
    apply (J_2_0 HB (λ a b f,
                     comp_adjoint_equivalence a b a f (inv_adjoint_equivalence a b f) =
                     internal_adjoint_equivalence_identity a)).
    intro c.
    rewrite adjoint_equivalence_lid.
    unfold inv_adjoint_equivalence.
    rewrite J_2_0_comp.
    exact (idpath _).
  Defined.

  Definition adjoint_equivalence_precategory_data : precategory_data.
  Proof.
    use make_precategory_data.
    - use make_precategory_ob_mor.
      + exact B.
      + exact adjoint_equivalence.
    - exact internal_adjoint_equivalence_identity.
    - exact comp_adjoint_equivalence.
  Defined.

  Definition adjoint_equivalence_is_precategory
    : is_precategory adjoint_equivalence_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - exact adjoint_equivalence_lid.
    - exact adjoint_equivalence_rid.
    - exact adjoint_equivalence_assoc.
  Qed.

  Definition adjoint_equivalence_precategory : precategory.
  Proof.
    use make_precategory.
    - exact adjoint_equivalence_precategory_data.
    - exact adjoint_equivalence_is_precategory.
  Defined.

  Definition adjoint_equivalence_is_pregroupoid
    : is_pregroupoid adjoint_equivalence_precategory.
  Proof.
    intros a b f.
    use is_iso_qinv.
    - exact (inv_adjoint_equivalence a b f).
    - split.
      + exact (adjoint_equivalence_rinv a b f).
      + exact (adjoint_equivalence_linv a b f).
  Qed.

  Definition adjoint_equivalence_pregroupoid : pregroupoid.
  Proof.
    use make_pregroupoid.
    - exact adjoint_equivalence_precategory.
    - exact adjoint_equivalence_is_pregroupoid.
  Defined.

End AdjointEquivPregroupoid.
