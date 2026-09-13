(********************************************************************************

 Reflexive Graphs of (Small) Categories

 We construct categories as a tower of reflexive graphs, obtaining that
 [catiso]s correspond to identifications of [category]s in
 [weq_category_paths_to_catiso].  Compare this file to [CategoryEquality.v].

 Contents:
 1. Reflexive graph of [precategory_ob_mor]
 2. Reflexive graph of [precategory_data]
 3. Reflexive graphs of [precategory] and [category]

 Author: B. Szilvasy
 September 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.IdentitySystems.RXGraph.
Require Import UniMath.IdentitySystems.Examples.
Require Import UniMath.IdentitySystems.Lenses.
Require Import UniMath.IdentitySystems.RXGraphOfRXGraphs.

Local Open Scope cat.
Local Open Scope rxgraph.

(** ** Reflexive graph of [precategory_ob_mor] *)

Definition precategory_mor_on_rxgraph : contra_lens UU_rxgraph.
Proof.
  use make_contra_lens.
  - intro ob; exact (ob ~> ob ~> UU_rxgraph).
  - cbn; intros C D w mor a b.
    exact (mor (w a) (w b)).
  - intros C mor; exact (refl mor).
Defined.

Definition precategory_ob_mor_rxgraph : rxgraph
  := ∑~ disp- precategory_mor_on_rxgraph.

Lemma is_univalent_precategory_ob_mor_rxgraph : is_univalent precategory_ob_mor_rxgraph.
Proof.
  apply is_univalent_total_rxgraph.
  - exact UU_univalent_rxgraph.
  - apply is_univalent_contra_lens_disp_rxgraph; intro.
    exact (∏! _ _, UU_univalent_rxgraph).
Qed.

Definition precategory_ob_mor_iso (C D : precategory_ob_mor) : UU
  := C ≈{precategory_ob_mor_rxgraph} D.
Coercion precategory_ob_mor_iso_to_functor_data {C D : precategory_ob_mor}
  (F : precategory_ob_mor_iso C D)
  : functor_data C D.
Proof.
  cbn in F.
  exists (pr1 F).
  exact (pr2 F).
Defined.

(** ** Reflexive graph of [precategory_data] *)

Definition precategory_id_comp_rxgraph : unbiased_lens precategory_ob_mor_rxgraph.
Proof.
  use make_unbiased_lens.
  - intros C D F.
    change precategory_ob_mor in C, D.
    change (precategory_ob_mor_iso C D) in F.
    exact ((∏~ (a : C), Δ D⟦F a, F a⟧) ×~
             (∏~ (a b c : C), C⟦a, b⟧ ~> C⟦b, c⟧ ~> Δ D⟦F a, F c⟧)).
  - cbn; intros C D F [id comp].
    change precategory_ob_mor in C, D.
    change (precategory_ob_mor_iso C D) in F.
    split.
    + exact (λ x, #F (id x)).
    + exact (λ _ _ _ f g, #F (comp _ _ _ f g)).
  - cbn; intros C D F [id comp].
    change precategory_ob_mor in C, D.
    change (precategory_ob_mor_iso C D) in F.
    split.
    + exact (λ x, id (F x)).
    + exact (λ _ _ _ f g, comp _ _ _ (#F f) (#F g)).
  - intros C idmor; exact (refl idmor).
  - intros C idmor; exact (refl idmor).
Defined.

Definition precategory_data_rxgraph₀ : rxgraph
  := ∑~ disp± precategory_id_comp_rxgraph.

Lemma is_univalent_precategory_data_rxgraph₀ : is_univalent precategory_data_rxgraph₀.
Proof.
  apply is_univalent_total_rxgraph.
  - exact is_univalent_precategory_ob_mor_rxgraph.
  - apply is_univalent_unbiased_lens_disp_rxgraph; intros x y e.
    apply is_univalent_dirprod_rxgraph.
    + apply is_univalent_product_rxgraph; intro.
      apply rxgraph_univalence.
    + do 5 (apply is_univalent_product_rxgraph; intro).
      apply rxgraph_univalence.
Qed.

Lemma weq_precategory_data_rxgraph₀_edge_catiso (C D : precategory_data)
  : C ≈{precategory_data_rxgraph₀} D ≃ catiso C D.
Proof.
  use weq_iso.
  - intros [F HF].
    change (precategory_ob_mor_iso C D) in F.
    change (is_functor F) in HF.
    exists (make_functor F HF).
    split.
    + intros a b; apply weqproperty.
    + apply weqproperty.
  - intros [F [HFF Hobs]].
    simple refine ((_,, _),, _,, _); cbn.
    + exact (make_weq F Hobs).
    + exact (weq_from_fully_faithful HFF).
    + exact (functor_id F).
    + intros a b c f g.
      exact (functor_comp F f g).
  - easy.
  - easy.
Defined.

Definition precategory_data_rxgraph : rxgraph.
Proof.
  use make_rxgraph.
  - exact precategory_data.
  - exact catiso.
  - exact identity_catiso.
Defined.

Lemma is_univalent_precategory_data_rxgraph : is_univalent precategory_data_rxgraph.
Proof.
  apply is_univalent_from_weq.
  intros a b.
  apply (weqcomp (weq_id_to_edge is_univalent_precategory_data_rxgraph₀ a b)).
  apply weq_precategory_data_rxgraph₀_edge_catiso.
Qed.

(** ** Reflexive graphs of [precategory] and [category] *)

(* This is not univalent *)
Definition precategory_rxgraph : rxgraph.
Proof.
  use make_rxgraph.
  - exact precategory.
  - exact catiso.
  - exact identity_catiso.
Defined.

Definition category_rxgraph : rxgraph.
Proof.
  use make_rxgraph.
  - exact category.
  - exact catiso.
  - exact identity_catiso.
Defined.

Definition is_univalent_category_rxgraph : is_univalent category_rxgraph.
Proof.
  use is_univalent_rxgraph_iso_f.
  - exact (sub_rxgraph precategory_data_rxgraph (λ (C : precategory_data),
               has_homsets C × is_precategory C)).
  - use make_rxgraph_iso.
    + use weq_iso.
      * intros [C [H₁ H₂]]; exact ((C,, H₂),, H₁).
      * intros [[C H₂] H₁]; exact (C,, H₁,, H₂).
      * easy.
      * easy.
    + intros C D; cbn.
      exact (idweq _).
    + easy.
  - apply is_univalent_sub_rxgraph.
    + apply is_univalent_precategory_data_rxgraph.
    + intro C.
      apply isaprop_assume_it_is.
      intros [hs H].
      apply isapropdirprod.
      * apply isaprop_has_homsets.
      * apply isaprop_is_precategory, hs.
Qed.

Corollary weq_category_paths_to_catiso (C D : category)
  : C = D ≃ catiso C D.
Proof.
  exact (weq_id_to_edge is_univalent_category_rxgraph C D).
Defined.
