(** **********************************************************

Ralph Matthes

2022
*)

(** **********************************************************

Contents :

- defines a notion of binary products for displayed categories that gives binary products on its total category
- same programme for terminal objects

 ************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp.

Section FixDispCat.

  Context {C : category} (D : disp_cat C).

  Definition is_dispBinProduct_naive (c d p : C) (p1 : p --> c) (p2 : p --> d) (cc : D c)
    (dd : D d) (pp : D p) (pp1 : pp -->[p1] cc) (pp2 : pp -->[p2] dd) : UU :=
    ∏ (a : C) (f : a --> c) (g : a --> d) (aa : D a) (ff : aa -->[f] cc) (gg : aa -->[g] dd),
      ∃! (fg : a --> p) (fgfg : aa -->[fg] pp),
      ∑ fgok : ((fg · p1 = f) × (fg · p2 = g)),
        (fgfg ;; pp1 = transportb _ (pr1 fgok) ff) × (fgfg ;; pp2 = transportb _ (pr2 fgok) gg).

  Definition is_dispBinProduct (c d : C) (P : BinProduct C c d)
    (cc : D c) (dd : D d) (pp : D (BinProductObject _ P))
    (pp1 : pp -->[BinProductPr1 _ P] cc) (pp2 : pp -->[BinProductPr2 _ P] dd) : UU :=
    ∏ (a : C) (f : a --> c) (g : a --> d) (aa : D a) (ff : aa -->[f] cc) (gg : aa -->[g] dd),
      ∃! (fgfg : aa -->[BinProductArrow _ P f g] pp),
      (fgfg ;; pp1 = transportb _ (BinProductPr1Commutes _ _ _ P _ f g) ff) ×
      (fgfg ;; pp2 = transportb _ (BinProductPr2Commutes _ _ _ P _ f g) gg).

  Definition dispBinProduct (c d : C) (P : BinProduct C c d) (cc : D c) (dd : D d) : UU :=
    ∑ pppp1pp2 : (∑ pp : D (BinProductObject _ P),
                     (pp -->[BinProductPr1 _ P] cc) × (pp -->[BinProductPr2 _ P] dd)),
        is_dispBinProduct c d P cc dd (pr1 pppp1pp2) (pr1 (pr2 pppp1pp2)) (pr2 (pr2 pppp1pp2)).

  Definition make_dispBinProduct_locally_prop (c d : C) (P : BinProduct C c d) (cc : D c) (dd : D d)
    (LP : locally_propositional D)
    (dBP_data : ∑ pp : D (BinProductObject _ P),
          (pp -->[BinProductPr1 _ P] cc) × (pp -->[BinProductPr2 _ P] dd))
    (mediating : ∏ (a : C) (f : a --> c) (g : a --> d) (aa : D a)
                   (ff : aa -->[f] cc) (gg : aa -->[g] dd),
        aa -->[ BinProductArrow C P f g] pr1 dBP_data)
    : dispBinProduct c d P cc dd.
  Proof.
    exists dBP_data.
    intro; intros.
    use tpair.
    - exists (mediating a f g aa ff gg).
      abstract (split; apply LP).
    - abstract (intro t; apply subtypePath;
                [intro; apply isapropdirprod; apply homsets_disp | apply LP]).
  Defined.

  Definition dispBinProductObject {c d : C} (P : BinProduct C c d) {cc : D c} {dd : D d}
    (dP : dispBinProduct c d P cc dd) : D (BinProductObject _ P) := pr1 (pr1 dP).

  Definition dispBinProductPr1 {c d : C} (P : BinProduct C c d) {cc : D c} {dd : D d}
    (dP : dispBinProduct c d P cc dd) : dispBinProductObject P dP -->[BinProductPr1 _ P] cc :=
    pr1 (pr2 (pr1 dP)).

  Definition dispBinProductPr2 {c d : C} (P : BinProduct C c d) {cc : D c} {dd : D d}
    (dP : dispBinProduct c d P cc dd) : dispBinProductObject P dP -->[BinProductPr2 _ P] dd :=
    pr2 (pr2 (pr1 dP)).

  Definition is_dispBinProduct_dispBinProduct {c d : C} (P : BinProduct C c d) {cc : D c} {dd : D d}
    (dP : dispBinProduct c d P cc dd) :
    is_dispBinProduct c d P cc dd (dispBinProductObject P dP) (dispBinProductPr1 P dP) (dispBinProductPr2 P dP).
  Proof.
    exact (pr2 dP).
  Defined.

  Definition dispBinProductArrow {c d : C} (P : BinProduct C c d) {cc : D c} {dd : D d}
    (dP : dispBinProduct c d P cc dd) {a : C} {f : a --> c} {g : a --> d} {aa : D a} (ff : aa -->[f] cc) (gg : aa -->[g] dd) :
       aa -->[BinProductArrow _ P f g] dispBinProductObject P dP.
  Proof.
    exact (pr1 (pr1 (is_dispBinProduct_dispBinProduct P dP _ _ _ _ ff gg))).
  Defined.

  Lemma dispBinProductPr1Commutes {c d : C} (P : BinProduct C c d) (cc : D c) (dd : D d) (dP : dispBinProduct c d P cc dd):
    ∏ (a : C) (f : a --> c) (g : a --> d) (aa : D a) (ff : aa -->[f] cc) (gg : aa -->[g] dd),
      dispBinProductArrow P dP ff gg ;; dispBinProductPr1 P dP = transportb _ (BinProductPr1Commutes _ _ _ P _ f g) ff.
  Proof.
    intros a f g aa ff gg.
    exact (pr1 (pr2 (pr1 (is_dispBinProduct_dispBinProduct P dP _ _ _ _ ff gg)))).
  Qed.

  Lemma dispBinProductPr2Commutes {c d : C} (P : BinProduct C c d) (cc : D c) (dd : D d) (dP : dispBinProduct c d P cc dd):
    ∏ (a : C) (f : a --> c) (g : a --> d) (aa : D a) (ff : aa -->[f] cc) (gg : aa -->[g] dd),
      dispBinProductArrow P dP ff gg ;; dispBinProductPr2 P dP = transportb _ (BinProductPr2Commutes _ _ _ P _ f g) gg.
  Proof.
    intros a f g aa ff gg.
    exact (pr2 (pr2 (pr1 (is_dispBinProduct_dispBinProduct P dP _ _ _ _ ff gg)))).
  Qed.

  Lemma dispBinProductArrowUnique  {c d : C} (P : BinProduct C c d) (cc : D c) (dd : D d)
    (dP : dispBinProduct c d P cc dd) {x : C} (xx : D x) (f : x --> c) (g : x --> d) (ff : xx -->[f] cc) (gg : xx -->[g] dd)
    (kk : xx -->[BinProductArrow _ P f g] dispBinProductObject P dP) :
    kk ;; dispBinProductPr1 P dP = transportb _ (BinProductPr1Commutes _ _ _ P _ f g) ff ->
    kk ;; dispBinProductPr2 P dP = transportb _ (BinProductPr2Commutes _ _ _ P _ f g) gg ->
    kk = dispBinProductArrow P dP ff gg.
  Proof.
    intros H1 H2.
    apply path_to_ctr; split; assumption.
  Qed.


  (* transparent proofs for the standard binary products -- upstream?
  Definition BinProductArrowUnique' (c d : C) (P : BinProduct C c d) (x : C)
    (f : x --> c) (g : x --> d) (k : x --> BinProductObject C P) :
    k · BinProductPr1 C P = f -> k · BinProductPr2 C P = g ->
    k = BinProductArrow C P f g.
  Proof.
    intros; apply path_to_ctr; split; assumption.
  Defined.

  Definition BinProductArrowEta' (c d : C) (P : BinProduct C c d) (x : C)
    (f : x --> BinProductObject C P) :
    f = BinProductArrow C P (f · BinProductPr1 C P) (f · BinProductPr2 C P).
  Proof.
    apply BinProductArrowUnique'; apply idpath.
  Defined.
*)


  Lemma dispBinProductArrowEta {c d : C} (P : BinProduct C c d) (cc : D c) (dd : D d)
    (dP : dispBinProduct c d P cc dd) {x : C} (xx : D x) {fg : x --> BinProductObject C P }
    (fgfg : xx -->[ fg] dispBinProductObject P dP) :
    fgfg =
      transportb (mor_disp xx (dispBinProductObject P dP)) (BinProductArrowEta C c d P x fg)
        (dispBinProductArrow P dP (fgfg ;; dispBinProductPr1 P dP) (fgfg ;; dispBinProductPr2 P dP)).
  Proof.
    apply transportf_transpose_right.
    apply dispBinProductArrowUnique.
    - etrans.
      { apply mor_disp_transportf_postwhisker. }
      unfold transportb.
      apply (maponpaths (fun z => transportf (mor_disp xx cc) z (fgfg ;; dispBinProductPr1 P dP))).
      apply C.
    - etrans.
      { apply mor_disp_transportf_postwhisker. }
      unfold transportb.
      apply (maponpaths (fun z => transportf (mor_disp xx dd) z (fgfg ;; dispBinProductPr2 P dP))).
      apply C.
  Qed.

  Lemma dispBinProduct_endo_is_identity {a b : C} (aa : D a) (bb : D b)
    (P : BinProduct _ a b) (dP : dispBinProduct a b P aa bb)
    {k : BinProductObject _ P --> BinProductObject _ P} (kk: dispBinProductObject P dP -->[k] dispBinProductObject P dP)
    (H1 : k · BinProductPr1 _ P = BinProductPr1 _ P) (dH1 : kk ;; dispBinProductPr1 P dP = transportb _ H1 (dispBinProductPr1 P dP))
    (H2 : k · BinProductPr2 _ P = BinProductPr2 _ P) (dH2 : kk ;; dispBinProductPr2 P dP = transportb _ H2 (dispBinProductPr2 P dP))
    : transportf _ (BinProduct_endo_is_identity C a b P k H1 H2) (id_disp (dispBinProductObject P dP)) = kk.
  Proof.
    apply pathsinv0.
    etrans.
    { apply dispBinProductArrowEta. }
    apply pathsinv0, transportf_comp_lemma.
    apply dispBinProductArrowUnique.
    - etrans.
      { apply mor_disp_transportf_postwhisker. }
      rewrite id_left_disp.
      rewrite transport_f_b.
      apply transportf_comp_lemma.
      etrans.
      2: { apply pathsinv0; exact dH1. }
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset;
        try apply homset_property; apply idpath.
    - etrans.
      { apply mor_disp_transportf_postwhisker. }
      rewrite id_left_disp.
      rewrite transport_f_b.
      apply transportf_comp_lemma.
      etrans.
      2: { apply pathsinv0; exact dH2. }
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset;
        try apply homset_property; apply idpath.
  Qed.

  Definition dispBinProductOfArrows {c d : C} {Pcd : BinProduct C c d}
    {cc : D c} {dd : D d}
    (dPcd : dispBinProduct c d Pcd cc dd)
    {a b : C} {Pab : BinProduct C a b}
    {aa : D a} {bb : D b}
    (dPab : dispBinProduct a b Pab aa bb)
    {f : a --> c} {g : b --> d}
    (ff : aa -->[f] cc) (gg : bb -->[g] dd)
    : dispBinProductObject Pab dPab -->[BinProductOfArrows C Pcd Pab f g] dispBinProductObject Pcd dPcd :=
    dispBinProductArrow Pcd dPcd (dispBinProductPr1 Pab dPab ;; ff) (dispBinProductPr2 Pab dPab ;; gg).

  Lemma dispBinProductOfArrowsPr1 {c d : C} {Pcd : BinProduct C c d}
    {cc : D c} {dd : D d}
    (dPcd : dispBinProduct c d Pcd cc dd)
    {a b : C} {Pab : BinProduct C a b}
    {aa : D a} {bb : D b}
    (dPab : dispBinProduct a b Pab aa bb)
    {f : a --> c} {g : b --> d}
    (ff : aa -->[f] cc) (gg : bb -->[g] dd) :
    dispBinProductOfArrows dPcd dPab ff gg ;; dispBinProductPr1 Pcd dPcd =
      transportb _ (BinProductOfArrowsPr1 _ Pcd Pab f g) (dispBinProductPr1 Pab dPab ;; ff).
  Proof.
    unfold dispBinProductOfArrows.
    etrans.
    { apply dispBinProductPr1Commutes. }
    apply (maponpaths (fun z => transportb (mor_disp (dispBinProductObject Pab dPab) cc) z (dispBinProductPr1 Pab dPab ;; ff))).
    apply C.
  Qed.

  Lemma dispBinProductOfArrowsPr2 {c d : C} {Pcd : BinProduct C c d}
    {cc : D c} {dd : D d}
    (dPcd : dispBinProduct c d Pcd cc dd)
    {a b : C} {Pab : BinProduct C a b}
    {aa : D a} {bb : D b}
    (dPab : dispBinProduct a b Pab aa bb)
    {f : a --> c} {g : b --> d}
    (ff : aa -->[f] cc) (gg : bb -->[g] dd) :
    dispBinProductOfArrows dPcd dPab ff gg ;; dispBinProductPr2 Pcd dPcd =
      transportb _ (BinProductOfArrowsPr2 _ Pcd Pab f g) (dispBinProductPr2 Pab dPab ;; gg).
  Proof.
    unfold dispBinProductOfArrows.
    etrans.
    { apply dispBinProductPr2Commutes. }
    apply (maponpaths (fun z => transportb (mor_disp (dispBinProductObject Pab dPab) dd) z (dispBinProductPr2 Pab dPab ;; gg))).
    apply C.
  Qed.

  Lemma dispPostcompWithBinProductArrow {c d : C} {Pcd : BinProduct C c d} {cc : D c} {dd : D d} (dPcd : dispBinProduct c d Pcd cc dd)
    {a b : C} {Pab : BinProduct C a b} {aa : D a} {bb : D b} (dPab : dispBinProduct a b Pab aa bb)
    {f : a --> c} {g : b --> d} (ff : aa -->[f] cc) (gg : bb -->[g] dd)
    {x : C} {xx : D x} {k : x --> a} {h : x --> b} (kk: xx -->[k] aa) (hh: xx -->[h] bb) :
    dispBinProductArrow Pab dPab kk hh ;; dispBinProductOfArrows dPcd dPab ff gg =
      transportb _ (postcompWithBinProductArrow C Pcd Pab f g k h) (dispBinProductArrow Pcd dPcd (kk ;; ff) (hh ;; gg)).
  Proof.
    apply transportb_transpose_right.
    apply dispBinProductArrowUnique.
    - etrans.
      { apply mor_disp_transportf_postwhisker. }
      rewrite assoc_disp_var.
      rewrite dispBinProductOfArrowsPr1.
      rewrite transport_f_f.
      apply pathsinv0, transportf_comp_lemma.
      etrans.
      2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
      rewrite assoc_disp.
      rewrite dispBinProductPr1Commutes.
      rewrite transport_f_b.
      apply transportf_comp_lemma.
      unfold transportb.
      etrans.
      2: { apply pathsinv0, mor_disp_transportf_postwhisker. }
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset;
        try apply homset_property; apply idpath.
    - etrans.
      { apply mor_disp_transportf_postwhisker. }
      rewrite assoc_disp_var.
      rewrite dispBinProductOfArrowsPr2.
      rewrite transport_f_f.
      apply pathsinv0, transportf_comp_lemma.
      etrans.
      2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
      rewrite assoc_disp.
      rewrite dispBinProductPr2Commutes.
      rewrite transport_f_b.
      apply transportf_comp_lemma.
      unfold transportb.
      etrans.
      2: { apply pathsinv0, mor_disp_transportf_postwhisker. }
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset;
        try apply homset_property; apply idpath.
  Qed.

  Lemma dispPrecompWithBinProductArrow {c d : C} {Pcd : BinProduct C c d}
    {cc : D c} {dd : D d} (dPcd : dispBinProduct c d Pcd cc dd)
    {a : C} {aa : D a}
    {f : a --> c} {g : a --> d} (ff: aa -->[f] cc) (gg: aa -->[g] dd)
    {x : C} {xx : D x} {k : x --> a} (kk: xx -->[k] aa) :
    kk ;; dispBinProductArrow Pcd dPcd ff gg  =
      transportb _ (precompWithBinProductArrow C Pcd f g k) (dispBinProductArrow Pcd dPcd (kk ;; ff) (kk ;; gg)).
  Proof.
    apply transportb_transpose_right.
    apply dispBinProductArrowUnique.
    - rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      rewrite dispBinProductPr1Commutes.
      rewrite transport_f_f.
      etrans.
      { apply maponpaths.
        apply mor_disp_transportf_prewhisker. }
      rewrite transport_f_f.
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset;
        try apply homset_property; apply idpath.
    - rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      rewrite dispBinProductPr2Commutes.
      rewrite transport_f_f.
      etrans.
      { apply maponpaths.
        apply mor_disp_transportf_prewhisker. }
      rewrite transport_f_f.
      apply transportf_comp_lemma.
      apply transportf_comp_lemma_hset;
        try apply homset_property; apply idpath.
  Qed.


  Definition dispBinProducts (Ps : BinProducts C)  : UU := ∏ (c d : C) (cc : D c) (dd : D d),
      dispBinProduct c d (Ps c d) cc dd.


  Lemma dispBinProductOfArrows_comp { Ps : BinProducts C } (dPs : dispBinProducts Ps) {a b c d x y : C}
    {aa : D a} {bb : D b} {cc : D c} {dd: D d} {xx : D x} {yy : D y}
    {f : a --> c} {f' : b --> d} {g : c --> x} {g' : d --> y}
    (ff : aa -->[f] cc) (ff' : bb -->[f'] dd) (gg : cc -->[g] xx) (gg' : dd -->[g'] yy) :
    dispBinProductOfArrows (dPs _ _ _ _) (dPs _ _ _ _) ff ff' ;; dispBinProductOfArrows (dPs _ _ _ _) (dPs _ _ _ _) gg gg' =
      transportb _ (BinProductOfArrows_comp _ _ _ _ _ _ _ _ f f' g g') (dispBinProductOfArrows (dPs _ _ _ _) (dPs _ _ _ _) (ff;;gg) (ff';;gg')).
  Proof.
    apply transportb_transpose_right.
    apply dispBinProductArrowUnique.
    - etrans.
      { apply mor_disp_transportf_postwhisker. }
      rewrite assoc_disp_var.
      rewrite dispBinProductOfArrowsPr1.
      rewrite transport_f_f.
      apply pathsinv0, transportf_comp_lemma.
      etrans.
      2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
      do 2 rewrite assoc_disp.
      rewrite dispBinProductOfArrowsPr1.
      do 2 rewrite transport_f_b.
      apply pathsinv0, transportf_comp_lemma.
      etrans.
      { apply maponpaths.
        apply mor_disp_transportf_postwhisker. }
      rewrite transport_f_f.
      apply transportf_comp_lemma_hset;
        try apply homset_property; apply idpath.
    - etrans.
      { apply mor_disp_transportf_postwhisker. }
      rewrite assoc_disp_var.
      rewrite dispBinProductOfArrowsPr2.
      rewrite transport_f_f.
      apply pathsinv0, transportf_comp_lemma.
      etrans.
      2: { apply pathsinv0, mor_disp_transportf_prewhisker. }
      do 2 rewrite assoc_disp.
      rewrite dispBinProductOfArrowsPr2.
      do 2 rewrite transport_f_b.
      apply pathsinv0, transportf_comp_lemma.
      etrans.
      { apply maponpaths.
        apply mor_disp_transportf_postwhisker. }
      rewrite transport_f_f.
      apply transportf_comp_lemma_hset;
        try apply homset_property; apply idpath.
  Qed.


  Definition total_category_Binproducts_data (Ps : BinProducts C) (dPs : dispBinProducts Ps) (ccc ddd : total_category D) :
    ∑ p : total_category D, total_category D ⟦ p, ccc ⟧ × total_category D ⟦ p, ddd ⟧.
  Proof.
    induction ccc as [c cc].
    induction ddd as [d dd].
    - exists (BinProductObject _ (Ps c d) ,, dispBinProductObject (Ps c d) (dPs c d cc dd)).
      split.
      + use tpair.
        * apply BinProductPr1.
        * apply dispBinProductPr1.
      + use tpair.
        * apply BinProductPr2.
        * apply dispBinProductPr2.
  Defined.

  Definition total_category_Binproducts_mediating_morphism (Ps : BinProducts C) (dPs : dispBinProducts Ps)
    {c d x : C} {cc : D c} {dd: D d} {xx : D x} {f : x --> c} (ff: xx -->[f] cc) {g : x --> d} (gg: xx -->[g] dd) :
     ∑ h : x --> BinProductObject C (Ps c d), xx -->[h] dispBinProductObject (Ps c d) (dPs c d cc dd).
  Proof.
    use tpair.
    - apply BinProductArrow; assumption.
    - apply dispBinProductArrow; assumption.
  Defined.

  Local Lemma total_category_Binproducts_mediating_morphism_ok (Ps : BinProducts C) (dPs : dispBinProducts Ps)
    {c d x : C} {cc : D c} {dd: D d} {xx : D x} {f : x --> c} (ff: xx -->[f] cc) {g : x --> d} (gg: xx -->[g] dd) :
    BinProductArrow C (Ps c d) f g · BinProductPr1 C (Ps c d),, dispBinProductArrow (Ps c d) (dPs c d cc dd) ff gg ;; dispBinProductPr1 (Ps c d) (dPs c d cc dd) = f,, ff ×
    BinProductArrow C (Ps c d) f g · BinProductPr2 C (Ps c d),, dispBinProductArrow (Ps c d) (dPs c d cc dd) ff gg ;; dispBinProductPr2 (Ps c d) (dPs c d cc dd) = g,, gg.
  Proof.
    split.
    - use total2_paths_f; cbn.
      + apply BinProductPr1Commutes.
      + apply transportf_pathsinv0.
        apply pathsinv0.
        apply dispBinProductPr1Commutes.
    - use total2_paths_f; cbn.
      + apply BinProductPr2Commutes.
      + apply transportf_pathsinv0.
        apply pathsinv0.
        apply dispBinProductPr2Commutes.
  Qed.

  Local Lemma total_category_Binproducts_mediating_morphism_unique (Ps : BinProducts C) (dPs : dispBinProducts Ps)
    {c d x : C} {cc : D c} {dd: D d} {xx : D x} {f : x --> c} (ff: xx -->[f] cc) {g : x --> d} (gg: xx -->[g] dd)
    {fg : x --> BinProductObject C (Ps c d)} (fgfg : xx -->[fg] dispBinProductObject (Ps c d) (dPs c d cc dd)) :
    fg · BinProductPr1 C (Ps c d),, fgfg ;; dispBinProductPr1 (Ps c d) (dPs c d cc dd) = f,, ff ×
    fg · BinProductPr2 C (Ps c d),, fgfg ;; dispBinProductPr2 (Ps c d) (dPs c d cc dd) = g,, gg →
    fg,, fgfg = total_category_Binproducts_mediating_morphism Ps dPs ff gg.
  Proof.
    intro H.
    induction H as [H1 H2].
    cbn in *.
    induction (total2_paths_equiv _ _ _ H1) as [H1l H1r].
    induction (total2_paths_equiv _ _ _ H2) as [H2l H2r].
    clear H1 H2.
    use total2_paths_f; cbn.
    - use path_to_ctr; split; assumption.
    - cbn in *.
      rewrite <- H1r, <- H2r.
      clear H1r H2r ff gg.
      induction H1l.
      induction H2l.
      (* apply dispBinProductArrowEta. would work with [BinProductArrowEta'] *)
      (* we proceed as follows: *)
      cbn.
      etrans.
      2: { assert (aux := dispBinProductArrowEta (Ps c d) cc dd (dPs _ _ cc dd) xx fgfg).
           apply transportf_transpose_left in aux.
           exact aux. }
      apply (maponpaths (fun z => transportf (mor_disp xx (dispBinProductObject (Ps c d) (dPs c d cc dd))) z fgfg)).
      apply C.
  Qed.

  Definition total_category_Binproducts (Ps : BinProducts C) (dPs : dispBinProducts Ps) : BinProducts (total_category D).
  Proof.
    intros ccc ddd.
    use tpair.
    - apply (total_category_Binproducts_data Ps dPs).
    - induction ccc as [c cc].
      induction ddd as [d dd].
      intros aaa fff ggg.
      destruct aaa as [a aa]; destruct fff as [f ff]; destruct ggg as [g gg].
      cbn.
      use unique_exists.
      + exact (total_category_Binproducts_mediating_morphism Ps dPs ff gg).
      + exact (total_category_Binproducts_mediating_morphism_ok Ps dPs ff gg).
      + intro y.
        apply isapropdirprod.
        * apply (homset_property (total_category D) (a ,, aa) (c ,, cc)).
        * apply (homset_property (total_category D) (a ,, aa) (d ,, dd)).
      + intro fgfgfg.
        induction fgfgfg as [fg fgfg].
        exact (total_category_Binproducts_mediating_morphism_unique Ps dPs ff gg fgfg).
  Defined.


(** ** analogously for terminal objects *)

  Definition is_dispTerminal (P : Terminal C) (pp : D (TerminalObject P)) : UU :=
    ∏ (a : C) (aa : D a), iscontr (aa -->[TerminalArrow P a] pp).

  Definition dispTerminal (P : Terminal C) : UU :=
    ∑ pp :  D (TerminalObject P), is_dispTerminal P pp.

  Definition make_dispTerminal_locally_prop (P : Terminal C)
    (LP : locally_propositional D) (dTO_data : D (TerminalObject P))
    (mediating : ∏ (a : C) (aa : D a), aa -->[TerminalArrow P a] dTO_data)
    : dispTerminal P.
  Proof.
    exists dTO_data.
    intro; intros.
    use tpair.
    - exact (mediating a aa).
    - intro; apply LP.
  Defined.

  Definition dispTerminalObject {P : Terminal C} (dP : dispTerminal P) : D (TerminalObject P) := pr1 dP.

  Definition is_dispTerminal_dispTerminal (P : Terminal C) (dP : dispTerminal P) :
    is_dispTerminal P (dispTerminalObject dP) := pr2 dP.

  Definition dispTerminalArrow (P : Terminal C) (dP : dispTerminal P) {a : C} (aa : D a) :
    aa -->[TerminalArrow P a] dispTerminalObject dP := pr1 (is_dispTerminal_dispTerminal P dP a aa).

  Lemma dispTerminalArrowUnique  (P : Terminal C)
    (dP : dispTerminal P) {x : C} (xx : D x)
    (kk : xx -->[TerminalArrow P x] dispTerminalObject dP) :
    kk = dispTerminalArrow P dP xx.
  Proof.
    apply (pr2 (pr2 dP x xx)).
  Qed.

  Lemma dispTerminalArrowUnique'  (P : Terminal C)
    (dP : dispTerminal P) {x : C} (xx : D x) (f: x --> TerminalObject P)
    (kk : xx -->[f] dispTerminalObject dP) :
    kk = transportb _ (TerminalArrowUnique P x f) (dispTerminalArrow P dP xx).
  Proof.
    apply transportf_transpose_right.
    apply dispTerminalArrowUnique.
  Qed.

  Lemma dispTerminalArrowEq {T : Terminal C} {TT: dispTerminal T} {a : C} {aa : D a} {f g : a --> T}
    (ff: aa -->[f] dispTerminalObject TT) (gg: aa -->[g] dispTerminalObject TT) :
    ff = transportb _ (TerminalArrowEq f g) gg.
  Proof.
    induction (TerminalArrowEq f g).
    cbn.
    rewrite (dispTerminalArrowUnique' _ _ _ _ ff).
    rewrite (dispTerminalArrowUnique' _ _ _ _ gg).
    apply idpath.
  Qed.


  Definition total_category_Terminal (P : Terminal C) (dP : dispTerminal P) : Terminal (total_category D).
  Proof.
    use tpair.
    - exists (TerminalObject P).
      exact (dispTerminalObject dP).
    - intros aaa.
      destruct aaa as [a aa].
      cbn.
      use tpair.
      + exact (TerminalArrow P a,, dispTerminalArrow P dP aa).
      + intro fff.
        induction fff as [f ff].
        use total2_paths_f; cbn.
        * apply TerminalArrowUnique.
        * apply dispTerminalArrowUnique.
  Defined.

  (**
   Displayed equalizers
   *)
  Definition is_disp_Equalizer
             {x y : C}
             {f g : x --> y}
             (e : Equalizer f g)
             {xx : D x}
             {yy : D y}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             (ee : D e)
             (ar_e : ee -->[ EqualizerArrow e ] xx)
             (pp : transportf
                     (λ z, _ -->[ z ] _)
                     (EqualizerEqAr e)
                     (ar_e ;; ff)
                   =
                   ar_e ;; gg)
    : UU
    := ∏ (w : C)
         (ww : D w)
         (h : w --> x)
         (hh : ww -->[ h ] xx)
         (q : h · f = h · g)
         (qq : transportf
                 (λ z, _ -->[ z ] _)
                 q
                 (hh ;; ff)
               =
               hh ;; gg),
       ∃! (ii : ww -->[ EqualizerIn e w h q ] ee),
       transportf
         (λ z, _ -->[ z ] _)
         (EqualizerCommutes e w h q)
         (ii ;; ar_e)
       =
       hh.

  Definition disp_Equalizer
             {x y : C}
             {f g : x --> y}
             {xx : D x}
             {yy : D y}
             (ff : xx -->[ f ] yy)
             (gg : xx -->[ g ] yy)
             (e : Equalizer f g)
    : UU
    := ∑ (ee : D e)
         (ar_e : ee -->[ EqualizerArrow e ] xx)
         (pp : transportf
                 (λ z, _ -->[ z ] _)
                 (EqualizerEqAr e)
                 (ar_e ;; ff)
               =
               ar_e ;; gg),
       is_disp_Equalizer e ee ar_e pp.

  Definition disp_Equalizers
             (EC : Equalizers C)
    : UU
    := ∏ (x y : C)
         (f g : x --> y)
         (xx : D x)
         (yy : D y)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy),
       disp_Equalizer ff gg (EC x y f g).

  Section TotalEqualizer.
    Context {x y : C}
            {f g : x --> y}
            {xx : D x}
            {yy : D y}
            (ff : xx -->[ f ] yy)
            (gg : xx -->[ g ] yy)
            (e : Equalizer f g)
            (ee : disp_Equalizer ff gg e).

    Let t_x : total_category D
      := x ,, xx.

    Let t_y : total_category D
      := y ,, yy.

    Let t_f : t_x --> t_y
      := f ,, ff.

    Let t_g : t_x --> t_y
      := g ,, gg.

    Let t_e : total_category D
      := _ ,, pr1 ee.

    Let t_i : t_e --> t_x
      := _ ,, pr12 ee.

    Proposition total_Equalizer_path
      : t_i · t_f = t_i · t_g.
    Proof.
      use total2_paths_f.
      - apply EqualizerEqAr.
      - apply (pr122 ee).
    Qed.

    Section TotalEqualizerUMP.
      Context {w : C}
              {ww : D w}
              {h : w --> x}
              (hh : ww -->[ h ] xx).

      Let t_w : total_category D
        := w ,, ww.

      Let t_h : t_w --> t_x
        := h ,, hh.

      Context (t_q : t_h · t_f = t_h · t_g).

      Let q : h · f = h · g
        := base_paths _ _ t_q.

      Let qq
        : transportf
            (λ z, _ -->[ z ] _)
            q
            (hh ;; ff)
          = hh ;; gg
       := fiber_paths t_q.

      Proposition total_Equalizer_unique
        : isaprop
            (∑ (φ : t_w --> t_e), φ · t_i = t_h).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        use total2_paths_f.
        - use EqualizerInsEq.
          exact (maponpaths pr1 (pr2 φ₁ @ !(pr2 φ₂))).
        - assert (r : pr11 φ₂ = EqualizerIn e w h q).
          {
            exact (isEqualizerInUnique
                     _ _ _ _
                     (pr22 e)
                     _ _ _
                     (pr11 φ₂)
                     (maponpaths pr1 (pr2 φ₂))).
          }
          rewrite <- (transportbfinv
                        (λ z, _ -->[ z ] _)
                        r
                        (pr21 φ₂)).
          rewrite <- (transportbfinv
                        (λ z, _ -->[ z ] _)
                        r
                        (transportf _ _ _)).
          apply maponpaths.
          use (maponpaths
                 pr1
                 (proofirrelevance
                    _
                    (isapropifcontr
                       (pr222 ee w ww h hh q qq))
                    (transportf _ _ _ ,, _)
                    (transportf _ _ _ ,, _))).
          + cbn.
            rewrite mor_disp_transportf_postwhisker.
            rewrite !transport_f_f.
            rewrite mor_disp_transportf_postwhisker.
            rewrite !transport_f_f.
            refine (_ @ fiber_paths (pr2 φ₁)).
            apply maponpaths_2.
            apply homset_property.
          + cbn.
            rewrite mor_disp_transportf_postwhisker.
            rewrite transport_f_f.
            refine (_ @ fiber_paths (pr2 φ₂)).
            apply maponpaths_2.
            apply homset_property.
      Qed.

      Definition total_EqualizerIn
        : t_w --> t_e.
      Proof.
        refine (EqualizerIn e w h q ,, _).
        exact (pr11 (pr222 ee w ww h hh q qq)).
      Defined.

      Proposition total_EqualizerIn_commutes
        : total_EqualizerIn · t_i = t_h.
      Proof.
        use total2_paths_f.
        - apply EqualizerCommutes.
        - exact (pr21 (pr222 ee w ww h hh q qq)).
      Defined.
    End TotalEqualizerUMP.

    Definition total_Equalizer
      : @Equalizer
          (total_category D)
          t_x t_y
          t_f t_g.
    Proof.
      use make_Equalizer.
      - exact t_e.
      - exact t_i.
      - exact total_Equalizer_path.
      - intros w h q.
        use iscontraprop1.
        + apply total_Equalizer_unique.
          exact q.
        + simple refine (_ ,, _).
          * exact (total_EqualizerIn (pr2 h) q).
          * exact (total_EqualizerIn_commutes (pr2 h) q).
    Defined.
  End TotalEqualizer.

  Definition total_Equalizers
             (EC : Equalizers C)
             (DC : disp_Equalizers EC)
    : Equalizers (total_category D).
  Proof.
    intros x y f g.
    exact (total_Equalizer
             (pr2 f)
             (pr2 g)
             (EC _ _ (pr1 f) (pr1 g))
             (DC _ _ _ _ _ _ (pr2 f) (pr2 g))).
  Defined.

  (**
   Displayed coequalizers
   *)
  Definition is_disp_Coequalizer
             {x y : C}
             {f g : x --> y}
             (e : Coequalizer f g)
             {xx : D x}
             {yy : D y}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             (ee : D e)
             (ar_e : yy -->[ CoequalizerArrow e ] ee)
             (pp : transportf
                     (λ z, _ -->[ z ] _)
                     (CoequalizerEqAr e)
                     (ff ;; ar_e)
                   =
                   gg ;; ar_e)
    : UU
    := ∏ (w : C)
         (ww : D w)
         (h : y --> w)
         (hh : yy -->[ h ] ww)
         (q : f · h = g · h)
         (qq : transportf
                 (λ z, _ -->[ z ] _)
                 q
                 (ff ;; hh)
               =
               gg ;; hh),
       ∃! (ii : ee -->[ CoequalizerOut e w h q ] ww),
       transportf
         (λ z, _ -->[ z ] _)
         (CoequalizerCommutes e w h q)
         (ar_e ;; ii)
       =
       hh.

  Definition disp_Coequalizer
             {x y : C}
             {f g : x --> y}
             {xx : D x}
             {yy : D y}
             (ff : xx -->[ f ] yy)
             (gg : xx -->[ g ] yy)
             (e : Coequalizer f g)
    : UU
    := ∑ (ee : D e)
         (ar_e : yy -->[ CoequalizerArrow e ] ee)
         (pp : transportf
                 (λ z, _ -->[ z ] _)
                 (CoequalizerEqAr e)
                 (ff ;; ar_e)
               =
               gg ;; ar_e),
       is_disp_Coequalizer e ee ar_e pp.

  Definition disp_Coequalizers
             (DC : Coequalizers C)
    : UU
    := ∏ (x y : C)
         (f g : x --> y)
         (xx : D x)
         (yy : D y)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy),
       disp_Coequalizer ff gg (DC x y f g).

  Section TotalCoequalizer.
    Context {x y : C}
            {f g : x --> y}
            {xx : D x}
            {yy : D y}
            (ff : xx -->[ f ] yy)
            (gg : xx -->[ g ] yy)
            (e : Coequalizer f g)
            (ee : disp_Coequalizer ff gg e).

    Let t_x : total_category D
      := x ,, xx.

    Let t_y : total_category D
      := y ,, yy.

    Let t_f : t_x --> t_y
      := f ,, ff.

    Let t_g : t_x --> t_y
      := g ,, gg.

    Let t_e : total_category D
      := _ ,, pr1 ee.

    Let t_i : t_y --> t_e
      := _ ,, pr12 ee.

    Proposition total_Coequalizer_path
      : t_f · t_i = t_g · t_i.
    Proof.
      use total2_paths_f.
      - apply CoequalizerEqAr.
      - apply (pr122 ee).
    Qed.

    Section TotalCoequalizerUMP.
      Context {w : C}
              {ww : D w}
              {h : y --> w}
              (hh : yy -->[ h ] ww).

      Let t_w : total_category D
        := w ,, ww.

      Let t_h : t_y --> t_w
        := h ,, hh.

      Context (t_q : t_f · t_h = t_g · t_h).

      Let q : f · h = g · h
        := base_paths _ _ t_q.

      Let qq
        : transportf
            (λ z, _ -->[ z ] _)
            q
            (ff ;; hh)
          = gg ;; hh
       := fiber_paths t_q.

      Proposition total_Coequalizer_unique
        : isaprop
            (∑ (φ : t_e --> t_w), t_i · φ = t_h).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        use total2_paths_f.
        - use CoequalizerOutsEq.
          exact (maponpaths pr1 (pr2 φ₁ @ !(pr2 φ₂))).
        - assert (r : pr11 φ₂ = CoequalizerOut e w h q).
          {
            exact (isCoequalizerOutUnique
                     _ _ _ _
                     (pr22 e)
                     _ _ _
                     (pr11 φ₂)
                     (maponpaths pr1 (pr2 φ₂))).
          }
          rewrite <- (transportbfinv
                        (λ z, _ -->[ z ] _)
                        r
                        (pr21 φ₂)).
          rewrite <- (transportbfinv
                        (λ z, _ -->[ z ] _)
                        r
                        (transportf _ _ _)).
          apply maponpaths.
          use (maponpaths
                 pr1
                 (proofirrelevance
                    _
                    (isapropifcontr
                       (pr222 ee w ww h hh q qq))
                    (transportf _ _ _ ,, _)
                    (transportf _ _ _ ,, _))).
          + cbn.
            rewrite mor_disp_transportf_prewhisker.
            rewrite !transport_f_f.
            rewrite mor_disp_transportf_prewhisker.
            rewrite !transport_f_f.
            refine (_ @ fiber_paths (pr2 φ₁)).
            apply maponpaths_2.
            apply homset_property.
          + cbn.
            rewrite mor_disp_transportf_prewhisker.
            rewrite transport_f_f.
            refine (_ @ fiber_paths (pr2 φ₂)).
            apply maponpaths_2.
            apply homset_property.
      Qed.

      Definition total_CoequalizerOut
        : t_e --> t_w.
      Proof.
        refine (CoequalizerOut e w h q ,, _).
        exact (pr11 (pr222 ee w ww h hh q qq)).
      Defined.

      Proposition total_CoequalizerOut_commutes
        : t_i · total_CoequalizerOut = t_h.
      Proof.
        use total2_paths_f.
        - apply CoequalizerCommutes.
        - exact (pr21 (pr222 ee w ww h hh q qq)).
      Defined.
    End TotalCoequalizerUMP.

    Definition total_Coequalizer
      : @Coequalizer
          (total_category D)
          t_x t_y
          t_f t_g.
    Proof.
      use make_Coequalizer.
      - exact t_e.
      - exact t_i.
      - exact total_Coequalizer_path.
      - intros w h q.
        use iscontraprop1.
        + apply total_Coequalizer_unique.
          exact q.
        + simple refine (_ ,, _).
          * exact (total_CoequalizerOut (pr2 h) q).
          * exact (total_CoequalizerOut_commutes (pr2 h) q).
    Defined.
  End TotalCoequalizer.

  Definition total_Coequalizers
             (EC : Coequalizers C)
             (DC : disp_Coequalizers EC)
    : Coequalizers (total_category D).
  Proof.
    intros x y f g.
    exact (total_Coequalizer
             (pr2 f)
             (pr2 g)
             (EC _ _ (pr1 f) (pr1 g))
             (DC _ _ _ _ _ _ (pr2 f) (pr2 g))).
  Defined.

  (**
   Type-indexed products
   *)
  Section FixType.
    Context (I : UU).

    Definition disp_isProduct
               {d : I → C}
               (dd : ∏ (i : I), D (d i))
               (p : Product I C d)
               (pp : D p)
               (ππ : ∏ (i : I), pp -->[ ProductPr _ _ p i ] dd i)
      : UU
      := ∏ (w : C)
           (ww : D w)
           (f : ∏ (i : I), w --> d i)
           (ff : ∏ (i : I), ww -->[ f i ] dd i),
         ∃! (hh : ww -->[ ProductArrow _ _ p f ] pp),
         ∏ (i : I),
         transportf
           (λ z, _ -->[ z ] _)
           (ProductPrCommutes _ _ _ p _ f i)
           (hh ;; ππ i)
         =
         ff i.

    Definition disp_Product
               {d : I → C}
               (dd : ∏ (i : I), D (d i))
               (p : Product I C d)
      : UU
      := ∑ (pp : D p)
           (ππ : ∏ (i : I), pp -->[ ProductPr _ _ p i ] dd i),
         disp_isProduct dd p pp ππ.

    Definition disp_Products
               (PC : Products I C)
      : UU
      := ∏ (d : I → C)
           (dd : ∏ (i : I), D (d i)),
         disp_Product dd (PC d).

    Section TotalProduct.
      Context (d_dd : I → total_category D).

      Let d : I → C
        := λ i, pr1 (d_dd i).

      Let dd : ∏ (i : I), D (d i)
        := λ i, pr2 (d_dd i).

      Context (p : Product I C d)
              (pp : disp_Product dd p).

      Definition total_category_Product
        : total_category D
        := _ ,, pr1 pp.

      Definition total_category_ProductPr
                 (i : I)
        : total_category_Product --> d_dd i
        := _ ,, pr12 pp i.

      Section TotalProductUMP.
        Context {w : C}
                (ww : D w)
                {f : ∏ (i : I), w --> d i}
                (ff : ∏ (i : I), ww -->[ f i ] dd i).

        Let t_w : total_category D
          := w ,, ww.

        Let t_f : ∏ (i : I), t_w --> d_dd i
          := λ i, f i ,, ff i.

        Proposition total_category_ProductUnique
          : isaprop
              (∑ (φ : t_w --> total_category_Product),
               ∏ (i : I), φ · total_category_ProductPr i = t_f i).
        Proof.
          use invproofirrelevance.
          intros φ₁ φ₂.
          use subtypePath.
          {
            intro.
            use impred ; intro.
            apply homset_property.
          }
          use total2_paths_f.
          - use ProductArrow_eq.
            intro i.
            exact (maponpaths pr1 (pr2 φ₁ i @ !(pr2 φ₂ i))).
          - assert (r : pr11 φ₂ = ProductArrow _ _ p f).
            {
              use ProductArrow_eq.
              intro i.
              refine (maponpaths pr1 (pr2 φ₂ i) @ _).
              cbn.
              rewrite ProductPrCommutes.
              apply idpath.
            }
            rewrite <- (transportbfinv
                          (λ z, _ -->[ z ] _)
                          r
                          (pr21 φ₂)).
            rewrite <- (transportbfinv
                          (λ z, _ -->[ z ] _)
                          r
                          (transportf _ _ _)).
            apply maponpaths.
            use (maponpaths
                   pr1
                   (proofirrelevance
                      _
                      (isapropifcontr
                         (pr22 pp w ww f ff))
                      (transportf _ _ _ ,, _)
                      (transportf _ _ _ ,, _))).
            + cbn.
              intro i.
              rewrite mor_disp_transportf_postwhisker.
              rewrite !transport_f_f.
              rewrite mor_disp_transportf_postwhisker.
              rewrite !transport_f_f.
              refine (_ @ fiber_paths (pr2 φ₁ i)).
              apply maponpaths_2.
              apply homset_property.
            + cbn.
              intro i.
              rewrite mor_disp_transportf_postwhisker.
              rewrite transport_f_f.
              refine (_ @ fiber_paths (pr2 φ₂ i)).
              apply maponpaths_2.
              apply homset_property.
        Qed.

        Definition total_category_ProductArrow
          : t_w --> total_category_Product
          := _ ,, pr11 (pr22 pp w ww f ff).

        Proposition total_category_ProductPrCommutes
                    (i : I)
          : total_category_ProductArrow · total_category_ProductPr i
            =
            t_f i.
        Proof.
          use total2_paths_f.
          - exact (ProductPrCommutes _ _ _ p _ _ i).
          - exact (pr21 (pr22 pp w ww f ff) i).
        Qed.
      End TotalProductUMP.

      Definition total_category_isProduct
        : isProduct
            _ _ _
            total_category_Product
            total_category_ProductPr.
      Proof.
        intros w f.
        use iscontraprop1.
        - apply total_category_ProductUnique.
        - simple refine (_ ,, _).
          + exact (total_category_ProductArrow (pr2 w) (λ i, pr2 (f i))).
          + exact (total_category_ProductPrCommutes (pr2 w) (λ i, pr2 (f i))).
      Defined.
    End TotalProduct.

    Definition total_Products
               (PC : Products I C)
               (DC : disp_Products PC)
      : Products I (total_category D).
    Proof.
      intros d.
      use make_Product.
      - exact (total_category_Product d _ (DC _ _)).
      - exact (total_category_ProductPr d _ (DC _ _)).
      - apply total_category_isProduct.
    Defined.
  End FixType.

  (**
   Displayed binary coproducts
   *)
  Definition disp_isBinCoproduct
             {x y : C}
             {xx : D x}
             {yy : D y}
             (p : BinCoproduct x y)
             (pp : D p)
             (ιι₁ : xx -->[ BinCoproductIn1 p ] pp)
             (ιι₂ : yy -->[ BinCoproductIn2 p ] pp)
    : UU
    := ∏ (w : C)
         (ww : D w)
         (f : x --> w)
         (ff : xx -->[ f ] ww)
         (g : y --> w)
         (gg : yy -->[ g ] ww),
       ∃! (hh : pp -->[ BinCoproductArrow p f g ] ww),
       (transportf
          (λ z, _ -->[ z ] _)
          (BinCoproductIn1Commutes _ _ _ p _ f g)
          (ιι₁ ;; hh)
        =
        ff)
       ×
       (transportf
          (λ z, _ -->[ z ] _)
          (BinCoproductIn2Commutes _ _ _ p _ f g)
          (ιι₂ ;; hh)
        =
        gg).

  Definition disp_BinCoproduct
             {x y : C}
             (xx : D x)
             (yy : D y)
             (p : BinCoproduct x y)
    : UU
    := ∑ (pp : D p)
         (ιι₁ : xx -->[ BinCoproductIn1 p ] pp)
         (ιι₂ : yy -->[ BinCoproductIn2 p ] pp),
       disp_isBinCoproduct p pp ιι₁ ιι₂.

    Definition disp_BinCoproducts
               (PC : BinCoproducts C)
      : UU
      := ∏ (x y : C)
           (xx : D x)
           (yy : D y),
         disp_BinCoproduct xx yy (PC x y).

    Section TotalBinCoproduct.
      Context (x_xx y_yy : total_category D).

      Let x : C := pr1 x_xx.
      Let y : C := pr1 y_yy.
      Let xx : D x := pr2 x_xx.
      Let yy : D y := pr2 y_yy.

      Context (p : BinCoproduct x y)
              (pp : disp_BinCoproduct xx yy p).

      Definition total_category_BinCoproduct
        : total_category D
        := _ ,, pr1 pp.

      Definition total_category_BinCoproductIn1
        : x_xx --> total_category_BinCoproduct
        := _ ,, pr12 pp.

      Definition total_category_BinCoproductIn2
        : y_yy --> total_category_BinCoproduct
        := _ ,, pr122 pp.

      Section TotalBinCoproductUMP.
        Context {w : C}
                (ww : D w)
                {f : x --> w}
                (ff : xx -->[ f ] ww)
                {g : y --> w}
                (gg : yy -->[ g ] ww).

        Let t_w : total_category D
          := w ,, ww.
        Let t_f : x_xx --> t_w
          := f ,, ff.
        Let t_g : y_yy --> t_w
          := g ,, gg.

        Proposition total_category_BinCoproductUnique
          : isaprop
              (∑ (fg : total_category_BinCoproduct --> t_w),
               (total_category_BinCoproductIn1 · fg = t_f)
               ×
               (total_category_BinCoproductIn2 · fg = t_g)).
        Proof.
          use invproofirrelevance.
          intros φ₁ φ₂.
          use subtypePath.
          {
            intro.
            use isapropdirprod ; apply homset_property.
          }
          use total2_paths_f.
          - use BinCoproductArrowsEq.
            + exact (maponpaths pr1 (pr12 φ₁ @ !(pr12 φ₂))).
            + exact (maponpaths pr1 (pr22 φ₁ @ !(pr22 φ₂))).
          - assert (r : pr11 φ₂ = BinCoproductArrow p f g).
            {
              use BinCoproductArrowsEq.
              + refine (maponpaths pr1 (pr12 φ₂) @ _).
                cbn.
                rewrite BinCoproductIn1Commutes.
                apply idpath.
              + refine (maponpaths pr1 (pr22 φ₂) @ _).
                cbn.
                rewrite BinCoproductIn2Commutes.
                apply idpath.
            }
            rewrite <- (transportbfinv
                          (λ z, _ -->[ z ] _)
                          r
                          (pr21 φ₂)).
            rewrite <- (transportbfinv
                          (λ z, _ -->[ z ] _)
                          r
                          (transportf _ _ _)).
            apply maponpaths.
            use (maponpaths
                   pr1
                   (proofirrelevance
                      _
                      (isapropifcontr
                         (pr222 pp w ww f ff g gg))
                      (transportf _ _ _ ,, _)
                      (transportf _ _ _ ,, _))).
            + cbn.
              split.
              * rewrite !mor_disp_transportf_prewhisker.
                rewrite !transport_f_f.
                refine (_ @ fiber_paths (pr12 φ₁)).
                apply maponpaths_2.
                apply homset_property.
              * rewrite !mor_disp_transportf_prewhisker.
                rewrite !transport_f_f.
                refine (_ @ fiber_paths (pr22 φ₁)).
                apply maponpaths_2.
                apply homset_property.
            + cbn.
              split.
              * rewrite !mor_disp_transportf_prewhisker.
                rewrite !transport_f_f.
                refine (_ @ fiber_paths (pr12 φ₂)).
                apply maponpaths_2.
                apply homset_property.
              * rewrite !mor_disp_transportf_prewhisker.
                rewrite !transport_f_f.
                refine (_ @ fiber_paths (pr22 φ₂)).
                apply maponpaths_2.
                apply homset_property.
        Qed.

        Definition total_category_BinCoproductArrow
          : total_category_BinCoproduct --> t_w
          := _ ,, pr11 (pr222 pp w ww f ff g gg).

        Proposition total_category_BinCoproductArrowIn1
          : total_category_BinCoproductIn1 · total_category_BinCoproductArrow = t_f.
        Proof.
          use total2_paths_f.
          - apply BinCoproductIn1Commutes.
          - exact (pr121 (pr222 pp w ww f ff g gg)).
        Qed.

        Proposition total_category_BinCoproductArrowIn2
          : total_category_BinCoproductIn2 · total_category_BinCoproductArrow = t_g.
        Proof.
          use total2_paths_f.
          - apply BinCoproductIn2Commutes.
          - exact (pr221 (pr222 pp w ww f ff g gg)).
        Qed.
      End TotalBinCoproductUMP.

      Definition total_category_isBinCoproduct
        : isBinCoproduct
            _ _ _
            total_category_BinCoproduct
            total_category_BinCoproductIn1
            total_category_BinCoproductIn2.
      Proof.
        intros w f g.
        use iscontraprop1.
        - apply total_category_BinCoproductUnique.
        - simple refine (_ ,, _ ,, _).
          + exact (total_category_BinCoproductArrow (pr2 w) (pr2 f) (pr2 g)).
          + apply total_category_BinCoproductArrowIn1.
          + apply total_category_BinCoproductArrowIn2.
      Defined.
    End TotalBinCoproduct.

    Definition total_BinCoproducts
               (PC : BinCoproducts C)
               (DC : disp_BinCoproducts PC)
      : BinCoproducts (total_category D).
    Proof.
      intros x y.
      use make_BinCoproduct.
      - exact (total_category_BinCoproduct
                 x y
                 (PC (pr1 x) (pr1 y))
                 (DC _ _ (pr2 x) (pr2 y))).
      - exact (total_category_BinCoproductIn1
                 x y
                 (PC (pr1 x) (pr1 y))
                 (DC _ _ (pr2 x) (pr2 y))).
      - exact (total_category_BinCoproductIn2
                 x y
                 (PC (pr1 x) (pr1 y))
                 (DC _ _ (pr2 x) (pr2 y))).
      - exact (total_category_isBinCoproduct
                 x y
                 (PC (pr1 x) (pr1 y))
                 (DC _ _ (pr2 x) (pr2 y))).
    Defined.

  (**
   Displayed coproducts indexed over arbitrary types
   *)
  Section FixType.
    Context (I : UU).

    Definition disp_isCoproduct
               {d : I → C}
               (dd : ∏ (i : I), D (d i))
               (p : Coproduct I C d)
               (pp : D p)
               (ππ : ∏ (i : I), dd i -->[ CoproductIn _ _ p i ] pp)
      : UU
      := ∏ (w : C)
           (ww : D w)
           (f : ∏ (i : I), d i --> w)
           (ff : ∏ (i : I), dd i -->[ f i ] ww),
         ∃! (hh : pp -->[ CoproductArrow _ _ p f ] ww),
         ∏ (i : I),
         transportf
           (λ z, _ -->[ z ] _)
           (CoproductInCommutes _ _ _ p _ f i)
           (ππ i ;; hh)
         =
         ff i.

    Definition disp_Coproduct
               {d : I → C}
               (dd : ∏ (i : I), D (d i))
               (p : Coproduct I C d)
      : UU
      := ∑ (pp : D p)
           (ππ : ∏ (i : I), dd i -->[ CoproductIn _ _ p i ] pp),
         disp_isCoproduct dd p pp ππ.

    Definition disp_Coproducts
               (PC : Coproducts I C)
      : UU
      := ∏ (d : I → C)
           (dd : ∏ (i : I), D (d i)),
         disp_Coproduct dd (PC d).

    Section TotalCoproduct.
      Context (d_dd : I → total_category D).

      Let d : I → C
        := λ i, pr1 (d_dd i).

      Let dd : ∏ (i : I), D (d i)
        := λ i, pr2 (d_dd i).

      Context (p : Coproduct I C d)
              (pp : disp_Coproduct dd p).

      Definition total_category_Coproduct
        : total_category D
        := _ ,, pr1 pp.

      Definition total_category_CoproductIn
                 (i : I)
        : d_dd i --> total_category_Coproduct
        := _ ,, pr12 pp i.

      Section TotalCoproductUMP.
        Context {w : C}
                (ww : D w)
                {f : ∏ (i : I), d i --> w}
                (ff : ∏ (i : I), dd i -->[ f i ] ww).

        Let t_w : total_category D
          := w ,, ww.

        Let t_f : ∏ (i : I), d_dd i --> t_w
          := λ i, f i ,, ff i.

        Proposition total_category_CoproductUnique
          : isaprop
              (∑ (φ : total_category_Coproduct --> t_w),
               ∏ (i : I), total_category_CoproductIn i · φ = t_f i).
        Proof.
          use invproofirrelevance.
          intros φ₁ φ₂.
          use subtypePath.
          {
            intro.
            use impred ; intro.
            apply homset_property.
          }
          use total2_paths_f.
          - use CoproductArrow_eq.
            intro i.
            exact (maponpaths pr1 (pr2 φ₁ i @ !(pr2 φ₂ i))).
          - assert (r : pr11 φ₂ = CoproductArrow _ _ p f).
            {
              use CoproductArrow_eq.
              intro i.
              refine (maponpaths pr1 (pr2 φ₂ i) @ _).
              cbn.
              rewrite CoproductInCommutes.
              apply idpath.
            }
            rewrite <- (transportbfinv
                          (λ z, _ -->[ z ] _)
                          r
                          (pr21 φ₂)).
            rewrite <- (transportbfinv
                          (λ z, _ -->[ z ] _)
                          r
                          (transportf _ _ _)).
            apply maponpaths.
            use (maponpaths
                   pr1
                   (proofirrelevance
                      _
                      (isapropifcontr
                         (pr22 pp w ww f ff))
                      (transportf _ _ _ ,, _)
                      (transportf _ _ _ ,, _))).
            + cbn.
              intro i.
              rewrite mor_disp_transportf_prewhisker.
              rewrite !transport_f_f.
              rewrite mor_disp_transportf_prewhisker.
              rewrite !transport_f_f.
              refine (_ @ fiber_paths (pr2 φ₁ i)).
              apply maponpaths_2.
              apply homset_property.
            + cbn.
              intro i.
              rewrite mor_disp_transportf_prewhisker.
              rewrite transport_f_f.
              refine (_ @ fiber_paths (pr2 φ₂ i)).
              apply maponpaths_2.
              apply homset_property.
        Qed.

        Definition total_category_CoproductArrow
          : total_category_Coproduct --> t_w
          := _ ,, pr11 (pr22 pp w ww f ff).

        Proposition total_category_CoproductInCommutes
                    (i : I)
          : total_category_CoproductIn i · total_category_CoproductArrow
            =
            t_f i.
        Proof.
          use total2_paths_f.
          - exact (CoproductInCommutes _ _ _ p _ _ i).
          - exact (pr21 (pr22 pp w ww f ff) i).
        Qed.
      End TotalCoproductUMP.

      Definition total_category_isCoproduct
        : isCoproduct
            _ _ _
            total_category_Coproduct
            total_category_CoproductIn.
      Proof.
        intros w f.
        use iscontraprop1.
        - apply total_category_CoproductUnique.
        - simple refine (_ ,, _).
          + exact (total_category_CoproductArrow (pr2 w) (λ i, pr2 (f i))).
          + exact (total_category_CoproductInCommutes (pr2 w) (λ i, pr2 (f i))).
      Defined.
    End TotalCoproduct.

    Definition total_Coproducts
               (PC : Coproducts I C)
               (DC : disp_Coproducts PC)
      : Coproducts I (total_category D).
    Proof.
      intros d.
      use make_Coproduct.
      - exact (total_category_Coproduct d _ (DC _ _)).
      - exact (total_category_CoproductIn d _ (DC _ _)).
      - apply total_category_isCoproduct.
    Defined.
  End FixType.
End FixDispCat.
