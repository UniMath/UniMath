(** **********************************************************

Ralph Matthes

2022
*)

(** **********************************************************

Contents :

- defines a notion of binary products for displayed categories that gives binary products on its total category
- same programme for terminal objects

 ************************************************************)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
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
    transportf (mor_disp xx (dispBinProductObject P dP)) (BinProductArrowEta C c d P x fg) fgfg =
      dispBinProductArrow P dP (fgfg ;; dispBinProductPr1 P dP) (fgfg ;; dispBinProductPr2 P dP).
  Proof.
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


  Definition total_category_Binproducts (Ps : BinProducts C) (dPs : dispBinProducts Ps) : BinProducts (total_category D).
  Proof.
    intros ccc ddd.
    induction ccc as [c cc].
    induction ddd as [d dd].
    use tpair.
    - exists (BinProductObject _ (Ps c d) ,, dispBinProductObject (Ps c d) (dPs c d cc dd)).
      split.
      + use tpair.
        * apply BinProductPr1.
        * apply dispBinProductPr1.
      + use tpair.
        * apply BinProductPr2.
        * apply dispBinProductPr2.
    - intros aaa fff ggg.
      destruct aaa as [a aa]; destruct fff as [f ff]; destruct ggg as [g gg].
      cbn.
      use unique_exists.
      + use tpair.
        * apply BinProductArrow; assumption.
        * apply dispBinProductArrow; assumption.
      + cbn; split.
        * use total2_paths_f; cbn.
          -- apply BinProductPr1Commutes.
          -- apply transportf_pathsinv0.
             apply pathsinv0.
             apply dispBinProductPr1Commutes.
        * use total2_paths_f; cbn.
          -- apply BinProductPr2Commutes.
          -- apply transportf_pathsinv0.
             apply pathsinv0.
             apply dispBinProductPr2Commutes.
      + intro y.
        apply isapropdirprod.
        -- apply (homset_property (total_category D) (a ,, aa) (c ,, cc)).
        -- apply (homset_property (total_category D) (a ,, aa) (d ,, dd)).
      + intro fgfgfg.
        induction fgfgfg as [fg fgfg].
        intro H.
        induction H as [H1 H2].
        cbn in *.
        induction (total2_paths_equiv _ _ _ H1) as [H1l H1r].
        induction (total2_paths_equiv _ _ _ H2) as [H2l H2r].
        clear H1 H2.
        use total2_paths_f; cbn.
        * use path_to_ctr; split; assumption.
        * cbn in *.
          rewrite <- H1r, <- H2r.
          clear H1r H2r ff gg.
          induction H1l.
          induction H2l.
          (* apply dispBinProductArrowEta. would work with [BinProductArrowEta'] *)
          (* we proceed as follows: *)
          cbn.
          etrans.
          2: { apply dispBinProductArrowEta. }
          apply (maponpaths (fun z => transportf (mor_disp aa (dispBinProductObject (Ps c d) (dPs c d cc dd))) z fgfg)).
          apply C.
  Defined.

(** ** analogously for terminal objects *)


  Definition is_dispTerminal (P : Terminal C) (pp : D (TerminalObject P)) : UU :=
    ∏ (a : C) (aa : D a), iscontr (aa -->[TerminalArrow P a] pp).

  Definition dispTerminal (P : Terminal C) : UU :=
    ∑ pp :  D (TerminalObject P), is_dispTerminal P pp.

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


End FixDispCat.
