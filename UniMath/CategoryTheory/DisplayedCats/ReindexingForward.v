
(* reindexing forward (reindexig_f) for displayed categories 
   and the universal property that it respects.*)

(*    D -- functor reindexing_forward --> reindexing_forward *)
(*    ↓                     ↓                      ↓         *)
(*    C ------------------- F -------------------> C'        *)

(* May 2023 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Export UniMath.CategoryTheory.Core.Categories.
Require Export UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.TransportMorphisms.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.

Local Open Scope cat. 

(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

Notation "X ◦ Y" := (disp_functor_composite X Y) (at level 45): cat. 

Declare Scope reindexing_forward_scope.
Notation "↙ x" := (pr1 x)  (at level 0):reindexing_forward_scope. 
Notation "← x" := (pr2 (pr2 x)) (at level 0):reindexing_forward_scope.
Notation "¤ x" := (pr1(pr2 x)) (at level 0):reindexing_forward_scope.

(* Recreate base objects from an object x' over c' of the reindexing_forward *)
(*  x:= (← x') -----?-----> x' =: (↙ x', ¤ x', ← x') *)
(*    ↓                     ↓                        *)
(*  c:= (↙ x') -----F-----> c'                       *)
(* ¤ x: F c = c'   *)

(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
Section reindexing_forward.

  Local Open Scope reindexing_forward_scope.

  Context {C C':category} (D :disp_cat C) (F :functor C C').

  (*    D -- functor reindexing_forward --> reindexing_forward *)
  (*    ↓                    ↓                      ↓          *)
  (*    C ------------------- F -------------------> C'        *)


  Definition reindexing_forward_ob_mor : disp_cat_ob_mor C'.
  Proof.
    use make_disp_cat_ob_mor.
    - exact (λ c', ∑c:C,(F c=c' × ob_disp D c)).
    - intros a' b' x' y' f'.
      exact (∑f:(↙ x')-->(↙ y'),
      (double_transport (¤ x') (¤ y') (# F f)=f' ×
      (← x')-->[f](← y'))).
  Defined.

  (*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
  (* Some lemmas to caracterize the equality of reindexing_forward objects and morphisms*)
  Lemma reindexing_forward_ob_eq {c' : C'}
  {x' :ob_disp reindexing_forward_ob_mor c'} {y' :ob_disp reindexing_forward_ob_mor c'}
  (e0 : ↙x' = ↙y')
  : transportf (λ c, F c = c') e0 ¤x' = ¤y' -> transportf _ e0 ←x' = ←y' -> x' = y'.
  Proof.
    intros e1 e2.
    apply (total2_paths_f e0).
    etrans. exact (transportf_dirprod C (λ c, F c = c') D x' y' e0).
    apply dirprod_paths.
    - exact e1.
    - exact e2.
  Defined.

  Lemma reindexing_forward_mor_eq {a' b':C'} 
  {x' :ob_disp reindexing_forward_ob_mor a'}
  {y' :ob_disp reindexing_forward_ob_mor b'}
  {f': C' ⟦ a', b' ⟧}
  {Df' : x' -->[ f'] y'} {Dg' : x' -->[ f'] y'} (e:↙ Df' = ↙ Dg')
  :transportf _ e ←Df' = ←Dg' -> Df'= Dg'.
  Proof.
    intro H.
    apply (total2_paths_f e).
    etrans. apply (transportf_dirprod (↙x' --> ↙ y')
    (λ f, double_transport ¤ (x') ¤ (y') (# F f) = f') (mor_disp ←x' ←y') Df' Dg' e).
    apply dirprod_paths.
    - apply uip. apply homset_property.
    - apply H.
  Defined.

  (*Theorem about the equality of reindexing_forward morphisms*)
  Theorem reindexing_forward_paths_f_mor {a' b':C'} 
  {x' :ob_disp reindexing_forward_ob_mor a'}
  {y' :ob_disp reindexing_forward_ob_mor b'}
  {f': C' ⟦ a', b' ⟧} {g': C' ⟦ a', b' ⟧} {p:g'=f'}
  (Df' : x' -->[ f'] y') (Dg' : x' -->[ g'] y') (e:↙ Dg' = ↙ Df')
  :← Df' = transportf _ e (← Dg') -> (Df'=transportf _ p Dg').
  Proof.
    intro H.
    destruct p.
    apply pathsinv0.
    etrans. exact (idpath_transportf _ Dg').
    exact (reindexing_forward_mor_eq e (! H)).
  Qed.
  (*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)


  Lemma reindexing_forward_id {c': C'} {x' : ob_disp reindexing_forward_ob_mor c'}
  : identity c' = double_transport (¤ x') (¤ x') (# F (identity (↙ x'))).
  Proof.
    destruct (¤ x').
    apply pathsinv0. 
    exact (functor_id_id C C' F _ _ (idpath _)).
  Qed.


  Lemma reindexing_forward_comp {a' b' c': C'} 
  {x' : ob_disp reindexing_forward_ob_mor a'} {y' : ob_disp reindexing_forward_ob_mor b'}
  {z' : ob_disp reindexing_forward_ob_mor c'} {f':C' ⟦ a', b' ⟧} {g':C' ⟦ b', c' ⟧}
  {Df':  x' -->[ f'] y'} {Dg': y' -->[ g'] z'}
  :f' · g' = double_transport (¤ x') (¤ z') (# F (↙ Df' · ↙ Dg')).
  Proof.
    destruct (¤ Df'), (¤ Dg').
    destruct (¤ x'), (¤ y'), (¤ z'). cbn.
    apply pathsinv0.
    apply functor_comp.
  Defined.

  Definition reindexing_forward_id_comp : disp_cat_id_comp C' reindexing_forward_ob_mor.
  Proof.
    use tpair.
    - intros c' x'.
      exists (identity (↙ x')).
      use tpair.
      * apply (! reindexing_forward_id). 
      * exact (id_disp (← x')).
    - intros a' b' c' f' g' x' y' z'.
      intros Df' Dg'.
      exists ((↙ Df')·(↙ Dg')). 
      use tpair. 
      * apply (! reindexing_forward_comp).
      * exact (comp_disp (← Df') (← Dg')).
  Defined.


  Definition reindexing_forward_disp_cat_data : disp_cat_data C'
    := (reindexing_forward_ob_mor,, reindexing_forward_id_comp).


  Local Open Scope mor_disp. 

  Definition reindexing_forward_disp_cat_axioms : disp_cat_axioms C' reindexing_forward_disp_cat_data.
  Proof.
    repeat apply tpair.
    - intros a' b' f' x' y' Df'.
      apply (reindexing_forward_paths_f_mor (id_disp x' ;; Df') Df' (! id_left (↙ Df'))).
      exact (id_left_disp (← Df')).
    - intros a' b' f' x' y' Df'.
      apply (reindexing_forward_paths_f_mor (Df';; id_disp y') Df' (! id_right (↙ Df'))).
      exact (id_right_disp (← Df')).
    - intros a' b' c' d' f' g' h' x' y' z' w' Df' Dg' Dh'.
      apply (reindexing_forward_paths_f_mor (Df' ;; (Dg' ;; Dh')) (Df' ;; Dg' ;; Dh') 
      (! assoc (↙ Df') (↙ Dg') (↙ Dh') )).
      exact (assoc_disp (← Df') (← Dg') (← Dh')).
    - intros a' b' f' x' y'.
      apply isaset_total2.
      * apply homset.
      * intro f.
        apply isaset_dirprod.
        --apply isasetaprop. 
           apply homset_property.
        --apply homsets_disp.
  Qed.

  Local Close Scope mor_disp. 


  Local Close Scope reindexing_forward_scope.
End reindexing_forward.
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)


Definition reindexing_forward {C C':category}
(D:disp_cat C) (F: functor C C') : disp_cat C'
:= (reindexing_forward_disp_cat_data D F,, reindexing_forward_disp_cat_axioms D F).


(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
Section functor_reindexing_forward.

  Context {C C':category} (D :disp_cat C) (F :functor C C').

  (*    D -- functor reindexing_forward --> reindexing_forward *)
  (*    ↓            ↓             ↓     *)
  (*    C ---------- F ----------> C'    *)


  Definition data_functor_reindexing_forward : disp_functor_data F D (reindexing_forward D F).
  Proof.
    use tpair.
    - exact (λ (c:C) (d: D c), (c,, idpath (F c),,  d)).
    - intros a b x y f Df.
      exact (f ,,idpath (# F f),, Df).
  Defined.

  Local Open Scope mor_disp. 

  Definition axioms_reindexing_forward_functor: disp_functor_axioms data_functor_reindexing_forward.
  Proof.
    use tpair.
    - intros a x.
      apply (reindexing_forward_paths_f_mor D F (♯ (data_functor_reindexing_forward) (id_disp x)) 
      (id_disp (data_functor_reindexing_forward a x)) 
      (idpath _)).
      exact (idpath (id_disp x)).
    - intros a b c x y z f g Df Dg.
      apply (reindexing_forward_paths_f_mor D F (♯ (data_functor_reindexing_forward) (Df;;Dg))
      (♯ data_functor_reindexing_forward Df ;; ♯ data_functor_reindexing_forward Dg)
      (idpath _)).
      exact (idpath (Df;;Dg)).
  Qed.

  Local Close Scope mor_disp. 
End functor_reindexing_forward.
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)


Definition functor_reindexing_forward {C C':category} (D:disp_cat C) (F:functor C C')
  : disp_functor F D (reindexing_forward D F)
  := (data_functor_reindexing_forward D F,, axioms_reindexing_forward_functor D F).


(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
Section functor_universal_property_reindexing_forward.

  Context {C C' C'': category} {D:disp_cat C} {F: functor C C'}.
  Let D' := reindexing_forward D F. Let DF := functor_reindexing_forward D F.
  Context (H: functor C' C'') (D'': disp_cat C'') (DG: disp_functor (F ∙ H) D D'').

  (*      ---------------- DG ---------------->     *)
  (*    D -- DF --> D' -- functor univ prop --> D'' *)
  (*    ↓    ↓      ↓             ↓             ↓   *)
  (*    C -- F  --> C' ---------- H ----------> C'' *)

  Local Open Scope reindexing_forward_scope.

  Definition data_functor_univ_prop_reindexing_forward: disp_functor_data H D' D''.
  Proof.
    use tpair.
    - intros c' d'.
      exact (transportf (λ x, D'' (H x)) (¤ d') (DG  (↙ d') (← d'))).
    - intros a' b' x' y' f' Df'.
      apply (transportf (λ f0, mor_disp _ _ (# H f0)) (¤ Df')).
      apply double_transport_disp.
      exact ((♯ DG (← Df'))%mor_disp).
  Defined.

  Local Close Scope reindexing_forward_scope.

  Definition axioms_functor_univ_prop_reindexing_forward
    : disp_functor_axioms data_functor_univ_prop_reindexing_forward.
  Proof.
    use tpair.
    - intros c' d'.
      induction d' as (c,(p,d)).
      destruct p. cbn.
      etrans. apply functtransportf.
      etrans. apply (maponpaths _ (disp_functor_id DG d)).
      etrans. apply transport_f_b.
      unfold transportb.
      apply two_arg_paths.
      * apply uip.
        apply homset_property.
      * reflexivity.
    - intros a' b' c' x' y' z' f' g' Df' Dg'.
      induction Df' as (f,(pf,Df)).
      induction Dg' as (g,(pg,Dg)).
      destruct pf, pg. cbn.
      etrans. apply functtransportf.
      rewrite (disp_functor_comp DG).
      destruct (pr1 (pr2 x')), (pr1 (pr2 z')). cbn.
      destruct (pr1 (pr2 y')). cbn.
      etrans. apply transport_f_b.
      unfold transportb.
      apply two_arg_paths.
      * apply uip.
        apply homset_property.
      * reflexivity.
  Qed.


End functor_universal_property_reindexing_forward.
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)


Definition functor_univ_prop_reindexing_forward {C C' C'': category} {D:disp_cat C} {F: functor C C'}
(H: functor C' C'') (D'': disp_cat C'') (DG: disp_functor (F ∙ H) D D'')
: disp_functor H (reindexing_forward D F) D''
:= (data_functor_univ_prop_reindexing_forward H D'' DG,,
axioms_functor_univ_prop_reindexing_forward H D'' DG).


(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
Section unicity_universal_property_reindexing_forward.

  Context {C C' C'': category} {D:disp_cat C} {F: functor C C'}.
  Let D' := reindexing_forward D F. Let DF := functor_reindexing_forward D F.
  Context (H: functor C' C'') (D'': disp_cat C'') (DG: disp_functor (F ∙ H) D D'').
  Let DH := functor_univ_prop_reindexing_forward H D'' DG.

  (* Here we prove the unicity of DH*)
  (*      -------- DG -------->     *)
  (*    D -- DF --> D' -- DH --> D'' *)
  (*    ↓    ↓      ↓     ↓      ↓   *)
  (*    C -- F  --> C' -- H  --> C'' *)


  Definition univ_prop_reindexing_forward_eq : 
    disp_functor_composite DF DH= DG.
  Proof.
    apply disp_functor_eq.
    reflexivity.
  Defined.

  Definition univ_prop_reindexing_forward : 
    disp_nat_z_iso (DF ◦ DH) DG (nat_z_iso_id (F ∙ H)).
  Proof.
    - repeat use tpair.
      * exact (λ c d,id_disp (DG c d)).
      * intros a b f x y Df.
        cbn.
        etrans. apply id_right_disp.
        apply pathsinv0.
        rewrite id_left_disp.
        etrans. apply transport_b_b.
        apply two_arg_paths.
        -- apply uip.
           apply homset_property.
        -- reflexivity.
      * intros c d. cbn.
        exists (id_disp (DG c d)).
        split; apply id_left_disp.
  Defined.


  Local Open Scope reindexing_forward_scope.

  (*Lemma to use the fact that the total functor of DF is invertible*)
  Definition DF_inv_mor (DM DN: disp_functor H D' D'') (c':C') (d':D' c') 
    : (DF ◦ DM) ↙d' ←d' -->[identity _] (DF ◦ DN) ↙d' ←d' ->
    DM c' d' -->[identity _] DN c' d'.
  Proof.
    intro Hyp.
    induction d' as (c,(p,d)).
    destruct p.
    exact Hyp.
  Defined.

  Lemma DF_inv_mor_simpl {DM DN: disp_functor H D' D''} {c':C'} {d':D' c'} 
  (A: (DF ◦ DM) ↙d' ←d' -->[identity _] (DF ◦ DN) ↙d' ←d')
  (B: (DF ◦ DN) ↙d' ← d'-->[identity _] (DF ◦ DM) ↙d' ←d')  
  : (A;;B = transportb _ (id_left _) (id_disp _)->
  (DF_inv_mor DM DN c' d' A);;(DF_inv_mor DN DM c' d' B) = 
  transportb _ (id_left _) (id_disp (DM c' d')))%mor_disp.
  Proof.  
    intro Hyp.
    induction d' as (c,(p,d)).
    destruct p.
    exact Hyp.
  Qed.

  Local Open Scope mor_disp. 

  (*creation of a natural transformation from DH0 to DH1 for any DH0 and DH1*)
  Lemma DH0_DH1_nat_trans_data {DH0 DH1:disp_functor H D' D''} 
  (β: disp_nat_trans (nat_z_iso_id (F ∙ H)) (DF ◦ DH0) (DF ◦ DH1)) 
  :disp_nat_trans_data (nat_z_iso_id H) DH0 DH1.
  Proof.
    intros c' d'.
    apply (DF_inv_mor DH0 DH1 c' d').
    exact (β ↙d' ←d').
  Defined.

  Lemma DH0_DH1_nat_trans_axioms {DH0 DH1 :disp_functor H D' D''} 
  (β: disp_nat_trans (nat_z_iso_id (F ∙ H)) (DF ◦ DH0) (DF ◦ DH1)) 
  : disp_nat_trans_axioms (DH0_DH1_nat_trans_data β).
  Proof.
    intros a' b' f' x' y' Df'.
    induction x' as (a,(px,x)).
    induction y' as (b,(py,y)).
    induction Df' as (f,(pf,Df)).
    destruct px, py, pf.
    cbn.
    etrans. apply (pr2 β a b f x y Df).
    apply two_arg_paths.
    - apply uip.
      apply homset_property.
    - reflexivity.
  Qed.

  Definition DH0_DH1_nat_trans {DH0 DH1 :disp_functor H D' D''}
  (β: disp_nat_trans (nat_z_iso_id (F ∙ H)) (DF ◦ DH0) (DF ◦ DH1)) 
  : disp_nat_trans (nat_z_iso_id H) DH0 DH1
  := (DH0_DH1_nat_trans_data β,, DH0_DH1_nat_trans_axioms β).

  (*Proof that the displayed natural transformation above is an isomorphism*)
  Lemma DH0_DH1_is_disp_nat_z_iso {DH0 DH1 :disp_functor H D' D''}
  (β: disp_nat_z_iso (DF ◦ DH0) (DF ◦ DH1) (nat_z_iso_id (F ∙ H)))
  : is_disp_nat_z_iso (nat_z_iso_id H) (DH0_DH1_nat_trans β).
  Proof.
    set (β_inv := disp_nat_z_iso_to_trans_inv β).
    intros c' d'.
    use tpair.
    - cbn. 
      apply (DF_inv_mor DH1 DH0 c' d').
      exact (β_inv ↙d' ←d').
    - split. 
      * apply DF_inv_mor_simpl.
        etrans. apply (pr2 (pr2 β ↙d' ←d')).
        apply (maponpaths (λ e, transportf _ e _)).
        apply uip.
        apply homset_property.
      * apply DF_inv_mor_simpl.
        etrans. apply (pr2 (pr2 β ↙d' ←d')).
        apply (maponpaths (λ e, transportf _ e _)).
        apply uip.
        apply homset_property.
  Defined.

  Lemma DH0_DH1_disp_nat_z_iso {DH0 DH1 :disp_functor H D' D''}
  (β: disp_nat_z_iso (DF ◦ DH0) (DF ◦ DH1) (nat_z_iso_id (F ∙ H)))
  : disp_nat_z_iso DH0 DH1 (nat_z_iso_id H).
  Proof.
    use tpair.
    - exact (DH0_DH1_nat_trans β).
    - apply DH0_DH1_is_disp_nat_z_iso.
  Defined.

  Theorem unicity_univ_prop_reindexing_forward : 
    ∏ DH' :disp_functor H D' D'',
    disp_nat_z_iso (disp_functor_composite DF DH') DG (nat_z_iso_id (F ∙ H)) ->
    disp_nat_z_iso DH' DH (nat_z_iso_id H).
  Proof.
    intros DH' µ'.
    apply DH0_DH1_disp_nat_z_iso.
    apply (transportf _ (comp_nat_z_iso_id_left (nat_z_iso_id (F ∙ H)))).
    apply (disp_nat_z_iso_comp µ').
    apply (transportf _ nat_z_iso_inv_id).
    exact (disp_nat_z_iso_inv univ_prop_reindexing_forward).
  Defined.

  Local Close Scope mor_disp. 
  Local Close Scope reindexing_forward_scope.
End unicity_universal_property_reindexing_forward.
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)


(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
Section fibrations_and_reindexing_forward.

  Context {C C' C'': category} {D:disp_cat C} {F: functor C C'}.
  Let D' := reindexing_forward D F. Let DF := functor_reindexing_forward D F.
  Context (H: functor C' C'') (D'': disp_cat C'') (DG: disp_functor (F ∙ H) D D'').
  Let DH := functor_univ_prop_reindexing_forward H D'' DG.

  (*      -------- DG -------->      *)
  (*    D -- DF --> D' -- DH --> D'' *)
  (*    ↓    ↓      ↓     ↓      ↓   *)
  (*    C -- F  --> C' -- H  --> C'' *)

  Local Open Scope reindexing_forward_scope.

  Local Lemma unicity_gg'
    {a' b' c': C'} {f' : a' --> b'} {g' : c' --> a'}
    {x' : D' a'} {y' : D' b'} {z' : D' c'} 
    (ff' : x' -->[f'] y') (gg' : z' -->[g'] x') (hh' : z' -->[g' · f'] y')
    e
    (Hyp1 : ∏ g : C ⟦ ↙z', ↙x' ⟧, 
    (# F g = double_transport (!¤z') (!¤x') g') × (g · ↙ff' = ↙hh') -> 
    ↙gg' = g)
    (Hyp2 : ∏ (gg : ←z' -->[ ↙gg' ] ←x'), 
    (gg ;; ←ff')%mor_disp = transportb (mor_disp ←z' ←y') e ←hh' -> 
    ←gg' = gg)
    : ∏ gg'_bis : z' -->[ g'] x', (gg'_bis ;; ff')%mor_disp = hh' ->
    gg'_bis = gg'.
  Proof.
    intros gg'_bis p.
    induction gg'_bis as (g_bis, (pg_bis, gg_bis)).
    assert (↙gg' = g_bis) as eq_g.
    { apply Hyp1.
      split.
      - exact (double_transport_transpose pg_bis).
      - exact (maponpaths pr1 p). 
    }
    destruct eq_g.
    assert (¤gg' = pg_bis) as eq_pg.
    { apply uip.
      apply homset_property. }
    destruct eq_pg.
    assert (←gg' = gg_bis) as eq_gg.
    { apply Hyp2.
      specialize (transportb_transpose_right (fiber_paths p)) as X.
      etrans. apply (transportb_transpose_right (fiber_paths X)).
      etrans. apply (maponpaths (λ f, f _) (transportf_const _ _)). cbn.
      etrans. apply pr2_transportf. cbn.
      unfold transportb.
      apply two_arg_paths.
      - apply uip. apply homset_property.
      - reflexivity. 
    }
    destruct eq_gg.
    reflexivity.
  Qed.

  Local Lemma commute_in_C'
    {a' b' c': C'} {f' : a' --> b'} {g' : c' --> a'}
    {x' : D' a'} {y' : D' b'} {z' : D' c'}
    (ff' : x' -->[f'] y') (hh' : z' -->[g' · f'] y')
    : # F ↙hh' = double_transport (! ¤z') (! ¤x') g' · # F ↙ff'.
  Proof.
    etrans. apply (double_transport_transpose (¤hh')).
    apply pathsinv0.
    etrans. apply (maponpaths (λ f0', _ · f0') (double_transport_transpose (¤ff'))).
    apply double_transport_compose.
  Qed.

  Local Lemma commute_in_D'
    {a' b' c': C'} {f' : a' --> b'} {g' : c' --> a'}
    {x' : D' a'} {y' : D' b'} {z' : D' c'}
    (ff' : x' -->[f'] y') (hh' : z' -->[g' · f'] y')
    (Hyp1 : ∑ φ : C ⟦ ↙ (z'), ↙ (x') ⟧,
    (# F φ = double_transport (! ¤z') (! ¤x') g') × (φ · ↙ff' = ↙hh'))
    (Hyp2 : ∑ gg : ←z' -->[pr1 Hyp1] ←x',
    (gg ;; ←ff')%mor_disp = transportb (mor_disp ←z' ←y') (pr22 Hyp1) ←hh')
    (g:= pr1 Hyp1)
    (pg := double_transport_transpose' (pr12 Hyp1))
    (gg := pr1 Hyp2)
    (gg' := g,, pg,,gg : z' -->[ g'] x')
    : (gg' ;; ff')%mor_disp = hh'.
  Proof.
    apply (total2_paths_f (pr22 Hyp1 : ↙(gg' ;; ff')%mor_disp = ↙hh')).
    assert (pr1 (transportf (λ f , 
    ( double_transport ¤z' ¤y' (# F f) =  g' · f' ) × ( ←z' -->[ f] ←y'))
    (pr22 Hyp1) (pr2 (gg' ;; ff')%mor_disp)) = ¤ hh').
    { apply uip. apply homset_property. }
    apply (total2_paths_f X).
    etrans. apply (maponpaths (λ f, f _) (transportf_const _ _)). cbn.
    etrans. apply pr2_transportf. cbn.
    exact (transportf_transpose_left (pr2 Hyp2)).
  Qed.

  Lemma is_cartesian_reindexing_forward_of_cleaving
    {a' b' : C'} {f' : a' --> b'}
    {x' : D' a'} {y' : D' b'} (ff' : x' -->[f'] y')
    (st_car : is_cartesian_sfib F (↙ff')) (car : is_cartesian (←ff'))
    : is_cartesian ff'.
  Proof.
    intros c' g' z' hh'.
    (* introduction of variables *)
    set (Hyp1 := st_car (↙z') (↙hh') (double_transport (!¤z') (!¤x') g') (commute_in_C' ff' hh')).
    set (Hyp2 := car (↙z') (pr11 Hyp1) (←z') (transportb (mor_disp _ _) (pr221 Hyp1) (←hh'))).
    set (g:= pr11 Hyp1).
    set (pg := double_transport_transpose' (pr121 Hyp1)).
    set (gg := pr11 Hyp2).
    (* introduction of gg' *)
    set (gg' := (g,, pg,, gg) : z' -->[ g'] x').
    (* proof that gg' is unique *)
    apply (unique_exists gg' (commute_in_D' ff' hh' (pr1 Hyp1) (pr1 Hyp2))).
    intro gg'_bis.
    - apply homsets_disp.
    - exact (unicity_gg' ff' gg' hh' (pr221 Hyp1) 
      (λ g0, uniqueExists (b:= g0) Hyp1 (pr21 Hyp1)) 
      (λ gg0, uniqueExists (b:= gg0) Hyp2 (pr21 Hyp2))).
  Defined.

  Theorem is_cleaving_reindexing_forward_of_cleaving 
    (cl:cleaving D) (st: street_fib F) (univ : is_univalent C')
    : cleaving D'.
  Proof.
    intros b' a' f' y'.
    (* introduction of variables *)
    set (st_fib := st ↙y' a' (transportb _ ¤y' f')).
    set (a := pr1 st_fib).
    set (f := pr112 st_fib : C ⟦ a, ↙y' ⟧). 
    set (px := isotoid C' univ (pr212 st_fib) : F a = a').
    set (cl_fib := cl ↙y' a f ←y').
    set (x := pr1 cl_fib).
    set (ff := pr12 cl_fib : x -->[f] ←y').
    assert (double_transport px ¤y' (# F f) = f') as pf.
    { unfold double_transport. 
      apply transportf_transpose_left.
      etrans. apply transportf_isotoid.
      apply z_iso_inv_on_right.
      exact (pr122 st_fib). }
    set (x' := (a,, px,, x) : D' a').
    set (ff' := (f,, pf,, ff) : x' -->[f'] y').
    (*cartesian lift*)
    exists x'.
    exists ff'.
    (*is cartesian *)
    apply (is_cartesian_reindexing_forward_of_cleaving ff' (pr222 st_fib) cl_fib).
  Defined.

  Local Close Scope reindexing_forward_scope.

End fibrations_and_reindexing_forward.
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)


(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

(* End of file. *)
