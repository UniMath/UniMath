
(* reindexing forward (reindexig_f) for displayed categories 
    and the universal property that it respects.*)

(*    D -- functor reindexing_f --> reindexing_f *)
(*    ↓            ↓             ↓     *)
(*    C ---------- F ----------> C'    *)

(* May 2023 *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Propositions.

Require Export UniMath.CategoryTheory.Core.Categories.
Require Export UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.TransportMorphisms.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.


Local Open Scope cat. 

(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

Definition transportf_mor {C:category} {a b a' b':C} 
(p:a=a') (q:b=b') (x:a-->b) : a'-->b'
  := transportf (precategory_morphisms a') q (transportf (λ z, z--> b) p x). 

Definition transportf_mor_disp {C C':category} {D':disp_cat C'} {a b a' b':C}
(F:functor C C') (f:a-->b)  (x:D' (F a)) (y:D' (F b)) (p:a=a') (q:b=b')  
    : x-->[#F f]y 
    -> transportf (λ z, D' (F z)) p x 
                -->[# F (transportf_mor p q f)] 
                        transportf (λ z, D' (F z)) q y.
Proof.
  intro Df.
  destruct p, q.
  exact Df.
Defined.

Notation "X ◦ Y" := (disp_functor_composite X Y) (at level 45): cat. 

Declare Scope reindexing_f_scope.
Notation  "↙ x" := (pr1 x)  (at level 0):reindexing_f_scope. 
Notation  "← x" := (pr2 (pr2 x)) (at level 0):reindexing_f_scope.
Notation "¤ x" := (pr1(pr2 x)) (at level 0):reindexing_f_scope.

(* Recreate base objects from an object x' over c' of the reindexing_f *)
(*  x:= (← x') -----?-----> x' =: (↙ x', ¤ x', ← x') *)
(*    ↓                     ↓                        *)
(*  c:= (↙ x') -----F-----> c'                       *)
(* ¤ x: F c = c'   *)

(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
Section reindexing_f.
Local Open Scope reindexing_f_scope.

Context {C C':category} (D :disp_cat C) (F :functor C C').

(*    D -- functor reindexing_f --> reindexing_f *)
(*    ↓            ↓             ↓     *)
(*    C ---------- F ----------> C'    *)


Definition reindexing_f_ob_mor : disp_cat_ob_mor C'.
Proof.
  use make_disp_cat_ob_mor.
  - exact (λ c', ∑c:C,(F c=c' × ob_disp D c)).
  - intros a' b' x' y' f'.
    exact (∑f:(↙ x')-->(↙ y'),
           (transportf_mor (¤ x') (¤ y') (# F f)=f' ×
            (← x')-->[f](← y'))).
Defined.


(* Some lemmas to create the theorem to caracterize the equality of reindexing_f morphisms*)
Lemma pr1_transportf_reindexing_f {a' b':C'} {f' g': C' ⟦ a', b' ⟧} 
{x' :ob_disp reindexing_f_ob_mor a'} {y' :ob_disp reindexing_f_ob_mor b'} 
{Df' : x' -->[ f'] y'} {Dg' : x' -->[ g'] y'}
    : ∏(p: g'=f'), ↙ Df'= ↙ Dg' → 
        ↙ Df' = ↙ (transportf _ p  Dg').
Proof.
  intros p e.
  unfold mor_disp. cbn.
  rewrite PartA.pr1_transportf.
  rewrite transportf_const.
  exact e.
Qed.
   
Lemma pr1_pr2_transportf_reindexing_f {a' b':C'} {f' g': C' ⟦ a', b' ⟧} 
{x' :ob_disp reindexing_f_ob_mor a'} {y' :ob_disp reindexing_f_ob_mor b'}
{Df' : x' -->[ f'] y'} {Dg' : x' -->[ g'] y'} (e:↙ Dg' =↙ Df') 
    : ∏ p: f' = g',
        ¤ (transportf _ p Df') = 
        transportf (λ f0:C ⟦↙ x',↙ y'⟧, 
            transportf_mor (¤ x') (¤ y') (# F f0)=g') 
                (pr1_transportf_reindexing_f p e) 
                    (¤ Dg'). 
Proof.
  intro.
  destruct p. cbn.
  induction Df' as (f,(pf,Df)).
  induction Dg' as (g,(pg,Dg)).
  cbn in *.
  induction e. cbn.
  apply homset_property.
Qed.    

Lemma pr2_pr2_transportf_reindexing_f {a' b':C'} {f' g': C' ⟦ a', b' ⟧} 
{x' :ob_disp reindexing_f_ob_mor a'} {y' :ob_disp reindexing_f_ob_mor b'}
{Df' : x' -->[ f'] y'} {Dg' : x' -->[ g'] y'} (e:↙ Df' =↙ Dg') 
    : ∏ p: f' = g',
    ← Dg' = transportf _ e (← Df') ->
        ← (transportf _ p Df') = 
       transportf _ (pr1_transportf_reindexing_f p (!e)) (← Dg'). 
Proof.
  intros p H.
  rewrite H.
  destruct p. cbn.
  apply PartA.transportf_transpose_right.
  unfold transportb.
  apply two_arg_paths.
  - apply uip.
    apply homset_property.
  - reflexivity.
Qed.


Lemma pr2_transportf_reindexing_f {a' b':C'} {f' g': C' ⟦ a', b' ⟧} 
{x' :ob_disp reindexing_f_ob_mor a'} {y' :ob_disp reindexing_f_ob_mor b'}
{Df' : x' -->[ f'] y'} 
   : ∏ p: f' = g', 
        pr2 (transportf _ p Df') =
        ¤ (transportf _ p Df'),, ← (transportf (mor_disp x' y') p Df').
Proof.
  intro.
  destruct p.
  rewrite idpath_transportf.
  exact (idpath (pr2 Df')). 
Qed.


(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*Theorem about the equality of reindexing_f morphisms*)
Theorem reindexing_f_paths_f_mor {a' b':C'} 
{x' :ob_disp reindexing_f_ob_mor a'}
{y' :ob_disp reindexing_f_ob_mor b'}
{f': C' ⟦ a', b' ⟧} {g': C' ⟦ a', b' ⟧} {p:g'=f'}
(Df' : x' -->[ f'] y') (Dg' : x' -->[ g'] y') (e:↙ Dg' = ↙ Df')
    :← Df' = transportf _ e (← Dg')
        -> (Df'=transportf _ p Dg').
Proof.
  intro H.
  apply (total2_paths_f (pr1_transportf_reindexing_f p (!e))).
  cbn; cbn in e, H.
  rewrite (pr2_transportf_reindexing_f p).
  rewrite transportf_dirprod.
  rewrite (pr1_pr2_transportf_reindexing_f (!e)).
  apply maponpaths.
  rewrite (pr2_pr2_transportf_reindexing_f e p H).
  rewrite <- (pr1_transportf_reindexing_f p (!e)).
  cbn.
  exact (idpath (← Df')). 
Qed.
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)


Lemma reindexing_f_id {c': C'} {x' : ob_disp reindexing_f_ob_mor c'}
    : identity c' = transportf_mor (¤ x') (¤ x') (# F (identity (↙ x'))).
Proof.
  destruct (¤ x').
  apply pathsinv0. 
  apply functor_id_id.
  reflexivity.
Defined.


Lemma reindexing_f_comp {a' b' c': C'} 
{x' : ob_disp reindexing_f_ob_mor a'} {y' : ob_disp reindexing_f_ob_mor b'}
{z' : ob_disp reindexing_f_ob_mor c'} {f':C' ⟦ a', b' ⟧} {g':C' ⟦ b', c' ⟧}
{Df':  x' -->[ f'] y'} {Dg': y' -->[ g'] z'}
    :f' · g' = transportf_mor (¤ x') (¤ z') (# F (↙ Df' · ↙ Dg')).
Proof.
  destruct (¤ Df'), (¤ Dg').
  destruct (¤ x'), (¤ y'), (¤ z'). cbn.
  apply pathsinv0.
  apply functor_comp.
Defined.

Definition reindexing_f_id_comp : disp_cat_id_comp C' reindexing_f_ob_mor.
Proof.
  use tpair.
  - intros c' x'.
    exists (identity (↙ x')).
    use tpair.
    * apply (! reindexing_f_id). 
    * cbn.
      exact (id_disp (← x')).
  - intros a' b' c' f' g' x' y' z'.
    intros Df' Dg'.
    exists ((↙ Df')·(↙ Dg')). 
    use tpair. 
    * apply (! reindexing_f_comp).
    * cbn.
      exact (comp_disp (← Df') (← Dg')).
Defined.


Definition reindexing_f_disp_cat_data : disp_cat_data C'
    := (reindexing_f_ob_mor,, reindexing_f_id_comp).


Local Open Scope mor_disp. 

Definition reindexing_f_disp_cat_axioms : disp_cat_axioms C' reindexing_f_disp_cat_data.
Proof.
  repeat apply tpair.
  - intros a' b' f' x' y' Df'.
    apply (reindexing_f_paths_f_mor (id_disp x' ;; Df') Df' (! id_left (↙ Df'))).
    exact (id_left_disp (← Df')).
  - intros a' b' f' x' y' Df'.
    apply (reindexing_f_paths_f_mor (Df';; id_disp y') Df' (! id_right (↙ Df'))).
    exact (id_right_disp (← Df')).
  - intros a' b' c' d' f' g' h' x' y' z' w' Df' Dg' Dh'.
    apply (reindexing_f_paths_f_mor (Df' ;; (Dg' ;; Dh')) (Df' ;; Dg' ;; Dh') 
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


Local Close Scope reindexing_f_scope.
End reindexing_f.
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)


Definition reindexing_f {C C':category}
(D:disp_cat C) (F: functor C C') : disp_cat C'
    := (reindexing_f_disp_cat_data D F,, reindexing_f_disp_cat_axioms D F).


(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
Section functor_reindexing_f.

Context {C C':category} (D :disp_cat C) (F :functor C C').

(*    D -- functor reindexing_f --> reindexing_f *)
(*    ↓            ↓             ↓     *)
(*    C ---------- F ----------> C'    *)


Definition data_functor_reindexing_f : disp_functor_data F D (reindexing_f D F).
Proof.
  use tpair.
  - exact (λ (c:C) (d: D c), (c,, idpath (F c),,  d)).
  - intros a b x y f Df.
    exact (f ,,idpath (# F f),, Df).
Defined.

Local Open Scope mor_disp. 

Definition axioms_reindexing_f_functor: disp_functor_axioms data_functor_reindexing_f.
Proof.
  use tpair.
  - intros a x.
    apply (reindexing_f_paths_f_mor D F (♯ (data_functor_reindexing_f) (id_disp x)) 
                                    (id_disp (data_functor_reindexing_f a x)) 
                                    (idpath _)).
    exact (idpath (id_disp x)).
  - intros a b c x y z f g Df Dg.
    apply (reindexing_f_paths_f_mor D F (♯ (data_functor_reindexing_f) (Df;;Dg))
                                    (♯ data_functor_reindexing_f Df ;; ♯ data_functor_reindexing_f Dg)
                                    (idpath _)).
    exact (idpath (Df;;Dg)).
Qed.

Local Close Scope mor_disp. 
End functor_reindexing_f.
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)


Definition functor_reindexing_f {C C':category} (D:disp_cat C) (F:functor C C')
  : disp_functor F D (reindexing_f D F)
  := (data_functor_reindexing_f D F,, axioms_reindexing_f_functor D F).

 
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
Section functor_universal_property_reindexing_f.

Context {C C' C'': category} {D:disp_cat C} {F: functor C C'}.
Let D' := reindexing_f D F. Let DF := functor_reindexing_f D F.
Context (H: functor C' C'') (D'': disp_cat C'') (DG: disp_functor (F ∙ H) D D'').

(*      ---------------- DG ---------------->     *)
(*    D -- DF --> D' -- functor univ prop --> D'' *)
(*    ↓    ↓      ↓             ↓             ↓   *)
(*    C -- F  --> C' ---------- H ----------> C'' *)

Local Open Scope reindexing_f_scope.

Definition data_functor_univ_prop_reindexing_f: disp_functor_data H D' D''.
Proof.
  use tpair.
  - intros c' d'.
    exact (transportf (λ x, D'' (H x)) (¤ d') (DG  (↙ d') (← d'))).
  - intros a' b' x' y' f' Df'.
    apply (transportf (λ f0, mor_disp _ _ (# H f0)) (¤ Df')).
    apply transportf_mor_disp.
    exact ((♯ DG (← Df'))%mor_disp).
Defined.

Local Close Scope reindexing_f_scope.

Definition axioms_functor_univ_prop_reindexing_f
    : disp_functor_axioms data_functor_univ_prop_reindexing_f.
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
    destruct pf, pg.  cbn.
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


End functor_universal_property_reindexing_f.
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)


Definition functor_univ_prop_reindexing_f {C C' C'': category} {D:disp_cat C} {F: functor C C'}
(H: functor C' C'') (D'': disp_cat C'') (DG: disp_functor (F ∙ H) D D'')
    : disp_functor H (reindexing_f D F) D''
  := (data_functor_univ_prop_reindexing_f H D'' DG,,
        axioms_functor_univ_prop_reindexing_f H D'' DG).


(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
Section unicity_universal_property_reindexing_f.

Context {C C' C'': category} {D:disp_cat C} {F: functor C C'}.
Let D' := reindexing_f D F. Let DF := functor_reindexing_f D F.
Context (H: functor C' C'') (D'': disp_cat C'') (DG: disp_functor (F ∙ H) D D'').
Let DH := functor_univ_prop_reindexing_f H D'' DG.

(* Here we prove the unicity of DH*)
(*      -------- DG -------->     *)
(*    D -- DF --> D' -- DH --> D'' *)
(*    ↓    ↓      ↓     ↓      ↓   *)
(*    C -- F  --> C' -- H  --> C'' *)


Definition univ_prop_reindexing_f_eq : 
        disp_functor_composite DF DH= DG.
Proof.
  apply disp_functor_eq.
  reflexivity.
Defined.

Definition univ_prop_reindexing_f : 
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
         

Local Open Scope reindexing_f_scope.

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

Theorem unicity_univ_prop_reindexing_f : 
  ∏ DH' :disp_functor H D' D'',
  disp_nat_z_iso (disp_functor_composite DF DH') DG (nat_z_iso_id (F ∙ H)) ->
   disp_nat_z_iso DH' DH (nat_z_iso_id H).
Proof.
  intros DH' µ'.
  apply DH0_DH1_disp_nat_z_iso.
  apply (transportf _ (comp_nat_z_iso_id_left (nat_z_iso_id (F ∙ H)))).
  apply (disp_nat_z_iso_comp µ').
  apply (transportf _ nat_z_iso_inv_id).
  exact (disp_nat_z_iso_inv univ_prop_reindexing_f).
Defined.

Local Close Scope mor_disp. 
Local Close Scope reindexing_f_scope.
End unicity_universal_property_reindexing_f.
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)


(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

(* End of file. *)
