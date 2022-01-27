(**
A module for “displayed categories”, based over UniMath’s [CategoryTheory] library.

Roughly, a “displayed category _D_ over a category _C_” is analogous to “a family of types _Y_ indexed over a type _X_”.  A displayed category has a “total category” ∑ _C_ _D_, with a functor to _D_; and indeed displayed categories should be equivalent to categories over _D_, by taking fibers.

In a little more detail: if [D] is a displayed category over [C], then [D] has a type of objects indexed over [ob C], and for each [x y : C, f : x --> y, xx : D x, yy : D y], a type of “morphisms over [f] from [xx] to [yy]”.  The identity and composition (and axioms) for [D] all overlie the corresponding structure on [C].

Two major motivations for displayed categories:

- Pragmatically, they give a convenient tool for building categories of “structured objects”, and functors into such categories, encapsulating a lot of frequently-used constructions, and allowing for very modular proofs of e.g. saturation of such categories.
- More conceptually, they give a setting for defining Grothendieck fibrations and isofibrations without mentioning equality of objects.

Contents:

- Displayed categories: [disp_cat C]
  - various access functions, etc.
  - utility lemmas
  - isomorphisms
  - saturation
- Total categories (and their forgetful functors)
  - [total_category D]
  - [pr1_category D]
- Functors between displayed categories, over functors between their bases
  - [functor_lifting], [lifted_functor]
  - [disp_functor], [total_functor]
  - properties of functors: [disp_functor_ff], …
  - natural transformations: [disp_nat_trans], …
*)

(* TODO: this file has become large and unwieldy; should probably be split up.  Displayed functors can certainly be happily split off.  Should total cats stay here, or also be split out? *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.AxiomOfChoice.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Local Open Scope cat.
Local Open Scope cat_deprecated.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.

Local Open Scope type_scope.

(* Undelimit Scope transport. *)

(** * Displayed categories *)

(*
  Here is an iterated ∑-type that displays a logical structure equivalent to the
  type called disp_cat defined below.
*)

Definition disp_cat' (C : category) : UU :=
  ∑ (ob_disp : C -> UU)
    (mor_disp : ∏ {x y : C}, (x --> y) -> ob_disp x -> ob_disp y -> UU)
    (id_disp : ∏ {x : C} (xx : ob_disp x), mor_disp (identity x) xx xx)
    (comp_disp : ∏ {x y z : C} {f : x --> y} {g : y --> z}
                   {xx : ob_disp x} {yy : ob_disp y} {zz : ob_disp z},
                 mor_disp f xx yy -> mor_disp g yy zz -> mor_disp (f ;; g) xx zz)
    (id_left_disp : ∏ {x y} {f : x --> y} {xx} {yy} (ff : mor_disp f xx yy),
                    comp_disp (id_disp xx) ff
                    = transportb (λ g, mor_disp g xx yy) (id_left _) ff)
    (id_right_disp : ∏ {x y} {f : x --> y} {xx} {yy} (ff : mor_disp f xx yy),
                     comp_disp ff (id_disp yy)
                     = transportb (λ g, mor_disp g xx yy) (id_right _) ff)
    (assoc_disp : ∏ {x y z w} {f : x --> y} {g : y --> z} {h : z --> w}
                    {xx} {yy} {zz} {ww}
                    (ff : mor_disp f xx yy) (gg : mor_disp g yy zz) (hh : mor_disp h zz ww),
                  comp_disp ff (comp_disp gg hh)
                  = transportb (λ k, mor_disp k _ _) (assoc _ _ _)
                               (comp_disp (comp_disp ff gg) hh)),
  (* homsets_disp : *) ∏ x y (f : x --> y) xx yy, isaset (mor_disp f xx yy).

(** ** Definition *)

(** The actual definition is structured analogously to [category], as an iterated ∑-type:

- [disp_cat]
  - [disp_cat_data]
    - [disp_cat_ob_mor]
      - [ob_disp]
      - [mod_disp]
    - [disp_cat_id_comp]
      - [id_disp]
      - [comp_disp]
  - [disp_cat_axioms]
    - [id_left_disp]
    - [id_right_disp]
    - [assoc_disp]
    - [homsets_disp]

*)

Section Disp_Cat.

Definition disp_cat_ob_mor (C : precategory_ob_mor)
  := ∑ (obd : C -> UU), (∏ x y:C, obd x -> obd y -> (x --> y) -> UU).

Definition make_disp_cat_ob_mor
           (C : precategory_ob_mor)
           (obd : C -> UU)
           (mord : ∏ x y:C, obd x -> obd y -> (x --> y) -> UU)
  : disp_cat_ob_mor C
  := obd,, mord.

Definition ob_disp {C: precategory_ob_mor} (D : disp_cat_ob_mor C) : C -> UU := pr1 D.
Coercion ob_disp : disp_cat_ob_mor >-> Funclass.

Definition mor_disp {C: precategory_ob_mor} {D : disp_cat_ob_mor C}
  {x y} xx yy (f : x --> y)
:= pr2 D x y xx yy f : UU.

Local Notation "xx -->[ f ] yy" := (mor_disp xx yy f) (at level 50, left associativity, yy at next level).

Definition disp_cat_id_comp (C : precategory_data)
  (D : disp_cat_ob_mor C)
  : UU
:= (forall (x:C) (xx : D x), xx -->[identity x] xx)
  × (forall (x y z : C) (f : x --> y) (g : y --> z) (xx:D x) (yy:D y) (zz:D z),
           (xx -->[f] yy) -> (yy -->[g] zz) -> (xx -->[f ;; g] zz)).

Definition disp_cat_data C := total2 (disp_cat_id_comp C).

Definition disp_cat_ob_mor_from_disp_cat_data {C: precategory_data}
  (D : disp_cat_data C)
  : disp_cat_ob_mor C
:= pr1 D.

Coercion disp_cat_ob_mor_from_disp_cat_data :
 disp_cat_data >-> disp_cat_ob_mor.

Definition id_disp {C: precategory_data} {D : disp_cat_data C} {x:C} (xx : D x)
  : xx -->[identity x] xx
:= pr1 (pr2 D) x xx.

Definition comp_disp {C: precategory_data} {D : disp_cat_data C}
  {x y z : C} {f : x --> y} {g : y --> z}
  {xx : D x} {yy} {zz} (ff : xx -->[f] yy) (gg : yy -->[g] zz)
  : xx -->[f;;g] zz
:= pr2 (pr2 D) _ _ _ _ _ _ _ _ ff gg.

Declare Scope mor_disp_scope.
Local Notation "ff ;; gg" := (comp_disp ff gg)
  (at level 50, left associativity, format "ff  ;;  gg")
  : mor_disp_scope.
Delimit Scope mor_disp_scope with mor_disp.
Bind Scope mor_disp_scope with mor_disp.
Local Open Scope mor_disp_scope.

Definition disp_cat_axioms (C : category) (D : disp_cat_data C)
  : UU
:= (∏ x y (f : x --> y) (xx : D x) yy (ff : xx -->[f] yy),
     id_disp _ ;; ff
     = transportb _ (id_left _) ff)
   × (∏ x y (f : x --> y) (xx : D x) yy (ff : xx -->[f] yy),
     ff ;; id_disp _
     = transportb _ (id_right _) ff)
   × (∏ x y z w f g h (xx : D x) (yy : D y) (zz : D z) (ww : D w)
        (ff : xx -->[f] yy) (gg : yy -->[g] zz) (hh : zz -->[h] ww),
     ff ;; (gg ;; hh)
     = transportb _ (assoc _ _ _) ((ff ;; gg) ;; hh))
   × (∏ x y f (xx : D x) (yy : D y), isaset (xx -->[f] yy)).


Definition disp_cat (C : category) := total2 (disp_cat_axioms C).

Definition disp_cat_data_from_disp_cat {C} (D : disp_cat C)
 := pr1 D : disp_cat_data C.
Coercion disp_cat_data_from_disp_cat : disp_cat >-> disp_cat_data.


(** All the axioms are given in two versions, [foo : T1 = transportb e T2] and [foo_var : T2 = transportf e T1], so that either direction can be invoked easily in “compute left-to-right” style. *)

(* TODO: consider naming conventions? *)
(* TODO: maybe would be better to have a single [pathsinv0_dep] lemma, or something. *)

Definition id_left_disp {C} {D : disp_cat C}
  {x y} {f : x --> y} {xx : D x} {yy} (ff : xx -->[f] yy)
: id_disp _ ;; ff = transportb _ (id_left _) ff
:= pr1 (pr2 D) _ _ _ _ _ _.

Definition id_left_disp_var {C} {D : disp_cat C}
  {x y} {f : x --> y} {xx : D x} {yy} (ff : xx -->[f] yy)
: ff = transportf _ (id_left _) (id_disp _ ;; ff).
Proof.
  apply transportf_transpose_right.
  apply @pathsinv0, id_left_disp.
Qed.

Definition id_right_disp {C} {D : disp_cat C}
  {x y} {f : x --> y} {xx : D x} {yy} (ff : xx -->[f] yy)
  : ff ;; id_disp _ = transportb _ (id_right _) ff
:= pr1 (pr2 (pr2 D)) _ _ _ _ _ _.

Definition id_right_disp_var {C} {D : disp_cat C}
  {x y} {f : x --> y} {xx : D x} {yy} (ff : xx -->[f] yy)
  : ff = transportf _ (id_right _) (ff ;; id_disp _).
Proof.
  apply transportf_transpose_right.
  apply @pathsinv0, id_right_disp.
Qed.

Definition assoc_disp {C} {D : disp_cat C}
  {x y z w} {f} {g} {h} {xx : D x} {yy : D y} {zz : D z} {ww : D w}
  (ff : xx -->[f] yy) (gg : yy -->[g] zz) (hh : zz -->[h] ww)
: ff ;; (gg ;; hh) = transportb _ (assoc _ _ _) ((ff ;; gg) ;; hh)
:= pr1 (pr2 (pr2 (pr2 D))) _ _ _ _ _ _ _ _ _ _ _ _ _ _.

Definition assoc_disp_var {C} {D : disp_cat C}
  {x y z w} {f} {g} {h} {xx : D x} {yy : D y} {zz : D z} {ww : D w}
  (ff : xx -->[f] yy) (gg : yy -->[g] zz) (hh : zz -->[h] ww)
: (ff ;; gg) ;; hh = transportf _ (assoc _ _ _) (ff ;; (gg ;; hh)).
Proof.
  apply pathsinv0, transportf_pathsinv0.
  apply pathsinv0, assoc_disp.
Defined.

Definition homsets_disp {C} {D : disp_cat C} {x y} (f : x --> y) (xx : D x) (yy : D y)
  : isaset (xx -->[f] yy) := pr2 (pr2 (pr2 (pr2 D))) _ _ _ _ _.

(** ** Utility lemmas *)
Section Lemmas.

(** [etrans_disp]: a version of [etrans_dep] for use when the equality transport in the RHS of the goal is already present, and not of the form produced by [etrans_dep], so [etrans_dep] doesn’t apply.  Where possible, [etrans_dep] should still be used, since it *produces* a RHS, whereas this does not (and so leads to lots of unsolved existentials if used where not needed).

NOTE: as with [etrans_dep], proofs using [etrans_disp] seem to typecheck more slowly than proofs using [etrans] plus other lemmas directly. *)
Lemma pathscomp0_disp {C} {D : disp_cat C}
  {x y} {f f' f'' : x --> y} (e : f' = f) (e' : f'' = f') (e'' : f'' = f)
  {xx : D x} {yy}
  (ff : xx -->[f] yy) (ff' : xx -->[f'] yy) (ff'' : xx -->[f''] yy)
: (ff = transportf _ e ff') -> (ff' = transportf _ e' ff'')
  -> ff = transportf _ e'' ff''.
Proof.
  intros ee ee'.
  etrans. eapply pathscomp0_dep. apply ee. apply ee'.
  apply maponpaths_2, homset_property.
Qed.

Tactic Notation "etrans_disp" := eapply @pathscomp0_disp.

Lemma isaprop_disp_cat_axioms (C : category) (D : disp_cat_data C)
  : isaprop (disp_cat_axioms C D).
Proof.
  apply isofhlevelsn.
  intro X.
  set (XR := ( _ ,, X) : disp_cat C).
  apply isofhleveltotal2.
  - repeat (apply impred; intro).
    apply (@homsets_disp _ XR).
  - intros x.
    repeat (apply isofhleveldirprod); repeat (apply impred; intro).
    + apply (@homsets_disp _ XR).
    + apply (@homsets_disp _ XR).
    + apply isapropiscontr.
Qed.

(* TODO: consider naming of following few transport lemmas *)
Lemma mor_disp_transportf_postwhisker
    {C : precategory} {D : disp_cat_data C}
    {x y z : C} {f f' : x --> y} (ef : f = f') {g : y --> z}
    {xx : D x} {yy} {zz} (ff : xx -->[f] yy) (gg : yy -->[g] zz)
  : (transportf _ ef ff) ;; gg
  = transportf _ (cancel_postcomposition _ _ g ef) (ff ;; gg).
Proof.
  destruct ef; apply idpath.
Qed.

Lemma mor_disp_transportf_prewhisker
    {C : precategory} {D : disp_cat_data C}
    {x y z : C} {f : x --> y} {g g' : y --> z} (eg : g = g')
    {xx : D x} {yy} {zz} (ff : xx -->[f] yy) (gg : yy -->[g] zz)
  : ff ;; (transportf _ eg gg)
  = transportf _ (maponpaths (compose f) eg) (ff ;; gg).
Proof.
  destruct eg; apply idpath.
Qed.

(* TODO: use the following lemmas in more of the displayed category proofs. Most instances of [mor_disp_transportf_Xwhisker] are places that can be simplified with these. *)
(* TODO: consider naming of [cancel_Xcomposition_disp].  Currently follows the UniMath base lemmas, but those are bad names — cancellation properties traditionally mean things like like [ ax = ay -> x = y ], whereas these lemmas are the converse of that. *)
Lemma cancel_postcomposition_disp {C} {D : disp_cat C}
  {x y z} {f f' : x --> y} {e : f' = f} {g : y --> z}
  {xx : D x} {yy} {zz}
  {ff : xx -->[f] yy} {ff' : xx -->[f'] yy} (gg : yy -->[g] zz)
  (ee : ff = transportf _ e ff')
: ff ;; gg = transportf _ (cancel_postcomposition _ _ g e) (ff' ;; gg).
Proof.
  etrans. apply maponpaths_2, ee.
  apply mor_disp_transportf_postwhisker.
Qed.

Lemma cancel_precomposition_disp {C} {D : disp_cat C}
  {x y z} {f : x --> y} {g g' : y --> z} {e : g' = g}
  {xx : D x} {yy} {zz}
  (ff : xx -->[f] yy) {gg : yy -->[g] zz} {gg' : yy -->[g'] zz}
  (ee : gg = transportf _ e gg')
: ff ;; gg = transportf _ (cancel_precomposition _ _ _ _ _ _ f e) (ff ;; gg').
Proof.
  etrans. apply maponpaths, ee.
  apply mor_disp_transportf_prewhisker.
Qed.

End Lemmas.

End Disp_Cat.

(** Redeclare sectional notations globally. *)
Notation "xx -->[ f ] yy" := (mor_disp xx yy f) (at level 50, left associativity, yy at next level).

Declare Scope mor_disp_scope.
Notation "ff ;; gg" := (comp_disp ff gg)
  (at level 50, left associativity, format "ff  ;;  gg")
  : mor_disp_scope.
Delimit Scope mor_disp_scope with mor_disp.
Bind Scope mor_disp_scope with mor_disp.
Local Open Scope mor_disp_scope.

(** A useful notation for hiding the huge irrelevant equalities that occur in algebra of displayed categories.  For individual proofs, use [Open Scope hide_transport_scope.] at the start, and then [Close Scope hide_transport_scope.] afterwards.  For whole files/sections, use [Local Open Scope hide_transport_scope.]

Level is chosen to bind *tighter* than categorical composition, for readability. *)
(* TODO: consider symbol(s) used. *)
Declare Scope hide_transport_scope.
Notation "#? x" := (transportf _ _ x) (at level 45) : hide_transport_scope.
Notation "#?' x" := (transportb _ _ x) (at level 45) : hide_transport_scope.

(** ** Isomorphisms (and lemmas) *)

Section Isos.

Definition is_iso_disp {C : precategory} {D : disp_cat_data C}
    {x y : C} (f : iso x y) {xx : D x} {yy} (ff : xx -->[f] yy)
  : UU
:= ∑ (gg : yy -->[inv_from_iso f] xx),
     gg ;; ff = transportb _ (iso_after_iso_inv _) (id_disp _)
     × ff ;; gg = transportb _ (iso_inv_after_iso _) (id_disp _).

Definition iso_disp {C : precategory} {D : disp_cat_data C}
    {x y : C} (f : iso x y) (xx : D x) (yy : D y)
  := ∑ ff : xx -->[f] yy, is_iso_disp f ff.

Definition make_iso_disp {C : precategory} {D : disp_cat_data C}
    {x y : C} {f : iso x y} {xx : D x} {yy : D y}
    (ff : xx -->[f] yy) (is : is_iso_disp f ff)
    : iso_disp _ _ _
  := (ff,, is).


Definition mor_disp_from_iso {C : precategory} {D : disp_cat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y}
    (i : iso_disp f xx yy) : _ -->[ _ ] _ := pr1 i.
Coercion mor_disp_from_iso : iso_disp >-> mor_disp.

Definition is_iso_disp_from_iso {C : precategory} {D : disp_cat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y}
    (i : iso_disp f xx yy) : is_iso_disp f i := pr2 i.
Coercion is_iso_disp_from_iso : iso_disp >-> is_iso_disp.

Definition inv_mor_disp_from_iso {C : precategory} {D : disp_cat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y}
    {ff : xx -->[f] yy} (i : is_iso_disp f ff)
  : _ -->[ _ ] _ := pr1 i.

Definition iso_disp_after_inv_mor {C : precategory} {D : disp_cat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y}
    {ff : xx -->[f] yy} (i : is_iso_disp f ff)
  : inv_mor_disp_from_iso i ;; ff
    = transportb _ (iso_after_iso_inv _) (id_disp _).
Proof.
  apply (pr2 i).
Qed.

Definition inv_mor_after_iso_disp {C : precategory} {D : disp_cat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y}
    {ff : xx -->[f] yy} (i : is_iso_disp f ff)
  : ff ;; inv_mor_disp_from_iso i
    = transportb _ (iso_inv_after_iso _) (id_disp _).
Proof.
  apply (pr2 (pr2 i)).
Qed.

Lemma isaprop_is_iso_disp {C : category} {D : disp_cat C}
    {x y : C} (f : iso x y) {xx : D x} {yy} (ff : xx -->[f] yy)
  : isaprop (is_iso_disp f ff).
Proof.
  apply invproofirrelevance; intros i i'.
  apply subtypePath.
  - intros gg. apply isapropdirprod; apply homsets_disp.
  (* uniqueness of inverses *)
  (* TODO: think about better lemmas for this sort of calculation?
  e.g. all that repeated application of [transport_f_f], etc. *)
  - destruct i as [gg [gf fg]], i' as [gg' [gf' fg']]; simpl.
    etrans. eapply pathsinv0, transportfbinv.
    etrans. apply maponpaths, @pathsinv0, id_right_disp.
    etrans. apply maponpaths, maponpaths.
      etrans. eapply pathsinv0, transportfbinv.
      apply maponpaths, @pathsinv0, fg'.
    etrans. apply maponpaths, mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths, assoc_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths, maponpaths_2, gf.
    etrans. apply maponpaths, mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths, id_left_disp.
    etrans. apply transport_f_f.
    use (@maponpaths_2 _ _ _ (transportf _) _ (idpath _)).
    apply homset_property.
Qed.

Lemma isaset_iso_disp {C : category} {D : disp_cat C}
  {x y} (f : iso x y) (xx : D x) (yy : D y)
  : isaset (iso_disp f xx yy).
Proof.
  apply isaset_total2.
  - apply homsets_disp.
  - intros. apply isasetaprop, isaprop_is_iso_disp.
Qed.

Lemma eq_iso_disp {C : category} {D : disp_cat C}
    {x y : C} (f : iso x y)
    {xx : D x} {yy} (ff ff' : iso_disp f xx yy)
  : pr1 ff = pr1 ff' -> ff = ff'.
Proof.
  apply subtypePath; intro; apply isaprop_is_iso_disp.
Qed.

Lemma is_iso_disp_transportf {C : category} {D : disp_cat C}
    {x y : C} {f f' : iso x y} (e : f = f')
    {xx : D x} {yy} {ff : xx -->[f] yy}
    (is : is_iso_disp _ ff)
  : is_iso_disp f' (transportf _ (maponpaths _ e) ff).
Proof.
  induction e.
  apply is.
Qed.

Lemma transportf_iso_disp {C : category} {D : disp_cat C}
    {x y : C} {xx : D x} {yy}
    {f f' : iso x y} (e : f = f')
    (ff : iso_disp f xx yy)
  : pr1 (transportf (λ g, iso_disp g _ _) e ff)
  = transportf _ (maponpaths pr1 e) (pr1 ff).
Proof.
  destruct e; apply idpath.
Qed.

Definition is_iso_inv_from_iso_disp {C : category} {D : disp_cat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y}
    (i : iso_disp f xx yy)
    :
    is_iso_disp (iso_inv_from_iso f) (inv_mor_disp_from_iso i).
Proof.
  use tpair.
  - change ( xx -->[ iso_inv_from_iso (iso_inv_from_iso f)] yy).
    set (XR := transportb (mor_disp xx yy )
                          (maponpaths pr1 (iso_inv_iso_inv _ _ f))).
    apply XR. apply i.
  - cbn.
    split.
    + abstract (
      etrans ;[ apply mor_disp_transportf_postwhisker |];
      etrans ; [ apply maponpaths; apply (inv_mor_after_iso_disp i)  | ];
      etrans ;[ apply transport_f_f |];
      apply transportf_comp_lemma; apply transportf_comp_lemma_hset;
      try apply homset_property; apply idpath ).
    + abstract (
      etrans ;[ apply mor_disp_transportf_prewhisker |];
      etrans ;[ apply maponpaths; apply (iso_disp_after_inv_mor i) |];
      etrans ;[ apply transport_f_f |];
      apply transportf_comp_lemma; apply transportf_comp_lemma_hset;
      try apply homset_property; apply idpath ).
Defined.

Definition is_iso_inv_from_is_iso_disp {C : category} {D : disp_cat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y}
    (ff : xx -->[f] yy)
    (i : is_iso_disp f ff)
    :
    is_iso_disp (iso_inv_from_iso f) (inv_mor_disp_from_iso i).
Proof.
  apply (is_iso_inv_from_iso_disp (ff ,, i)).
Defined.

Definition iso_inv_from_iso_disp {C : category} {D : disp_cat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y}
    (i : iso_disp f xx yy)
    :
    iso_disp (iso_inv_from_iso f) yy xx.
Proof.
  exists (inv_mor_disp_from_iso i).
  apply is_iso_inv_from_iso_disp.
Defined.

Definition iso_disp_comp {C : category} {D : disp_cat C}
    {x y z : C} {f : iso x y} {g : iso y z} {xx : D x} {yy : D y} {zz : D z}
    (ff : iso_disp f xx yy) (gg : iso_disp g yy zz)
    :
    iso_disp (iso_comp f g) xx zz.
Proof.
  use tpair.
  - apply (ff ;; gg).
  - use tpair.
    + apply (transportb (mor_disp zz xx) (maponpaths pr1 (iso_inv_of_iso_comp _ _ _ _ f g))).
      cbn.
      apply (inv_mor_disp_from_iso gg ;; inv_mor_disp_from_iso ff).
    + split.
      * etrans.  apply mor_disp_transportf_postwhisker.
        etrans. apply maponpaths. apply assoc_disp_var.
        etrans. apply maponpaths, maponpaths, maponpaths.
                apply assoc_disp.
        etrans. apply maponpaths, maponpaths, maponpaths, maponpaths.
                eapply (maponpaths (λ x, x ;; gg)).
                apply iso_disp_after_inv_mor.
        etrans. apply transport_f_f.
        etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
        etrans.  apply transport_f_f.
        etrans. apply maponpaths, maponpaths.
          apply mor_disp_transportf_postwhisker.
        etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
        etrans. apply transport_f_f.
        etrans. apply maponpaths, maponpaths. apply id_left_disp.
        etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
        etrans. apply transport_f_f.
        etrans. apply maponpaths.        apply iso_disp_after_inv_mor.
        etrans. apply transport_f_f.
        apply transportf_comp_lemma; apply transportf_comp_lemma_hset;
        try apply homset_property; apply idpath.
      * cbn. simpl.
        etrans. apply assoc_disp_var.
        etrans. apply maponpaths, maponpaths.
                 apply mor_disp_transportf_prewhisker.
        etrans. apply maponpaths, maponpaths, maponpaths.
                apply assoc_disp.
        etrans. apply maponpaths, maponpaths, maponpaths, maponpaths.
                eapply (maponpaths (λ x, x ;; inv_mor_disp_from_iso ff )).
                apply inv_mor_after_iso_disp.
        etrans. apply maponpaths, maponpaths, maponpaths, maponpaths.
                 apply mor_disp_transportf_postwhisker.
        etrans. apply maponpaths, maponpaths, maponpaths, maponpaths, maponpaths.
                apply id_left_disp.
        etrans. apply maponpaths, maponpaths. apply transport_f_f.
        etrans. apply maponpaths, maponpaths. apply transport_f_f.
        etrans.  apply maponpaths, maponpaths. apply transport_f_f.
        etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
        etrans. apply transport_f_f.
        etrans. apply maponpaths.
                apply inv_mor_after_iso_disp.
        etrans. apply transport_f_f.
        apply transportf_comp_lemma; apply transportf_comp_lemma_hset;
        try apply homset_property; apply idpath.
Defined.

Definition id_is_iso_disp {C} {D : disp_cat C} {x : C} (xx : D x)
  : is_iso_disp (identity_iso x) (id_disp xx).
Proof.
  exists (id_disp _); split.
  - etrans. apply id_left_disp.
    apply maponpaths_2, homset_property.
  - etrans. apply id_left_disp.
    apply maponpaths_2, homset_property.
Defined.

Definition identity_iso_disp {C} {D : disp_cat C} {x : C} (xx : D x)
  : iso_disp (identity_iso x) xx xx
:= (_ ,, id_is_iso_disp _).

Lemma idtoiso_disp {C} {D : disp_cat C}
    {x x' : C} (e : x = x')
    {xx : D x} {xx' : D x'} (ee : transportf _ e xx = xx')
  : iso_disp (idtoiso e) xx xx'.
Proof.
  destruct e, ee; apply identity_iso_disp.
Defined.

Lemma idtoiso_fiber_disp {C} {D : disp_cat C} {x : C}
    {xx xx' : D x} (ee : xx = xx')
  : iso_disp (identity_iso x) xx xx'.
Proof.
  exact (idtoiso_disp (idpath _) ee).
Defined.


Lemma iso_disp_precomp {C : category} {D : disp_cat C}
    {x y : C} (f : iso x y)
    {xx : D x} {yy} (ff : iso_disp f xx yy)
  : forall (y' : C) (f' : y --> y') (yy' : D y'),
          isweq (fun ff' : yy -->[ f' ] yy' => pr1 ff ;; ff').
Proof.
  intros y' f' yy'.
  use isweq_iso.
  + intro X.
    set (XR := (pr1 (pr2 ff)) ;; X).
    set (XR' := transportf _ (assoc _ _ _   ) XR).
    set (XRRT := transportf _
           (maponpaths (λ xyz, xyz · f') (iso_after_iso_inv f))
           XR').
    set (XRRT' := transportf _ (id_left _ )
           XRRT).
    apply XRRT'.
  + intros. simpl.
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply assoc_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths_2. apply (pr2 (pr2 ff)).
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    apply transportf_comp_lemma_hset.
    apply (pr2 C). apply idpath.
  + intros; simpl.
    etrans. apply maponpaths. apply transport_f_f.
    etrans. apply mor_disp_transportf_prewhisker.
    etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply assoc_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths_2.
    assert (XR := pr2 (pr2 (pr2 ff))). simpl in XR. apply XR.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    apply transportf_comp_lemma_hset.
    apply (pr2 C). apply idpath.
Defined.

Lemma iso_disp_postcomp {C : category} {D : disp_cat C}
    {x y : C} (i : iso x y)
    {xx : D x} {yy} (ii : iso_disp i xx yy)
  : forall (x' : C) (f' : x' --> x) (xx' : D x'),
          isweq (fun ff : xx' -->[ f' ] xx => ff ;; ii)%mor_disp.
Proof.
  intros y' f' yy'.
  use isweq_iso.
  + intro X.
    set (XR := X ;; (pr1 (pr2 ii))).
    set (XR' := transportf (λ x, _ -->[ x ] _) (!assoc _ _ _   ) XR).
    set (XRRT := transportf (λ x, _ -->[ x ] _ )
           (maponpaths (λ xyz, _ · xyz) (iso_inv_after_iso _ ))
           XR').
    set (XRRT' := transportf _ (id_right _ )
           XRRT).
    apply XRRT'.
  + intros. simpl.
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply assoc_disp_var.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths. apply (pr2 (pr2 (pr2 ii))).
    etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply id_right_disp.
    etrans. apply transport_f_f.
    apply transportf_comp_lemma_hset.
    apply (pr2 C). apply idpath.
  + intros; simpl.
    etrans. apply maponpaths_2. apply transport_f_f.
    etrans. apply mor_disp_transportf_postwhisker.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply assoc_disp_var.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths.
    assert (XR := pr1 (pr2 (pr2 ii))). simpl in XR. apply XR.
    etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply id_right_disp.
    etrans. apply transport_f_f.
    apply transportf_comp_lemma_hset.
    apply (pr2 C). apply idpath.
Defined.


(* Useful when you want to prove [is_iso_disp], and you have some lemma [awesome_lemma] which gives that, but over a different (or just opaque) proof of [is_iso] in the base.  Then you can use [eapply is_iso_disp_independent_of_is_iso; apply awesome_lemma.]. *)
Lemma is_iso_disp_independent_of_is_iso
    {C : category} {D : disp_cat_data C}
    {x y : C} (f : iso x y) {xx : D x} {yy} (ff : xx -->[f] yy)
    {H'f : is_iso f} (Hff : is_iso_disp ((f : _ --> _),,H'f) ff)
  : is_iso_disp f ff.
Proof.
  destruct f as [F Hf].
  assert (E : Hf = H'f). apply isaprop_is_iso.
  destruct E. exact Hff.
Qed.

End Isos.

(** ** More utility lemmas *)

(** A few more general lemmas for displayed-cat algebra, that require isomorphisms to state. *)
Section Utilities.

(** Note: closely analogous to [idtoiso_precompose].  We name it differently to fit the convention of naming equalities according to their LHS, for reference during calculation. *)
Lemma transportf_precompose_disp {C} {D : disp_cat C}
    {c d : C} (f : c --> d )
    {cc cc' : D c} (e : cc = cc') {dd} (ff : cc -->[f] dd)
  : transportf (λ xx : D c, xx -->[f] dd) e ff
  = transportf _ (id_left _)
    (iso_inv_from_iso_disp (idtoiso_disp (idpath _) (e)) ;; ff).
Proof.
  destruct e; cbn.
  rewrite (@id_left_disp _ _ _ _ _ cc).
  apply pathsinv0, transportfbinv.
Qed.

(* TODO: add dual [transportf_postcompose_disp]. *)

Definition precomp_with_iso_disp_is_inj
    {C : category} {D : disp_cat C}
    {a b c : C} {i : iso a b} {f : b --> c}
    {aa : D a} {bb} {cc} (ii : iso_disp i aa bb) {ff ff' : bb -->[f] cc}
  : (ii ;; ff = ii ;; ff') -> ff = ff'.
Proof.
  intros e.
  use pathscomp0.
  - use (transportf _ _ ((iso_inv_from_iso_disp ii ;; ii) ;; ff)).
    etrans; [ apply maponpaths_2, iso_after_iso_inv | apply id_left ].
  - apply pathsinv0.
    etrans. eapply transportf_bind.
      eapply cancel_postcomposition_disp, (iso_disp_after_inv_mor ii).
    rewrite (@id_left_disp _ _ _ _ _ bb).
    etrans. apply transport_f_f.
    use (@maponpaths_2 _ _ _ _ _ (idpath _)).
    apply homset_property.
  - etrans. eapply transportf_bind, assoc_disp_var.
    rewrite e.
    etrans. eapply transportf_bind, assoc_disp.
    etrans. eapply transportf_bind.
      eapply cancel_postcomposition_disp, (iso_disp_after_inv_mor ii).
    rewrite id_left_disp.
    etrans. apply transport_f_f.
    use (@maponpaths_2 _ _ _ _ _ (idpath _)).
    apply homset_property.
Qed.

(* TODO: add dual [postcomp_with_iso_disp_is_inj]. *)

Definition postcomp_with_iso_disp_is_inj
           {C : category}
           {D : disp_cat C}
           {x y z : C}
           {f : x --> y}
           {g : x --> y}
           {h : y --> z}
           (Hh : is_iso h)
           (p : f = g)
           {xx : D x}
           {yy : D y}
           {zz : D z}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           {hh : yy -->[ h ] zz}
           (Hhh : is_iso_disp (make_iso h Hh) hh)
           (pp : (ff ;; hh
                  =
                  transportb
                    (λ z, _ -->[ z ] _)
                    (maponpaths (λ z, _ · h) p)
                    (gg ;; hh))%mor_disp)
  : ff = transportb _ p gg.
Proof.
  refine (id_right_disp_var _ @ _).
  pose (transportb_transpose_left (inv_mor_after_iso_disp Hhh)) as q.
  etrans.
  {
    do 2 apply maponpaths.
    exact (!q).
  }
  unfold transportb.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite assoc_disp.
  unfold transportb.
  rewrite transport_f_f.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    exact pp.
  }
  unfold transportb.
  rewrite mor_disp_transportf_postwhisker.
  rewrite transport_f_f.
  rewrite assoc_disp_var.
  rewrite transport_f_f.
  etrans.
  {
    do 2 apply maponpaths.
    exact (inv_mor_after_iso_disp Hhh).
  }
  unfold transportb.
  rewrite mor_disp_transportf_prewhisker.
  rewrite id_right_disp.
  unfold transportb.
  rewrite !transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.
End Utilities.

(** ** Saturation: displayed univalent categories *)
Section Univalent_Categories.

Definition is_univalent_disp {C} (D : disp_cat C)
  := ∏ x x' (e : x = x') (xx : D x) (xx' : D x'),
     isweq (λ ee, @idtoiso_disp _ _ _ _ e xx xx' ee).

Definition isaprop_is_univalent_disp
           {C : category}
           (D : disp_cat C)
  : isaprop (is_univalent_disp D).
Proof.
  unfold is_univalent_disp.
  do 5 (use impred ; intro).
  apply isapropisweq.
Defined.

Definition is_univalent_in_fibers {C} (D : disp_cat C) : UU
  := ∏ x (xx xx' : D x), isweq (fun e : xx = xx' => idtoiso_fiber_disp e).

(* TODO: maybe rename further.  *)
Lemma is_univalent_disp_from_fibers {C} {D : disp_cat C}
  : is_univalent_in_fibers D
  -> is_univalent_disp D.
Proof.
  intros H x x' e. destruct e. apply H.
Qed.

Definition is_univalent_in_fibers_from_univalent_disp {C} (D : disp_cat C)
  : is_univalent_disp D -> is_univalent_in_fibers D.
Proof.
  unfold is_univalent_disp , is_univalent_in_fibers.
  intros H x xx xx'.
  specialize (H x x (idpath _ ) xx xx').
  apply H.
Defined.

Lemma univalent_disp_cat_has_groupoid_obs {C} (D : disp_cat C)
  (is_u : is_univalent_disp D) : ∏ c, isofhlevel 3 (D c).
Proof.
  intro c.
  change (isofhlevel 3 (D c)) with
      (∏ a b : D c, isofhlevel 2 (a = b)).
  intros xx xx'.
  set (XR := is_univalent_in_fibers_from_univalent_disp _ is_u).
  apply (isofhlevelweqb _ (make_weq _ (XR _ xx xx'))).
  apply isaset_iso_disp.
Defined.


Definition disp_univalent_category C
  := ∑ D : disp_cat C, is_univalent_disp D.

Definition make_disp_univalent_category
    {C} {D : disp_cat C} (H : is_univalent_disp D)
  : disp_univalent_category C
:= (D,,H).

Definition disp_cat_of_disp_univalent_cat {C} (D : disp_univalent_category C)
  : disp_cat C
:= pr1 D.
Coercion disp_cat_of_disp_univalent_cat : disp_univalent_category >-> disp_cat.

Definition disp_univalent_category_is_univalent_disp {C} (D : disp_univalent_category C)
  : is_univalent_disp D
:= pr2 D.
Coercion disp_univalent_category_is_univalent_disp : disp_univalent_category >-> is_univalent_disp.

Definition isotoid_disp
    {C} {D : disp_cat C} (D_cat : is_univalent_disp D)
    {c c' : C} (e : c = c') {d : D c} {d'} (i : iso_disp (idtoiso e) d d')
  : transportf _ e d = d'.
Proof.
  exact (invmap (make_weq (idtoiso_disp e) (D_cat _ _ _ _ _)) i).
Defined.

Definition idtoiso_isotoid_disp
    {C} {D : disp_cat C} (D_cat : is_univalent_disp D)
    {c c' : C} (e : c = c') {d : D c} {d'} (i : iso_disp (idtoiso e) d d')
  : idtoiso_disp e (isotoid_disp D_cat e i) = i.
Proof.
  use homotweqinvweq.
Qed.

Definition isotoid_idtoiso_disp
    {C} {D : disp_cat C} (D_cat : is_univalent_disp D)
    {c c' : C} (e : c = c') {d : D c} {d'} (ee : transportf _ e d = d')
  : isotoid_disp D_cat e (idtoiso_disp e ee) = ee.
Proof.
  use homotinvweqweq.
Qed.

End Univalent_Categories.



(** * Functors

- Reindexing of displayed cats along functors: [reindex_disp_cat]
- Functors into displayed cats, lifting functors into the base: [functor_lifting]
- Functors between displayed cats, over functors between the bases: [disp_functor]
- Natural transformations between these: [disp_nat_trans] *)

(** ** Reindexing *)

Section Reindexing.

Context {C' C : category} (F : functor C' C) (D : disp_cat C).

Definition reindex_disp_cat_ob_mor : disp_cat_ob_mor C'.
Proof.
  exists (λ c, D (F c)).
  intros x y xx yy f. exact (xx -->[# F f] yy).
Defined.

Definition reindex_disp_cat_id_comp : disp_cat_id_comp C' reindex_disp_cat_ob_mor.
Proof.
  apply tpair.
  - simpl; intros x xx.
    refine (transportb _ _ _).
    apply functor_id. apply id_disp.
  - simpl; intros x y z f g xx yy zz ff gg.
    refine (transportb _ _ _).
    apply functor_comp. exact (ff ;; gg).
Defined.

Definition reindex_disp_cat_data : disp_cat_data C'
  := (_ ,, reindex_disp_cat_id_comp).

Definition reindex_disp_cat_axioms : disp_cat_axioms C' reindex_disp_cat_data.
Proof.
  repeat apply tpair; cbn.
  - intros x y f xx yy ff.
    eapply pathscomp0. apply maponpaths, mor_disp_transportf_postwhisker.
    eapply pathscomp0. apply transport_b_f.
    eapply pathscomp0. apply maponpaths, id_left_disp.
    eapply pathscomp0. apply transport_f_b.
    eapply pathscomp0. 2: apply @pathsinv0, (functtransportb (# F)).
    unfold transportb; apply maponpaths_2, homset_property.
  - intros x y f xx yy ff.
    eapply pathscomp0. apply maponpaths, mor_disp_transportf_prewhisker.
    eapply pathscomp0. apply transport_b_f.
    eapply pathscomp0. apply maponpaths, id_right_disp.
    eapply pathscomp0. apply transport_f_b.
    eapply pathscomp0. 2: apply @pathsinv0, (functtransportb (# F)).
    unfold transportb; apply maponpaths_2, homset_property.
  - intros x y z w f g h xx yy zz ww ff gg hh.
    eapply pathscomp0. apply maponpaths, mor_disp_transportf_prewhisker.
    eapply pathscomp0. apply transport_b_f.
    eapply pathscomp0. apply maponpaths, assoc_disp.
    eapply pathscomp0. apply transport_f_b.
    apply pathsinv0.
    eapply pathscomp0. apply (functtransportb (# F)).
    eapply pathscomp0. apply transport_b_b.
    eapply pathscomp0. apply maponpaths, mor_disp_transportf_postwhisker.
    eapply pathscomp0. apply transport_b_f.
    unfold transportb; apply maponpaths_2, homset_property.
  - intros; apply homsets_disp.
Qed.

Definition reindex_disp_cat : disp_cat C'
  := (_ ,, reindex_disp_cat_axioms).

End Reindexing.

(** some TODOs for the displayed-cats library:

- add lemmas connecting with products of cats (as required for displayed bicats)
- add more applications of the displayed arrow category: slices; equalisers, inserters; hence groups etc.

 *)
