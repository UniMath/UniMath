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
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Local Open Scope cat_deprecated.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.


Local Open Scope type_scope.

(* Undelimit Scope transport. *)

(** * Displayed categories *)

Module Record_Preview.

  Record disp_cat (C : category) : UU :=
    { ob_disp : C -> UU
    ; mor_disp {x y : C} : (x --> y) -> ob_disp x -> ob_disp y -> UU
    ; id_disp {x : C} (xx : ob_disp x) : mor_disp (identity x) xx xx
    ; comp_disp {x y z : C} {f : x --> y} {g : y --> z}
                   {xx : ob_disp x} {yy : ob_disp y} {zz : ob_disp z}
        : mor_disp f xx yy -> mor_disp g yy zz -> mor_disp (f ;; g) xx zz
    ; id_left_disp {x y} {f : x --> y} {xx} {yy} (ff : mor_disp f xx yy)
        : comp_disp (id_disp xx) ff
          = transportb (λ g, mor_disp g xx yy) (id_left _) ff
    ; id_right_disp {x y} {f : x --> y} {xx} {yy} (ff : mor_disp f xx yy)
        : comp_disp ff (id_disp yy)
          = transportb (λ g, mor_disp g xx yy) (id_right _) ff
    ; assoc_disp {x y z w} {f : x --> y} {g : y --> z} {h : z --> w}
        {xx} {yy} {zz} {ww}
        (ff : mor_disp f xx yy) (gg : mor_disp g yy zz) (hh : mor_disp h zz ww)
        : comp_disp ff (comp_disp gg hh)
          = transportb (λ k, mor_disp k _ _) (assoc _ _ _)
            (comp_disp (comp_disp ff gg) hh)
    ; homsets_disp {x y} {f : x --> y} {xx} {yy} : isaset (mor_disp f xx yy)
    }.

End Record_Preview.

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

Definition ob_disp {C} (D : disp_cat_ob_mor C) : C -> UU := pr1 D.
Coercion ob_disp : disp_cat_ob_mor >-> Funclass.

Definition mor_disp {C} {D : disp_cat_ob_mor C}
  {x y} xx yy (f : x --> y)
:= pr2 D x y xx yy f : UU.

Local Notation "xx -->[ f ] yy" := (mor_disp xx yy f) (at level 50, yy at next level).

Definition disp_cat_id_comp (C : precategory_data)
  (D : disp_cat_ob_mor C)
  : UU
:= (forall (x:C) (xx : D x), xx -->[identity x] xx)
  × (forall (x y z : C) (f : x --> y) (g : y --> z) (xx:D x) (yy:D y) (zz:D z),
           (xx -->[f] yy) -> (yy -->[g] zz) -> (xx -->[f ;; g] zz)).

Definition disp_cat_data C := total2 (disp_cat_id_comp C).

Definition disp_cat_ob_mor_from_disp_cat_data {C}
  (D : disp_cat_data C)
  : disp_cat_ob_mor C
:= pr1 D.

Coercion disp_cat_ob_mor_from_disp_cat_data :
 disp_cat_data >-> disp_cat_ob_mor.

Definition id_disp {C} {D : disp_cat_data C} {x:C} (xx : D x)
  : xx -->[identity x] xx
:= pr1 (pr2 D) x xx.

Definition comp_disp {C} {D : disp_cat_data C}
  {x y z : C} {f : x --> y} {g : y --> z}
  {xx : D x} {yy} {zz} (ff : xx -->[f] yy) (gg : yy -->[g] zz)
  : xx -->[f;;g] zz
:= pr2 (pr2 D) _ _ _ _ _ _ _ _ ff gg.

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
  {x y} {f : x --> y} {xx : D x} {yy} {ff : xx -->[f] yy}
: id_disp _ ;; ff = transportb _ (id_left _) ff
:= pr1 (pr2 D) _ _ _ _ _ _.

Lemma id_left_disp_var {C} {D : disp_cat C}
  {x y} {f : x --> y} {xx : D x} {yy} {ff : xx -->[f] yy}
: ff = transportf _ (id_left _) (id_disp _ ;; ff).
Proof.
  apply transportf_transpose.
  apply @pathsinv0, id_left_disp.
Qed.

Definition id_right_disp {C} {D : disp_cat C}
  {x y} {f : x --> y} {xx : D x} {yy} {ff : xx -->[f] yy}
  : ff ;; id_disp _ = transportb _ (id_right _) ff
:= pr1 (pr2 (pr2 D)) _ _ _ _ _ _.

Definition id_right_disp_var {C} {D : disp_cat C}
  {x y} {f : x --> y} {xx : D x} {yy} {ff : xx -->[f] yy}
  : ff = transportf _ (id_right _) (ff ;; id_disp _).
Proof.
  apply transportf_transpose.
  apply @pathsinv0, id_right_disp.
Qed.

Definition assoc_disp {C} {D : disp_cat C}
  {x y z w} {f} {g} {h} {xx : D x} {yy : D y} {zz : D z} {ww : D w}
  {ff : xx -->[f] yy} {gg : yy -->[g] zz} {hh : zz -->[h] ww}
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

Definition homsets_disp {C} {D :disp_cat C} {x y} {f} {xx : D x} {yy : D y}
  : isaset (xx -->[f] yy)
:= pr2 (pr2 (pr2 (pr2 D))) _ _ _ _ _.

(** ** Utility lemmas *)
Section Lemmas.

(** [etrans_disp]: a version of [etrans_dep] for use when the equality transport in the RHS of the goal is already present, and not of the form produced by [etrans_dep], so [etrans_dep] doesn’t apply.  Where possible, [etrans_dep] should still be used, since it *produces* a RHS, whereas this does not (and so leads to lots of unsolved existentials if used where not needed).

NOTE: as with [etrans_dep], proofs using [etrans_disp] seem to typecheck more slowly than proofs using [etrans] plus other lemmas directly. *)
Lemma pathscomp0_disp {C} {D : disp_cat C}
  {x y} {f f' f'' : x --> y} {e : f' = f} {e' : f'' = f'} {e'' : f'' = f}
  {xx : D x} {yy}
  {ff : xx -->[f] yy} {ff' : xx -->[f'] yy} {ff'' : xx -->[f''] yy}
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
Notation "xx -->[ f ] yy" := (mor_disp xx yy f) (at level 50, yy at next level).

Notation "ff ;; gg" := (comp_disp ff gg)
  (at level 50, left associativity, format "ff  ;;  gg")
  : mor_disp_scope.
Delimit Scope mor_disp_scope with mor_disp.
Bind Scope mor_disp_scope with mor_disp.
Local Open Scope mor_disp_scope.

(** A useful notation for hiding the huge irrelevant equalities that occur in algebra of displayed categories.  For individual proofs, use [Open Scope hide_transport_scope.] at the start, and then [Close Scope hide_transport_scope.] afterwards.  For whole files/sections, use [Local Open Scope hide_transport_scope.]

Level is chosen to bind *tighter* than categorical composition, for readability. *)
(* TODO: consider symbol(s) used. *)
Notation "#? x" := (transportf _ _ x) (at level 45) : hide_transport_scope.
Notation "#?' x" := (transportb _ _ x) (at level 45) : hide_transport_scope.

(** ** Isomorphisms (and lemmas) *)

Section Isos.

Definition is_iso_disp {C : category} {D : disp_cat_data C}
    {x y : C} (f : iso x y) {xx : D x} {yy} (ff : xx -->[f] yy)
  : UU
:= ∑ (gg : yy -->[inv_from_iso f] xx),
     gg ;; ff = transportb _ (iso_after_iso_inv _) (id_disp _)
     × ff ;; gg = transportb _ (iso_inv_after_iso _) (id_disp _).

Definition iso_disp {C : category} {D : disp_cat_data C}
    {x y : C} (f : iso x y) (xx : D x) (yy : D y)
  := ∑ ff : xx -->[f] yy, is_iso_disp f ff.

Definition iso_disp_pair {C : category} {D : disp_cat_data C}
    {x y : C} {f : iso x y} {xx : D x} {yy : D y}
    (ff : xx -->[f] yy) (is : is_iso_disp f ff)
    : iso_disp _ _ _
  := (ff,, is).


Definition mor_disp_from_iso {C : category} {D : disp_cat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y}
    (i : iso_disp f xx yy) : _ -->[ _ ] _ := pr1 i.
Coercion mor_disp_from_iso : iso_disp >-> mor_disp.

Definition is_iso_disp_from_iso {C : category} {D : disp_cat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y}
    (i : iso_disp f xx yy) : is_iso_disp f i := pr2 i.
Coercion is_iso_disp_from_iso : iso_disp >-> is_iso_disp.

Definition inv_mor_disp_from_iso {C : category} {D : disp_cat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y}
    {ff : xx -->[f] yy} (i : is_iso_disp f ff)
  : _ -->[ _ ] _ := pr1 i.

Definition iso_disp_after_inv_mor {C : category} {D : disp_cat_data C}
    {x y : C} {f : iso x y}{xx : D x} {yy : D y}
    {ff : xx -->[f] yy} (i : is_iso_disp f ff)
  : inv_mor_disp_from_iso i ;; ff
    = transportb _ (iso_after_iso_inv _) (id_disp _).
Proof.
  apply (pr2 i).
Qed.

Definition inv_mor_after_iso_disp {C : category} {D : disp_cat_data C}
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
  apply subtypeEquality.
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
  apply subtypeEquality; intro; apply isaprop_is_iso_disp.
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
                          (maponpaths pr1 (iso_inv_iso_inv _ _ _ f))).
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
  use gradth.
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
  use gradth.
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
  destruct e; cbn; unfold idfun; cbn.
  rewrite id_left_disp.
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
    rewrite id_left_disp.
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

End Utilities.

(** ** Saturation: displayed univalent categories *)
Section Univalent_Categories.

Definition is_univalent_disp {C} (D : disp_cat C)
  := forall x x' (e : x = x') {xx : D x} {xx' : D x'},
       isweq (λ ee, @idtoiso_disp _ _ _ _ e xx xx' ee).

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
  apply (isofhlevelweqb _ (weqpair _ (XR _ xx xx'))).
  apply isaset_iso_disp.
Defined.


Definition disp_univalent_category C
  := ∑ D : disp_cat C, is_univalent_disp D.

Definition disp_univalent_category_pair
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
  exact (invmap (weqpair (idtoiso_disp e) (D_cat _ _ _ _ _)) i).
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


(** * Total categories *)

(** ** Definition and forgetful functor *)

(* Any displayed category has a total category, with a forgetful functor to the base category. *)
Section Total_Category.

Context {C : category} (D : disp_cat C).

Definition total_category_ob_mor : precategory_ob_mor.
Proof.
  exists (∑ x:C, D x).
  intros xx yy.
  (* note: we use projections rather than destructing, so that [ xx --> yy ]
  can β-reduce without [xx] and [yy] needing to be in whnf *)
  exact (∑ (f : pr1 xx --> pr1 yy), pr2 xx -->[f] pr2 yy).
Defined.

Definition total_category_id_comp : precategory_id_comp (total_category_ob_mor).
Proof.
  apply tpair; simpl.
  - intros. exists (identity _). apply id_disp.
  - intros xx yy zz ff gg.
    exists (pr1 ff · pr1 gg).
    exact (pr2 ff ;; pr2 gg).
Defined.

Definition total_category_data : precategory_data
  := (total_category_ob_mor ,, total_category_id_comp).

(* TODO: make notations [( ,, )] and [ ;; ] different levels?  ;; should bind tighter, perhaps, and ,, looser? *)
Lemma total_category_is_precat : is_precategory (total_category_data).
Proof.
  repeat apply tpair; simpl.
  - intros xx yy ff; cbn.
    use total2_paths_f; simpl.
    apply id_left.
    eapply pathscomp0.
      apply maponpaths, id_left_disp.
  (* Note: [transportbfi] is from [UniMath.Ktheory.Utilities].
  We currently can’t import that, due to notation clashes. *)
    apply transportfbinv.
  - intros xx yy ff; cbn.
    use total2_paths_f; simpl.
    apply id_right.
    eapply pathscomp0.
      apply maponpaths, id_right_disp.
    apply transportfbinv.
  - intros xx yy zz ww ff gg hh.
    use total2_paths_f; simpl.
    apply assoc.
    eapply pathscomp0.
      apply maponpaths, assoc_disp.
    apply transportfbinv.
Qed.

(* The “pre-category” version, without homsets *)
Definition total_precategory : precategory
  := (total_category_data ,, total_category_is_precat).

Lemma total_category_has_homsets : has_homsets (total_category_data).
Proof.
  intros xx yy; simpl. apply isaset_total2. apply homset_property.
  intros; apply homsets_disp.
Qed.

Definition total_category : category
  := (total_precategory ,, total_category_has_homsets).

Definition pr1_category_data : functor_data total_category C.
Proof.
  exists pr1.
  intros a b; exact pr1.
Defined.

Lemma pr1_category_is_functor : is_functor pr1_category_data.
Proof.
  apply tpair.
  - intros x; apply idpath.
  - intros x y z f g; apply idpath.
Qed.

Definition pr1_category : functor total_category C
  := (pr1_category_data ,, pr1_category_is_functor).



Lemma full_pr1_category  (H : ∏ (a b : total_category)  (x : C ⟦ pr1 a, pr1 b ⟧),
                            ∥ pr2 a -->[ x] pr2 b ∥)
  : full pr1_category.
Proof.
  intros a b.
  use pr1_issurjective.
  apply H.
Defined.

Lemma faithful_pr1_category (H : ∏ (a b : total_category) (x : C ⟦ pr1 a, pr1 b ⟧),
                               isaprop (pr2 a -->[ x] pr2 b))
  : faithful pr1_category.
Proof.
  intros a b. cbn.
  apply isinclpr1.
  apply H.
Defined.


Definition fully_faithful_pr1_category (H : ∏ (a b : total_category) (x : C ⟦ pr1 a, pr1 b ⟧),
                                          iscontr (pr2 a -->[ x] pr2 b))
  : fully_faithful pr1_category.
Proof.
  intros a b.
  apply isweqpr1.
  apply H.
Defined.



(** ** Isomorphisms and saturation *)

Definition is_iso_total {xx yy : total_category} (ff : xx --> yy)
  (i : is_iso (pr1 ff))
  (fi := isopair (pr1 ff) i)
  (ii : is_iso_disp fi (pr2 ff))
  : is_iso ff.
Proof.
  apply is_iso_from_is_z_iso.
  exists (inv_from_iso fi,, pr1 ii).
  split.
  - use total2_paths_f.
    apply (iso_inv_after_iso fi).
    etrans. apply maponpaths. apply (inv_mor_after_iso_disp ii).
    apply transportfbinv.
  - use total2_paths_f.
    apply (iso_after_iso_inv fi).
    etrans. apply maponpaths. apply (iso_disp_after_inv_mor ii).
    apply transportfbinv.
Qed.

Definition is_iso_base_from_total {xx yy : total_category} {ff : xx --> yy} (i : is_iso ff)
  : is_iso (pr1 ff).
Proof.
  set (ffi := isopair ff i).
  apply (is_iso_qinv _ (pr1 (inv_from_iso ffi))).
  split.
  - exact (maponpaths pr1 (iso_inv_after_iso ffi)).
  - exact (maponpaths pr1 (iso_after_iso_inv ffi)).
Qed.

Definition iso_base_from_total {xx yy : total_category} (ffi : iso xx yy)
  : iso (pr1 xx) (pr1 yy)
:= isopair _ (is_iso_base_from_total (pr2 ffi)).

Definition inv_iso_base_from_total {xx yy : total_category} (ffi : iso xx yy)
  : inv_from_iso (iso_base_from_total ffi) = pr1 (inv_from_iso ffi).
Proof.
  apply pathsinv0, inv_iso_unique'. unfold precomp_with.
  exact (maponpaths pr1 (iso_inv_after_iso ffi)).
Qed.

Definition is_iso_disp_from_total {xx yy : total_category}
    {ff : xx --> yy} (i : is_iso ff)
    (ffi := isopair ff i)
  : is_iso_disp (iso_base_from_total (ff,,i)) (pr2 ff).
Proof.
  use tpair; [ | split].
  - eapply transportb. apply inv_iso_base_from_total.
    exact (pr2 (inv_from_iso ffi)).
  - etrans. apply mor_disp_transportf_postwhisker.
    etrans. apply maponpaths, @pathsinv0.
      exact (fiber_paths (!iso_after_iso_inv ffi)).
    etrans. apply transport_f_f.
    use (toforallpaths _ _ _ _ (id_disp _)).
    unfold transportb; apply maponpaths, homset_property.
  - etrans. apply mor_disp_transportf_prewhisker.
    etrans. apply maponpaths, @pathsinv0.
      exact (fiber_paths (!iso_inv_after_iso ffi)).
    etrans. apply transport_f_f.
    use (toforallpaths _ _ _ _ (id_disp _)).
    unfold transportb; apply maponpaths, homset_property.
Qed.

Definition iso_disp_from_total {xx yy : total_category}
    (ff : iso xx yy)
  : iso_disp (iso_base_from_total ff) (pr2 xx) (pr2 yy).
Proof.
  exact (_,, is_iso_disp_from_total (pr2 ff)).
Defined.

Definition total_iso {xx yy : total_category}
  (f : iso (pr1 xx) (pr1 yy)) (ff : iso_disp f (pr2 xx) (pr2 yy))
  : iso xx yy.
Proof.
  exists (pr1 f,, pr1 ff).
  apply (is_iso_total (pr1 f,, pr1 ff) (pr2 f) (pr2 ff)).
Defined.

(* TODO: look more for this in library.  If doesn’t exist, upstream it? *)
Lemma cancel_precomposition_iso {C' : precategory} {x y z : C'}
    (f : iso x y) (g1 g2 : y --> z)
  : (f ;; g1 = f ;; g2 -> g1 = g2)%cat_deprecated.
Proof.
  intros e.
  apply @pathscomp0 with (inv_from_iso f · (f · g1)).
  apply @pathsinv0.
  - etrans. apply assoc.
    etrans. apply maponpaths_2, iso_after_iso_inv.
    apply id_left.
  - etrans. apply maponpaths, e.
    etrans. apply assoc.
    etrans. apply maponpaths_2, iso_after_iso_inv.
    apply id_left.
Qed.


Lemma inv_mor_total_iso {xx yy : total_category}
  (f : iso (pr1 xx) (pr1 yy)) (ff : iso_disp f (pr2 xx) (pr2 yy))
  : inv_from_iso (total_iso f ff)
  = (inv_from_iso f,, inv_mor_disp_from_iso ff).
Proof.
  (* Could de-opacify [is_iso_total] and then use [inv_from_iso_from_is_z_iso].  If de-opacfying [is_iso_total] would make its inverse compute definitionally, that’d be wonderful, but for the sake of just this one lemma, it’s probably not worth it.  So we prove this the hard way. *)
  apply cancel_precomposition_iso with (total_iso f ff).
  etrans. apply iso_inv_after_iso. apply pathsinv0.
  use total2_paths_f; cbn.
  - apply iso_inv_after_iso.
  - etrans. apply maponpaths, inv_mor_after_iso_disp.
    apply transportfbinv.
Qed.

Definition total_iso_equiv_map {xx yy : total_category}
  : (∑ f : iso (pr1 xx) (pr1 yy), iso_disp f (pr2 xx) (pr2 yy))
  -> iso xx yy
:= λ ff, total_iso (pr1 ff) (pr2 ff).

Definition total_iso_isweq (xx yy : total_category)
  : isweq (@total_iso_equiv_map xx yy).
Proof.
  use gradth.
  - intros ff. exists (iso_base_from_total ff). apply iso_disp_from_total.
  - intros [f ff]. use total2_paths_f.
    + apply eq_iso, idpath.
    + apply eq_iso_disp.
      etrans. apply transportf_iso_disp.
      simpl pr2. simpl (pr1 (iso_disp_from_total _)).
      use (@maponpaths_2 _ _ _ (transportf _) _ (idpath _)).
      apply homset_property.
  - intros f. apply eq_iso; simpl.
    destruct f as [[f ff] w]; apply idpath.
Qed.

Definition total_iso_equiv (xx yy : total_category)
  : (∑ f : iso (pr1 xx) (pr1 yy), iso_disp f (pr2 xx) (pr2 yy))
  ≃ iso xx yy
:= weqpair _ (total_iso_isweq xx yy).

Lemma is_univalent_total_category (CC : is_univalent C) (DD : is_univalent_disp D)
  : is_univalent (total_category).
Proof.
  split. Focus 2. apply homset_property.
  intros xs ys.
  set (x := pr1 xs). set (xx := pr2 xs).
  set (y := pr1 ys). set (yy := pr2 ys).
  use weqhomot.
  apply (@weqcomp _ (∑ e : x = y, transportf _ e xx = yy) _).
    apply total2_paths_equiv.
  apply (@weqcomp _ (∑ e : x = y, iso_disp (idtoiso e) xx yy) _).
    apply weqfibtototal.
    intros e. exists (λ ee, idtoiso_disp e ee).
    apply DD.
  apply (@weqcomp _ (∑ f : iso x y, iso_disp f xx yy) _).
    use (weqfp (weqpair _ _)). apply CC.
  apply total_iso_equiv.
  intros e; destruct e; apply eq_iso; cbn.
    apply idpath.
Qed.

End Total_Category.

Arguments pr1_category [C] D.

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
    eapply pathscomp0. Focus 2. apply @pathsinv0, (functtransportb (# F)).
    unfold transportb; apply maponpaths_2, homset_property.
  - intros x y f xx yy ff.
    eapply pathscomp0. apply maponpaths, mor_disp_transportf_prewhisker.
    eapply pathscomp0. apply transport_b_f.
    eapply pathscomp0. apply maponpaths, id_right_disp.
    eapply pathscomp0. apply transport_f_b.
    eapply pathscomp0. Focus 2. apply @pathsinv0, (functtransportb (# F)).
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

(** ** Functors into displayed categories *)

(** Just like how context morphisms in a CwA can be built up out of terms, similarly, the basic building-block for functors into (total cats of) displayed categories will be analogous to a term.

We call it a _section_ (though we define it intrinsically, not as a section in a (bi)category), since it corresponds to a section of the forgetful functor. *)

Section Sections.

Definition section_disp_data {C} (D : disp_cat C) : UU
  := ∑ (Fob : forall x:C, D x),
       (forall (x y:C) (f:x --> y), Fob x -->[f] Fob y).

Definition section_disp_on_objects {C} {D : disp_cat C}
  (F : section_disp_data D) (x : C)
:= pr1 F x : D x.

Coercion section_disp_on_objects : section_disp_data >-> Funclass.

Definition section_disp_on_morphisms {C} {D : disp_cat C}
  (F : section_disp_data D) {x y : C} (f : x --> y)
:= pr2 F _ _ f : F x -->[f] F y.

Notation "# F" := (section_disp_on_morphisms F)
  (at level 3) : mor_disp_scope.

Definition section_disp_axioms {C} {D : disp_cat C}
  (F : section_disp_data D) : UU
:= ((forall x:C, # F (identity x) = id_disp (F x))
  × (forall (x y z : C) (f : x --> y) (g : y --> z),
      # F (f · g) = (# F f) ;; (# F g))).

Definition section_disp {C} (D : disp_cat C) : UU
  := total2 (@section_disp_axioms C D).

Definition section_disp_data_from_section_disp {C} {D : disp_cat C}
  (F : section_disp D) := pr1 F.

Coercion section_disp_data_from_section_disp
  : section_disp >-> section_disp_data.

Definition section_disp_id {C} {D : disp_cat C} (F : section_disp D)
  := pr1 (pr2 F).

Definition section_disp_comp {C} {D : disp_cat C} (F : section_disp D)
  := pr2 (pr2 F).

End Sections.

(** With sections defined, we can now define _lifts_ to a displayed category of a functor into the base. *)
Section Functor_Lifting.

Notation "# F" := (section_disp_on_morphisms F)
  (at level 3) : mor_disp_scope.

Definition functor_lifting
  {C C' : category} (D : disp_cat C) (F : functor C' C)
  := section_disp (reindex_disp_cat F D).

Identity Coercion section_from_functor_lifting
  : functor_lifting >-> section_disp.

(** Note: perhaps it would be better to define [functor_lifting] directly?
  Reindexed displayed-cats are a bit confusing to work in, since a term like [id_disp xx] is ambiguous: it can mean both the identity in the original displayed category, or the identity in the reindexing, which is nearly but not quite the same.  This shows up already in the proofs of [lifted_functor_axioms] below. *)

Definition lifted_functor_data {C C' : category} {D : disp_cat C}
  {F : functor C' C} (FF : functor_lifting D F)
  : functor_data C' (total_category D).
Proof.
  exists (λ x, (F x ,, FF x)).
  intros x y f. exists (# F f)%cat. exact (# FF f).
Defined.

Definition lifted_functor_axioms {C C' : category} {D : disp_cat C}
  {F : functor C' C} (FF : functor_lifting D F)
  : is_functor (lifted_functor_data FF).
Proof.
  split.
  - intros x. use total2_paths_f; simpl.
    apply functor_id.
    eapply pathscomp0. apply maponpaths, (section_disp_id FF).
    cbn. apply transportfbinv.
  - intros x y z f g. use total2_paths_f; simpl.
    apply functor_comp.
    eapply pathscomp0. apply maponpaths, (section_disp_comp FF).
    cbn. apply transportfbinv.
Qed.

Definition lifted_functor {C C' : category} {D : disp_cat C}
  {F : functor C' C} (FF : functor_lifting D F)
  : functor C' (total_category D)
:= (_ ,, lifted_functor_axioms FF).

End Functor_Lifting.

(** ** Functors over functors between bases *)

(** One could define these in terms of functor-liftings, as:

[[
Definition disp_functor {C C' : category} (F : functor C C')
    (D : disp_cat C) (D' : disp_cat C')
  := functor_lifting D' (functor_composite (pr1_category D) F).
]]

However, it seems like it may probably be cleaner to define these independently.

TODO: reassess this design decision after some experience using it! *)

Section Disp_Functor.

Definition disp_functor_data {C' C : precategory_data} (F : functor_data C' C)
  (D' : disp_cat_data C') (D : disp_cat_data C)
:= ∑ (Fob : ∏ x, D' x -> D (F x)),
     ∏ x y (xx : D' x) (yy : D' y) (f : x --> y),
       (xx -->[f] yy) -> (Fob _ xx -->[ # F f ] Fob _ yy).

Definition disp_functor_on_objects {C' C : precategory_data} {F : functor_data C' C}
    {D' : disp_cat_data C'} {D : disp_cat_data C}
    (FF : disp_functor_data F D' D) {x : C'} (xx : D' x)
  : D (F x)
:= pr1 FF x xx.

Coercion disp_functor_on_objects : disp_functor_data >-> Funclass.

(** Unfortunately, the coercion loses implicitness of the {x:C'} argument:
  we have to write [ FF _ xx ] instead of just [ FF xx ].

  If anyone knows a way to avoid this, we would be happy to hear it! *)

Definition disp_functor_on_morphisms {C' C : precategory_data} {F : functor_data C' C}
    {D' : disp_cat_data C'} {D : disp_cat_data C}
    (FF : disp_functor_data F D' D)
    {x y : C'} {xx : D' x} {yy} {f : x --> y} (ff : xx -->[f] yy)
  : (FF _ xx) -->[ # F f ] (FF _ yy)
:= pr2 FF x y xx yy f ff.

Notation "# F" := (disp_functor_on_morphisms F)
  (at level 3) : mor_disp_scope.

Definition disp_functor_axioms {C' C : category} {F : functor C' C}
  {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor_data F D' D)
:=  (∏ x (xx : D' x),
      # FF (id_disp xx) = transportb _ (functor_id F x) (id_disp (FF _ xx)))
  × (∏ x y z (xx : D' x) yy zz (f : x --> y) (g : y --> z)
        (ff : xx -->[f] yy) (gg : yy -->[g] zz),
      # FF (ff ;; gg)
      = transportb _ (functor_comp F f g) (# FF ff ;; # FF gg)).

Lemma isaprop_disp_functor_axioms {C' C : category} {F : functor C' C}
  {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor_data F D' D)
  : isaprop (disp_functor_axioms FF).
Proof.
  apply isapropdirprod;
  repeat (apply impred; intros);
  apply homsets_disp.
Qed.

Definition disp_functor {C' C : category} (F : functor C' C)
  (D' : disp_cat C') (D : disp_cat C)
:= ∑ FF : disp_functor_data F D' D, disp_functor_axioms FF.

Definition disp_functor_data_from_disp_functor
    {C' C} {F} {D' : disp_cat C'} {D : disp_cat C}
    (FF : disp_functor F D' D)
  : disp_functor_data F D' D
:= pr1 FF.

Coercion disp_functor_data_from_disp_functor
  : disp_functor >-> disp_functor_data.

Definition disp_functor_id {C' C} {F} {D' : disp_cat C'} {D : disp_cat C}
    (FF : disp_functor F D' D)
    {x} (xx : D' x)
  : # FF (id_disp xx) = transportb _ (functor_id F x) (id_disp (FF _ xx))
:= pr1 (pr2 FF) x xx.

Definition disp_functor_comp {C' C} {F} {D' : disp_cat C'} {D : disp_cat C}
    (FF : disp_functor F D' D)
    {x y z} {xx : D' x} {yy} {zz} {f : x --> y} {g : y --> z}
    (ff : xx -->[f] yy) (gg : yy -->[g] zz)
  : # FF (ff ;; gg)
    = transportb _ (functor_comp F f g) (# FF ff ;; # FF gg)
:= pr2 (pr2 FF) _ _ _ _ _ _ _ _ ff gg.

(** variant access function *)
Definition disp_functor_comp_var {C' C} {F} {D' : disp_cat C'} {D : disp_cat C}
    (FF : disp_functor F D' D)
    {x y z} {xx : D' x} {yy} {zz} {f : x --> y} {g : y --> z}
    (ff : xx -->[f] yy) (gg : yy -->[g] zz)
  : transportf _ (functor_comp F f g) (# FF (ff ;; gg))
     = # FF ff ;; # FF gg.
Proof.
  apply transportf_pathsinv0.
  apply pathsinv0, disp_functor_comp.
Defined.

(** Useful transport lemma for [disp_functor]. *)
Lemma disp_functor_transportf {C' C : category}
  {D' : disp_cat C'} {D : disp_cat C}
  (F : functor C' C) (FF : disp_functor F D' D)
  (x' x : C') (f' f : x' --> x) (p : f' = f)
  (xx' : D' x') (xx : D' x)
  (ff : xx' -->[ f' ] xx)
  :
  # FF (transportf _ p ff)
  =
  transportf _ (maponpaths (#F)%cat p) (#FF ff) .
Proof.
  induction p.
  apply idpath.
Defined.

(** ** Composite and identity functors. *)

Definition disp_functor_composite_data
    {C C' C'' : category} {D} {D'} {D''}
    {F : functor C C'} {F' : functor C' C''}
    (FF : disp_functor F D D')
    (FF' : disp_functor F' D' D'')
  : disp_functor_data (functor_composite F F') D D''.
Proof.
  use tpair.
  + intros x xx. exact (FF' _ (FF _ xx)).
  + intros x y xx yy f ff. exact (# FF' (# FF ff)).
Defined.

Lemma disp_functor_composite_axioms
    {C C' C'' : category} {D} {D'} {D''}
    {F : functor C C'} {F' : functor C' C''}
    (FF : disp_functor F D D')
    (FF' : disp_functor F' D' D'')
: disp_functor_axioms (disp_functor_composite_data FF FF').
Proof.
  split; simpl.
  + intros x xx.
    etrans. apply maponpaths. apply disp_functor_id.
    etrans. apply disp_functor_transportf.
    etrans. apply maponpaths. apply disp_functor_id.
    etrans. apply transport_f_f.
    unfold transportb.
    apply maponpaths_2, homset_property.
  + intros.
    etrans. apply maponpaths. apply disp_functor_comp.
    etrans. apply disp_functor_transportf.
    etrans. apply maponpaths. apply disp_functor_comp.
    etrans. apply transport_f_f.
    unfold transportb.
    apply maponpaths_2, homset_property.
Qed.

Definition disp_functor_composite
    {C C' C'' : category} {D} {D'} {D''}
    {F : functor C C'} {F' : functor C' C''}
    (FF : disp_functor F D D')
    (FF' : disp_functor F' D' D'')
  : disp_functor (functor_composite F F') D D''.
Proof.
  use tpair.
  - apply (disp_functor_composite_data FF FF').
  - apply disp_functor_composite_axioms.
Defined.

Definition disp_functor_identity
    {C : category} (D : disp_cat C)
  : disp_functor (functor_identity _ ) D D.
Proof.
  use tpair.
  - use tpair.
    + intros; assumption.
    + cbn. intros. assumption.
  - split; simpl.
    + intros; apply idpath.
    + intros; apply idpath.
Defined.

(** ** Action of functors on isos. *)
Section Functors_on_isos.

(* TODO: functor_on_inv_from_iso should have implicit arguments *)

Lemma disp_functor_on_iso_disp_aux1 {C C'} {F}
    {D : disp_cat C} {D' : disp_cat C'}
    (FF : disp_functor F D D')
    {x y} {xx : D x} {yy} {f : iso x y}
    (ff : xx -->[f] yy)
    (Hff : is_iso_disp f ff)
  : transportf _ (functor_on_inv_from_iso F f)
      (# FF (inv_mor_disp_from_iso Hff))
    ;; # FF ff
  = transportb _ (iso_after_iso_inv _) (id_disp _).
Proof.
  etrans. apply mor_disp_transportf_postwhisker.
  etrans. apply maponpaths, @pathsinv0, disp_functor_comp_var.
  etrans. apply transport_f_f.
  etrans. apply maponpaths, maponpaths, iso_disp_after_inv_mor.
  etrans. apply maponpaths, disp_functor_transportf.
  etrans. apply transport_f_f.
  etrans. apply maponpaths, disp_functor_id.
  etrans. apply transport_f_b.
  unfold transportb. apply maponpaths_2, homset_property.
Qed.

Lemma disp_functor_on_iso_disp_aux2 {C C'} {F}
    {D : disp_cat C} {D' : disp_cat C'}
    (FF : disp_functor F D D')
    {x y} {xx : D x} {yy} {f : iso x y}
    (ff : xx -->[f] yy)
    (Hff : is_iso_disp f ff)
  : # FF ff
    ;; transportf _ (functor_on_inv_from_iso F f)
         (# FF (inv_mor_disp_from_iso Hff))
  =
    transportb _ (iso_inv_after_iso (functor_on_iso _ _)) (id_disp (FF x xx)).
Proof.
  etrans. apply mor_disp_transportf_prewhisker.
  etrans. apply maponpaths, @pathsinv0, disp_functor_comp_var.
  etrans. apply transport_f_f.
  etrans. apply maponpaths, maponpaths, inv_mor_after_iso_disp.
  etrans. apply maponpaths, disp_functor_transportf.
  etrans. apply transport_f_f.
  etrans. apply maponpaths, disp_functor_id.
  etrans. apply transport_f_f.
  unfold transportb. apply maponpaths_2, homset_property.
Qed.

(** Let's see how [disp_functor]s behave on [iso_disp]s *)
(** TODO: consider naming *)
(* Undelimit Scope transport. *)
Definition disp_functor_on_is_iso_disp {C C'} {F}
    {D : disp_cat C} {D' : disp_cat C'}
    (FF : disp_functor F D D')
    {x y} {xx : D x} {yy} {f : iso x y}
    {ff : xx -->[f] yy} (Hff : is_iso_disp f ff)
    : is_iso_disp (functor_on_iso F f) (# FF ff).
Proof.
  exists (transportf _ (functor_on_inv_from_iso F f)
           (# FF (inv_mor_disp_from_iso Hff))); split.
  - apply disp_functor_on_iso_disp_aux1.
  - apply disp_functor_on_iso_disp_aux2.
Defined.

Definition disp_functor_on_iso_disp {C C'} {F}
    {D : disp_cat C} {D' : disp_cat C'}
    (FF : disp_functor F D D')
    {x y} {xx : D x} {yy} {f : iso x y}
    (ff : iso_disp f xx yy)
  : iso_disp (functor_on_iso F f) (FF _ xx) (FF _ yy)
:= (_ ,, disp_functor_on_is_iso_disp _ ff).

End Functors_on_isos.


(** ** Properties of functors *)

Section Functor_Properties.

Definition disp_functor_ff {C C'} {F}
  {D : disp_cat C} {D' : disp_cat C'} (FF : disp_functor F D D')
:=
  ∏ x y (xx : D x) (yy : D y) (f : x --> y),
    isweq (fun ff : xx -->[f] yy => # FF ff).

Section ff_reflects_isos.

(* TODO: Try making FF implicit, since it can be inferred from [FF_ff]. *)
Context {C C' : category}
        {F : functor C C'}
        {D : disp_cat C}
        {D' : disp_cat C'}
        (FF : disp_functor F D D')
        (FF_ff : disp_functor_ff FF).

Definition disp_functor_ff_weq {x y} xx yy f
  := weqpair _ (FF_ff x y xx yy f).
Definition disp_functor_ff_inv {x y} {xx} {yy} {f : x --> y}
  := invmap (disp_functor_ff_weq xx yy f).

(* TODO: add a general version [disp_functor_ff_inv_transportf], where the transportf on the LHS is arbitrary. *)
Lemma disp_functor_ff_inv_transportf
    {x y : C} {f f' : x --> y} (e : f = f')
    {xx : D x} {yy : D y} (ff : FF _ xx -->[(#F)%cat f] FF _ yy)
  : disp_functor_ff_inv (transportf _ (maponpaths (# F )%cat e) ff)
    =
    transportf _ e (disp_functor_ff_inv ff).
Proof.
  induction e.
  apply idpath.
Qed.

(* TODO: move the transport to the RHS. *)
Lemma disp_functor_ff_inv_identity {x : C} (xx : D x)
  : disp_functor_ff_inv (transportb _ (functor_id F _ ) (id_disp (FF _ xx)))
  = id_disp xx.
Proof.
  apply invmap_eq.
  apply pathsinv0.
  apply (disp_functor_id FF).
Qed.

(* TODO: move the transport to the RHS. *)
Lemma disp_functor_ff_inv_compose {x y z : C} {f : x --> y} {g : y --> z}
    {xx} {yy} {zz}
    (ff : FF _ xx -->[(#F)%cat f] FF _ yy) (gg : FF _ yy -->[(#F)%cat g] FF _ zz)
  : disp_functor_ff_inv (transportb _ (functor_comp F _ _ ) (ff ;; gg))
  = disp_functor_ff_inv ff ;; disp_functor_ff_inv gg.
Proof.
  apply invmap_eq. cbn.
  apply pathsinv0.
  etrans. apply (disp_functor_comp FF).
  apply maponpaths.
  etrans. apply maponpaths. exact (homotweqinvweq _ _).
  apply maponpaths_2. exact (homotweqinvweq _ _).
Qed.

Definition disp_functor_ff_reflects_isos
  {x y} {xx : D x} {yy : D y} {f : iso x y}
  (ff : xx -->[f] yy) (isiso: is_iso_disp (functor_on_iso F f) (# FF ff))
  : is_iso_disp _ ff.
Proof.
  set (FFffinv := inv_mor_disp_from_iso isiso).
  set (FFffinv' := transportb _ (functor_on_inv_from_iso _ _ ) FFffinv).
  set (ffinv := disp_functor_ff_inv FFffinv').
  exists ffinv.
  split.
  - unfold ffinv. unfold FFffinv'.
    admit.
  - admit.
Abort.

End ff_reflects_isos.

(** Given a base functor [F : C —> C'] and a displayed functor [FF : D' -> D] over it, there are two different “essential surjectivity” conditions one can put on [FF].

Given [c : C] and [d : D' (F c)], one can ask for a lift of [d] either in [D c] itself, or more generally in some fiber [D c'] with [c'] isomorphic to [c].

The second version is better-behaved in general; but the stricter first version is equivalent when [D] is an isofibration, and is simpler to work with.  So we call the second version “essentially split surjective”, [disp_functor_ess_split_surj], and the first “displayed ess. split surj.”, [disp_functor_disp_ess_split_surj].
*)

Definition disp_functor_ess_split_surj {C' C} {F}
  {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor F D D')
  : UU
:=
  ∏ x (xx : D' (F x)),
    ∑ y : C,
    ∑ i : iso y x,
    ∑ yy : D y,
      iso_disp (functor_on_iso F i) (FF _ yy) xx.

Definition disp_functor_disp_ess_split_surj {C' C} {F}
  {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor F D D')
  : UU
:=
  ∏ x (xx : D' (F x)),
    ∑ (yy : D x),
      iso_disp (identity_iso _) (FF _ yy) xx.

(* TODO: add access functions for these. *)

End Functor_Properties.

(** ** Total functors of displayed functors*)
Section Total_Functors.

Definition total_functor_data {C' C} {F}
    {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor F D' D)
  : functor_data (total_category D') (total_category D).
Proof.
  use tpair.
  - intros xx. exists (F (pr1 xx)). exact (FF _ (pr2 xx)).
  - intros xx yy ff. exists (# F (pr1 ff))%cat. exact (# FF (pr2 ff)).
Defined.

Definition total_functor_axioms {C' C} {F}
    {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor F D' D)
  : is_functor (total_functor_data FF).
Proof.
  split.
  - intros xx; use total2_paths_f.
      apply functor_id.
    etrans. apply maponpaths, disp_functor_id.
    apply transportfbinv.
  - intros xx yy zz ff gg; use total2_paths_f; simpl.
      apply functor_comp.
    etrans. apply maponpaths, disp_functor_comp.
    apply transportfbinv.
Qed.

Definition total_functor {C' C} {F}
    {D' : disp_cat C'} {D : disp_cat C} (FF : disp_functor F D' D)
  : functor (total_category D') (total_category D)
:= (total_functor_data FF,, total_functor_axioms FF).

End Total_Functors.

End Disp_Functor.

(* Redeclare notations globally: *)

Notation "# F" := (disp_functor_on_morphisms F)
  (at level 3) : mor_disp_scope.

(** ** A functor of displayed categories from reindexing *)

Section reindexing_disp_functor.

Context {C C' : category} (F : functor C C') (D' : disp_cat C').

Definition reindex_disp_functor : disp_functor F (reindex_disp_cat F D') D'.
Proof.
  use tpair.
  - use tpair.
    + cbn. intro x. exact (idfun _ ).
    + cbn. intros x x' d d' f.  exact (idfun _ ).
  - abstract (
        split;
        [intros; apply idpath |];
        intros; apply idpath
      ).
Defined.

End reindexing_disp_functor.


(** ** Natural Transformations *)
Section Disp_Nat_Trans.

Definition disp_nat_trans_data
  {C' C : precategory_data}
  {F' F : functor_data C' C}
  (a : forall x, F' x --> F x)
  {D' : disp_cat_data C'}
  {D : disp_cat_data C}
  (R' : disp_functor_data F' D' D)
  (R : disp_functor_data F D' D) :=
forall (x : C')  (xx : D' x),
      R' x  xx -->[ a x ] R x xx .
(*
Check @nat_trans_ax.

@nat_trans_ax
     : ∏ (C C' : precategory_data) (F F' : functor_data C C')
       (a : nat_trans F F') (x x' : C) (f : x --> x'),
       (# F f ;; a x')%mor = (a x ;; # F' f)%mor
*)

Definition disp_nat_trans_axioms
  {C' C : precategory_data}
  {F' F : functor_data C' C}
  {a : nat_trans F' F}
  {D' : disp_cat_data C'}
  {D : disp_cat_data C}
  {R' : disp_functor_data F' D' D}
  {R : disp_functor_data F D' D}
  (b : disp_nat_trans_data a R' R) : UU
 :=
   forall (x' x : C') (f : x' --> x)
          (xx' : D' x') (xx : D' x)
          (ff : xx' -->[ f ] xx),
     # R'  ff ;; b _ xx =
     transportb _ (nat_trans_ax a _ _ f ) (b _ xx' ;; # R ff).

Lemma isaprop_disp_nat_trans_axioms
  {C' C : category}
  {F' F : functor_data C' C}
  (a : nat_trans F' F)
  {D' : disp_cat_data C'}
  {D : disp_cat C}
  {R' : disp_functor_data F' D' D}
  {R : disp_functor_data F D' D}
  (b : disp_nat_trans_data a R' R)
  :
    isaprop (disp_nat_trans_axioms b).
Proof.
  repeat (apply impred; intro).
  apply homsets_disp.
Qed.

Definition disp_nat_trans
  {C' C : precategory_data}
  {F' F : functor_data C' C}
  (a : nat_trans F' F)
  {D' : disp_cat_data C'}
  {D : disp_cat_data C}
  (R' : disp_functor_data F' D' D)
  (R : disp_functor_data F D' D) : UU :=
  ∑ b : disp_nat_trans_data a R' R,
    disp_nat_trans_axioms b.

Definition disp_nat_trans_pr1
  {C' C : precategory_data}
  {F' F : functor_data C' C}
  {a : nat_trans F' F}
  {D' : disp_cat_data C'}
  {D : disp_cat_data C}
  {R' : disp_functor_data F' D' D}
  {R : disp_functor_data F D' D}
  (b : disp_nat_trans a R' R)
  {x : C'}  (xx : D' x):
    R' x  xx -->[ a x ] R x xx
  := pr1 b x xx.

Coercion disp_nat_trans_pr1 : disp_nat_trans >-> Funclass.

Definition disp_nat_trans_ax
  {C' C : precategory_data}
  {F' F : functor_data C' C}
  {a : nat_trans F' F}
  {D' : disp_cat_data C'}
  {D : disp_cat_data C}
  {R' : disp_functor_data F' D' D}
  {R : disp_functor_data F D' D}
  (b : disp_nat_trans a R' R)
  {x' x : C'}
  {f : x' --> x}
  {xx' : D' x'}
  {xx : D' x}
  (ff : xx' -->[ f ] xx):
  # R'  ff ;; b _ xx =
  transportb _ (nat_trans_ax a _ _ f ) (b _ xx' ;; # R ff)
  :=
  pr2 b _ _ f _ _ ff.

Lemma disp_nat_trans_ax_var
  {C' C : precategory_data}
  {F' F : functor_data C' C}
  {a : nat_trans F' F}
  {D' : disp_cat_data C'}
  {D : disp_cat_data C}
  {R' : disp_functor_data F' D' D}
  {R : disp_functor_data F D' D}
  (b : disp_nat_trans a R' R)
  {x' x : C'}
  {f : x' --> x}
  {xx' : D' x'}
  {xx : D' x}
  (ff : xx' -->[ f ] xx):
  b _ xx' ;; # R ff =
  transportf _ (nat_trans_ax a _ _ f) (# R'  ff ;; b _ xx).
Proof.
  apply pathsinv0, transportf_pathsinv0.
  apply pathsinv0, disp_nat_trans_ax.
Defined.


(** identity disp_nat_trans *)

Definition disp_nat_trans_id_ax
  {C' C : category}
  {F': functor_data C' C}
  {D' : disp_cat_data C'}
  {D : disp_cat C}
  (R' : disp_functor_data F' D' D)
  : @disp_nat_trans_axioms _ _ _ _
                           (nat_trans_id _ )
                           _ _ R' R' (λ (x : C') (xx : D' x), id_disp (R' x xx)).
Proof.
  intros x' x f xx' xx ff;
  etrans; [ apply id_right_disp |];
  apply transportf_comp_lemma;
  apply pathsinv0.
  etrans; [apply id_left_disp |].
  unfold transportb.
  apply maponpaths_2, homset_property.
Qed.


Definition disp_nat_trans_id
  {C' C : category}
  {F': functor_data C' C}
  {D' : disp_cat_data C'}
  {D : disp_cat C}
  (R' : disp_functor_data F' D' D)
  : disp_nat_trans (nat_trans_id F') R' R'.
Proof.
  use tpair.
  - intros x xx.
    apply id_disp.
  - apply disp_nat_trans_id_ax.
Defined.


(** composition of disp_nat_trans *)

Definition disp_nat_trans_comp_ax
  {C' C : category}
  {F'' F' F : functor_data C' C}
  {a' : nat_trans F'' F'}
  {a : nat_trans F' F}
  {D' : disp_cat_data C'}
  {D : disp_cat C}
  {R'' : disp_functor_data F'' D' D}
  {R' : disp_functor_data F' D' D}
  {R : disp_functor_data F D' D}
  (b' : disp_nat_trans a' R'' R')
  (b : disp_nat_trans a R' R)
  : @disp_nat_trans_axioms _ _ _ _
        (nat_trans_comp _ _ _ a' a) _ _ R'' R
        (λ (x : C') (xx : D' x), b' x xx ;; b x xx).
Proof.
  intros x' x f xx' xx ff;
  etrans; [ apply assoc_disp |];
  apply transportf_comp_lemma;
  apply transportf_pathsinv0; apply pathsinv0;
  rewrite (disp_nat_trans_ax b');
  etrans; [ apply mor_disp_transportf_postwhisker |];
  apply transportf_comp_lemma;
  apply pathsinv0;
  etrans; [ apply assoc_disp_var |];
  apply pathsinv0;
  apply transportf_comp_lemma;
  apply pathsinv0;
  rewrite (disp_nat_trans_ax_var b);
  rewrite mor_disp_transportf_prewhisker;
  apply transportf_comp_lemma;
  apply pathsinv0;
  etrans; [ apply assoc_disp_var |].
  apply maponpaths_2, homset_property.
Qed.

Definition disp_nat_trans_comp
  {C' C : category}
  {F'' F' F : functor_data C' C}
  {a' : nat_trans F'' F'}
  {a : nat_trans F' F}
  {D' : disp_cat_data C'}
  {D : disp_cat C}
  {R'' : disp_functor_data F'' D' D}
  {R' : disp_functor_data F' D' D}
  {R : disp_functor_data F D' D}
  (b' : disp_nat_trans a' R'' R')
  (b : disp_nat_trans a R' R)
  : disp_nat_trans (nat_trans_comp _ _ _ a' a) R'' R.
Proof.
  use tpair.
  - intros x xx.
    apply (comp_disp (b' _ _ )  (b _ _ )).
  - apply disp_nat_trans_comp_ax.
Defined.

End Disp_Nat_Trans.

(** some TODOs for the displayed-cats library:

- add lemmas connecting with products of cats (as required for displayed bicats)
- add more applications of the displayed arrow category: slices; equalisers, inserters; hence groups etc.

*)
