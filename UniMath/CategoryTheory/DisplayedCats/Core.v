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

(** * Functors

- Reindexing of displayed cats along functors: [reindex_disp_cat]
- Functors into displayed cats, lifting functors into the base: [functor_lifting]
- Functors between displayed cats, over functors between the bases: [disp_functor]
- Natural transformations between these: [disp_nat_trans] *)


(** some TODOs for the displayed-cats library:

- add lemmas connecting with products of cats (as required for displayed bicats)
- add more applications of the displayed arrow category: slices; equalisers, inserters; hence groups etc.

 *)
