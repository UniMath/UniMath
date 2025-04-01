(** * Sorted types. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2023 *)
(*
This file contains a formalization of _sorted types_, i.e. types indexed by elements of another
type, called _index type_. Notation and terminologies are inspired by Wolfgang Wechler,
_Universal Algebra for Computer Scientist_, Springer.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Export UniMath.Combinatorics.MoreLists.

Require Export UniMath.Algebra.Universal.HVectors.

Declare Scope sorted_scope.

Delimit Scope sorted_scope with sorted.

Local Open Scope sorted_scope.

(** An element of [sUU S] is an [S]-sorted type, i.e., an [S]-indexed family of types. *)

Definition sUU (S: UU): UU := S → UU.
Identity Coercion Id_sUU : sUU >-> Funclass.

(** If [X] and [Y] are [S]-sorted types, then [sfun X Y] is an [S]-sorted mapping, i.e.,
a [S]-indexed family of functions [X s → Y s]. *)

Definition sfun {S: UU} (X Y: sUU S): UU := ∏ s: S, X s → Y s.
Identity Coercion sfun_Id : sfun >-> Funclass.

Notation "x s→ y" := (sfun x y) (at level 99, y at level 200, right associativity): type_scope.

Bind Scope sorted_scope with sUU.

Bind Scope sorted_scope with sfun.

Definition idsfun {S: UU} (X: sUU S): X s→ X := λ s: S, idfun (X s).

Definition scomp {S: UU} {X Y Z: sUU S} (f: Y s→ Z) (g: X s→ Y): sfun X Z
  := λ s: S, (f s) ∘ (g s).

Infix "s∘" := scomp (at level 40, left associativity): sorted_scope.

Definition sunit (S: UU): sUU S := λ σ: S, unit.

Definition tosunit {S: UU} {X: sUU S}: X s→ sunit S := λ σ: S, tounit.

Lemma iscontr_sfuntosunit {S: UU} {X: sUU S}: iscontr (X s→ sunit S).
Proof.
  apply impred_iscontr.
  intros.
  apply iscontrfuntounit.
Defined.

(** An element of [shSet S] is an [S]-sorted set, i.e., an [S]-indexed family of sets. It can be
immediately coerced to an [S]-sorted type. *)

Definition shSet (S: UU): UU := S → hSet.

Definition sunitset (S: UU): shSet S := λ _, unitset.

Lemma isaset_set_sfun_space {S: UU} {X: sUU S} {Y: shSet S}: isaset (X s→ Y).
Proof.
  change (isaset (X s→ Y)).
  apply impred_isaset.
  intros.
  apply isaset_forall_hSet.
Defined.

(** If [X: sUU S], then [star X] is the lifting of [X] to the index type [list S], given
by [star X] [s1; s2; ...; sn] = [X s1 ; X s2 ; ... ; X sn]. *)

Definition star {S: UU} (X: sUU S): sUU (list S) := λ l: list S, hvec (vec_map X l).

Definition setstar {S: UU} (X: shSet S): shSet (list S).
Proof.
  intro l.
  use make_hSet.
  - exact (star X l).
  - unfold star.
    apply isasethvec.
    apply make_hvec.
    intros i.
    rewrite !el_vec_map.
    apply setproperty.
Qed.

Bind Scope hvec_scope with star.

Notation "A ⋆" := (star A) (at level 3, format "'[ ' A '⋆' ']'"): sorted_scope.

(** If [f] is an indexed mapping between [S]-indexed types [X] and [Y], then [starfun X] is the lifting of
[f] to a [list S]-indexed mapping between [list S]-indexed sets [star X] and [star Y].
*)

Definition starfun {S: UU} {X Y: sUU S} (f: sfun X Y) : sfun X⋆ Y⋆ := λ s: list S, h1map f.

Notation "f ⋆⋆" := (starfun f) (at level 3, format "'[ ' f '⋆⋆' ']'"): sorted_scope.

(** Here follows the proof that [starfun] is functorial. Compositionality w.r.t. [s∘] is presented as
[(f s∘ g)⋆⋆ _ x = f⋆⋆ _ (g⋆⋆ _ x)] instead of [(f s∘ g)⋆⋆ = (f⋆⋆) s∘ (g⋆⋆ )] since the former
does not require function extensionality. *)

Lemma staridfun {S: UU} {X: sUU S} (l: list S) (x: X⋆ l): (idsfun X)⋆⋆ _ x = idsfun X⋆ _ x.
Proof.
  apply h1map_idfun.
Defined.

Lemma starcomp {S: UU} {X Y Z: sUU S} (f: Y s→ Z) (g: X s→ Y) (l: list S) (x: X⋆ l)
  : (f s∘ g)⋆⋆ _ x = f⋆⋆ _ (g⋆⋆ _ x).
Proof.
  unfold starfun.
  apply pathsinv0.
  apply h1map_compose.
Defined.

(*indexed hsubtypes*)

Definition shsubtype {S:UU} (X : sUU S) : UU := ∏ s: S, hsubtype (X s).

(*indexed image*)

Definition simage {S:UU} {X Y: sUU S} (f:X s→ Y) : sUU S
  := λ s, image (f s).

Definition shfiber {S:UU} {X Y: sUU S} (f:X s→ Y) : ∏ s, Y s → UU
  := λ (s:S) (y : Y s), (∑ (x : X s), f s x = y).

Definition shfiber_fiber {S:UU} {X Y: sUU S} {f:X s→ Y}
  {s : S} {y : Y s}
  (fib : shfiber f s y)
  : X s := pr1 fib.

Definition shfiber_path {S:UU} {X Y: sUU S} {f:X s→ Y}
  {s : S} {y : Y s}
  (fib : shfiber f s y)
  : f s (shfiber_fiber fib) = y
  := pr2 fib.

Definition simage_shsubtype {S:UU} {X Y : sUU S} (f : X s→ Y)
  : shsubtype Y := λ (s:S) (y : Y s), (∃ (x : X s), f s x = y).

Lemma hvec_of_shfiber {S : UU} {A B : sUU S}
{h : A s→ B} {l : list S}
(bs : hvec (vec_map B l))
(xs : hvec (h1map_vec (shfiber h) bs))
: (h ⋆⋆)%sorted l (h2lower (h2map (λ (s:S) (b : B s), pr1) xs)) = bs.
Proof.
  use hvec_ofpaths.
Defined.

(*TODO: generalize the map in the type of [ys] to any type starting with [is_hinh]*)
Theorem squash_simage
  {S:UU} {X Y : sUU S} (f : X s→ Y)
        (ss : list S)
        (ys : (simage_shsubtype f)⋆ ss)
  {Q:UU} (isQ : isaprop Q) :
  (hvec (h1lower ((shfiber f)⋆⋆ ss (h1map (λ s, pr1) ys))) → Q)
  → Q.
Proof.
  revert ss ys.
  use list_ind.
  - intros t tQ. exact (tQ t).
  - intros ss_hd ss_tl IH ys IHH.
    use (IH (htl ys)).
    intro fib_tl.
    destruct ys as [ys_hd ys_tl].
    destruct ys_hd as [ys_hd ys_hd_is]. (*TODO (?): use accessors instead*)
    use (squash_to_prop ys_hd_is isQ).
    intro fib_hd.
    use IHH.
    use make_dirprod.
    + simpl.
      use fib_hd.
    + use fib_tl.
Qed.

Definition transportf_sfun {X S : UU} {Y: sUU S} (P : X -> sUU S)
           {x1 x2 : X}(e : x1 = x2)(f : P x1 s→ Y) (s:S):
  transportf (λ x, (P x s→ Y)) e f s = (f s) ∘ (transportb (λ x, P x s) e).
Proof.
  intros. induction e. apply idpath.
Defined.

Definition transportb_funextfun_hvec {S:UU}
  {n:nat} {v: vec S n}
  (F F' : sUU S) (H : F ~ F')
  (f' : hvec (vec_map F' v))
  : transportb (λ x : sUU S, hvec (vec_map x v))
    (funextsec _ F F' H) f'
  = h1map (λ s, transportb (idfun UU) (H s)) f'.
Proof.
  revert n v f'.
  use (vec_ind _ _).
  - intro f'.
    use proofirrelevancecontr.
    use iscontrunit.
  - intros s n v IH f'.
    use dirprod_paths.
    + simpl.
      eapply pathscomp0.
      { use pr1_transportb. }
      use (transportb_funextfun (idfun UU)).
    + simpl.
      eapply pathscomp0.
      { use pr2_transportb. }
      use IH.
Defined.