(** This file contains various useful tactics. *) 
(** ** Contents:

- [unimath_easy]
- [now]
- [hSet_induction]
- [hlevelmatch] - Author: Langston Barrett (@siddharthist)
- [hleveltac] - Author: Langston Barrett (@siddharthist)
- [hleveltacS] - Author: Langston Barrett (@siddharthist)
 *)

Require Import UniMath.MoreFoundations.Foundations.

(** A version of "easy" specialized for the needs of UniMath.
This tactic is supposed to be simple and predictable. The goal
is to use it to finish "trivial" goals *)
Ltac unimath_easy :=
  trivial; intros; solve
   [ repeat (solve [trivial | apply pathsinv0; trivial] || split)
   | match goal with | H : ∅ |- _ => induction H end
   | match goal with | H : ¬ _ |- _ => induction H; trivial end
   | match goal with | H : _ → ∅ |- _ => induction H; trivial end
   | match goal with | H : _ → _ → ∅ |- _ => induction H; trivial end ].

(** Override the Coq now tactic so that it uses unimath_easy instead *)
Tactic Notation "now" tactic(t) := t; unimath_easy.

(* hSet_induction in Foundations is wrong, so redefine it here: *)
Ltac hSet_induction f e := generalize f; apply hSet_rect; intro e; clear f.

(** The tactics hlevelmatch performs one "step" in proving that a type has a
    given hlevel. Specifically, it applies one of several lemmas based on the
    type formers used in the expression. It is mainly used as a helper for the
    more fully automated tactic [hleveltac].

    Here are some ideas for improvement:
    - When proving a [homot], use [impred]
    - Reason more about coproducts using [isofhlevelssncoprod]
    - Reason that terms using [hProppair] are of any hlevel higher than [iscontr]
    - Reason about weak equivalences, as in [isofhlevelweqf] and [isofhlevelweqb]
    - Reason about double negation using [isapropdneg] and [isapropaninvprop]
    - If we have Z : hSet, and our goal is isaset (pr1hSet Z), solve it.
    - If we have Z : hProp, and our goal is isaprop (hProptoType Z), solve it.
    - Do the more general version of the above two (unfold them to ∑-types and pr1)?

    We don't include [isapropneg] because its proof includes an axiom.
 *)
Ltac hlevelmatch :=
  multimatch goal with

  (** h-levels involving positive type formers *)
  (*01*)| [ |- isofhlevel ?n unit ] => apply iscontrunit
  (*02*)| [ |- isofhlevel ?n (?X × ?Y) ] => apply isofhleveldirprod
  (*03*)| [ |- isofhlevel ?n (total2 ?Y) ] => apply isofhleveltotal2
  (*04*)| [ |- isofhlevel ?n (?X -> ?Y) ] => apply impred; intro
  (*05*)| [ |- isofhlevel ?n (forall _ : ?X, _) ] => apply impred; intro

  (** h-levels involving negative type formers. Some of these are only
      useful if we have the appropriate hypothesis. For instance, when proving
      <<
        isofhlevel n (X × Y)
      >>
      we almost always want to split into cases for A and B. However, when
      proving
      <<
        isofhlevel n Y
      >>
      we rarely want to instead prove
      <<
        isofhlevel n (X ⨿ Y)
      >>
      unless this is a hypothesis of our context. We try to apply *all*
      hypotheses in this way, which is not the best, but it works. Someone who
      knows more about Ltac might want to fix this.
   *)
  (*06*)| [ H : (?X -> empty) |- isofhlevel _ ?X ] => apply isapropifnegtrue
  (*07*)| [ H : _ |- isofhlevel (S ?n) _ ] => apply (@isofhlevelsnsummand1 n _ _ H)
  (*07*)| [ H : _ |- isofhlevel (S ?n) _ ] => apply (@isofhlevelsnsummand2 n _ _ H)

  (*08*)| [|- isofhlevel _ empty] => apply isapropempty
  (*09*)| [|- isofhlevel _ (isaset _)] => apply isapropisaset
  (*10*)| [|- isofhlevel _ (isofhlevel _ _)] => apply isapropisofhlevel
  end.

(** This tactic attempts to automatically (partially) solve goals of the form
    [isofhlevel]. It breaks the goal down using lemmas about hlevels of terms
    formed using various constructors, and recurses on subterms.
 *)
Ltac hleveltac :=
  intros;
  (** We unfold isaprop so as to match directly against isofhlevel ?n ?X, for
      more generality. *)
  unfold isaprop in *;

  (** For similar reasons, we replace iscontr with isofhlevel *)
  change iscontr with (isofhlevel 0) in *;
  change isaset with (isofhlevel 2) in *;
  repeat (hlevelmatch ||
          (** It's possible we just need to unfold a bit more. Try this. *)
          multimatch goal with
          | |- isofhlevel ?n (?f _) => try (unfold f)
          | |- isofhlevel ?n ?X => try (unfold X)
          | |- _ => idtac (* we never want the match to fail *)
          end);
  try assumption.

(** hlevel is cumulative, so we can try removing successors until it
    works. This isn't the default because we don't want to stick users with a
    goal of the form isofhlevel 0 X if nothing works. Optimally, this would
    backtrack, but I'm not sure how to get that right.

    We use easy instead of assumption because this one sometimes generates
    a goal like isofhlevel n (x y) where we have ∏ y, isofhlevel n (x y) in
    the context.
 *)
Ltac hleveltacS :=
  repeat hleveltac;
  repeat (apply hlevelntosn; hleveltac);
  easy || fail "hleveltacS could not solve this goal".
