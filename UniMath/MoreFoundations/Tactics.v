(************************************************************************

This file contains various useful tactics

************************************************************************)

Require Import UniMath.Foundations.All.

(** A version of "easy" specialized for the needs of UniMath.
This tactic is supposed to be simple and predictable. The goal
is to use it to finish "trivial" goals *)
Ltac easy :=
  trivial; intros; solve
   [ repeat (solve [trivial | apply pathsinv0; trivial] || split)
   | match goal with | H : ∅ |- _ => induction H end
   | match goal with | H : ¬ _ |- _ => induction H; trivial end
   | match goal with | H : _ → ∅ |- _ => induction H; trivial end
   | match goal with | H : _ → _ → ∅ |- _ => induction H; trivial end ].

(** Override the Coq now tactic so that it uses unimath_easy instead *)
Tactic Notation "now" tactic(t) := t; easy.

(* hSet_induction in Foundations is wrong, so redefine it here: *)
Ltac hSet_induction f e := generalize f; apply hSet_rect; intro e; clear f.

(* When the goal is displayed as x=y and the types of x and y are hard to discern,
   use this tactic -- it will add the type to the context in simplified form. *)
Ltac show_id_type := match goal with |- @paths ?ID _ _ => set (TYPE := ID); simpl in TYPE end.

Require Import UniMath.Foundations.Sets UniMath.Foundations.UnivalenceAxiom.

Definition post_cat {X} {x y z:X} {p:y = z} : x = y -> x = z.
Proof. intros q. exact (pathscomp0 q p). Defined.

Definition pre_cat {X} {x y z:X} {p:x = y} : y = z -> x = z.
Proof. intros q. exact (pathscomp0 p q). Defined.

Ltac maponpaths_pre_post_cat :=
  repeat rewrite path_assoc; repeat apply (maponpaths post_cat); repeat rewrite <- path_assoc;
  repeat apply (maponpaths pre_cat); repeat rewrite path_assoc; repeat rewrite maponpathsinv0;
  try reflexivity.

Ltac prop_logic :=
  abstract (intros; simpl;
            repeat (try (apply isapropdirprod);try (apply isapropishinh);apply impred ;intro);
            try (apply isapropiscontr); try assumption) using _L_.

Lemma iscontrweqb' {X Y} (is:iscontr Y) (w:X ≃ Y) : iscontr X.
Proof. intros. apply (iscontrweqb (Y:=Y)). assumption. assumption. Defined.

Ltac intermediate_iscontr  Y' := apply (iscontrweqb (Y := Y')).
Ltac intermediate_iscontr' Y' := apply (iscontrweqb' (Y := Y')).

Ltac isaprop_goal x :=
  let G := match goal with |- ?G => constr:(G) end in
  assert (x : isaprop(G)).

(* less fancy than [isaprop_goal ig.] is [apply isaprop_goal; intro ig.] *)
Definition isaprop_goal X (ig:isaprop X) (f:isaprop X -> X) : X.
Proof. intros. exact (f ig). Defined.

Ltac isaset_goal x :=
  let G := match goal with |- ?G => constr:(G) end in
  assert (x : isaset(G)).

Ltac split3 := split; [| split].
Ltac split4 := split; [| split3].
Ltac split5 := split; [| split4].
Ltac split6 := split; [| split5].
Ltac split7 := split; [| split6].
Ltac split8 := split; [| split7].
Ltac split9 := split; [| split8].
Ltac split10 := split; [| split9].
Ltac split11 := split; [| split10].
Ltac split12 := split; [| split11].
Ltac split13 := split; [| split12].
Ltac split14 := split; [| split13].
Ltac split15 := split; [| split14].
Ltac split16 := split; [| split15].
Ltac split17 := split; [| split16].
Ltac split18 := split; [| split17].
Ltac split19 := split; [| split18].
Ltac split20 := split; [| split19].
Ltac split21 := split; [| split20].
(** this allows to decompose a goal for [prebicat_laws] *)

(** Repeats `t` times and afterwards prints an equivalent `do` statement  *)
Ltac repeatc n t :=
  (t; repeatc (S n) t) || (
    match n with
    | 0 => idtac
    | 1 => idtac t "."
    | S (S _) => idtac "do" n t "."
    end
  ).

Tactic Notation "repeatc" tactic(t) :=
  repeatc 0 t.
