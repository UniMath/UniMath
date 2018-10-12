(* from Peter Lumsdaine, Aug 29, 2018 *)

(*
  Prompted by a question of Dan Grayson:

  If you assume a relation is a well-order in the sense of having induction into families of propositions,
  does it then have induction into arbitrary type families?
*)

Set Universe Polymorphism.

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Local Arguments funextsec {_ _ _ _} _.
Local Arguments toforallpaths {_ _ _ _} _.

(* A predicate is called hereditary with respect to a relation if whenever it holds everywhere below
   some element, it holds at that element.  Hereditariness is the usual hypothesis required for
   well-founded induction into a predicate. *)

Definition hereditary {X} (lt : X -> X -> Type) (P : X -> Type) : Type
  := ∏ x, (∏ y, lt y x -> P y) -> P x.

Definition strongly_well_founded {X} (lt : X -> X -> Type)
  := ∏ (P : X -> Type) (H : hereditary lt P),
     ∑ (f : ∏ x, P x), ∏ x, f x = H x (λ y _, f y).

Definition weakly_well_founded {X} (lt : X -> X -> Type)
  := ∏ P : X -> hProp, hereditary lt P -> ∏ x, P x.

Section Attempts.

  Context {X} (lt : X -> X -> Type).

  Notation "x < y" := (lt x y).

  Definition chain (n : nat) (x y:X) : Type.
  (* An element of [chain n] will be an ascending sequence [x = s_1 < t_1 = s_2 < t_2 = ... = s_n < t_n = y].
     We use this to implement the transitive reflexive closure of [lt]. *)
  Proof.
    revert x y.
    induction n as [|n H].
    - intros x y. exact (x = y).
    - intros x y. exact (∑ s t, H x s × s<t × t=y).
  Defined.

  Definition le (x y : X) : Type := ∑ n, chain n x y.

  Notation "x ≤ y" := (le x y) (at level 70).

  Definition nil {x} : x≤x := (0,,idpath x).

  Definition cons' {x x' y z} (p : z ≤ y) (l : y < x') (e : x' = x) : z ≤ x.
  Proof.
    induction p as [n c].
    exact (S n,,y,,x',,c,,l,,e).
  Defined.

  Definition cons1 {n x y z z'} (e : z = z') (l : z' < y) (c : chain n y x) : chain (S n) z x.
  Proof.
    revert e l x c.
    induction n as [|n H].
    - intros e l x c. exact (z',,y,,e,,l,,c).
    - intros e l x c. induction c as [s [t [c' [l' e']]]].
      exact (s,,t,,H e l s c',,l',,e').
  Defined.

  Definition cons {x y z z'} (e : z = z') (l : z' < y) (p : y ≤ x) : z ≤ x.
  Proof.
    induction p as [n c]. exists (S n). exact (cons1 e l c).
  Defined.

  Lemma assoc {w w' x y z' z} (e : w=w') (l : w'<x) (p : x≤y) (m : y<z') (f : z'=z) :
    cons e l (cons' p m f) = cons' (cons e l p) m f.
  (* This associativity property is used implicitly below, so let's check it.
     Here we see the advantage of defining [x≤y] the way we did, as it makes some identities judgmental. *)
  Proof.
    reflexivity.
  Defined.

  Context (P : X -> Type) (H : hereditary lt P).

  (* An “attempt” up to x: a partial function into P defined just for all y ≤ x, and guided by the
     term H witnessing the hereditariness of P.

     Caveat: we should actually have said not “partial function” but “multivalued partial function”,
     since (y ≤ x) isn’t necessarily an hprop. *)

  Definition guided_by x (f : ∏ y, y ≤ x -> P y) H
    := ∏ y pyx, f y pyx = H y (λ z l, f z (cons (idpath z) l pyx)).

  Definition attempt x := ∑ f, guided_by x f H.

  Definition attempt_fun {x} : attempt x -> (∏ y _, P y) := pr1.
  Coercion attempt_fun : attempt >-> Funclass.

  Definition attempt_comp {x} : ∏ (f : attempt x), _ := pr2.

  Definition disassemble_attempt {x} : attempt x -> (∏ y w, y<w -> w=x -> attempt y).
  Proof.
    intros f y' y l e. exists (λ t p, f t (cons' p l e)).
    intros z p. use attempt_comp.
  Defined.

  Definition assemble_attempt {x}
    : (∏ y y', y<y' -> y'=x -> attempt y) -> attempt x.
  Proof.
    intros fs. use tpair.
    - intros y [[|n] c].
      + apply H. intros z lzy. exact (fs z y lzy c z nil).
      + induction c as [s [t [c' [l' e']]]]. exact (fs s t l' e' y (n,,c')).
    - intros y [[|n] c].
      + reflexivity.
      + use attempt_comp.
  Defined.

  Definition attempt_lemma {x} (f g : attempt x)
             (T : (∏ y (pyx : y ≤ x), f y pyx = g y pyx) -> Type) :
    (∏ (e : attempt_fun f = attempt_fun g), T (λ y pyx, toforallpaths (toforallpaths e y) pyx))
    -> ∏ e, T e.
  Proof.
    intros HT e.
    simple refine (transportf _ _ (HT _)).
    { apply funextsec; intros y; apply funextsec; intros pyx.
      eapply pathscomp0.
      { refine (toforallpaths _ _). apply maponpaths.
        refine (toforallpaths _ _). apply toforallpaths_funextsec. }
      refine (toforallpaths _ _). apply toforallpaths_funextsec. }
  Defined.

  Definition attempt_paths {x} (f g : attempt x) :
      ∏ (e_fun : ∏ y pyx, f y pyx = g y pyx),
      (∏ y pyx,
          attempt_comp f y pyx
           @ maponpaths (H y) (funextsec (λ z, funextsec (λ lzy, e_fun z (cons (idpath z) lzy pyx))))
          = e_fun y pyx @ attempt_comp g y pyx)
    -> f = g.
  Proof.
    use attempt_lemma.
    intros e. induction f as [f0 f1], g as [g0 g1]. cbn in e. induction e.
    cbn.
    intros e_comp. apply maponpaths.
    apply funextsec; intros y; apply funextsec; intros pyx.
    refine (!_ @ e_comp _ _).
    refine (maponpaths _ _ @ pathscomp0rid _).
    refine (@maponpaths _ _ _ _ (idpath _) _).
    refine (maponpaths funextsec _ @ funextsec_toforallpaths _).
    apply funextsec; intros z.
    apply (funextsec_toforallpaths (idpath _)).
  Defined.

  Definition assemble_disassemble {x} (f : attempt x)
    : assemble_attempt (disassemble_attempt f) = f.
  Proof.
    use attempt_paths.
    - intros y [[|n] pyx].
      + apply pathsinv0. use attempt_comp.
      + reflexivity.
    - intros y [[|n] pyx].
      + cbn.
        refine (@maponpaths _ _ _ _ (idpath _) _ @ ! pathsinv0l _).
        refine (maponpaths _ _ @ funextsec_toforallpaths _).
        apply funextsec; intros z.
        apply (funextsec_toforallpaths (idpath _)).
      + refine (maponpaths _ _ @ pathscomp0rid _).
        refine (@maponpaths _ _ _ _ (idpath _) _).
        refine (maponpaths funextsec _ @ funextsec_toforallpaths _).
        apply funextsec; intros w.
        apply (funextsec_toforallpaths (idpath _)).
  Defined.

  Context (wwf_lt : weakly_well_founded lt).

  Definition iscontr_attempt : ∏ x, iscontr (attempt x).
  Proof.
    apply (wwf_lt (λ x, iscontr_hProp (attempt x))).
    intros x IH.
    apply (iscontrretract _ _ assemble_disassemble).
    apply impred_iscontr; intro z; apply impred_iscontr; intro z';
      apply impred_iscontr; intro l; apply impred_iscontr; intro e.
    induction e.
    exact (IH z l).
  Defined.

  Local Definition the_attempt x : attempt x
    := iscontrpr1 (iscontr_attempt x).

  Local Definition the_value x : P x
    := the_attempt x x nil.

  Local Definition the_comp x : the_value x = H x (λ y l, the_value y).
  Proof.
    assert (e : the_attempt x = assemble_attempt (λ y _ _ _, the_attempt y)).
    { apply pathsinv0, iscontr_uniqueness. }
    exact (toforallpaths (toforallpaths (maponpaths attempt_fun e) x) nil).
  Defined.

End Attempts.

Arguments le {_ _} _ _.

(* The main theorem of this file, due to Peter Lumsdaine. *)

Theorem strongly_from_weakly_well_founded {X} (lt : X -> X -> Type)
  : weakly_well_founded lt -> strongly_well_founded lt.
Proof.
  intros wwf_lt P H_P.
  exists (the_value lt P H_P wwf_lt).
  exact  (the_comp  lt P H_P wwf_lt).
Defined.

Require Export UniMath.Combinatorics.OrderedSets.

Section OrderedSets.

  (* These facts might be well known. *)

  Context {X:UU} (lt : X -> X -> Type).

  Context (wwf_lt : weakly_well_founded lt).

  Notation "x < y" := (lt x y).

  Open Scope logic.

  Lemma irrefl z : ¬ (z < z).
  Proof.
    (** This proof is provided by Marc Bezem. *)
    intro l. use (wwf_lt (λ t, ¬ (z=t))).
    - intros x h. intro e. induction e. exact (h z l (idpath z)).
    - exact z.
    - reflexivity.
  Defined.

  Lemma notboth {r s} : (r<s) -> ¬ (s<r).
  Proof.
    (** This proof is modeled after Marc's proof above. *)
    intros l m. use (wwf_lt (λ t, ¬ ((r=t) ⨿ (s=t)))).
    - intros x h. intro c. induction c as [e|e].
      + induction e. exact (h s m (ii2 (idpath s))).
      + induction e. exact (h r l (ii1 (idpath r))).
    - exact r.
    - exact (ii1 (idpath r)).
  Defined.

  Lemma diagRecursion
        (f : nat -> nat -> Type)
        (init : ∏ n, f 0 n)
        (ind : ∏ m n, f m (S n) -> f (S m) n):
    ∏ m n, f m n.
  Proof.
    intros m.
    induction m as [|m H].
    - exact init.
    - intros n. apply ind. apply H.
  Defined.

  Lemma chaintrans {x y z m n} : chain lt m x y -> chain lt n y z -> chain lt (m+n) x z.
  Proof.
    revert m n y.
    apply (diagRecursion (λ m n, ∏ y, chain lt m x y → chain lt n y z → chain lt (m + n) x z)).
    - intros k y c. induction c. exact (idfun _).
    - intros r s p y c d.
      induction c as [u [t [b [k e]]]].
      change ((S r) + s) with (S (r+s)).
      rewrite plus_n_Sm.
      apply (p u b); clear p b x r.
      induction e.
      exact (cons1 lt (idpath u) k d).
  Defined.

End OrderedSets.
