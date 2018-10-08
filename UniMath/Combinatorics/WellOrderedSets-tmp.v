(* from Peter Lumsdaine, Aug 29, 2018 *)

(*
Attempt at an answer to a question of Dan Grayson:

if you assume a relation is a well-order in the sense of having induction into families of _propositions_,
does it then have induction into arbitrary type families?
*)

Set Universe Polymorphism.

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Local Arguments funextsec {_ _ _ _} _.

Section Background.

  (* Hopefully already somewhere in library: *)
  Lemma funextsec_refl {A} {B} (f : forall x:A, B x)
    : funextsec (λ x, idpath (f x)) = idpath f.
  Proof.
    exact (funextsec_toforallpaths (idpath f)).
  Defined.

End Background.

(* A predicate is _hereditary_ w.r.t. a relation if whenever it holds everywhere below some element, it holds at some element.

Hereditariness is the usual hypothesis required for well-founded induction into a predicate. *)
Definition hereditary {X} (lt : X -> X -> UU) (P : X -> UU) : UU
  := forall x, (forall y, lt y x -> P y) -> P x.

Definition strongly_well_founded {X} (lt : X -> X -> UU)
  := forall (P : X -> UU) (H_P : hereditary lt P),
    ∑ (f : forall x, P x), forall x, f x = H_P x (λ y lxy, f y).

Definition weakly_well_founded {X} (lt : X -> X -> UU)
  := forall P : X -> hProp, hereditary lt (λ x, P x) -> forall x, P x.

Section Attempts.

  Context {X} (lt : X -> X -> UU).

  Notation "x < y" := (lt x y).

  (* a list-like/path-like presentation of the reflexive+transitive closure of the relation [lt] *)
  Inductive ltstar : X -> X -> UU :=
    | nil (x:X) : ltstar x x
    | cons' {x y z} (pzy : ltstar z y) (lyx : y < x) : ltstar z x.
  Notation "x <* y" := (ltstar x y) (at level 70).

  Fixpoint cons {x y z} (l : z < y) (p : y <* x) : z <* x.
  Proof.
    induction p as [ y | w x' y' p' _ l' ].
    - exact (cons' (nil z) l).
    - exact (cons' (cons _ _ _ l p') l').
  Defined.

  Context (P : X -> UU) (H : hereditary lt P).

  (* An “attempt” up to x: a partial function into P defined for all y <* x, and satisfying the
     specification given by hereditariness of P.

     Caveat: we should actually have said not “partial function” but “multivalued partial function”,
     since (y <* x) isn’t necessarily an hprop. *)

  Definition attempt (x:X)
    := ∑ (f : forall y, y <* x -> P y), forall y pyx, f y pyx = H y (λ z lzy, f z (cons lzy pyx)).

  Definition attempt_fun {x} : attempt x -> (forall y pyx, P y) := pr1.
  Coercion attempt_fun : attempt >-> Funclass.

  Definition attempt_comp {x} : forall (f : attempt x), _ := pr2.

  Definition disassemble_attempt {x:X}
    : attempt x -> (forall y, y < x -> attempt y).
  Proof.
    intros f y lyx.
    exists (λ z pzy, f _ (cons' pzy lyx)).
    intros z pzy.
    apply attempt_comp.
  Defined.

  Definition assemble_attempt {x:X}
    : (forall y, y < x -> attempt y) -> attempt x.
  Proof.
    intros fs. use tpair.
    - intros y pyx. induction pyx as [ x | x y z pzy _ lyx ].
      + apply H. intros y lyx. exact (fs _ lyx _ (nil _)).
      + exact (fs _ lyx _ pzy).
    - intros y pyx; induction pyx as [ x | x y z pzy lyx ]; cbn.
      + apply idpath.
      + apply attempt_comp.
  Defined.

  Definition attempt_paths {x:X} (f g : attempt x)
      (e_fun : forall y pyx, f y pyx = g y pyx)
      (e_comp : forall y pyx,
          attempt_comp f y pyx
           @ (maponpaths (H y) (funextsec (λ z, funextsec (λ lzy, e_fun z (cons lzy pyx)))))
          = e_fun y pyx @ attempt_comp g y pyx)
    : f = g.
  Proof.
    revert e_fun e_comp.
    assert (wlog
      : forall (T : (∏ (y:X) (pyx : y <* x), f y pyx = g y pyx) -> UU),
        (forall (e : attempt_fun f = attempt_fun g),
              T (λ y pyx, toforallpaths _ _ _ (toforallpaths _ _ _ e y) pyx))
        -> forall e, T e).
    { intros T HT e.
      transparent assert (e' : (attempt_fun f = attempt_fun g)).
        apply funextsec; intros y; apply funextsec; intros pyx; apply e.
      refine (transportb T _ (HT e')).
      apply funextsec; intros y; apply funextsec; intros pyx.
      apply pathsinv0.
      eapply pathscomp0.
      { refine (toforallpaths _ _ _ _ _); apply maponpaths.
        refine (toforallpaths _ _ _ _ _); apply toforallpaths_funextsec.
      }
      refine (toforallpaths _ _ _ _ _); apply toforallpaths_funextsec.
    }
    refine (wlog _ _); clear wlog.
    intros e. induction f as [f0 f1], g as [g0 g1]. cbn in e; induction e.
    cbn. intros e_comp; apply maponpaths.
    apply funextsec; intros y; apply funextsec; intros pyx.
    refine (!_ @ e_comp _ _).
    refine (maponpaths _ _ @ pathscomp0rid _).
    refine (@maponpaths _ _ _ _ (idpath _) _).
    refine (maponpaths funextsec _ @ funextsec_refl _).
    apply funextsec; intros w.
    apply funextsec_refl.
  Defined.

  Definition assemble_disassemble {x} (f : attempt x)
    : assemble_attempt (disassemble_attempt f) = f.
  Proof.
    use attempt_paths.
    - intros y pyx; induction pyx as [ x | x y z pzy lyx ]; cbn.
      + apply pathsinv0, attempt_comp.
      + apply idpath.
    - intros y pyx; induction pyx as [ x | x y z pzy lyx ]; cbn.
      + refine (@maponpaths _ _ _ _ (idpath _) _ @ ! pathsinv0l _).
        refine (maponpaths _ _ @ funextsec_refl _).
        apply funextsec; intros z.
        apply funextsec_refl.
      + refine (maponpaths _ _ @ pathscomp0rid _).
        refine (@maponpaths _ _ _ _ (idpath _) _).
        refine (maponpaths funextsec _ @ funextsec_refl _).
        apply funextsec; intros w.
        apply funextsec_refl.
  Defined.

  Context (wwf_lt : weakly_well_founded lt).

  Definition iscontr_attempt : forall x, iscontr (attempt x).
  Proof.
    apply (wwf_lt (λ x, iscontr_hProp (attempt x))).
    intros x IH.
    apply (iscontrretract _ _ assemble_disassemble).
    apply impred_iscontr; intros y; apply impred_iscontr; intros l.
    exact (IH y l).
  Defined.

  Local Definition the_attempt (x:X) : attempt x
    := iscontrpr1 (iscontr_attempt x).

  Local Definition the_value (x : X) : P x
    := the_attempt x x (nil x).

  Local Definition the_comp (x : X) : the_value x = H x (λ y lyx, the_value y).
  Proof.
    assert (e : the_attempt x = assemble_attempt (λ y _, the_attempt y)).
    { apply isapropifcontr, iscontr_attempt. }
    exact (toforallpaths _ _ _ (toforallpaths _ _ _ (maponpaths attempt_fun e) x) (nil x)).
  Defined.

End Attempts.

(* Main goal of the file: *)
Theorem strongly_from_weakly_well_founded {X} (lt : X -> X -> UU)
  : weakly_well_founded lt -> strongly_well_founded lt.
Proof.
  intros wwf_lt P H_P.
  exists (the_value lt P H_P wwf_lt).
  exact  (the_comp  lt P H_P wwf_lt).
Defined.
