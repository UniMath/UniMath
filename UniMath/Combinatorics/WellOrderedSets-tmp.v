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
Local Arguments toforallpaths {_ _ _ _} _.

Section Background.

  (* Hopefully already somewhere in library: *)
  Lemma funextsec_refl {A} {B} (f : ∏ x:A, B x)
    : funextsec (λ x, idpath (f x)) = idpath f.
  Proof.
    exact (funextsec_toforallpaths (idpath f)).
  Defined.

End Background.

(* A predicate is _hereditary_ w.r.t. a relation if whenever it holds everywhere below some element, it holds at some element.

Hereditariness is the usual hypothesis required for well-founded induction into a predicate. *)
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
  (* an element of [chain n] will be an ascending sequence [x = s_1 < t_1 = s_2 < t_2 = ... = s_n < t_n = y] *)
  Proof.
    revert x y.
    induction n as [|n H].
    - intros x y. exact (x = y).
    - intros x y. exact (∑ s t, H x s × s<t × t=y).
  Defined.

  Definition ltstar (x y : X) : Type := ∑ n, chain n x y.

  Notation "x ≤ y" := (ltstar x y) (at level 70).

  Definition nil {x} : x≤x := (0,,idpath x).

  Definition cons' {x x' y z} (p : z ≤ y) (l : y < x') (e : x' = x) : z ≤ x.
  Proof.
    induction p as [n c].
    exact (S n,,y,,x',,c,,l,,e).
  Defined.

  Definition cons {x y z z'} (e : z = z') (l : z' < y) (p : y ≤ x) : z ≤ x.
  Proof.
    induction p as [n c].
    exists (S n).
    revert e l x c.
    induction n as [|n H].
    - intros e l x c. exact (z',,y,,e,,l,,c).
    - intros e l x c. induction c as [s [t [c' [l' e']]]].
      exact (s,,t,,H e l s c',,l',,e').
  Defined.

  Lemma assoc {w w' x y z' z} (e : w=w') (l : w'<x) (p : x≤y) (m : y<z') (f : z'=z) : cons e l (cons' p m f) = cons' (cons e l p) m f.
  (* used implicitly below, so let's check it *)
  Proof.
    reflexivity.
  Defined.

  Context (P : X -> Type) (H : hereditary lt P).

  (* An “attempt” up to x: a partial function into P defined for all y ≤ x, and satisfying the
     specification given by hereditariness of P.

     Caveat: we should actually have said not “partial function” but “multivalued partial function”,
     since (y ≤ x) isn’t necessarily an hprop. *)

  Definition attempt x
    := ∑ (f : ∏ y, y ≤ x -> P y), ∏ y pyx, f y pyx = H y (λ z l, f z (cons (idpath z) l pyx)).

  Definition attempt_fun {x} : attempt x -> (∏ y pyx, P y) := pr1.
  Coercion attempt_fun : attempt >-> Funclass.

  Definition attempt_comp {x} : ∏ (f : attempt x), _ := pr2.

  Definition disassemble_attempt {x}
    : attempt x -> (∏ y w, y<w -> w=x -> attempt y).
  Proof.
    intros f y' y l e.
    exists (λ t p, f _ (cons' p l e)).
    intros z p.
    use attempt_comp.
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

  Definition attempt_paths {x} (f g : attempt x) :
      ∏ (e_fun : ∏ y pyx, f y pyx = g y pyx),
      (∏ y pyx,
          attempt_comp f y pyx
           @ maponpaths (H y) (funextsec (λ z, funextsec (λ lzy : z<y, e_fun z (cons (idpath z) lzy pyx))))
          = e_fun y pyx @ attempt_comp g y pyx)
    -> f = g.
  Proof.
    assert (wlog :
              ∏ (T : (∏ y (pyx : y ≤ x), f y pyx = g y pyx) -> Type),
                (∏ (e : attempt_fun f = attempt_fun g),
                    T (λ y pyx, toforallpaths (toforallpaths e y) pyx))
                -> ∏ e, T e).
    { intros T HT e.
      transparent assert (e' : (attempt_fun f = attempt_fun g)).
      { apply funextsec; intros y; apply funextsec; intros pyx; apply e. }
      refine (transportb _ _ (HT e')).
      apply funextsec; intros y; apply funextsec; intros pyx.
      apply pathsinv0.
      eapply pathscomp0.
      { refine (toforallpaths _ _); apply maponpaths.
        refine (toforallpaths _ _); apply toforallpaths_funextsec. }
      refine (toforallpaths _ _); apply toforallpaths_funextsec. }
    refine (wlog _ _); clear wlog.
    intros e. induction f as [f0 f1], g as [g0 g1]. cbn in e. induction e.
    cbn. intros e_comp; apply maponpaths.
    apply funextsec; intros y; apply funextsec; intros pyx.
    refine (!_ @ e_comp _ _).
    refine (maponpaths _ _ @ pathscomp0rid _).
    refine (@maponpaths _ _ _ _ (idpath _) _).
    refine (maponpaths funextsec _ @ funextsec_refl _).
    apply funextsec; intros z.
    apply funextsec_refl.
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

  Definition iscontr_attempt : ∏ x, iscontr (attempt x).
  Proof.
    apply (wwf_lt (λ x, iscontr_hProp (attempt x))).
    intros x IH.
    apply (iscontrretract _ _ assemble_disassemble).
    apply impred_iscontr; intro z.
    apply impred_iscontr; intro z'.
    apply impred_iscontr; intro l.
    apply impred_iscontr; intro e.
    exact (IH z (transportf _ e l)).
  Defined.

  Local Definition the_attempt x : attempt x
    := iscontrpr1 (iscontr_attempt x).

  Local Definition the_value x : P x
    := the_attempt x x nil.

  Local Definition the_comp x : the_value x = H x (λ y l, the_value y).
  Proof.
    assert (e : the_attempt x = assemble_attempt (λ y _ _ _, the_attempt y)).
    { apply isapropifcontr, iscontr_attempt. }
    exact (toforallpaths (toforallpaths (maponpaths attempt_fun e) x) nil).
  Defined.

End Attempts.

(* Main goal of the file: *)
Theorem strongly_from_weakly_well_founded {X} (lt : X -> X -> Type)
  : weakly_well_founded lt -> strongly_well_founded lt.
Proof.
  intros wwf_lt P H_P.
  exists (the_value lt P H_P wwf_lt).
  exact  (the_comp  lt P H_P wwf_lt).
Defined.
