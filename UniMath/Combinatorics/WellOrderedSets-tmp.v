
(*
Attempt at an answer to a question of Dan Grayson:

if you assume a relation is a well-order in the sense of having induction into families of _propositions_,
does it then have induction into arbitrary type families?
*)

Set Universe Polymorphism.

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Section Background.

  (* Hopefully already somewhere in library: *)
  Lemma funextsec_refl {A} {B} (f : forall x:A, B x)
    : funextsec _ f f (fun x => paths_refl (f x)) = paths_refl f.
  Proof.
    refine (funextsec_toforallpaths (paths_refl f)).
  Defined.

  (* Hopefully already somewhere in library: *)
  Lemma funextsec_comp0 {A} {B} {f g h : forall x:A, B x}
      (efg : f ~ g) (egh : g ~ h)
    : funextsec _ _ _ (fun x => efg x @ egh x)
      = funextsec _ _ _ efg @ funextsec _ _ _ egh.
  Proof.
  Admitted.

End Background.

(* A predicate is _hereditary_ w.r.t. a relation if whenever it holds everywhere below some element, it holds at some element.

Hereditariness is the usual hypothesis required for well-founded induction into a predicate. *)
Definition hereditary {X} (lt : X -> X -> UU) (P : X -> UU) : UU
  := forall x, (forall y, lt y x -> P y) -> P x.

Definition strongly_well_founded {X} (lt : X -> X -> UU)
  := forall (P : X -> UU) (H_P : hereditary lt P),
    ∑ (f : forall x, P x), forall x, f x = H_P x (fun y lxy => f y).

Definition weakly_well_founded {X} (lt : X -> X -> UU)
  := forall P : X -> hProp, hereditary lt (fun x => P x) -> forall x, P x.

(* Main goal of the file: *)
Theorem strongly_from_weakly_well_founded {X} (lt : X -> X -> UU)
  : weakly_well_founded lt -> strongly_well_founded lt.
Abort.
(* Can’t prove this yet; will need various auxiliary lemmas first. *)

Section Attempts.

  Context {X} (lt : X -> X -> UU).
  
  Section Paths.
    
    (* a list-like/path-like presentation of the reflexive+transitive closure of the relation [lt] *)
    Inductive path : X -> X -> UU
    :=
      | nil (x:X) : path x x
      | snoc {x y z} (pzy : path z y) (lyx : lt y x) : path z x
    .

    Fixpoint cons {x y z} (lzy : lt z y) (pyx : path y x) : path z x.
    Proof.
      destruct pyx as [ y | w x y pyx lxw ].
      - exact (snoc (nil _) lzy).
      - exact (snoc (cons _ _ _ lzy pyx) lxw).
    Defined.

  End Paths.

  Context (P : X -> UU) (H : hereditary lt P).

  (* An “attempt” up to x: a partial function into P defined for all y <* x, and satisfying the specification given by hereditariness of P.

  Caveat: we should actually have said not “partial function” but “multivalued partial function”, since (y <* x) isn’t necessarily an hprop. *)
  Definition attempt (x:X)
    := ∑ (f : forall y, path y x -> P y),
         forall y pyx, (f y pyx) = H y (fun z lzy => f z (cons lzy pyx)).
  Definition attempt_fun {x} : attempt x -> (forall y pyx, P y) := pr1.
  Coercion attempt_fun : attempt >-> Funclass.
  Definition attempt_comp {x} : forall (f : attempt x), _ := pr2.

  Definition attempt_paths {x:X} (f g : attempt x)
      (e_fun : forall y pyx, f y pyx = g y pyx)
      (e_comp : forall y pyx,
          attempt_comp f y pyx
           @ (maponpaths _ (funextsec _ _ _ 
                  (fun z => funextsec _ _ _ (fun lwz => e_fun _ _)))) 
          = e_fun y pyx @ attempt_comp g y pyx)
    : f = g. 
  Proof.
    revert e_fun e_comp.
    assert (wlog
      : forall (T : (∏ (y:X) (pyx : path y x), f y pyx = g y pyx) -> UU),
        (forall (e : attempt_fun f = attempt_fun g),
              T (fun y pyx => toforallpaths _ _ _ (toforallpaths _ _ _ e y) pyx))
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
    intros e. destruct f as [f0 f1], g as [g0 g1]. cbn in e; destruct e.
    cbn. intros e_comp; apply maponpaths.
    apply funextsec; intros y; apply funextsec; intros pyx.
    refine (!_ @ e_comp _ _).
    refine (maponpaths _ _ @ pathscomp0rid _).
    refine (@maponpaths _ _ _ _ (paths_refl _) _).
    refine (maponpaths (funextsec _ _ _) _ @ _).
    2: { apply funextsec_refl. }
    apply funextsec; intros w.
    apply funextsec_refl.
  Defined.

  Definition disassemble_attempt {x:X}
    : attempt x -> (forall y, lt y x -> attempt y).
  Proof.
    intros f y lyx.
    exists (fun z pzy => f _ (snoc pzy lyx)).
    intros z pzy.
    apply attempt_comp. 
  Defined.

  Definition assemble_attempt {x:X}
    : (forall y, lt y x -> attempt y) -> attempt x.
  Proof.
    intros fs. simple refine (_,,_).
    - intros y pyx; destruct pyx as [ x | x y z pzy lyx ].
      + apply H. intros y lyx. exact (fs _ lyx _ (nil _)).
      + exact (fs _ lyx _ pzy).
    - intros y pyx; destruct pyx as [ x | x y z pzy lyx ]; cbn.
      + apply paths_refl.
      + apply attempt_comp.
  Defined.

  Definition assemble_disassemble {x} (f : attempt x)
    : assemble_attempt (disassemble_attempt f) = f.
  Proof.
    use attempt_paths.
    - intros y pyx; destruct pyx as [ x | x y z pzy lyx ]; cbn.
      + apply pathsinv0, attempt_comp.
      + apply paths_refl.
    - intros y pyx; destruct pyx as [ x | x y z pzy lyx ]; cbn.
      + refine (@maponpaths _ _ _ _ (paths_refl _) _ @ ! pathsinv0l _).
        refine (maponpaths _ _ @ funextsec_refl _).
        apply funextsec; intros z.
        apply funextsec_refl.
      + refine (maponpaths _ _ @ pathscomp0rid _).
        refine (@maponpaths _ _ _ _ (paths_refl _) _).
        refine (maponpaths (funextsec _ _ _) _ @ _).
        2: { apply funextsec_refl. }
        apply funextsec; intros w.
        apply funextsec_refl.
  Defined.

  Context (wwf_lt : weakly_well_founded lt).

  Definition iscontr_attempt : forall x, iscontr (attempt x).
  Proof.
    apply (wwf_lt (fun x => iscontr_hProp (attempt x))).
    intros x IH.
    apply (iscontrretract _ _ assemble_disassemble).
    apply impred_iscontr; intros y.
    apply impred_iscontr, IH.
  Defined.
  
  Local Definition the_attempt (x:X) : attempt x
    := iscontrpr1 (iscontr_attempt x).

  Local Definition the_value (x : X) : P x
    := the_attempt x x (nil x).
    
  Local Definition the_comp (x : X)
      : the_value x = H x (fun y lyx => the_value y).
  Proof.
    assert (e : the_attempt x = assemble_attempt (fun y _ => the_attempt y)).
    { apply isapropifcontr, iscontr_attempt. }
    set (e_fun := maponpaths attempt_fun e). cbn in e_fun.
    exact (toforallpaths _ _ _ (toforallpaths _ _ _ e_fun x) (nil x)).
  Defined.
    
  Proof.

End Attempts.
 
Theorem strongly_from_weakly_well_founded {X} (lt : X -> X -> UU)
  : weakly_well_founded lt -> strongly_well_founded lt.
Proof.
  intros wwf_lt P H_P.
  exists (fun x => the_value _ _ H_P wwf_lt x).
  exact (the_comp _ _ _ _).
Defined.