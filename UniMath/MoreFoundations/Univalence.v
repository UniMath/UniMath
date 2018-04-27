(** * Additional results about univalence *)

Require Import UniMath.Foundations.UnivalenceAxiom.

(** Funextsec and toforallpaths are mutually inverses *)
Lemma funextsec_toforallpaths {T : UU} {P : T -> UU} {f g : ∏ t : T, P t} :
      ∏ (h : f = g), funextsec _  _ _ (toforallpaths _ _ _ h) = h.
Proof.
  intro h; exact (!homotinvweqweq0 (weqtoforallpaths _ _ _) h).
Defined.

(** Funextsec and toforallpaths are mutually inverses *)
Lemma toforallpaths_funextsec {T : UU} {P : T -> UU} {f g : ∏ t : T, P t} :
      ∏ (h : ∏ t : T, f t = g t), toforallpaths _  _ _ (funextsec _ _ _ h) = h.
Proof.
  intro h; exact (homotweqinvweq (weqtoforallpaths _ _ _) h).
Defined.
