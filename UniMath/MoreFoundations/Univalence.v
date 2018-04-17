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

(** Paths in a fibration over the universe are equivalent to weak equivalences
    such that, when transporting the second projections over the equality
    given by univalence, they're equal.

    Compare to [total2_paths_equiv]. *)
Lemma total2_paths_UU_equiv {B : UU -> UU} (s s' : ∑ x, B x) :
    s = s' ≃
    (∑ p : pr1 s ≃ pr1 s', transportf (λ x, B x) (weqtopaths p) (pr2 s) = pr2 s').
Proof.
  intermediate_weq (∑ p : pr1 s = pr1 s', transportf (λ x, B x) p (pr2 s) = pr2 s').
  - apply total2_paths_equiv.
  - use weqbandf.
    + use weqpair.
      * apply eqweqmap.
      * apply univalenceAxiom.
    + intros path; cbn.
      apply eqweqmap, pathsinv0.
      apply (maponpaths (λ p, transportf _ p (pr2 s) = pr2 s')
                        (! homotinvweqweq0 (univalence _ _) path)).
Defined.