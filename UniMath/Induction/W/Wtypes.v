(** * Axiomatic definition of a W-type. *)
(**
Gianluca Amato, Matteo Calosci, Marco Maggesi, Cosimo Perini Brogi 2019-2024.

Derived from the code in the GitHub repository #<a href="https://github.com/HoTT/Archive/tree/master/LICS2012">#
https://github.com/HoTT/Archive/tree/master/LICS2012 #</a>#, which accompanies the paper
"_Inductive Types in Homotopy Type Theory_", by S. Awodey, N. Gambino and K. Sojakova.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.PartA.

(** ** Axiomatic definition of a W-Type. *)

Definition Wtype (A: UU) (B: ∏ x: A, UU): UU
  := ∑ (U: UU)
       (w_sup: ∏ (x : A) (f : B x → U), U)
       (w_ind: ∏ (P : U → UU) (e_s : ∏ (x: A) (f: B x → U) (IH: ∏ u: B x, P (f u)), P (w_sup x f)) (w: U), P w),
       (∏ (P : U → UU)
          (e_s : ∏ (x: A) (f: B x → U) (IH: ∏ u: B x, P (f u)), P (w_sup x f))
          (x : A) (f : B x → U)
        , w_ind P e_s (w_sup x f) = e_s x f (λ u, w_ind P e_s (f u))).

#[reversible=no] Coercion w_carrier {A: UU} {B: ∏ x: A, UU} (W: Wtype A B): UU := pr1 W.

Section W.

(** ** Constructor. *)

Definition makeWtype {A: UU} {B: ∏ x: A, UU}
  (U: UU)
  (w_sup: ∏ (x : A) (f : B x → U), U)
  (w_ind: ∏ (P : U → UU) (e_s : ∏ (x: A) (f: B x → U) (IH: ∏ u: B x, P (f u)), P (w_sup x f)) (w: U), P w)
  (w_beta: ∏ (P : U → UU)
    (e_s : ∏ (x: A) (f: B x → U) (IH: ∏ u: B x, P (f u)), P (w_sup x f))
    (x : A) (f : B x → U)
    , w_ind P e_s (w_sup x f) = e_s x f (λ u, w_ind P e_s (f u)))
  : Wtype A B
  := (U,,w_sup,,w_ind,,w_beta).

Context {A: UU} {B: ∏ x: A, UU} {W: Wtype A B}.

(** ** Accessors. *)

Definition w_sup := pr12 W.

Definition w_ind := pr122 W.

Definition w_beta := pr222 W.

(** ** Derived rules. *)

(** *** First-order eta rule. *)

Definition w_eta_1 (P: W → UU) (e_s: ∏ (x: A) (f: B x → W) (IH: ∏ u: B x, P (f u)), P (w_sup x f))
                   (h: ∏ x: W, P x) (p_s: ∏ (x: A) (f: B x → W), h (w_sup x f) = (e_s x f (λ b, h (f b))))
  : ∏ (w : W), h w = w_ind P e_s w.
Proof.
  refine (w_ind _ _).
  intros.
  cbn.
  cbn in IH.
  etrans.
  - apply p_s.
  - etrans.
    all: revgoals.
    * apply pathsinv0.
      apply w_beta.
    * apply maponpaths.
      apply funextsec.
      intro.
      apply IH.
Defined.

(** *** Second-order eta rule. *)

Definition w_eta_2 (P: W → UU) (e_s: ∏ (x: A) (f: B x → W) (IH: ∏ u: B x, P (f u)), P (w_sup x f))
                               (h: ∏ x: W, P x) (p_s: ∏ (x: A) (f: B x → W), h (w_sup x f) = (e_s x f (λ b, h (f b))))
  : ∏ (x : A) (f : B x → W)
      , w_eta_1 P e_s h p_s (w_sup x f) @ w_beta P e_s x f
        = p_s x f @ maponpaths (e_s x f) (funextsec _ _ _ (fun b => w_eta_1 P e_s h p_s (f b))).
Proof.
  intros.
  apply hornRotation_rr.
  etrans.
  - apply (w_beta (λ w, h w = w_ind  P e_s w)).
  - apply path_assoc.
Defined.

End W.
