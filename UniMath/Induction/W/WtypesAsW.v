(** * From axiomatic W-types to W-types as initial algebras. *)
(**
Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021.

It is a proof that the rules for W-types gives an initial agebra

Derived from the code in the GitHub repository #<a href="https://github.com/HoTT/Archive/tree/master/LICS2012">#
https://github.com/HoTT/Archive/tree/master/LICS2012 #</a>#, which accompanies the paper
"_Inductive Types in Homotopy Type Theory_", by S. Awodey, N. Gambino and K. Sojakova.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.Induction.W.Wtypes.
Require Import UniMath.Induction.W.Core.
Require Import UniMath.Induction.FunctorAlgebras_legacy.
Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.PolynomialAlgebras2Cells.
Require Import UniMath.CategoryTheory.Core.Functors.

Local Open Scope cat.
Local Notation "a ;; b" := (funcomp a b).

Section From_W_types_to_initiality.

Context {A: UU} {B: A → UU} (W: Wtype A B).

(** We define the algebra associated to W *)

Notation P := (polynomial_functor A B).

Let s_W (c: P W) : W := w_sup (pr1 c) (pr2 c).

Definition w_algebra: algebra_ob P := w_carrier W ,, s_W.

Notation WW := (w_algebra).

(** We consider another algebra. For simplicity we first prove the claim for algebras in canonical form. *)

Section Towards_contractibility.

Context (EE: algebra_ob P).

Let E := alg_carrier P EE.

Let s_E := alg_map P EE.

(** The map j : W → E, which we will show to be an algebra map.
It is defined by W-recursion, so we construct the eliminating term. *)

Let d_j (x : A) (u: B x → W) (IH : B x → E): E := s_E (x,, IH).

Let j (w: W): E := w_ind _ d_j w.

(** Construction of a homotopy sigma_j which is used to show that j is an algebra map. *)

Let sigma_j_flat : ∏ (c: P W), j (s_W c) = s_E (# P j c).
Proof.
  induction c as [x u].
  apply (w_beta (λ _ : W, E)).
Defined.

Let sigma_j_sharp : is_algebra_mor _ WW EE j.
Proof.
  apply funextfun.
  intro.
  apply sigma_j_flat.
Defined.

(** We introduce the evaluation morphism as the algebra map (j, sigma_j_sharp), which will be the center of the contraction. *)

Definition w_eval : algebra_mor _ WW EE := j ,, sigma_j_sharp.

Notation jj := (w_eval).

(** We now assume that to have a  algebra map kk : WW → EE and we show that it is propositionally equal to jj
For simplicity, we first prove this for algebra maps in canonical form. *)

Context (kk : algebra_mor _ WW EE).

Let k : W → E := mor_from_algebra_mor P WW EE kk.

Let sigma_k : is_algebra_mor _ WW EE k := pr2 kk.

(** The homotopy associated to s_k  *)

Let sigma_k_flat: ∏ (x: P W), k (s_W x) = s_E (# P k x).
Proof.
  apply toforallpaths.
  exact sigma_k.
Defined.

(** Construction of the homotopy from j to k by W-elimination *)

Let d_theta (x : A) (u : B x → W) (IH : ∏ c: B x, j (u c) = k (u c))
  : j (w_sup x u) = k (w_sup x u).
Proof.
  assert (e_1 : j (w_sup x u) = s_E (x,, u ;; j)).
  {
    apply (sigma_j_flat (x,, u)).
  }
  assert (e_2 : s_E (x,, u ;; j) = s_E (x,, u ;; k)).
  {
    do 2 apply maponpaths.
    apply funextfun.
    exact IH.
  }
  assert (e_3 : s_E (x,, u ;; k) = k (w_sup x u)).
  {
    apply (! (sigma_k_flat (x,, u))).
  }
  exact ((e_1 @ e_2) @ e_3).
Defined.

(** The homotopy between j and k *)

Let theta : j ~ k := w_ind (λ w : W, j w = k w) d_theta.

Let theta_comp (x : A) (u : B x → W)
  : theta (w_sup x u) = d_theta x u (λ y : B x, theta (u y))
  := w_beta (λ w : W, j w = k w) d_theta x u.

(** Verification that theta is a algebra map homotopy *)

Let s_theta : isalgmaphomotopy _ j sigma_j_flat k sigma_k_flat theta.
Proof.
  intro c.
  unfold homotcomp.
  apply hornRotation_rr.
  apply theta_comp.
Defined.

(** The path p : k = j associated to theta *)

Let p : j = k := funextfun _ _ theta.

(** The proof that p is an algebra 2-cell. This exploits the work on
relating algebra map homotopies and algebra map 2-cells done earlier *)

Let s_p : isalg2cell _ jj kk p.
Proof.
  set (s_k_flat_sharp := funextfun _ _ sigma_k_flat).
  assert (e : sigma_k = s_k_flat_sharp).
  {
    apply homotinvweqweq0.
  }
  apply (transportb (λ u, isalg2cell _ jj (k ,, u) p) e).
  apply alghomotopytoalg2cell.
  exact s_theta.
Defined.

(** Proof that jj is propositionally equal to kk *)

Definition pq : jj = kk.
Proof.
  apply weqfromalg2celltoidalgmap.
  exact (p ,, s_p).
Defined.

End Towards_contractibility.

(** Proof of initiality of W *)

Lemma w_types_are_initial : is_initial WW.
Proof.
  intro EE.
  exists (w_eval EE).
  intro kk.
  apply (! (pq EE kk)).
Defined.

End From_W_types_to_initiality.

Theorem Wtype_is_W {A: UU} {B: A → UU} (W': Wtype A B) : W B.
Proof.
  exists (w_algebra W').
  apply w_types_are_initial.
Defined.
