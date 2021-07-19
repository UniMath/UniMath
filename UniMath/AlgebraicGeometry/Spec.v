(** ** Contents

- Zariski topology
- Structure sheaf
 *)

Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.RigsAndRings.Ideals.
Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.Topology.Topology.

Local Open Scope logic.
Local Open Scope subtype.


(** ** Zariski topology *)

Section spec.
  Context {R : commring}.

  Definition zariski_topology : (prime_ideal R -> hProp) -> hProp :=
    λ U, ∃ A, U ≡ (λ p, A ⊈ p).

  Lemma zariski_topology_union :
    isSetOfOpen_union zariski_topology.
  Proof.
    intros O H0. unfold zariski_topology.
    set (S := λ A, ∃ U, O U ∧ U ≡ (λ p, A ⊈ p)).
    apply hinhpr. exists (union S). intro p.
    apply issymm_logeq, (logeq_trans (union_not_contained_in S p)).
    unfold union. use make_dirprod; intro H.
    - use (hinhuniv _ H); intro HA.
      induction HA as [A HA].
      use (hinhfun _ (dirprod_pr1 HA)); intro HU.
      induction HU as [U HU].
      exists U. use make_dirprod.
      + exact (dirprod_pr1 HU).
      + apply (dirprod_pr2 (dirprod_pr2 HU p)), (dirprod_pr2 HA).
    - use (hinhuniv _ H); intro HU. induction HU as [U HU].
      use (hinhfun _ (H0 U (dirprod_pr1 HU))); intro HA.
      induction HA as [A HA].
      exists A. use make_dirprod.
      + apply hinhpr. exists U. exact (make_dirprod (dirprod_pr1 HU) HA).
      + apply (dirprod_pr1 (HA p)), (dirprod_pr2 HU).
  Defined.

  Lemma zariski_topology_htrue :
    isSetOfOpen_htrue zariski_topology.
  Proof.
    apply hinhpr. exists (λ x, htrue). intro p.
    use make_dirprod; intro H.
    - use (hinhfun _ (prime_ideal_ax2 p)); intro Hx'.
      induction Hx' as [x Hx'].
      exists x. exact (make_dirprod tt Hx').
    - exact tt.
  Defined.

  Lemma zariski_topology_and :
    isSetOfOpen_and zariski_topology.
  Proof.
    unfold zariski_topology. intros U V HU HV.
    use (hinhuniv _ HU); intros HA.
    use (hinhfun _ HV); intros HB.
    induction HA as [A HA]. induction HB as [B HB].
    exists (λ x, ∃ a b, A a × B b × x = (a * b)%ring). intro p.
    assert (H0 : U p ∧ V p ⇔ A ⊈ p ∧ B ⊈ p).
    { use make_dirprod; intro H.
      - use make_dirprod.
        + apply (dirprod_pr1 (HA p)), (dirprod_pr1 H).
        + apply (dirprod_pr1 (HB p)), (dirprod_pr2 H).
      - use make_dirprod.
        + apply (dirprod_pr2 (HA p)), (dirprod_pr1 H).
        + apply (dirprod_pr2 (HB p)), (dirprod_pr2 H). }
    apply (logeq_trans H0). unfold subtype_notContainedIn.
    use make_dirprod; intro H.
    - use (hinhuniv _ (dirprod_pr1 H)); intro Ha.
      use (hinhfun _ (dirprod_pr2 H)); intro Hb.
      induction Ha as [a Ha]. induction Hb as [b Hb].
      exists (a * b)%ring. use make_dirprod.
      + apply hinhpr. exists a, b.
        exact (make_dirprod (dirprod_pr1 Ha)
                            (make_dirprod (dirprod_pr1 Hb) (idpath _))).
      + apply (@negf _ (p a ∨ p b)).
        * exact (prime_ideal_ax1 _ a b).
        * apply toneghdisj.
          exact (make_dirprod (dirprod_pr2 Ha) (dirprod_pr2 Hb)).
    - use (hinhuniv _ H); intro Hx.
      induction Hx as [x Hx]. induction Hx as [Hx Hpx].
      use (hinhuniv _ Hx); intro Hab.
      induction Hab as [a Hab]. induction Hab as [b Hab].
      induction Hab as [Ha Hab]. induction Hab as [Hb Hab].
      use make_dirprod; apply hinhpr.
      + exists a. use make_dirprod.
        * exact Ha.
        * use (negf _ Hpx). intro Hpa.
          apply (transportb (λ y, p y) Hab).
          apply (ideal_isr p b a), Hpa.
      + exists b. use make_dirprod.
        * exact Hb.
        * use (negf _ Hpx). intro Hpb.
          apply (transportb (λ y, p y) Hab).
          apply (ideal_isl p a b), Hpb.
  Defined.

  Definition spec_top : TopologicalSet :=
    mkTopologicalSet (prime_ideal R)
                     zariski_topology
                     zariski_topology_union
                     zariski_topology_htrue
                     zariski_topology_and.
End spec.

Arguments spec_top _ : clear implicits.


(** ** Structure sheaf *)

(** For each prime ideal p of R, let R_p be the localization of R at p. For an open set U from the
    spectrum of R, we define [section U] to be the family of functions s : ∏ p, R_p, such that s is
    locally a quotient of elements of R: to be precise, we require that for each p in U there is a
    neighborhood V of p, contained in U, and elements f, g in R, such that for each q in V, g not in
    q, and s q = f/g. *)

Section section.
  Context {R : commring} {U : @Open (spec_top R)}.

  Definition is_quotient_on (V : Open)
                            (s : ∏ q : carrier U, localization_at (pr1 q)) : UU :=
    ∑ (f g : R), ∏ q : carrier U,
        V (pr1 q) -> ∑ Hg : ¬ (pr1 q : prime_ideal R) g, s q = quotient f (g ,, Hg).

  Definition is_section (s : ∏ p : carrier U, localization_at (pr1 p)) : hProp :=
    ∀ p : carrier U, ∃ V : Open, V (pr1 p) × V ⊆ U × is_quotient_on V s.

  Definition section : UU :=
    ∑ s : (∏ p : carrier U, localization_at (pr1 p)), is_section s.

  Definition make_section (s : ∏ p : carrier U, localization_at (pr1 p)) (H : is_section s) :
    section := s ,, H.

  Definition section_map (s : section) : ∏ p : carrier U, localization_at (pr1 p) := pr1 s.
  Coercion section_map : section >-> Funclass.

  Definition section_prop (s : section) : is_section s := pr2 s.
End section.

Arguments section {_} _.
