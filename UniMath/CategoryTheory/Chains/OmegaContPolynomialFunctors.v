(** ** Set-Based Polynomial Functors are omega-continuous

    Author : Antoine Fisse (@AextraT), 2025
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Induction.FunctorCoalgebras_legacy.
Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.M.Core.
Require Import UniMath.Induction.M.MWithSets.

Require Import UniMath.CategoryTheory.Categories.Type.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Chains.CoAdamek.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Cochains.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.

Local Open Scope cat.
Local Open Scope functions.

Section OmegaContinuity.

  Context {A : ob HSET} (B : pr1hSet A → ob HSET).

  Local Definition F' := MWithSets.F' B.

  Lemma comp_right_eq_hset
    {X Y Z : UU}
    {f g : X -> Y}
    (h : Y -> Z)
    (p : f = g)
    : h ∘ f = h ∘ g.
  Proof.
    use funextfun.
    apply homotfun.
    induction p.
    apply homotrefl.
  Defined.

  Lemma pullback_cone_edge
    {X Y0 Y1 Y2: SET}
    (x : pr1hSet X)
    {f : SET ⟦ Y1, Y2 ⟧}
    {g0 : SET ⟦ X, F' Y0 ⟧}
    {g1 : SET ⟦ X, F' Y1 ⟧}
    {g2 : SET ⟦ X, F' Y2 ⟧}
    (p : (#F' f) ∘ g1 = g2)
    (q1 : pr1 ∘ g0 = pr1 ∘ g1)
    (q2 : pr1 ∘ g0 = pr1 ∘ g2)
    : (λ b, f (pr2 (g1 x) (transportf (λ φ, pr1hSet (B (φ x))) q1 b))) = (λ b, pr2 (g2 x) (transportf (λ φ, pr1hSet (B (φ x))) q2 b)).
  Proof.
    induction p.
    cbn.
    assert (r : q1 = q2).
    { apply (setproperty (SET ⟦ X, A ⟧,, isaset_forall_hSet (pr1hSet X) (λ _, A)) (pr1 ∘ g0) (pr1 ∘ g1)).
    }
    induction r.
    apply idpath.
  Defined.

  Lemma pathtozero_cone
    {c0 : SET}
    {c : cochain SET}
    (cc0 : Graphs.Limits.cone (Diagrams.mapdiagram F' c) c0)
    (v : nat)
    : pr1 ∘ (pr1 cc0 0) = pr1 ∘ (pr1 cc0 v).
  Proof.
    induction v.
    - apply idpath.
    - symmetry.
      etrans.
      + apply (comp_right_eq_hset (λ x : pr1hSet (F' (Diagrams.dob c v)), pr1 x) (pr2 cc0 (S v) v (idpath (S v)))).
      + symmetry. apply IHv.
  Defined.

  Lemma pullback_cone
    {c0 : SET}
    (x : pr1hSet c0)
    {c : cochain SET}
    (cc0 : Graphs.Limits.cone (Diagrams.mapdiagram F' c) c0)
    : Graphs.Limits.cone c (B (pr1 (pr1 cc0 0 x))).
  Proof.
    unfold Graphs.Limits.cone.
    unfold Graphs.Limits.cone in cc0.
    unfold Limits.forms_cone in cc0.
    set (f := λ v : Diagrams.vertex conat_graph, (λ b, pr2 (pr1 cc0 v x) (transportf (λ φ, pr1hSet (B (φ x))) (pathtozero_cone cc0 v) b)) : SET ⟦ B (pr1 (pr1 cc0 0 x)), Diagrams.dob c v ⟧).
    assert (p : Limits.forms_cone c f).
    {
      unfold Limits.forms_cone.
      simpl.
      intros u v e.
      induction e.
      set (p := pullback_cone_edge x (pr2 cc0 (S v) v (idpath (S v))) (pathtozero_cone cc0 (S v)) (pathtozero_cone cc0 v)).
      apply p.
    }
    exact (f,, p).
  Defined.

  Lemma Exists_fun_mapdiagram
    {c : cochain SET}
    {L : SET}
    {cc : Graphs.Limits.cone c L}
    (c_limcone : Graphs.Limits.isLimCone c L cc)
    (c0 : SET)
    (cc0 : Graphs.Limits.cone (Diagrams.mapdiagram F' c) c0)
    : SET ⟦ c0, F' L ⟧.
  Proof.
    intro x.
    cbn.
    unfold polynomial_functor_obj.
    set (a := pr1 (pr1 cc0 0 x) : pr1hSet A).
    set (cx := B a).
    set (ccx := pullback_cone x cc0).
    set (f2x := pr11 (c_limcone cx ccx)).
    exact (a,, f2x).
  Defined.

  Lemma is_mor_mapdiagram2_point
    {X Y c : UU}
    (x : X)
    {φ1 φ2 : X -> pr1hSet A}
    {f : pr1hSet (B (φ1 x)) -> c}
    {g : c -> Y}
    {h : pr1hSet (B (φ2 x)) -> Y}
    (q : φ1 = φ2)
    (p : g ∘ f = λ b, h (transportf (λ ψ, pr1hSet (B (ψ x))) q b))
    : transportf (λ a, pr1hSet (B a) -> Y) (toforallpaths _ _ _ q x) (g ∘ f) = h.
  Proof.
    induction q.
    apply p.
  Defined.

  Lemma Exists_mor_mapdiagram
    {c : cochain SET}
    {L : SET}
    {cc : Graphs.Limits.cone c L}
    (c_limcone : Graphs.Limits.isLimCone c L cc)
    (c0 : SET)
    (cc0 : Graphs.Limits.cone (Diagrams.mapdiagram F' c) c0)
    : ∑ f : SET ⟦ c0, F' L ⟧, Limits.is_cone_mor cc0 (Limits.mapcone F' c cc) f.
  Proof.
    set (f := Exists_fun_mapdiagram c_limcone c0 cc0).
    assert (p : Limits.is_cone_mor cc0 (Limits.mapcone F' c cc) f).
    {
      unfold Limits.is_cone_mor.
      intro v.
      apply funextfun.
      intro x.
      use total2_paths_f.
      - unfold Graphs.Limits.coneOut.
        unfold Limits.mapcone.
        cbn.
        apply (toforallpaths _ _ _ (pathtozero_cone cc0 v) x).
      - cbn.
        unfold Graphs.Limits.coneOut.
        set (a := pr1 (pr1 cc0 0 x) : pr1hSet A).
        set (cx := B a).
        set (ccx := pullback_cone x cc0).
        set (p := pr2 (pr1 (c_limcone cx ccx)) v).
        cbn in p.
        unfold Graphs.Limits.coneOut in p.
        apply (is_mor_mapdiagram2_point x (pathtozero_cone cc0 v) p).
    }
    exact (f,, p).
  Defined.

  Lemma move_proof
    {X Y Z : SET}
    {x : pr1hSet X}
    (h1 h2 : SET⟦ X, A ⟧)
    (f : SET ⟦ B (h2 x), Y ⟧)
    (g : SET ⟦ Y, Z ⟧ )
    (q : h1 = h2)
    : g ∘ (transportf (λ a, SET ⟦ B a, Y ⟧) (pathsinv0 (toforallpaths _ _ _ q x)) f) = λ b, g (f (transportf (λ φ, pr1hSet (B (φ x))) q b)).
  Proof.
    induction q.
    cbn.
    apply idpath.
  Defined.

  Lemma proj_is_cone_mor_point
    {X Y Z0 Z : SET}
    (x : pr1hSet X)
    {f : SET ⟦ X, F' Y ⟧}
    {g : SET⟦ Y, Z ⟧}
    (h0 : SET⟦ X, F' Z0 ⟧)
    (h1 : SET⟦ X, F' Z ⟧)
    (p : #F' g ∘ f = h1)
    (q : pr1 (f x) = pr1 (h0 x))
    (q' : pr1 ∘ h0 = pr1 ∘ h1)
    : g ∘ (transportf _ q (pr2 (f x))) = λ b, (pr2 (h1 x)) (transportf (λ φ, pr1hSet (B (φ x))) q' b).
  Proof.
    induction p.
    cbn.
    set (q'x := toforallpaths _ _ _ q' x).
    cbn in q'x.
    set (q'x' := pathsinv0 q'x).
    assert (r : q'x' = q) by apply (setproperty A).
    induction r.
    apply (move_proof (pr1 ∘ h0) (pr1 ∘ # F' g ∘ f) (pr2 (f x)) g q').
  Defined.

  Lemma proj_is_cone_mor
    {c : cochain SET}
    {c0 L : SET}
    {x : pr1hSet c0}
    {cc :  Graphs.Limits.cone c L}
    {cc0 : Graphs.Limits.cone (Diagrams.mapdiagram F' c) c0}
    (f : SET ⟦ c0, F' L ⟧)
    {p : pr1 (f x) = pr1 (pr1 cc0 0 x)}
    (pf : Limits.is_cone_mor cc0 (Limits.mapcone F' c cc) f)
    : Limits.is_cone_mor (pullback_cone x cc0) cc (transportf _ p (pr2 (f x))).
  Proof.
    set (ccx := pullback_cone x cc0).
    cbn.
    unfold Limits.is_cone_mor.
    intro v.
    unfold Limits.is_cone_mor in pf.
    unfold Graphs.Limits.coneOut in pf.
    apply (proj_is_cone_mor_point x (pr1 cc0 0) (pr1 cc0 v) (pf v) p (pathtozero_cone cc0 v)).
  Defined.

  Lemma morph_unicity_pushout
    {c : cochain SET}
    {c0 L : SET}
    {cc : Graphs.Limits.cone c L}
    (c_limcone : Graphs.Limits.isLimCone c L cc)
    (cc0 : Graphs.Limits.cone (Diagrams.mapdiagram F' c) c0)
    {f' : SET⟦ c0, F' L ⟧}
    (pf' : Limits.is_cone_mor cc0 (Limits.mapcone F' c cc) f')
    : f' = pr1 (Exists_mor_mapdiagram c_limcone c0 cc0).
  Proof.
    set (f_pf := Exists_mor_mapdiagram c_limcone c0 cc0).
    set (f := pr1 f_pf).
    set (pf := pr2 f_pf).
    apply funextfun.
    intro x.
    set (p := maponpaths (λ z, pr1 z) (toforallpaths _ _ _ (pf' 0) x)).
    use total2_paths_f.
    - unfold Limits.is_cone_mor in pf'.
      unfold Limits.mapcone in pf'.
      unfold Graphs.Limits.coneOut in pf'.
      cbn in pf'.
      apply p.
    - cbn.
      set (a := pr1 (pr1 cc0 0 x) : pr1hSet A).
      set (cx := B a).
      set (ccx := pullback_cone x cc0).
      set (f'2 := transportf _ p (pr2 (f' x)) : SET ⟦ cx, L ⟧).
      set (f'2_cone_mor := proj_is_cone_mor f' pf' : Limits.is_cone_mor ccx cc f'2).
      apply (maponpaths (λ z, pr1 z) (pr2 (c_limcone cx ccx) (f'2,, f'2_cone_mor))).
  Defined.

  Lemma PolyFunctor_omega_cont : is_omega_cont F'.
  Proof.
    unfold is_omega_cont.
    unfold Limits.preserves_limit.
    unfold Graphs.Limits.isLimCone.
    intros c L cc c_limcone c0 cc0.
    use tpair.
    - exact (Exists_mor_mapdiagram c_limcone c0 cc0).
    - set (f_pf := Exists_mor_mapdiagram c_limcone c0 cc0).
      set (f := pr1 f_pf).
      set (pf := pr2 f_pf).
      intro t.
      destruct t as [f' pf'].
      use total2_paths_f.
      + apply (morph_unicity_pushout c_limcone cc0 pf').
      + set (p1 := morph_unicity_pushout c_limcone cc0 pf').
        set (tpf' := transportf (Limits.is_cone_mor cc0 (Limits.mapcone F' c cc)) p1 pf').
        unfold Limits.is_cone_mor in pf.
        use funextsec.
        intro v.
        apply (isaset_forall_hSet (pr1hSet c0) (λ _, F' (Diagrams.dob c v))).
  Defined.

End OmegaContinuity.
