Require Import UniMath.MoreFoundations.All.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.limits.Opp.

Require Import UniMath.CategoryTheory.ModelCategories.Retract.
Require Import UniMath.CategoryTheory.ModelCategories.MorphismClass.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.

Local Open Scope cat.
Local Open Scope morcls.
Local Open Scope retract.

Section Lifting.

Context {C : category}.

(* in a category, we know that homs are sets, so equality must be a prop *)
(* Lean: lp @ https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L14 *)
(* Normal ∑-type is not a proposition, we need it to be to use it to create morphism classes *)
Definition filler {x y a b : C} {f : x --> y} {g : a --> b}
    {h : x --> a} {k : y --> b} (H : h · g = f · k) := 
  ∑ l : y --> a, (f · l = h) × (l · g = k).

Definition filler_map {x y a b : C} {f : x --> y} {g : a --> b}
    {h : x --> a} {k : y --> b} {H : h · g = f · k} (l : filler H) := pr1 l.
Definition filler_comm {x y a b : C} {f : x --> y} {g : a --> b}
    {h : x --> a} {k : y --> b} {H : h · g = f · k} (l : filler H) := pr2 l.

Definition lp {x y a b : C} (f : x --> y) (g : a --> b) : hProp := 
  ∀ (h : x --> a) (k : y --> b) (H : h · g = f · k), ∥filler H∥.

(* "existential" lifting property *)
Definition elp {x y a b : C} (f : x --> y) (g : a --> b) : UU := 
  ∏ (h : x --> a) (k : y --> b) (H : h · g = f · k), filler H.

(* Lean: llp @ https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L18 *)
(* 
       g
    A ---> E
    |     /|
  i |  λ/  | p
    v /    v
    X ---> B
       f 
*)
Section Lp.
Local Open Scope logic.
Definition llp (R : morphism_class C) : (morphism_class C) :=
    λ {x y : C} (f : x --> y), ∀ (a b : C) (g : a --> b), ((R _ _) g ⇒ lp f g).
Definition rlp (L : morphism_class C) : (morphism_class C) :=
    λ {a b : C} (g : a --> b), ∀ (x y : C) (f : x --> y), ((L _ _) f ⇒ lp f g).
End Lp.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L24 *)
(* MCAT: Lemma 14.1.9 *)
Lemma llp_anti {R R' : morphism_class C} (h : R ⊆ R') : llp R' ⊆ llp R.
Proof.
  unfold "⊆" in *.
  intros ? ? f H.
  intros ? ? g K.
  (* LLP for i in R' *)
  apply (H _ _ g).
  (* R ⊆ R' *)
  apply (h _ _ g).
  (* i in R *)
  exact K.
Qed.

End Lifting.

(* not in Lean file *)
Lemma opp_rlp_is_llp_opp {C : category} (L : morphism_class C) : 
    morphism_class_opp (rlp L) = (llp (morphism_class_opp L)).
Proof.
  apply morphism_class_subset_antisymm; intros x y f.
  (* todo: these proofs are the same *)
  - intro rlpf.
    intros a b g hg.
    intros top bottom H.
    (* extract lift fro rlp of f with respect to the opposite morphism of g *)
    use (rlpf _ _ (rm_opp_mor g)).
    * exact hg.
    (* flip diagram *)
    * exact (rm_opp_mor bottom).
    * exact (rm_opp_mor top).
    (* commutativity *)
    * symmetry.
      exact H.
    * (* extract lift *)
      intros hl.
      destruct hl as [l [hlg hlf]].
      apply hinhpr.

      (* the opposite morphism of the lift is the lift of the opposite diagram *)
      exists (opp_mor l).
      split; assumption.
  - intro rlpf.
    intros a b g hg.
    intros top bottom H.
    use (rlpf _ _ (rm_opp_mor g)).
    * exact hg.
    * exact (rm_opp_mor bottom).
    * exact (rm_opp_mor top).
    * symmetry.
      exact H.
    * intro hl.
      destruct hl as [l [hlg hlf]].
      apply hinhpr.

      exists (opp_mor l).
      split; assumption.
Qed.

(* dual statement *)
Lemma opp_llp_is_rlp_opp {C : category} (L : morphism_class C) : 
    morphism_class_opp (llp L) = rlp (morphism_class_opp L).
Proof.
  rewrite <- (morphism_class_opp_opp (rlp _)).
  rewrite (opp_rlp_is_llp_opp _).
  trivial.
Qed.

Lemma elp_of_retracts {C : category} 
    {a b x y a' b' x' y' : C} 
    {f : x --> y} {f' : x' --> y'}
    {g : a --> b} {g' : a' --> b'}
    (rf : retract f' f) (rg : retract g' g) :
  (elp f' g') -> (elp f g).
Proof.
  intros Hlp h k Hcomm.
  destruct rf as [ia [ra [ib [rb [ha [hb [hif hrf]]]]]]].
  destruct rg as [ix [rx [iy [ry [hx [hy [hig hrg]]]]]]].

  destruct (Hlp (ra · h · ix) (rb · k · iy)) as [l [H1 H2]].
  {
    rewrite <- assoc, hig, assoc, <- (assoc _ h g), Hcomm, assoc, hrf, assoc, assoc.
    reflexivity.
  }

  exists (ib · l · rx).
  split.
  * rewrite assoc, assoc, <- hif, <- (assoc _ f' l), H1, assoc, assoc.
    now rewrite ha, id_left, <- assoc, hx, id_right.
  * rewrite <- assoc, hrg, assoc, <- (assoc _ l g'), H2, assoc, assoc.
    now rewrite hb, id_left, <- assoc, hy, id_right.
Qed.

(* todo: use elp_of_retracts for this?  *)
Lemma lp_of_retracts {C : category} 
    {a b x y a' b' x' y' : C} 
    {f : x --> y} {f' : x' --> y'}
    {g : a --> b} {g' : a' --> b'}
    (rf : retract f' f) (rg : retract g' g) :
  (lp f' g') -> (lp f g).
Proof.
  intros Hlp h k Hcomm.
  destruct rf as [ia [ra [ib [rb [ha [hb [hif hrf]]]]]]].
  destruct rg as [ix [rx [iy [ry [hx [hy [hig hrg]]]]]]].

  use Hlp.
  - exact (ra · h · ix).
  - exact (rb · k · iy).
  - rewrite <- assoc, hig, assoc, <- (assoc _ h g), Hcomm, assoc, hrf, assoc, assoc.
    reflexivity.
  - intro Hl.
    destruct Hl as [l [H1 H2]].
    
    apply hinhpr.
    exists (ib · l · rx).
    split.
    * rewrite assoc, assoc, <- hif, <- (assoc _ f' l), H1, assoc, assoc.
      now rewrite ha, id_left, <- assoc, hx, id_right.
    * rewrite <- assoc, hrg, assoc, <- (assoc _ l g'), H2, assoc, assoc.
      now rewrite hb, id_left, <- assoc, hy, id_right.
Qed.