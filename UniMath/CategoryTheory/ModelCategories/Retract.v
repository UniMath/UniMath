Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.

Declare Scope retract.
Delimit Scope morcls with retract.

Local Open Scope retract.

Local Open Scope cat.

(* structure retract {a b a' b' : C} (f : a ⟶ b) (f' : a' ⟶ b') : Type v :=
(ia : a' ⟶ a) (ra : a ⟶ a')
(ib : b' ⟶ b) (rb : b ⟶ b')
(ha : ia ≫ ra = 𝟙 a')
(hb : ib ≫ rb = 𝟙 b')
(hi : ia ≫ f = f' ≫ ib)
(hr : ra ≫ f' = f ≫ rb) *)
(*
        f
    a ----> b
  ^ ^       ^ ^
 ia | ra rb | ib
    v v   v v
    a'----> b'
        f'
*)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/retract.lean#L15 *)
Definition is_retract {C : category} {a b a' b' : C} (f : a --> b) (f' : a' --> b')
    (ia : a' --> a) (ra : a --> a') (ib : b' --> b) (rb : b --> b') : UU :=
  (ra ∘ ia = identity a') × (rb ∘ ib = identity b') × (f  ∘ ia = ib ∘ f') × (f' ∘ ra = rb ∘ f).

Definition make_is_retract {C : category} {a b a' b' : C} {f : a --> b} {f' : a' --> b'}
    {ia : a' --> a} {ra : a --> a'} {ib : b' --> b} {rb : b --> b'} 
    (ha : ra ∘ ia = identity a') (hb : rb ∘ ib = identity b')  (hi : f  ∘ ia = ib ∘ f') (hr : f' ∘ ra = rb ∘ f): is_retract f f' ia ra ib rb :=
  make_dirprod ha (make_dirprod hb (make_dirprod hi hr)).

Definition retract {C : category} {a b a' b' : C} (f : a --> b) (f' : a' --> b') : UU :=
  ∑ (ia : a' --> a) (ra : a --> a') (ib : b' --> b) (rb : b --> b'), is_retract f f' ia ra ib rb.

Definition make_retract {C : category} {a b a' b' : C} {f : a --> b} {f' : a' --> b'} 
    (ia : a' --> a) (ra : a --> a') (ib : b' --> b) (rb : b --> b') (r : is_retract f f' ia ra ib rb) : retract f f' :=
  tpair _ ia (tpair _ ra (tpair _ ib (tpair _ rb r))).

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/retract.lean#L23 *)
(* Lemma 14.1.2 in MCAT *)
Lemma retract_is_iso {C : category} {a b a' b' : C} {f : iso a b} {f' : a' --> b'} (r : retract f f') : is_iso f'.
Proof.
  destruct r as [ia [ra [ib [rb [ha [hb [hi hr]]]]]]].

  (* we construct an explicit inverse from the retract diagram *)  
  apply is_iso_from_is_z_iso.

  (* inverse is ra ∘ f^{-1} ∘ ib *)
  exists (ra ∘ (inv_from_iso f) ∘ ib).
  split.
  (* diagram chasing *)
  - rewrite assoc, <- hi, assoc.
    rewrite <- (assoc ia _ _).
    rewrite iso_inv_after_iso, id_right.
    exact ha.
  - rewrite <- assoc, <- assoc, hr, assoc, assoc.
    rewrite <- (assoc ib _ _).
    rewrite iso_after_iso_inv, id_right.
    exact hb.
Defined.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/retract.lean#L36 *)
Lemma functor_on_retract {C D : category} (F : functor C D) {a b a' b' : C} {f : a --> b} {f' : a' --> b'} (r : retract f f') :
  retract (#F f) (#F f').
Proof.
  destruct r as [ia [ra [ib [rb [ha [hb [hi hr]]]]]]].
  use (make_retract (#F ia) (#F ra) (#F ib) (#F rb)).
  use make_is_retract; repeat rewrite <- functor_comp; try rewrite <- functor_id.
  - now rewrite ha.
  - now rewrite hb.
  - now rewrite hi.
  - now rewrite hr.
Defined.

Definition opp_retract {C : category} {a b a' b' : C} {f : a --> b} {f' : a' --> b'} (r : retract f f') : 
    retract (C:=op_cat C) (opp_mor f) (opp_mor f').
Proof.
  destruct r as [ia [ra [ib [rb [ha [hb [hi hr]]]]]]].
  use make_retract.
  - exact (opp_mor rb).
  - exact (opp_mor ib).
  - exact (opp_mor ra).
  - exact (opp_mor ia).
  - use make_is_retract.
    * exact hb.
    * exact ha.
    * symmetry. exact hr.
    * symmetry. exact hi.
Defined.

Definition retract_self {C : category} {a b : C} (f : a --> b) :
    retract f f.
Proof.
  use make_retract; try exact (identity _).
  use make_is_retract; rewrite id_left; try rewrite id_right; trivial.
Defined.