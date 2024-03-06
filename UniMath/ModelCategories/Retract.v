Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.

Declare Scope retract.
Delimit Scope morcls with retract.

Local Open Scope retract.

Local Open Scope cat.

Section Retract.

Context {C : category}.

(* structure retract {a b a' b' : C} (f : a ⟶ b) (f' : a' ⟶ b') : Type v :=
(ix : a' ⟶ a) (ra : a ⟶ a')
(iy : b' ⟶ b) (ry : b ⟶ b')
(hx : ix ≫ ra = 𝟙 a')
(hy : iy ≫ ry = 𝟙 b')
(hi : ix ≫ f = f' ≫ iy)
(hr : ra ≫ f' = f ≫ ry) *)
(*
        f
    a ----> b
  ^ ^       ^ ^
 ix | ra ry | iy
    v v   v v
    a'----> b'
        f'
*)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/retract.lean#L15 *)
Definition is_retract {x y x' y' : C} (f : x --> y) (f' : x' --> y')
    (ix : x' --> x) (rx : x --> x') (iy : y' --> y) (ry : y --> y') : UU :=
  (ix · rx = identity x') × (iy · ry = identity y')
  × (ix · f = f' · iy) × (rx · f' = f · ry).

Definition make_is_retract {x y x' y' : C} {f : x --> y} {f' : x' --> y'}
    {ix : x' --> x} {rx : x --> x'} {iy : y' --> y} {ry : y --> y'}
    (hx : rx ∘ ix = identity x') (hy : ry ∘ iy = identity y')
    (hi : f  ∘ ix = iy ∘ f') (hr : f' ∘ rx = ry ∘ f): is_retract f f' ix rx iy ry :=
  make_dirprod hx (make_dirprod hy (make_dirprod hi hr)).

Definition retract {x y x' y' : C} (f : x --> y) (f' : x' --> y') : UU :=
  ∑ (ix : x' --> x) (rx : x --> x') (iy : y' --> y) (ry : y --> y'),
    is_retract f f' ix rx iy ry.

Definition make_retract {x y x' y' : C} {f : x --> y} {f' : x' --> y'}
    (ix : x' --> x) (rx : x --> x') (iy : y' --> y) (ry : y --> y')
    (r : is_retract f f' ix rx iy ry) :
  retract f f' :=
    tpair _ ix (tpair _ rx (tpair _ iy (tpair _ ry r))).

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/retract.lean#L23 *)
(* Lemma 14.1.2 in MCAT *)
Lemma retract_is_iso {x y x' y' : C} {f : iso x y} {f' : x' --> y'}
    (r : retract f f') :
  is_iso f'.
Proof.
  destruct r as [ix [rx [iy [ry [hx [hy [hi hr]]]]]]].

  (* we construct an explicit inverse from the retract dixgram *)
  apply is_iso_from_is_z_iso.

  (* inverse is ra ∘ f^{-1} ∘ iy *)
  exists (iy · (inv_from_iso f) · rx).
  split.
  (* dixgram chasing *)
  - rewrite assoc, assoc, <- hi.
    rewrite <- (assoc ix _ _).
    rewrite iso_inv_after_iso, id_right.
    exact hx.
  - rewrite <- assoc, <- assoc, hr, assoc, assoc.
    rewrite <- (assoc iy _ _).
    rewrite iso_after_iso_inv, id_right.
    exact hy.
Defined.

End Retract.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/retract.lean#L36 *)
Lemma functor_on_retract {C D : category}
    (F : functor C D)
    {x y x' y' : C} {f : x --> y} {f' : x' --> y'}
    (r : retract f f') :
  retract (#F f) (#F f').
Proof.
  destruct r as [ix [ra [iy [ry [hx [hy [hi hr]]]]]]].
  use (make_retract (#F ix) (#F ra) (#F iy) (#F ry)).
  use make_is_retract; repeat rewrite <- functor_comp; try rewrite <- functor_id.
  - now rewrite hx.
  - now rewrite hy.
  - now rewrite hi.
  - now rewrite hr.
Defined.

Definition opp_retract {C : category}
    {x y x' y' : C} {f : x --> y} {f' : x' --> y'}
    (r : retract f f') :
  retract (C:=op_cat C) (opp_mor f) (opp_mor f').
Proof.
  destruct r as [ix [rx [iy [ry [hx [hy [hi hr]]]]]]].
  use make_retract.
  - exact (opp_mor ry).
  - exact (opp_mor iy).
  - exact (opp_mor rx).
  - exact (opp_mor ix).
  - use make_is_retract.
    * exact hy.
    * exact hx.
    * symmetry. exact hr.
    * symmetry. exact hi.
Defined.

Definition retract_self {C : category} {a b : C} (f : a --> b) :
    retract f f.
Proof.
  use make_retract; try exact (identity _).
  abstract (
    use make_is_retract; rewrite id_left; try rewrite id_right; trivial
  ).
Defined.