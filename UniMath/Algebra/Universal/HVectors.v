(** * Heterogeneous vectors. *)
(** Gianluca Amato, Matteo Calosci, Marco Maggesi, Cosimo Perini Brogi 2019-2024. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Export UniMath.Combinatorics.Vectors.

Local Open Scope stn.

(** ** Basic definitions.
If [v] is a vector of types [U1], [U2], ..., [Un], then [hvec v] is the product type [U1 × (U2 × ... × Un)]. We
introduce several basic operations on heterogeneous vectors: often they have the same syntax then the
corresponding operation on plain vectors, and a name which begins with h.

We also introduce a new scope, [hvec_scope], delimited by [hvec], which adds useful notations for
heterogeneous vectors. A vector of elements [x1], [x2], ..., [xn] may be written a [[x1; x2; ...; xn]].
Moreover [[]] denotes the empty vector and [:::] is the cons operator.
*)

Definition hvec {n: nat} (v: vec UU n): UU.
Proof.
  revert n v.
  exact (vec_ind (λ _ _, UU) unit (λ x _ _ IHv, x × IHv)).
Defined.

Declare Scope hvec_scope.

Delimit Scope hvec_scope with hvec.

Local Open Scope hvec_scope.

Bind Scope hvec_scope with hvec.

(** *** Constructors. *)

Definition hnil : hvec vnil := tt.

Definition hcons {A: UU} (x: A) {n: nat} {v: vec UU n} (hv: hvec v) : hvec (A ::: v) := x ,, hv.

(** *** Notations. *)

Notation "[( x ; .. ; y )]" := (hcons x .. (hcons y hnil) ..): hvec_scope.

Notation "[()]" := hnil (at level 0, format "[()]"): hvec_scope.

Infix ":::" := hcons: hvec_scope.

Definition hvec_ind (P : ∏ n (v: vec UU n), hvec v → UU) :
  P 0 [()] [()]
  → (∏ X x n (v: vec UU n) (hv : hvec v), P n v hv → P (S n) (vcons X v) (x ::: hv))
  → (∏ n (v: vec UU n) (hv : hvec v), P n v hv).
Proof.
  intros H0 HI n v hv.
  induction n as [|n IHn].
  - induction v, hv.
    exact H0.
  - change v with (pr1 v ::: pr2 v)%vec.
    change hv with (pr1 hv ::: pr2 hv).
    apply HI, IHn.
Defined.

(*two variations on hvec_ind, with weaker hypothesis*)

Definition hvec_ind_fixedv {v:∏ n:nat, vec UU n} (P : ∏ n , hvec (v n) → UU) :
  (∏ hv0 , P 0 hv0)
  → (∏ n , (∏ hv , P n hv) → (∏ hv, P (S n) hv) )
  → (∏ n (hv : hvec (v n)), P n hv).
Proof.
  intros H0 HI n hv.
  induction n as [|n IHn].
  - use H0.
  - change hv with (pr1 hv ::: pr2 hv).
    apply HI, IHn.
Defined.

Definition hvec_ind' {n:nat} {v: vec UU n} (P : ∏ n' (v': vec UU n'), hvec v' → UU)
  : P 0 [()] [()]
  → (∏ X x m (w: vec UU m) (hw : hvec w), m<n → P m w hw → P (S m) (vcons X w) (x ::: hw))
  → ∏ hv : hvec v, P n v hv.
Proof.
  intros H0 HI hv.
  induction n as [| n IHn].
  - induction v, hv.
    exact H0.
  - change v with (pr1 v ::: pr2 v)%vec.
    change hv with (pr1 hv ::: pr2 hv).
    apply HI.
    * apply natlthnsn.
    * apply IHn.
      intros X x m w hw Hm HIm.
      apply HI.
      + apply (istransnatlth _ n).
        ++ exact Hm.
        ++ apply natlthnsn.
      + exact HIm.
Defined.


Definition hdrop {n:nat} {P: ⟦ S n ⟧ → UU} (f: ∏ i: ⟦ S n ⟧, P i) : (∏ i: ⟦ n ⟧, P (dni_firstelement i)) := f ∘ dni_firstelement.

Definition functionToHVec {n: nat} {P: ⟦ n ⟧ → UU} (f: ∏ i: ⟦ n ⟧, P i) : hvec (make_vec P).
Proof.
  induction n.
  - exact [()].
  - exact ((f firstelement) ::: (IHn (P ∘ dni_firstelement) (f ∘ dni_firstelement))).
Defined.

Definition make_hvec {n: nat} {v: vec UU n} (f: ∏ i: ⟦ n ⟧, el v i) : hvec v.
Proof.
  revert n v f.
  use vec_ind.
  + intro. exact tt.
  + intros X n v IH f.
    exists (f firstelement).
    exact (IH (hdrop f)).
Defined.

(** *** Projections. *)

Definition hhd {A: UU} {n: nat} {v: vec UU n} (hv: hvec (A ::: v)): A := pr1 hv.

Definition htl {A: UU} {n: nat} {v: vec UU n} (hv: hvec (A ::: v)): hvec v := pr2 hv.

Definition hel {n: nat} {v: vec UU n} (hv: hvec v): ∏ i: ⟦ n ⟧, el v i.
Proof.
  revert n v hv.
  refine (vec_ind _ _ _).
  - intros.
    apply (fromempty (negnatlthn0 (pr1 i) (pr2 i))).
  - intros x n xs IHxs.
    induction i as [i iproof].
    induction i.
    + exact (hhd hv).
    + exact (IHxs (htl hv) (make_stn _ i iproof)).
Defined.

(** *** Some identities for computing [hel]. *)

Lemma hel_make_hvec {n} {v: vec UU n} (f : ∏ i: ⟦ n ⟧, el v i) : hel (make_hvec f) ~ f .
Proof.
  intro i.
  induction n as [|m meq].
  - exact (fromstn0 i).
  - induction i as (j,jlt).
    induction j as [|k _].
    + (*This subgoal seems easy enough to not require a proof so cumbersome...
      can we do better without make the goal family explicit?*)
      use (stn_predicate (λ z , hel (make_hvec f) z = f z) 0 _ jlt).
      { reflexivity. }
      apply idpath.
    + use meq.
Defined.

Lemma hel_make_hvec_fun {n} {v: vec UU n} (f : ∏ i: ⟦ n ⟧, el v i) : hel (make_hvec f) = f.
Proof.
  apply funextsec.
  apply hel_make_hvec.
Defined.

Lemma hel_hcons_htl {n} {v: vec UU n} (hv : hvec v) {X:UU} (x : X) (i : ⟦ n ⟧) :
  hel (x ::: hv) (dni_firstelement i) = hel hv i.
Proof.
  apply idpath.
Defined.

Lemma hel_hcons_hhd {n} {v: vec UU n} (hv : hvec v) {X:UU} (x : X) :
  hel (x ::: hv) (firstelement) = x.
Proof.
  reflexivity.
Defined.

Lemma drop_hel {n} {v: vec UU (S n)} (hv : hvec v) (i: ⟦ n ⟧ ) : hdrop (hel hv) i = hel (htl hv) i.
Proof.
  apply idpath.
Defined.

Lemma hel_htl {n} {v: vec UU (S n)} (hv : hvec v) (i : ⟦ n ⟧)
  : hel (htl hv) i = hdrop (hel hv) i.
Proof.
  apply idpath.
Defined.

Lemma hvec_extens {n} {v: vec UU n} {hu hv: hvec v} :
  (∏ i : ⟦ n ⟧, hel hu i = hel hv i) → hu = hv.
Proof.
  intros H.
  revert n v hu hv H.
  use vec_ind.
  - cbn beta.
    intros.
    use proofirrelevance.
    use isapropunit.
  - cbn beta.
    intros X n v IH hv hu H.
    induction hv as (xv,htv).
    induction hu as (xu,htu).
    use dirprod_paths.
    * use (H firstelement).
    * use IH.
      intro i.
      use (H (dni_firstelement i)).
Defined.

Lemma make_hvec_hel {n} {v: vec UU n} (hv : hvec v) : (make_hvec (hel hv)) = hv .
Proof.
  apply hvec_extens.
  intros i.
  rewrite hel_make_hvec.
  reflexivity.
Defined.

(** *** Weak equivalence with functions. *)

Definition helf_weq {n: nat} {v: vec UU n} : (hvec v) ≃ ∏ i: ⟦ n ⟧, el v i.
Proof.
  use weq_iso.
  + use hel.
  + use make_hvec.
  + use make_hvec_hel.
  + use hel_make_hvec_fun.
Defined.

Lemma inv_helf_weq {n:nat} {v:vec UU n} : invmap (helf_weq (n:=n) (v:=v)) = make_hvec.
Proof.
  use funextsec.
  intro.
  use (invmaponpathsweq helf_weq).
  rewrite homotweqinvweq.
  simpl.
  rewrite hel_make_hvec_fun.
  apply idpath.
Defined.


Lemma hcons_paths {A: UU} (x y: A) {n: nat} (v: vec UU n) (xs ys: hvec v) (p: x = y) (ps: xs = ys)
  : x ::: xs = y ::: ys.
Proof.
  apply (map_on_two_paths (λ x xs, @hcons A x n v xs)) ; assumption.
Defined.

Lemma isofhlevelhvec {m: nat} {n: nat} (v: vec UU n) (levels: hvec (vec_map (isofhlevel m) v))
  : isofhlevel m (hvec v).
Proof.
  revert n v levels.
  refine (vec_ind _ _ _).
  - intro.
    apply isofhlevelcontr.
    apply iscontrunit.
  - intros x n xs IHxs levels.
    simpl.
    apply isofhleveldirprod.
    + apply (pr1 levels).
    + apply (IHxs (pr2 levels)).
Defined.

Lemma hvec_vec_fill {A: UU} {n: nat} : hvec (vec_fill A n) = vec A n.
Proof.
  induction n.
  - apply idpath.
  - simpl.
    apply maponpaths.
    assumption.
Defined.

(*Lemma for transport. It can be seen as a generalization of [transportf_dirprod]*)

Lemma transportf_hvec' {n: nat} {v v': vec UU (S n)}
  (p : v = v')
  (hv : hvec v)
  : transportf hvec p hv
    = transportf (idfun UU) (maponpaths hd p) (hhd hv) ::: transportf hvec (maponpaths tl p) (htl hv).
Proof.
  induction p.
  reflexivity.
Qed.

Lemma transportf_hvec {n: nat} {v v': vec UU (S n)}
  (p : v = v')
  (hv : hvec v)
  : transportf hvec p hv
    = (transportf hd p (hhd hv)) ::: (transportf (hvec ∘ tl) p (htl hv)).
Proof.
  induction p.
  reflexivity.
Defined.

Lemma transportf_hvec_vecS_eq {n: nat} {v v': vec UU (S n)}
  (p : hd v = hd v')
  (q : tl v = tl v')
  (hv : hvec v)
  : transportf hvec (vecS_eq p q) hv
    = (transportf (idfun UU) p (hhd hv)) ::: (transportf hvec q (htl hv)).
Proof.
  destruct v as [v_hd v_tl].
  destruct v' as [v'_hd v'_tl].
  induction (p: v_hd = v'_hd).
  induction (q: v_tl = v'_tl).
  apply idpath.
Defined.

(** ** Level-1 heterogeneous vectors.

A level-1 hvec is a term of type [hvec (vec_map P v)] for some [v: vec A n] and [P: A → UU].
Some operations may be easily defined for a level-1 hvec but not for a generic heterogeneous. Operations
on level-1 hvec have names beginning with h1.
*)

(** *** Miscellanea of operations on level-1 hvecs. *)

(** [h1const_is_vec] proves that an [hvec (vec_map P v)] is a [vec] when [P] is a constant map. *)

Definition h1const_is_vec {A: UU} {n: nat} (v: vec A n) (B: UU)
  : hvec (vec_map (λ _, B) v) = vec B n.
Proof.
  induction n.
  - apply idpath.
  - simpl.
    apply maponpaths.
    apply IHn.
Defined.

(** [h1lower] transforms a [hvec (vec_map P v)]  into a [vec] when [P] is a constant map. Although
it would be possibile to define [h1lower] starting from [h1const_is_vec], this would make difficult
to work by induction over [v]. *)

Definition h1lower {A: UU} {n: nat} {v: vec A n} {B: UU} (h1v: hvec (vec_map (λ _, B) v))
  : vec B n.
Proof.
  revert n v h1v.
  refine (vec_ind _ _ _).
  - apply idfun.
  - intros x n xs IHxs h1v.
    exact (vcons (hhd h1v) (IHxs (htl h1v))).
Defined.

Definition h1lower_vec_map_comp {I : UU} {n: nat} {v: vec I n}
  (A : ∏ (i: I), UU)
  (hv : hvec (vec_map (λ (_:I),UU) v))
  : h1lower hv
  = h1lower (transportf hvec (vec_map_comp A (λ _ : UU, UU) v) hv).
Proof.
  revert n v hv.
  use vec_ind.
  - use idpath.
  - intros x n v IH hv.
    (* change (vec_map_comp A (λ _ : UU, UU) (x ::: v)) with
      (vecS_eq
        (u:= UU ::: vec_map (λ _ : I, UU) v)
        (v := UU ::: (((vec_map (λ _ : UU, UU))∘(vec_map A)) v))
        (idpath _)
        (vec_map_comp A (λ _ : UU, UU) v)). *)
    eapply pathscomp0.
    2:{
      apply pathsinv0.
      eapply (maponpaths h1lower).
      use transportf_hvec_vecS_eq.
    }
    use dirprod_paths.
    + apply idpath.
    + use IH.
Defined.

(** [h1foldr] is the analogous of [foldr] for level-1 hvecs. *)

Definition h1foldr {A: UU} {n: nat} {v: vec A n} {P: A → UU} {B: UU} (comb: ∏ (a: A), P a → B → B)
                  (s: B) (h1v: hvec (vec_map P v)): B.
Proof.
   revert n v h1v.
   refine (vec_ind _ _ _).
   - intro.
     exact s.
   - intros x n xs IHxs.
     simpl.
     intro.
     exact (comb _ (pr1 h1v) (IHxs (pr2 h1v))).
Defined.

(** *** Map involving level-1 hvecs.

The [h1map] (resp. [h01map]) function is analogous to [map] for level-1 hvecs:
[h1map f hv] (resp. h01map f v) applies the function [f]
to all elements of [hv] (resp. [v:vec A n]).
The result is of type [hvec (vec_map Q v)] for an appropriate [Q: A → UU].

When [Q] is the constant map in [h1map], we may instead use [h1map_vec] which returns a vec instead of an hvec.
*)

Definition h1map {A: UU} {n: nat} {v: vec A n} {P: A → UU}
                 {Q: A → UU} (f: ∏ (a: A), P a → Q a) (h1v: hvec (vec_map P v))
  : hvec (vec_map Q v).
Proof.
  revert n v f h1v.
  refine (vec_ind _ _ _ ).
  - intros.
    exact [()].
  - intros x n xs IHxs.
    simpl.
    intros f h1v.
    exact (f x (hhd h1v) ::: IHxs f (htl h1v)).
Defined.

Definition h01map {A: UU} {n: nat} {P: A → UU}
  (f: ∏ (a: A), P a) (v : vec A n)
  : hvec (vec_map P v).
Proof.
  use (vec_ind (λ n v, hvec (vec_map P v))).
  - exact tt.
  - intros x n' v' hv.
    exact (f x ::: hv).
Defined.


Lemma h01maph1lower {I : UU} {n: nat} {v: vec I n}
  (A : ∏ (i: I), UU)
  (R : UU → UU)
  (r : ∏ (i: I), R (A i))
  (s : ∏ (X:UU), R X → UU)
  : vec_map (λ (i:I), s (A i) (r i)) v
  = h1lower (h01map (λ (i:I), s (A i) (r i)) v).
Proof.
  revert n v.
  use vec_ind.
  - apply idpath.
  - intros x n v IH.
    use dirprod_paths.
    + apply idpath.
    + use IH.
Defined.

Lemma vec_map_conspath {A: UU} {n: nat} {a:A} {v: vec A n} {P: A → UU}
  : vcons (P a) (vec_map P v) = vec_map P (vcons a v).
Proof.
  apply idpath.
Defined.

Lemma h1map_conspath {A: UU} {n: nat} {a:A} {v: vec A n} {P: A → UU}
                 {Q: A → UU} (f: ∏ (a: A), P a → Q a)
                 (h1hd : P a) (h1v: hvec (vec_map P v))
  : h1map f (h1hd ::: h1v : hvec (vec_map P (vcons a v)))
    = (f a h1hd) ::: h1map f h1v.
Proof.
  apply idpath.
Defined.

Lemma h1h01map_comp
  {A: UU} {n: nat} {v: vec A n} {P: A → UU}
  {Q: A → UU} (f: ∏ (a: A), P a) (g: ∏ (a: A), P a → Q a)
  : h1map g (h01map f v) = h01map (λ a, g a (f a)) v.
Proof.
  use (vec_ind
    (λ n v, h1map g (h01map f v) = h01map (λ a : A, g a (f a)) v)).
  - apply idpath.
  - intros x n' v' IH.
    simpl.
    use dirprod_paths.
    + apply idpath.
    + use IH.
Defined.

Lemma h1map_transport_vec_map_comp
  {I : UU} {n: nat} {v: vec I n}
  (A : ∏ (i: I), UU)
  (R : UU → UU)
  (s : ∏ (X:UU), R X → UU)
  (hv : hvec (vec_map (λ i : I, R (A i)) v))
  : h1map s (transportf hvec (vec_map_comp A R v) hv)
    = transportf hvec (vec_map_comp A (λ _ : UU, UU) v) (h1map (Q:=λ(_:I), UU) (λ (i:I) (rel : R (A i)), s (A i) rel) hv).
Proof.
  revert hv.
  use (vec_ind (λ n v, ∏ hv : hvec (vec_map (λ i : I, R (A i)) v),
    h1map s (transportf hvec (vec_map_comp A R v) hv) =
      transportf hvec (vec_map_comp A (λ _ : UU, UU) v)
        (h1map (λ (i : I) (rel : R (A i)), s (A i) rel) hv))).
  { intro. apply idpath. }
  intros x n' v' IH hv.
  (* change (vec_map_comp A R (x ::: v')) with
    (vecS_eq
      (u:= R (A x) ::: vec_map (R∘A) v')
      (v := R (A x) ::: (((vec_map R)∘(vec_map A)) v'))
      (idpath _) (vec_map_comp A R v')).
  change (vec_map_comp A (λ _ : UU, UU) (x ::: v')) with
    (vecS_eq
      (u:= UU ::: vec_map (λ _ : I, UU) v')
      (v := UU ::: (((vec_map (λ _ : UU, UU))∘(vec_map A)) v'))
      (idpath _) (vec_map_comp A (λ _ : UU, UU) v')). *)
  eapply pathscomp0.
  {
    eapply maponpaths.
    use transportf_hvec_vecS_eq.
  }
  eapply pathscomp0.
  2:{
    use pathsinv0.
    use transportf_hvec_vecS_eq.
  }
  use dirprod_paths.
  - reflexivity.
  - use IH.
Defined.

Lemma h1h01map_transport_vec_map_comp
  {I : UU} {n: nat} {v: vec I n}
  (A : ∏ (i: I), UU)
  (R : UU → UU)
  (r : ∏ (i: I), R (A i))
  (s : ∏ (X:UU), R X → UU)
  : h1map s (transportf hvec (vec_map_comp A R v) (h01map r v)) = transportf hvec (vec_map_comp A (λ _, UU) v) (h01map (λ i, s (A i) (r i)) v).
Proof.
  eapply pathscomp0.
  - use h1map_transport_vec_map_comp.
  - use maponpaths.
    use h1h01map_comp.
Defined.

Lemma h1map_idfun {A: UU} {n: nat} {v: vec A n} {P: A → UU} (h1v: hvec (vec_map P v))
  : h1map (λ a: A, idfun (P a)) h1v = h1v.
Proof.
  revert n v h1v.
  refine (vec_ind _ _ _).
  - induction h1v.
    apply idpath.
  - simpl.
    intros x n xs IHxs h1v.
    change h1v with (pr1 h1v ::: pr2 h1v).
    apply maponpaths.
    apply (IHxs (pr2 h1v)).
Defined.

Lemma h1map_compose {A: UU} {n: nat} {v: vec A n} {P: A → UU} {Q: A → UU} {R: A → UU}
                    (f: ∏ a: A, P a → Q a) (g: ∏ (a: A), Q a → R a) (h1v: hvec (vec_map P v))
  : h1map g (h1map f h1v) = h1map (λ a: A, (g a) ∘ (f a)) h1v.
Proof.
  revert n v h1v.
  refine (vec_ind _ _ _).
  - induction h1v.
    apply idpath.
  - simpl.
    intros x n xs IHxs h1v.
    apply maponpaths.
    apply (IHxs (pr2 h1v)).
Defined.

(** [h1map_vec] is just the composition of [h1map] and [h1lower], but it deserves a name
since it is used in the definition of level-2 hvecs (see later). *)

Definition h1map_vec {A: UU} {n: nat} {v: vec A n} {P: A → UU}
                        {B: UU} (f: ∏ (a: A), P a → B) (h1v: hvec (vec_map P v))
  : vec B n := h1lower (h1map f h1v).

(*[[el]] of an [[h1map_vec]] is just the appropriate casting of function application*)
Definition hel_h1map_vec {A: UU} {n: nat} {v: vec A n} {P: A → UU} {B: UU}
  (f: ∏ (a: A), P a → B)
  (hv: hvec (vec_map P v)) (i:⟦ n ⟧)
  : el (h1map_vec f hv) i = f (el v i) (eqweqmap (el_vec_map P v i) (hel hv i)).
Proof.
  induction n as [|m IHn0].
  + use fromstn0.
    exact i.
  + induction v as [vhead vtail].
    induction hv as [hvhead hvtail].
    induction i as [j  jlt].
    induction j as [| k].
    - apply idpath.
    - use IHn0.
Defined.

Section hel_h1map_vec_vec_fill.
(*This is just [[hel_h1map_vec]] for the special case in which
  [[v]] is of the form [[(vec_fill a n)]].

  In this case we can have [[a]] judgemntally in the right hand side*)

Context {A: UU} {n: nat} {a:A} {P: A → UU} {B: UU} (f: ∏ (x: A), P x → B)
  (hv: hvec (vec_map P (vec_fill a n))) (i:⟦ n ⟧).

Definition hel_h1map_vec_vec_fill_lemma : f (el (vec_fill a n) i) (eqweqmap (el_vec_map P (vec_fill a n) i) (hel hv i)) = f a (eqweqmap (el_vec_map_vec_fill P a i) (hel hv i)).
Proof.
  induction n as [|m IHn0].
  + use fromstn0.
    exact i.
  + induction hv as [hvhead hvtail].
    induction i as [j  jlt].
    induction j as [| k].
    - apply idpath.
    - use IHn0.
Defined.

Definition hel_h1map_vec_vec_fill : el (h1map_vec f hv) i = f a (eqweqmap (el_vec_map_vec_fill P a i) (hel hv i)).
Proof.
  etrans.
  { apply hel_h1map_vec. }
  use hel_h1map_vec_vec_fill_lemma.
Defined.

End hel_h1map_vec_vec_fill.

(** ** Level-2 heterogeneous vectors.

A level-2 hvec is a term of type [hvec (h1map_vec Q h1v)] for some [h1v: hvec (vec_map P v)],
[v: vec A n], [P: A → UU], [Q: ∏ a: A, P a → UU]. Operators on level-2 hvecs have names which
begins with h2.

The need to work explicitly with level-1 and level-2 hvecs, instead of generic heterogeneous vecs,
seems unfortunate. A refactoring of this library could free us from the burden of working with such
articulate data types
*)

(** [h2map] is like [h1map] for level-2 hvecs. *)

Definition h2map {A: UU} {n: nat} {v: vec A n} {P: A → UU} {h1v: hvec (vec_map P v)}
                 {Q: ∏ (a: A) (p: P a), UU} {R: ∏ (a: A) (p: P a), UU}
                 (f: ∏ (a: A) (p: P a), Q a p → R a p) (h2v: hvec (h1map_vec Q h1v))
  : hvec (h1map_vec R h1v).
Proof.
  revert n v f h1v h2v.
  refine (vec_ind _ _ _ ).
  - intros.
    exact [()].
  - intros x n xs IHv f h1v h2v.
    exact (f x (pr1 h1v) (pr1 h2v) ::: IHv f (pr2 h1v) (pr2 h2v)).
Defined.

(*TODO: write comment*)
Definition h12map {A: UU} {n: nat} {v: vec A n}
                  {P: A → UU} {R: ∏ (a: A) (p: P a), UU}
                  (f: ∏ (a: A) (p: P a), R a p) (*h2v: hvec (h1map_vec Q h1v)*)
                  (h1v: hvec (vec_map P v))
  : hvec (h1map_vec R h1v).
Proof.
  revert n v f h1v.
  refine (vec_ind _ _ _ ).
  - intros.
    exact [()].
  - intros x n xs IHv f h1v.
    exact (f x (pr1 h1v) ::: IHv f (pr2 h1v)).
Defined.

(*[[hel]] of an [[h2map]] is just the appropriate casting of function application*)
Definition helh2map {A: UU} {n: nat} {v: vec A n} {P: A → UU} {h1v: hvec (vec_map P v)}
                 {Q: ∏ (a: A) (p: P a), UU} {R: ∏ (a: A) (p: P a), UU}
                 (f: ∏ (a: A) (p: P a), Q a p → R a p) (h2v: hvec (h1map_vec Q h1v))
                 (i:⟦ n ⟧)
  : hel (h2map f h2v) i = (invweq (eqweqmap (hel_h1map_vec R h1v i)) (f _ _ (eqweqmap (hel_h1map_vec Q h1v i) (hel h2v i)))).
Proof.
  revert n v f h1v h2v i.
  refine (vec_ind _ _ _ ).
  - intros f h1v h2v i.
    use fromstn0.
    exact i.
  - intros x n v X f h1v h2v i.
    induction i as [j  jlt].
    induction j as [| k].
    * apply idpath.
    * use X.
Defined.

Definition h2map_makehvec {A: UU} {n: nat} {v: vec A n} {P: A → UU} {h1v: hvec (vec_map P v)}
                 {Q: ∏ (a: A) (p: P a), UU} {R: ∏ (a: A) (p: P a), UU}
                 (f: ∏ (a: A) (p: P a), Q a p → R a p) (h2v: hvec (h1map_vec Q h1v))
  : h2map f h2v = make_hvec (λ i, (invweq (eqweqmap (hel_h1map_vec R h1v i)) (f _ _ (eqweqmap (hel_h1map_vec Q h1v i) (hel h2v i))))).
Proof.
  use (invmaponpathsweq helf_weq).
  simpl.
  use funextsec.
  intro i.
  etrans.
  { apply helh2map. }
  use pathsinv0.
  use hel_make_hvec.
Defined.

(*[[helh2map_basevecfill]] and [[h2map_makehvec_basevecfill]] are just [[helh2map]] and [[h2map_makehvec]] in the case in which [[v]] is the form [[(vec_fill a n)]]*)
Definition helh2map_basevecfill {A: UU} {n: nat} {a: A} {P: A → UU} {h1v: hvec (vec_map P (vec_fill a n))}
                 {Q: ∏ (a: A) (p: P a), UU} {R: ∏ (a: A) (p: P a), UU}
                 (f: ∏ (a: A) (p: P a), Q a p → R a p) (h2v: hvec (h1map_vec Q h1v))
                 (i:⟦ n ⟧)
  : hel (h2map f h2v) i = invweq (eqweqmap (hel_h1map_vec_vec_fill R h1v i)) (f _ _ (eqweqmap (hel_h1map_vec_vec_fill Q h1v i) (hel h2v i))).
Proof.
  revert n h1v h2v i.
  use hvec_ind_fixedv.
  - intros h1v h2v i.
    use fromstn0.
    exact i.
  - intros n IH h1v h2v i.
    induction i as [j  jlt].
    induction j as [| k].
    * apply idpath.
    * use IH.
Defined.

Definition h2map_makehvec_basevecfill {A: UU} {n: nat} {a: A} {P: A → UU} {h1v: hvec (vec_map P (vec_fill a n))}
                 {Q: ∏ (a: A) (p: P a), UU} {R: ∏ (a: A) (p: P a), UU}
                 (f: ∏ (a: A) (p: P a), Q a p → R a p) (h2v: hvec (h1map_vec Q h1v))
  : h2map f h2v = make_hvec (λ i, invweq (eqweqmap (hel_h1map_vec_vec_fill R h1v i)) (f _ _ (eqweqmap (hel_h1map_vec_vec_fill Q h1v i) (hel h2v i)))).
Proof.
  use (invmaponpathsweq helf_weq).
  simpl.
  use funextsec.
  intro i.
  etrans.
  { apply helh2map_basevecfill. }
  use pathsinv0.
  use hel_make_hvec.
Defined.


(** [h1lift] transforms a level-1 hvec into a level-2 hvec. *)

Definition h1lift {A: UU} {n: nat} {v: vec A n} {P: A → UU} (h1v: hvec (vec_map P v))
  : hvec (h1map_vec (λ a _, P a) h1v).
Proof.
  revert n v h1v.
  refine (vec_ind _ _ _ ).
  - intros.
    exact [()].
  - intros x n xs IHv h1v.
    exact ((pr1 h1v) ::: IHv (pr2 h1v)).
Defined.

(** [h2lower] transforms a level-2 hvec [h2v: hvec (hmap_vec Q h1v)] into a level-1 hvec when
[Q: ∏ a: A, P a → UU] is constant on the argument of type [P a].
*)
Definition h2lower {A: UU} {n: nat} {v: vec A n} {P: A → UU} {h1v: hvec (vec_map P v)}
                 {Q: A → UU} (h2v: hvec (h1map_vec (λ a _, Q a) h1v))
  : hvec (vec_map Q v).
Proof.
  revert n v h1v h2v.
  refine (vec_ind _ _ _).
  - reflexivity.
  - simpl.
    intros x n xs IHxs h1v h2v.
    split.
    + exact (pr1 h2v).
    + exact (IHxs (pr2 h1v) (pr2 h2v)).
Defined.

(** [h2lower_h1map_h1lift] and [h1map_h1lift_as_h2map] are two normalization lemmas relating level-1 and
level-2 hvecs. *)

Lemma h2lower_h1map_h1lift {A: UU} {n: nat} {v: vec A n}  {P: A → UU}
                       {Q: ∏ (a: A), UU} (f: ∏ (a: A), P a → Q a) (h1v: hvec (vec_map P v))
  : h2lower (h2map (λ a p _, f a p) (h1lift h1v)) = h1map f h1v.
Proof.
  revert n v h1v.
  refine (vec_ind _ _ _).
  - reflexivity.
  - intros x n xs IHxs h1v.
    simpl.
    apply maponpaths.
    exact (IHxs (pr2 h1v)).
Defined.

Lemma h1map_h1lift_as_h2map {A: UU} {n: nat} {v: vec A n} {P: A → UU} (h1v: hvec (vec_map P v))
             {Q: ∏ (a: A) (p: P a), UU} (h2v: hvec (h1map_vec Q h1v))
             {R: ∏ (a: A) (p: P a), UU} (f: ∏ (a: A) (p: P a), R a p)
  : h2map (λ a p _, f a p) (h1lift h1v) = h2map (λ a p _, f a p) h2v.
Proof.
  revert n v h1v h2v.
  refine (vec_ind _ _ _).
  - reflexivity.
  - simpl.
    intros x n xs IHxs h1v h2v.
    apply maponpaths.
    exact (IHxs (pr2 h1v) (pr2 h2v)).
Defined.

(** [h2foldr] is the analogous of [foldr] for level-2 hvecs. *)

Definition h2foldr {A: UU} {n: nat} {v: vec A n} {P: A → UU} {h1v: hvec (vec_map P v)}
                   {Q: ∏ (a: A) (p: P a), UU} {B: UU}
                   (comp: ∏ (a: A) (p: P a), Q a p → B → B) (s: B) (h2v: hvec (h1map_vec Q h1v))
  : B.
Proof.
   revert n v h1v h2v.
   refine (vec_ind _ _ _).
   - intros.
     exact s.
   - simpl.
     intros x n xs IHxs h1v h2v.
     exact (comp _ _ (pr1 h2v) (IHxs (pr2 h1v) (pr2 h2v))).
Defined.

(** [h1map_path] returns a proof that [hmap f h1v] and [hmap g h1v] are equal, provided that we
have a level-2 hvec [h2path] of proofs that the images of [f] and [g] on corresponding elements
of [h1v] are equal.
*)

Lemma h1map_path {A: UU} {n: nat} {v: vec A n} {P: A → UU} {Q: A → UU} (f: ∏ a: A, P a → Q a)
                (g: ∏ (a: A), P a → Q a) (h1v: hvec (vec_map P v))
                (h2path: hvec (h1map_vec (λ a p, f a p = g a p) h1v))
  : h1map f h1v = h1map g h1v.
Proof.
  revert n v h1v h2path.
  refine (vec_ind _ _ _).
  - induction h1v.
    reflexivity.
  - simpl.
    intros x n xs IHxs h1v h2path.
    use map_on_two_paths.
    + exact (pr1 h2path).
    + exact (IHxs (pr2 h1v) (pr2 h2path)).
Defined.

(** ** Functions from hvecs and their curried variants. *)

(**
  If [v] is a vector of types of length [n], [iterfun v B] is the curried version of [hvec v → B], i.e.
  [iterfun v B] =  [(el v 1) → ((el v 2) → ...... → ((el v n) → B)].
*)

Definition iterfun {n: nat} (v: vec UU n) (B: UU): UU.
Proof.
  revert n v.
  refine (vec_ind _ _ _).
  - exact B.
  - intros x n xs IHxs.
    exact (x → IHxs).
Defined.

(**
   If  [f: hvec v → B], then [currify f] is the curried version of [f], which has type
   [iterfun v B].
*)

Definition currify {n: nat} {v: vec UU n} {B: UU} (f: hvec v → B): iterfun v B.
Proof.
  revert n v f.
  refine (vec_ind _ _ _).
  - intros.
    exact (f tt).
  - intros x n xs IHxs f.
    simpl in f.
    simpl.
    intro a.
    exact (IHxs (λ l, f (a,, l))).
Defined.

(**
   [uncurrify] is the inverse transformation of [currify].
*)

Definition uncurrify {n: nat} {v: vec UU n} {B: UU} (f: iterfun v B): hvec v → B.
Proof.
  revert n v f.
  refine (vec_ind _ _ _).
  - intros.
    exact f.
  - intros x n xs IHxs f.
    simpl in *.
    intro a.
    exact (IHxs (f (pr1 a)) (pr2 a)).
Defined.


(** *** An hvec made up of sets is an hSet *)

Definition pr1vechSet {n: nat} : vec hSet n → vec UU n.
Proof.
  induction n.
  - apply tounit.
  - intros Xv.
    destruct Xv as [X v].
    exact ((X:UU) ,, IHn v).
Defined.

(* Lemma isasethvec {n: nat} (v: vec hSet n) : isaset (hvec (pr1vechSet v)).
Proof.
  induction n.
  - use isasetunit.
  - use isasetdirprod.
    + use setproperty.
    + use IHn.
Qed. *)

Lemma isasethvec {n: nat} (v: vec UU n)
  (iss : hvec (vec_map (isaset) v))
  : isaset (hvec v).
Proof.
  revert iss.
  apply (vec_ind (λ n v, hvec (vec_map isaset v) → isaset (hvec v))).
  - intro.
    apply isasetunit.
  - intros X n' tl IH_tl H.
    apply isasetdirprod.
    + (* change (isaset X). *)
      apply H.
    + (* change (isaset (hvec tl)). *)
      apply IH_tl.
      apply H.
Qed.

Section Hvec_ofpaths.
  Context {S: UU} {n: nat} {v: vec S n}
          {B A: S → UU}
          (L: ∏ (s:S), B s → A s)
          (hv : hvec (vec_map A v))
          (fib : hvec (h1lower (h1map (λ s a, ∑ (b: B s), L s b = a)hv)))
          (E : hvec (h1map_vec (λ (s:S) (a:A s), ∏ (t: ∑ (b: B s), L s b = a), L s (pr1 t) = a) hv)).

  (*TODO: this hypothesis are specific to prove [[issubuniverse_image]] in [[SubAlgebras.v]]. Can we generalize? *)

  Theorem hvec_ofpaths : h1map L (h2lower (h2map (λ s (p:A s), pr1 ) fib)) = hv.
  Proof.
    revert n v hv fib E.
    use (vec_ind _ _).
    - intros hv fib E.
      cbn.
      induction hv.
      apply idpath.
    - intros s n v IH hv fib E.
      use dirprod_paths.
      + use (hhd E).
      + use IH.
        use (htl E). 
  Defined.

End Hvec_ofpaths.