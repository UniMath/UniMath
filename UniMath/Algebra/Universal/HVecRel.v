Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Algebra.Universal.HVectors.

(**
  Given a vector of relations on types
  we can define the corresponding relation on the corresponding hvec.

  If the relations are equivalence relations
  then the quotients hvec is equivalent (as a type)
  to the quotient of the defined relation
*)

Definition hrelhvec {n:nat} (v : vec UU n) (rels: hvec (vec_map hrel v))
  : (hrel (hvec v)).
Proof.
  revert n v rels.
  use vec_ind.
  - intros rels. use uniteqrel.
  - intros X n v IH rels.
    destruct rels as [relX relsv].
    use hreldirprod.
    + use relX.
    + use IH.
      exact relsv.
Defined.

Definition pr1eqrelhvec {n:nat} {v : vec UU n} : hvec (vec_map eqrel v) -> hvec (vec_map hrel v).
Proof.
  use h1map.
  use pr1eqrel.
Defined.

Definition eqrelhvec {n:nat} (v : vec UU n) (rels: hvec (vec_map eqrel v))
  : (eqrel (hvec v)).
Proof.
  use make_eqrel.
  - exact (hrelhvec v (pr1eqrelhvec rels)).
  - revert rels.
    use (vec_ind (λ n v, ∏ rels : hvec (vec_map eqrel v), iseqrel (hrelhvec v (pr1eqrelhvec rels)))).
    + intro v'. use iseqrelunittrivialrel.
    + intros x n' v' IH rels.
      use iseqreldirprod.
      * use (iseqreleqrel (hhd rels)).
      * use IH.
Defined.

Lemma pr1eqrelhvec_eq {n:nat} {v : vec UU n} (rels: hvec (vec_map eqrel v))
  : pr1eqrel _ (eqrelhvec v rels) =
    hrelhvec v (pr1eqrelhvec rels).
Proof.
  reflexivity.
Qed.

Definition hvectosetquot {n:nat} {v : vec UU n} (rels: hvec (vec_map hrel v))
  (c : hvec (h1map_vec (λ _, setquot) rels)) :
  setquot (hrelhvec v rels).
Proof.
  revert rels c.
  use (vec_ind (λ n v, ∏ rels0 : hvec (vec_map hrel v),
    hvec (h1map_vec (λ a : UU, setquot) rels0) →
    setquot (hrelhvec v rels0))).
  - (*This bullet is just trivialities on [[unit]]
    TODO: move in MoreFoundations*)
    intros rels c.
    cbn.
    exact unittrivialrel_setquot.
  - intros x n' v' IH rels c.
    destruct rels as [relX relsv].
    destruct c as [repX repsv].
    use dirprodtosetquot.
    split.
    + exact repX.
    + use IH.
      exact repsv.
Defined.

Definition setquottohvec {n:nat} {v : vec UU n} (rels: hvec (vec_map eqrel v))
  (c : setquot (eqrelhvec v rels))
  : hvec (h1map_vec (λ _, setquot) (pr1eqrelhvec rels)).
Proof.
  revert rels c.
  use (vec_ind (λ n v, ∏ rels : hvec (vec_map eqrel v),
    setquot (eqrelhvec v rels)
    → hvec
    (h1map_vec (λ a : UU, setquot)
    (pr1eqrelhvec rels)))).
  - intros rels c.
    exact tt.
  - intros X n' v' IH rels c.
    (* change (eqrelhvec (X ::: v') rels)
      with (eqreldirprod (hhd rels) (eqrelhvec v' (htl rels)))
      in c. *)
    destruct (setquottodirprod (hhd rels) (eqrelhvec v' (htl rels)) c) as [clsX clssv].
    use tpair.
    + exact clsX.
    + use IH.
      exact clssv.
Defined.

Theorem weqsetquottohvec {n:nat} (v : vec UU n) (rels: hvec (vec_map eqrel v)) :
  weq (setquot (eqrelhvec v rels)) (hvec (h1map_vec (λ _, setquot) (pr1eqrelhvec rels))).
Proof.
  revert rels.
  use (vec_ind (λ n v, ∏ (rels : hvec (vec_map eqrel v)),
    setquot (eqrelhvec v rels) ≃
    hvec (h1map_vec (λ a : UU, setquot) (pr1eqrelhvec rels)))).
  - intros t.
    cbn.
    use weqcontrtounit.
    use iscontr_setquotuniteqrel.
  - intros x n' v' IH rels.
    change (eqrelhvec (x ::: v') rels) with (eqreldirprod (hhd rels) (eqrelhvec v' (htl rels))).
    use (weqcomp (weqsetquottodirprod (hhd rels) (eqrelhvec v' (htl rels)))).
    simpl.
    use eqweqmap.
    use (maponpaths (λ arg, setquot (hhd rels) × arg)).
    use weqtopaths.
    use IH.
Qed.