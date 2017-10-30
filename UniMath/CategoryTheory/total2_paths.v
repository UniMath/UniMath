Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.


Definition propproperty ( X : hProp ) := pr2 X .

(** * Paths in total spaces are equivalent to pairs of paths *)

(** proofs are inspired by HoTT library, http://github.com/HoTT/HoTT *)

(** these lemmas are proved in Foundations for fibrations over a type in the universe;
    here we consider fibrations over the universe [UU] itself *)




Lemma total2_paths_UU  {B : UU -> UU} {s s' : total2 (λ x, B x)}
    (p : pr1 s = pr1 s')
    (q : transportf (λ x, B x) p (pr2 s) = pr2 s') :
               s = s'.
Proof.
  induction s as [a b].
  induction s' as [a' b']; simpl in *.
  induction p.
  induction q.
  apply idpath.
Defined.



Lemma total2_paths2_UU {B : UU -> UU} {A A': UU} {b : B A}
     {b' : B A'} (p : A = A') (q : transportf (λ x, B x) p b = b') :
    tpair (λ x, B x) A b = tpair (λ x, B x) A' b'.
Proof.
  apply (@total2_paths_f _ _
     (tpair (λ x, B x) A b)(tpair (λ x, B x) A' b') p q).
Defined.


Lemma base_paths_UU {B : UU -> UU}(a b : total2 B) : a = b -> pr1 a = pr1 b.
Proof.
  apply maponpaths.
Defined.


Definition fiber_paths_UU {B : UU -> UU} {u v : total2 (λ x, B x)}
  (p : u = v) : transportf (λ x, B x) (base_paths_UU _ _ p) (pr2 u) = pr2 v.
Proof.
  induction p.
  apply idpath.
Defined.


Lemma total2_fiber_paths_UU {B : UU -> UU} {x y : total2 (λ x, B x)}
 (p : x = y) : total2_paths_UU  _ (fiber_paths_UU p) = p.
Proof.
  induction p.
  induction x.
  apply idpath.
Defined.


Lemma base_total2_paths_UU {B : UU -> UU} {x y : total2 (λ x, B x)}
  {p : pr1 x = pr1 y} (q : transportf _ p (pr2 x) = pr2 y) :
  (base_paths_UU _ _ (total2_paths_UU _ q)) = p.
Proof.
  induction x as [x H]. induction y as [y K].
  simpl in *.
  induction p.
  induction q.
  apply idpath.
Defined.


Lemma transportf_fiber_total2_paths_UU (B : UU -> UU) (x y : total2 (λ x, B x))
  (p : pr1 x = pr1 y) (q : transportf _ p (pr2 x) = pr2 y) :
  transportf (fun p' : pr1 x = pr1 y => transportf _ p' (pr2 x) = pr2 y)
  (base_total2_paths_UU q)  (fiber_paths_UU (total2_paths_UU _ q)) = q.
Proof.
  induction x as [x H].
  induction y as [y K].
  simpl in *.
  induction p.
  induction q.
  apply idpath.
Defined.



Lemma eq_equalities_between_pairs (A : UU)(B : A -> UU)(x y : total2 (λ x, B x))
    (p q : x = y) (H : base_paths _ _ p = base_paths _ _ q)
    (H2 : transportf (fun p : pr1 x = pr1 y =>  transportf _ p (pr2 x) = pr2 y )
         H (fiber_paths p) = fiber_paths q) :  p = q.
Proof.
  apply (invmaponpathsweq (total2_paths_equiv _ _ _ )).
  apply (total2_paths_f (B:=(fun p : pr1 x = pr1 y =>
          transportf (λ x : A, B x) p (pr2 x) = pr2 y))
          (s:=(total2_paths_equiv B x y) p)
          (s':=(total2_paths_equiv B x y) q) H).
  assumption.
Defined.
