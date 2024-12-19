
* Introducing and eliminating paths, maybe? Like path induction, path inversion and composition, `total2_paths_f`, `base_paths`, `fiber_paths`, `maponpaths`, `split`


We have already seen the `reflexivity` tactic, which uses the fact that paths are 'reflexive' (because the existence of `idpath`). There is also the `symmetry` tactic, which turns a goal `x = y` into the goal `y = x`. Lastly, there is the `transitivity a` tactic, which splits a goal `x = y` into `x = a` and `a = y`:
```coq
Lemma path_inv_transitivity
  (X : UU)
  (x y z : X)
  (p : x = y)
  (q : y = z)
  : z = x.
Proof.
  symmetry.       (* This turns the goal into x = z *)
  transitivity y. (* This splits the goal into x = y and y = z *)
  - exact p.
  - exact q.
Qed.
```
If you do not yet want to provide `a`, you can use `etrans` instead.
