Require Export UniMath.Foundations.Sets.

Lemma transportf_fun_pointwise1 {X Y : UU} (e : X = Y) (f : X -> X) (y : Y) :
  (transportf (λ X0 : UU, X0 → X0) e f) y =
  transportf (λ X0 : UU, X0) e (f (transportb (λ X0 : UU, X0) e y)).
Proof.
  induction e. use idpath.
Defined.
Opaque transportf_fun_pointwise1.

Lemma transportf_fun_pointwise2 {X Y : UU} (e : X = Y) (f : X -> X -> X) (y1 y2 : Y) :
  (transportf (λ X0 : UU, X0 → X0 -> X0) e f) y1 y2 =
  transportf (λ X0 : UU, X0) e (f (transportb (λ X0 : UU, X0) e y1)
                                  (transportb (λ X0 : UU, X0) e y2)).
Proof.
  induction e. use idpath.
Defined.
Opaque transportf_fun_pointwise2.

Lemma hfiber_paths_isaset {X Y : UU} {f : X -> Y} {y : Y} (h1 h2 : hfiber f y) (e1 : pr1 h1 = pr1 h2)
      (H : isaset Y) : h1 = h2.
Proof.
  use total2_paths_f.
  - exact e1.
  - exact (iscontrpr1
             (H (f (hfiberpr1 _ _ h2)) y (transportf (λ x : X, f x = y) e1 (hfiberpr2 _ _ h1))
                (hfiberpr2 _ _ h2))).
Defined.
Opaque hfiber_paths_isaset.

Unset Automatic Introduction.
Lemma total2_paths_f_paths {X : UU} (P : X -> UU) (s s' : total2 P) (e1 e1' : pr1 s = pr1 s')
      (e2 : transportf P e1 (pr2 s) = pr2 s') (e2' : transportf P e1' (pr2 s) = pr2 s')
      (e3 : e1 = e1')
      (e4 : e2 = maponpaths (fun ee : pr1 s = pr1 s' => transportf P ee (pr2 s)) e3 @ e2') :
  total2_paths_f e1 e2 = total2_paths_f e1' e2'.
Proof.
  intros X P s s' e1 e1' e2 e2' e3. induction e3. cbn. intros e4. induction e4. use idpath.
Defined.
Opaque total2_paths_f_paths.
Set Automatic Introduction.

Lemma total2_paths_f_components {X : UU} (P : X -> UU) (s s' : total2 P) (e : s = s') :
  e = total2_paths_f (base_paths _ _ e) (fiber_paths e).
Proof.
  induction s as [s1 s2]. induction s' as [s1' s2']. induction e. use idpath.
Defined.
Opaque total2_paths_f_paths.

Lemma transportf_total2_base_paths {X : UU} (P : X -> UU) (s s' : total2 P) (e1 : pr1 s = pr1 s')
  (e2 : transportf _ e1 (pr2 s) = pr2 s') (Q : X -> UU) (XX : Q (pr1 s)) :
  transportf (λ x : total2 P, Q (pr1 x)) (total2_paths_f e1 e2) XX =
  transportf (λ x : X, Q x) e1 XX.
Proof.
  rewrite functtransportf.
  use transportf_paths.
  exact (@base_total2_paths X P s s' e1 e2).
Defined.
Opaque transportf_total2_base_paths.

Definition hSet_paths {X Y : hSet} (e : pr1 X = pr1 Y) : X = Y.
Proof.
  use total2_paths_f.
  - exact e.
  - use proofirrelevance. use isapropisaset.
Defined.
Opaque hSet_paths.
