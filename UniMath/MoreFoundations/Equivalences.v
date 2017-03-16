Require Export UniMath.Foundations.PartD.

Lemma weqtopaths_idweq (X : UU) : @weqtopaths X X (idweq X) = idpath X.
Proof.
  use (invmaponpathsweq (weqpair _ (@univalenceAxiom X X)) (@weqtopaths X X (idweq X)) (idpath X)).
  use weqpathsweq.
Defined.
Opaque weqtopaths_idweq.

Lemma weqtopaths_invweq {X Y : UU} (w : X ≃ Y) : @weqtopaths Y X (invweq w) = ! (@weqtopaths X Y w).
Proof.
  use (invmaponpathsweq (weqpair _ (@univalenceAxiom Y X)) (@weqtopaths Y X (invweq w))).
  use (pathscomp0 (@weqpathsweq _ _ _)).
  use pathsinv0.
  use (pathscomp0 (@eqweqmap_pathsinv0 X Y (weqtopaths w))).
  use maponpaths.
  exact (homotweqinvweq (univalenceUAH univalenceAxiom X Y) w).
Defined.
Opaque weqtopaths_invweq.

Lemma transportf_weqtopaths' {X Y : UU} (e : X = Y) (x : X) :
  transportf (λ X0, X0) (@weqtopaths X Y (eqweqmap e)) x = pr1weq (eqweqmap e) x.
Proof.
  induction e.
  exact (toforallpaths
           _ _ _ (maponpaths (λ ee, transportf (λ X0 : UU, X0) ee) (weqtopaths_idweq X)) x).
Defined.
Opaque transportf_weqtopaths'.

Lemma transportf_weqtopaths {X Y : UU} (w : X ≃ Y) (x : X) :
  transportf (λ X0, X0) (@weqtopaths X Y w) x = pr1weq w x.
Proof.
  use (pathscomp0 (maponpaths (λ w', transportf (λ X0 : UU, X0) (@weqtopaths X Y w') x)
                              (! homotweqinvweq (weqpair _ (@univalenceAxiom X Y)) w))).
  use (pathscomp0 (transportf_weqtopaths' _ x)).
  exact (maponpaths (λ w' : X ≃ Y, w' x) (homotweqinvweq (weqpair _ (@univalenceAxiom X Y)) w)).
Defined.
Opaque transportf_weqtopaths.

(** Useful for rewrite *)
Lemma transportf_invmap_eqweqmap {X Y : UU} (w : X ≃ Y) (x : X) :
  transportf (λ X0 : UU, X0) (invmap (weqpair eqweqmap (univalenceAxiom X Y)) w) x = (pr1weq w) x.
Proof.
  exact (@transportf_weqtopaths X Y w x).
Defined.
Opaque transportf_invmap_eqweqmap.
