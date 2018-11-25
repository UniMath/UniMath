(** * Weak equivalences *)

Require Import UniMath.Foundations.PartA.

(** ** Contents

 - Direct products

 *)

(** If x = y, then x = z if and only if y = z by transitivity. *)
Definition transitive_paths_weq {X : UU} {x y z : X} :
  x = y -> (x = z ≃ y = z).
Proof.
  intro xeqy.
  use weq_iso.
  - intro xeqz.
    exact (!xeqy @ xeqz).
  - intro yeqz.
    exact (xeqy @ yeqz).
  - intro xeqz.
    refine (path_assoc _ _ _ @ _).
    refine (maponpaths (λ p, p @ xeqz) (pathsinv0r xeqy) @ _).
    reflexivity.
  - intro yeqz.
    refine (path_assoc _ _ _ @ _).
    refine (maponpaths (λ p, p @ yeqz) (pathsinv0l xeqy) @ _).
    reflexivity.
Defined.

(** TODO: can this be derived from [weqtotal2comm12] or similar? *)
Definition weqtotal2comm {A B : UU} {C : A → B → UU} :
  (∑ (a : A) (b : B), C a b) ≃ (∑ (b : B) (a : A), C a b).
Proof.
  use weq_iso.
  - exact (λ pair, pr1 (pr2 pair),, pr1 pair,, pr2 (pr2 pair)).
  - exact (λ pair, pr1 (pr2 pair),, pr1 pair,, pr2 (pr2 pair)).
  - reflexivity.
  - reflexivity.
Defined.

(** ** Direct products *)

(** A rewrite of [pathsdirprod] as an equivalence:
    Two pairs are equal if and only if both of their components are. *)
Definition pathsdirprodweq {X Y : UU} {x1 x2 : X} {y1 y2 : Y} :
  (dirprodpair x1 y1 = dirprodpair x2 y2) ≃ (x1 = x2) × (y1 = y2).
Proof.
  intermediate_weq (dirprodpair x1 y1 ╝ dirprodpair x2 y2).
  - apply total2_paths_equiv.
  - unfold PathPair; cbn.
    use weqfibtototal; intro p; cbn.
    apply transitive_paths_weq.
    apply (toforallpaths _ _ _ (transportf_const p Y) y1).
Defined.

(** Contractible types are neutral elements for ×, up to weak equivalence. *)
Lemma dirprod_with_contr_r : ∏ X Y : UU, iscontr X -> (Y ≃ Y × X).
Proof.
  intros X Y iscontrX.
  intermediate_weq (Y × unit); [apply weqtodirprodwithunit|].
  - apply weqdirprodf.
    * apply idweq.
    * apply invweq, weqcontrtounit; assumption.
Defined.

Lemma dirprod_with_contr_l : ∏ X Y : UU, iscontr X -> (Y ≃ X × Y).
Proof.
  intros X Y iscontrX.
  intermediate_weq (Y × X).
  - apply dirprod_with_contr_r; assumption.
  - apply weqdirprodcomm.
Defined.
