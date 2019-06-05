(** Authors Langston Barrett (@siddharthist), November-December 2017 *)

Require Import UniMath.Algebra.Modules.Core.
Require Import UniMath.Algebra.Modules.Multimodules.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.MoreFoundations.Tactics.

(** ** Contents
- Morphisms
- (Multi)modules
 - Bimodules
*)

(** ** Morphisms *)
Local Open Scope ring_scope.

(** The identity function is linear *)
Definition idfun_linear {R : ring} (M : module R) : islinear (idfun M).
Proof. easy. Defined.

(** The identity function is multilinear *)
Definition idfun_multilinear {I : UU} {rings : I -> ring} (MM : multimodule rings) :
  @ismultilinear I rings MM MM (idfun MM) :=
  (fun i => idfun_linear (ith_module MM i)).

(** The identity function is a morphism of modules *)
Definition id_modulefun {R : ring} (M : module R) : ismodulefun (idfun M).
Proof. easy. Defined.

(** The identity function is a morphism of modules *)
Definition idmoduleiso {R : ring} (M : module R) : moduleiso M M.
Proof.
   use make_moduleiso.
   - exact (idweq (pr1module M)).
   - apply make_dirprod.
     + intros x y. apply idpath.
     + intros r x. apply idpath.
Defined.

(** The identity function is a multimodule morphism *)
Definition id_multimodulefun {I : UU} {rings : I -> ring} (MM : multimodule rings)
  : @ismultimodulefun I rings MM MM (idfun MM) :=
  (make_dirprod (λ x y : MM, idpath _) (fun i => idfun_linear (ith_module MM i))).

(** ** (Multi)modules *)

(** The left action of a ring through a ring homomorphism
    See Bourbaki's Algebra, II §1.4, no. 1, Example 1.
 *)
Definition ringfun_left_mult {R S : ring} (f : ringfun R S) (r : R)
: ringofendabgr S.
Proof.
  refine
  (* This is the actual definition of the function *)
  ((λ x : S, (f r * x)),,
   (* And this is the justification that it's a monoid morphism *)
                       (λ _ _, _),, _).
  apply (rigldistr S _ _ _). apply (rigmultx0 S).
Defined.

(** An important special case: the left action of a ring on itself *)
Example ring_left_mult {R : ring} : R -> ringofendabgr R :=
  ringfun_left_mult (rigisotorigfun (idrigiso R)).


(** A ring morphism R -> S defines an R-module structure on the additive abelian
    group of S *)
Definition ringfun_module {R S : ring} (f : ringfun R S) : module R.
  refine (@ringaddabgr S,, _).
  apply (@mult_to_module_struct R S (pr1 ∘ ringfun_left_mult f)%functions);
    unfold funcomp, pr1, ringfun_left_mult.
  - exact (fun r x y => ringldistr S x y (f r)).
  - exact (fun r s x => (maponpaths (λ x, x * _) ((pr1 (pr1 (pr2 f))) r s)) @
                        (ringrdistr _ (f r) (f s) x)).
  - exact (fun r s x => ((maponpaths (fun y => y * x) ((pr1 (pr2 (pr2 f))) r s) @
                         (rigassoc2 S (f r) (f s) x)))).
  - exact (fun x => maponpaths (fun y => y * x) (pr2 (pr2 (pr2 f))) @
                               (@riglunax2 S x)).
Defined.

(** An important special case: a ring is a module over itself *)
Definition ring_is_module (R : ring) : module R :=
  ringfun_module (rigisotorigfun (idrigiso R)).

(** The zero module is the unique R-module structure on the zero group (the
    group with a single element) *)
Definition zero_module (R : ring) : module R.
Proof.
  refine (unitabgr,, _).
  apply (@mult_to_module_struct _ _ (λ _ u, u));
    easy.
Defined.

(** *** Bimodules *)

Local Open Scope ring.

(** An R-S-bimodule is a left R module and a right S module, that is
    With our definitions, this means a multimodule over bool with an R-module
    structre, an S⁰-module structure, and some compatibility between them. *)
Definition bimodule (R S : ring) : UU := @multimodule _ (bool_rect _ R (S⁰)).

(** The more immediate/intuitive description of a bimodule. Below, we provide a
    way to construct a bimodule from this definition (make_bimodule). *)
Definition bimodule_struct' (R S : ring) (G : abgr) : UU :=
  (* A bimodule structure consists of two modules structures... *)
  ∑ (mr : module_struct R G) (ms : module_struct (S⁰) G),
    (* ...and a notion of compatibility between them. *)
    let mulr := module_mult (G,, mr) in
    let muls := module_mult (G,, ms) in
    ∏ (r : R) (s : S), mulr r ∘ muls s = muls s ∘ mulr r.

Definition make_bimodule (R S : ring) {G} (str : bimodule_struct' R S G) : bimodule R S.
  refine (G,, _).

  (** Index the module structs over bool *)
  refine (bool_rect _ (pr1 str) (pr1 (pr2 str)),, _).

  unfold multimodule_struct.
  (** the [ | ] pattern yields cases with hypotheses false ≠ false and
      true ≠ true, so we use them as contradictions or clear the useless
      hypothesis *)
  intros [ | ] [ | ] neq r s;
    try (contradiction (neq (idpath _))); clear neq; cbn in *.

  - exact ((pr2 (pr2 str)) r s).
  - exact (!((pr2 (pr2 str)) s r)).
Defined.

(** A commutative ring is a bimodule over itself *)
Example commring_bimodule (R : commring) : bimodule R R.
  apply (@make_bimodule R R (@ringaddabgr R)).
  unfold bimodule_struct'.
  refine (pr2module (ring_is_module R),, _).

  (** We transport the module structure across the isomorphism R ≅ R⁰ *)
  refine (pr2module
            (ringfun_module
               (rigisotorigfun (invrigiso (iso_commring_opposite R)))),, _).

  unfold funcomp; cbn.
  intros r s.
  apply funextfun.
  intros x.
  exact (!@rigassoc2 R r s x @ (maponpaths (fun z => z * x) (@ringcomm2 R r s))
                      @ (rigassoc2 R s r x)).
Defined. (* TODO: this line takes a while, not sure why *)

Local Close Scope ring.
