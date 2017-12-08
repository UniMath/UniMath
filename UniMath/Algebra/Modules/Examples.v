(** Authors Langston Barrett (@siddharthist), November-December 2017 *)

Require Import UniMath.Algebra.Modules.Core.
Require Import UniMath.Algebra.Modules.Multimodules.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Foundations.Preamble.

(** ** Contents
- Morphisms
- (Multi)modules
 - Bimodules
*)

(** ** Morphisms *)
Local Open Scope rng_scope.

(** The identity function is linear *)
Definition idfun_linear {R : rng} (M : module R) : islinear (idfun M).
Proof. easy. Defined.

(** The identity function is multilinear *)
Definition idfun_multilinear {I : UU} {rngs : I -> rng} (MM : multimodule rngs) :
  @ismultilinear I rngs MM MM (idfun MM) :=
  (fun i => idfun_linear (ith_module MM i)).

(** The identity function is a morphism of modules *)
Definition id_modulefun {R : rng} (M : module R) : ismodulefun (idfun M).
Proof. easy. Defined.

(** The identity function is a multimodule morphism *)
Definition id_multimodulefun {I : UU} {rngs : I -> rng} (MM : multimodule rngs)
  : @ismultimodulefun I rngs MM MM (idfun MM) :=
  (dirprodpair (λ x y : MM, idpath _) (fun i => idfun_linear (ith_module MM i))).

(** ** (Multi)modules *)

(** The right action of a ring through a ring homomorphism
    See Bourbaki's Algebra, II §1.4, no. 1, Example 1.
 *)
Definition rngfun_right_mult {R S : rng} (f : rngfun R S) (r : R)
  : rngofendabgr S :=
  (* This is the actual definition of the function *)
  ((λ x : S, (x * (f r))),,
   (* And this is the justification that it's a monoid morphism *)
   (λ _ _, rigrdistr S _ _ _),, rigmult0x S _).

(** An important special case: the right action of a ring on itself *)
Example rng_right_mult {R : rng} : R -> rngofendabgr R :=
  rngfun_right_mult (rigisotorigfun (idrigiso R)).


(** A ring morphism R -> S defines an R-module structure on the additive abelian
    group of S *)
Definition ringfun_module {R S : rng} (f : rngfun R S) : module R.
  refine (@rngaddabgr S,, _).
  apply (@mult_to_module_struct R S (pr1 ∘ rngfun_right_mult f)%functions);
    unfold funcomp, pr1, rngfun_right_mult.
  - exact (fun r x y => rngrdistr S x y (f r)).
  - exact (fun r s x => (maponpaths _ ((pr1 (pr1 (pr2 f))) r s)) @
                        (rngldistr _ (f r) (f s) x)).
  - exact (fun r s x => (maponpaths (fun y => x * y) ((pr1 (pr2 (pr2 f))) r s)) @
                        !(rigassoc2 S x (f r) (f s))).
  - unfold mult_unel.
    exact (fun x => maponpaths (fun y => x * y) (pr2 (pr2 (pr2 f))) @
                               (@rigrunax2 S x)).
Defined.

(** An important special case: a ring is a module over itself *)
Definition ring_is_module (R : rng) : module R :=
  ringfun_module (rigisotorigfun (idrigiso R)).

(** *** Bimodules *)

Local Open Scope rng.

(** An R-S-bimodule is a left R module and a right S module, that is
    With our definitions, this means a multimodule over bool with an R-module
    structre, an S⁰-module structure, and some compatibility between them. *)
Definition bimodule (R S : rng) : UU := @multimodule _ (bool_rect _ R (S⁰)).

(** The more immediate/intuitive description of a bimodule. Below, we provide a
    way to construct a bimodule from this definition (mk_bimodule). *)
Definition bimodule_struct' (R S : rng) (G : abgr) : UU :=
  (* A bimodule structure consists of two modules structures... *)
  ∑ (mr : module_struct R G) (ms : module_struct (S⁰) G),
    (* ...and a notion of compatibility between them. *)
    let mulr := module_mult (G,, mr) in
    let muls := module_mult (G,, ms) in
    ∏ (r : R) (s : S), mulr r ∘ muls s = muls s ∘ mulr r.

Definition mk_bimodule (R S : rng) {G} (str : bimodule_struct' R S G) : bimodule R S.
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
Example commrng_bimodule (R : commrng) : bimodule R R.
  apply (@mk_bimodule R R (@rngaddabgr R)).
  unfold bimodule_struct'.
  refine (pr2module (ring_is_module R),, _).

  (** We transport the module structure across the isomorphism R ≅ R⁰ *)
  refine (pr2module
            (ringfun_module
               (rigisotorigfun (invrigiso (iso_commrng_opposite R)))),, _).

  unfold funcomp; cbn.
  intros r s.
  apply funextfun.
  intros x.
  exact (!(@rigassoc2 R x r s @ (maponpaths (fun z => x * z) (@rngcomm2 R r s))
                      @ !(rigassoc2 R x s r))).
Defined. (* TODO: this line takes a while, not sure why *)

Local Close Scope rng.