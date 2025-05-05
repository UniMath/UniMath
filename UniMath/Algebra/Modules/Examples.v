(**

  Examples of Ring Modules

  This file lists some examples of ring modules, like the identity multimodule morphism, the
  R-module structure on a ring S from a morphism R → S (the identity on R gives the R-module
  structure on R). It also gives the zero module, and the definition of R-S bimodules (a module with
  a left R-action and a right S-action) via multimodules.

  Contents
  1. The identity multimodule morphism
  2. Constructing a module from a ring morphism
  3. The zero module
  4. Bimodules

  Originally written by Langston Barrett (@siddharthist), November-December 2017

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.ModuleCore.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Modules.Core.
Require Import UniMath.Algebra.Modules.Multimodules.
Require Import UniMath.Algebra.RigsAndRings.

Local Open Scope ring_scope.

(** * 1. The identity multimodule morphism *)

(** The identity function is multilinear *)
Lemma idfun_multilinear {I : UU} {rings : I -> ring} (MM : multimodule rings) :
  ismultilinear (rings := rings) (idfun MM).
Proof.
  easy.
Qed.

(** The identity function is a multimodule morphism *)
Lemma id_multimodulefun {I : UU} {rings : I -> ring} (MM : multimodule rings)
  : ismultimodulefun (rings := rings) (idfun MM).
Proof.
  easy.
Qed.

(** * 2. Constructing a module from a ring morphism *)

(** The left action of a ring through a ring homomorphism
    See Bourbaki's Algebra, II §1.4, no. 1, Example 1.
 *)
Definition ringfun_left_mult {R S : ring} (f : ringfun R S) (r : R)
  : group_endomorphism_ring S.
Proof.
  use make_abelian_group_morphism.
  - intro x.
    exact (f r * x).
  - do 2 intro.
    apply (rigldistr S _ _ _).
Defined.

(** An important special case: the left action of a ring on itself *)
Example ring_left_mult {R : ring} : R → group_endomorphism_ring R :=
  ringfun_left_mult (rigisotorigfun (idrigiso R)).


(** A ring morphism R -> S defines an R-module structure on the additive abelian
    group of S *)
Definition ringfun_module {R S : ring} (f : ringfun R S) : module R.
  apply (make_module (@ringaddabgr S)).
  apply (@mult_to_module_struct R S (λ x, (ringfun_left_mult f x : abelian_group_morphism _ _)));
    unfold funcomp, pr1, ringfun_left_mult.
  - intros r x y.
    apply ringldistr.
  - intros r s x.
    refine (_ @ ringrdistr _ _ _ _).
    apply (maponpaths (λ x, x * _)).
    apply (binopfunisbinopfun (ringaddfun f)).
  - intros r s x.
    refine (_ @ rigassoc2 S _ _ _).
    apply (maponpaths (λ x, x * _)).
    apply (binopfunisbinopfun (ringmultfun f)).
  - intro x.
    refine (_ @ riglunax2 S _).
    apply (maponpaths (λ x, x * _)).
    apply (monoidfununel (ringmultfun f)).
Defined.

(** An important special case: a ring is a module over itself *)
Definition ring_is_module (R : ring) : module R :=
  ringfun_module (rigisotorigfun (idrigiso R)).

(** * 3. The zero module *)
Definition zero_module (R : ring) : module R.
Proof.
  refine (unitabgr,, _).
  apply (@mult_to_module_struct _ _ (λ _ u, u));
    easy.
Defined.

(** 4. Bimodules *)

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

  simpl.
  intros r s.
  apply funextfun.
  intros x.
  exact (!@rigassoc2 R r s x @ (maponpaths (fun z => z * x) (@ringcomm2 R r s))
                      @ (rigassoc2 R s r x)).
Defined.

Local Close Scope ring.
