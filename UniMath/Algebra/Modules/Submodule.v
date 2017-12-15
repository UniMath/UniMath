(** Authors Floris van Doorn, December 2017 *)

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Algebra.Modules.Core.
Require Import UniMath.MoreFoundations.Subtypes.

(** ** Contents
- Subobjects of modules
- Kernels
- Images
*)

Definition issubsetwithsmul {R : hSet} {M : hSet} (smul : R → M → M) (A : hsubtype M) : UU :=
  ∏ r m, A m → A (smul r m).

Definition issubmodule {R : rng} {M : module R} (A : hsubtype M) : UU :=
  issubgr A × issubsetwithsmul (module_mult M) A.

Definition issubmodulepair {R : rng} {M : module R} {A : hsubtype M}
           (H1 : issubgr A) (H2 : issubsetwithsmul (module_mult M) A) : issubmodule A :=
  dirprodpair H1 H2.

Definition issubmodule_is {R : rng} {M : module R} (A : hsubtype M) : UU :=
  issubgr A × issubsetwithsmul (module_mult M) A.

Lemma isapropissubmodule {R : rng} {M : module R} (A : hsubtype M) : isaprop (issubmodule A).
Proof.
  intros. apply (isofhleveldirprod 1).
  - apply isapropissubgr.
  - apply impred. intro x.
    apply impred. intro m.
    apply impred. intro a.
    apply (pr2 (A _)).
Defined.

(* Submodules *)

Definition submodule {R : rng} (M : module R) : UU := total2 (λ A : hsubtype M, issubmodule A).

Definition submodulepair {R : rng} {M : module R} :
  ∏ (t : hsubtype M), (λ A : hsubtype M, issubmodule A) t → ∑ A : hsubtype M, issubmodule A :=
  tpair (λ A : hsubtype M, issubmodule A).

Definition submoduletosubabgr {R : rng} {M : module R} : submodule M -> @subabgr M :=
  λ A : _, subgrpair (pr1 A) (pr1 (pr2 A)).
Coercion submoduletosubabgr : submodule >-> subabgr.

Definition submodule_to_issubsetwithsmul {R : rng} {M : module R} (A : submodule M) :
  issubsetwithsmul (module_mult M) A :=
  pr2 (pr2 A).

Local Open Scope module_scope.

Definition submodule_smul {R : rng} {M : module R} {A : submodule M} (r : R) (m : A) : A.
Proof.
  use tpair.
  exact (r * pr1 m).
  exact (submodule_to_issubsetwithsmul A r (pr1 m) (pr2 m)).
Defined.

Definition carrierofasubmodule {R : rng} {M : module R} (A : submodule M) : module R.
Proof.
  use mult_to_module.
  - exact (carrierofasubabgr A).
  - exact (submodule_smul).
  - intros r a b. apply (invmaponpathsincl _ (isinclpr1carrier A)). apply module_mult_is_ldistr.
  - intros r s a. apply (invmaponpathsincl _ (isinclpr1carrier A)). apply module_mult_is_rdistr.
  - intros r s a. apply (invmaponpathsincl _ (isinclpr1carrier A)). apply module_mult_assoc.
  - intros f. apply (invmaponpathsincl _ (isinclpr1carrier A)). apply module_mult_unel2.
Defined.

Coercion carrierofasubmodule : submodule >-> module.
Lemma intersection_submodule {R : rng} {M : module R} {I : UU} (S : I -> hsubtype M)
      (each_is_submodule : ∏ i : I, issubmodule (S i)) :
  issubmodule (subtype_intersection S).
Proof.
  intros.
  use issubmodulepair.
  - exact (intersection_subgr S (λ i, (pr1 (each_is_submodule i)))).
  - intros r m a i. exact (pr2 (each_is_submodule i) r m (a i)).
Qed.

Lemma ismodulefun_pr1 {R : rng} {M : module R} (A : submodule M) : @ismodulefun R A M pr1.
Proof.
  use ismodulefunpair.
  exact (pr1 (ismonoidfun_pr1 A)).
  easy.
Defined.

Definition submodule_incl {R : rng} {M : module R} (A : submodule M) : modulefun A M :=
  modulefunpair _ (ismodulefun_pr1 A).


(* Kernel and image *)
Lemma issubmodule_kernel {R : rng} {A B : module R} (f : modulefun A B) :
  issubmodule (abgr_kernel_hsubtype (modulefun_to_monoidfun f)).
Proof.
  split.
  apply abgr_Kernel_subabgr_issubgr.
  intros r x. apply hinhfun. cbn. intro p.
  now rewrite (modulefun_to_islinear f), p, module_mult_1.
Defined.

Definition module_kernel {R : rng} {A B : module R} (f : modulefun A B) : submodule A :=
  submodulepair _ (issubmodule_kernel f).

Lemma module_kernel_eq {R : rng} {A B : module R} (f : modulefun A B) x :
  f (submodule_incl (module_kernel f) x) = unel B.
Proof.
  unshelve refine (@hinhuniv _ (tpair _ _ _) _ (pr2 x)).
  - apply isasetmodule.
  - apply idfun.
Defined.

Lemma issubmodule_image {R : rng} {A B : module R} (f : modulefun A B) :
  issubmodule (abgr_image_hsubtype (modulefun_to_monoidfun f)).
Proof.
  split.
  apply abgr_image_issubgr.
  intros r x. apply hinhfun. cbn. intro ap. induction ap as [a p].
  split with (r * a). now rewrite (modulefun_to_islinear f), <- p.
Defined.

Definition module_image {R : rng} {A B : module R} (f : modulefun A B) : submodule B :=
  submodulepair _ (issubmodule_image f).
