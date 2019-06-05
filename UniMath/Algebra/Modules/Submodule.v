(** Authors Floris van Doorn, December 2017 *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Modules.Core.

(** ** Contents
- Subobjects of modules
- Kernels
- Images
*)

Definition issubsetwithsmul {R : hSet} {M : hSet} (smul : R → M → M) (A : hsubtype M) : UU :=
  ∏ r m, A m → A (smul r m).

Definition issubmodule {R : ring} {M : module R} (A : hsubtype M) : UU :=
  issubgr A × issubsetwithsmul (module_mult M) A.

Definition make_issubmodule {R : ring} {M : module R} {A : hsubtype M}
           (H1 : issubgr A) (H2 : issubsetwithsmul (module_mult M) A) : issubmodule A :=
  make_dirprod H1 H2.

Definition issubmodule_is {R : ring} {M : module R} (A : hsubtype M) : UU :=
  issubgr A × issubsetwithsmul (module_mult M) A.

Lemma isapropissubmodule {R : ring} {M : module R} (A : hsubtype M) : isaprop (issubmodule A).
Proof.
  intros. apply (isofhleveldirprod 1).
  - apply isapropissubgr.
  - apply impred. intro x.
    apply impred. intro m.
    apply impred. intro a.
    apply (pr2 (A _)).
Defined.

(* Submodules *)

Definition submodule {R : ring} (M : module R) : UU := total2 (λ A : hsubtype M, issubmodule A).

Definition make_submodule {R : ring} {M : module R} :
  ∏ (t : hsubtype M), (λ A : hsubtype M, issubmodule A) t → ∑ A : hsubtype M, issubmodule A :=
  tpair (λ A : hsubtype M, issubmodule A).

Definition submoduletosubabgr {R : ring} {M : module R} : submodule M -> @subabgr M :=
  λ A : _, make_subgr (pr1 A) (pr1 (pr2 A)).
Coercion submoduletosubabgr : submodule >-> subabgr.

Definition submodule_to_issubsetwithsmul {R : ring} {M : module R} (A : submodule M) :
  issubsetwithsmul (module_mult M) A :=
  pr2 (pr2 A).

Local Open Scope module_scope.

Definition submodule_smul {R : ring} {M : module R} {A : submodule M} (r : R) (m : A) : A.
Proof.
  use tpair.
  - exact (r * pr1 m).
  - exact (submodule_to_issubsetwithsmul A r (pr1 m) (pr2 m)).
Defined.

Definition carrierofasubmodule {R : ring} {M : module R} (A : submodule M) : module R.
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
Lemma intersection_submodule {R : ring} {M : module R} {I : UU} (S : I -> hsubtype M)
      (each_is_submodule : ∏ i : I, issubmodule (S i)) :
  issubmodule (subtype_intersection S).
Proof.
  intros.
  use make_issubmodule.
  - exact (intersection_subgr S (λ i, (pr1 (each_is_submodule i)))).
  - intros r m a i. exact (pr2 (each_is_submodule i) r m (a i)).
Qed.

Lemma ismodulefun_pr1 {R : ring} {M : module R} (A : submodule M) : @ismodulefun R A M pr1.
Proof.
  use make_ismodulefun.
  exact (pr1 (ismonoidfun_pr1 A)).
  intros r a. reflexivity.
Defined.

Definition submodule_incl {R : ring} {M : module R} (A : submodule M) : modulefun A M :=
  make_modulefun _ (ismodulefun_pr1 A).


(* Kernel and image *)
Lemma issubmodule_kernel {R : ring} {A B : module R} (f : modulefun A B) :
  issubmodule (abgr_kernel_hsubtype (modulefun_to_monoidfun f)).
Proof.
  split.
  - apply abgr_Kernel_subabgr_issubgr.
  - intros r x p.
    cbn.
    rewrite (modulefun_to_islinear f).
    rewrite <- (module_mult_1 r), <- p.
    reflexivity.
Defined.

Definition module_kernel {R : ring} {A B : module R} (f : modulefun A B) : submodule A :=
  make_submodule _ (issubmodule_kernel f).

Definition module_kernel_eq {R : ring} {A B : module R} (f : modulefun A B) x :
  f (submodule_incl (module_kernel f) x) = unel B := (pr2 x).

Lemma issubmodule_image {R : ring} {A B : module R} (f : modulefun A B) :
  issubmodule (abgr_image_hsubtype (modulefun_to_monoidfun f)).
Proof.
  split.
  - apply abgr_image_issubgr.
  - intros r x. apply hinhfun. cbn. intro ap. induction ap as [a p].
    split with (r * a). now rewrite (modulefun_to_islinear f), <- p.
Defined.

Definition module_image {R : ring} {A B : module R} (f : modulefun A B) : submodule B :=
  make_submodule _ (issubmodule_image f).

Section submodule_helpers.

  Context {R : ring}
          {M : module R}
          (A : submodule M).

  Local Notation "x + y" := (@op _ x y).
  Local Notation "x - y" := (@op _ x (grinv _ y)).

  Definition submoduleadd (x y : M) : A x -> A y -> A (x + y).
  Proof.
    intros ax ay.
    exact (pr1 (pr1 (pr1 (pr2 A))) (make_carrier A x ax) (make_carrier A y ay)).
  Defined.

  Definition submodule0 : A (unel M) := pr2 (pr1 (pr1 (pr2 A))).

  Definition submoduleinv (x : M) : A x -> A (grinv _ x) := λ ax, (pr2 (pr1 (pr2 A)) x ax).

  Local Open Scope module.

  Definition submodulemult (r : R) (m : M) : A m -> A (r * m) := (pr2 (pr2 A) r m).

End submodule_helpers.
