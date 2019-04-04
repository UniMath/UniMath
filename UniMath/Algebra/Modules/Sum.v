(** Author Emil Skoldberg, April 2019 *)


Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Modules.Core.

Definition sumbinop_smul {R : ring} {M N : module R} (r : R) (p : M × N) :
  M × N.
Proof.
  induction p as (m, n).
  exact ((module_mult _ r m),, (module_mult _ r n)).
Defined.

Local Open Scope module.
Local Open Scope multmonoid.

Definition summodule {R : ring} (M N : module R) : module R.
Proof.
  use modulepair.
  - use abgrdirprod.
    + exact M.
    + exact N.
  - use mult_to_module_struct.
    + cbn.
      apply sumbinop_smul.
    + unfold mult_isldistr_wrt_grop.
      intros r p q.
      apply total2_paths2.
      cbn.
      * induction p as (m1, n1).
        induction q as (m2, n2).
        cbn.
        apply module_mult_is_ldistr.
      * induction p as (m1, n1).
        induction q as (m2, n2).
        cbn.
        apply module_mult_is_ldistr.
    + unfold mult_isrdistr_wrt_ringop1.
      intros r s p.
      apply total2_paths2.
      cbn.
      * induction p as (m, n).
        cbn.
        apply (module_mult_is_rdistr r s m).
      * induction p as (m, n).
        cbn.
        apply (module_mult_is_rdistr r s n).
    + unfold mult_isrdistr_wrt_ringop2.
      intros r s p.
      apply total2_paths2.
      cbn.
      * induction p as (m, n).
        cbn.
        apply (module_mult_assoc r s m).
      * induction p as (m, n).
        cbn.
        apply (module_mult_assoc r s n).
    + unfold mult_unel.
      intros p.
      apply total2_paths2.
      cbn.
      * induction p as (m, n).
        cbn.
        apply (module_mult_unel2 m).
      * induction p as (m, n).
        cbn.
        apply (module_mult_unel2 n).
Defined.

Definition inj1 {R : commring} (M N : module R) : modulefun M (summodule M N).
Proof.
  use tpair.
  - intros x.
    exact (x,, (unel N)).
  - cbn.
    split.
    + red.
      intros x y.
      apply total2_paths2.
      * cbn.
        apply idpath.
      * cbn.
        apply pathsinv0.
        apply (lunax _ (unel N)).
    + red.
      intros r x.
      apply total2_paths2.
      * apply idpath.
      * apply pathsinv0.
        apply module_mult_1.
Defined.

Definition inj2 {R : commring} (M N : module R) : modulefun N (summodule M N).
Proof.
  use tpair.
  - intros y.
    exact ((unel M),, y).
  - cbn.
    split.
    + red.
      intros x y.
      apply total2_paths2.
      * cbn.
        apply pathsinv0.
        apply (lunax _ (unel M)).
      * cbn.
        apply idpath.
    + red.
      intros r x.
      apply total2_paths2.
      * apply pathsinv0.
        apply module_mult_1.
      * apply idpath.
Defined.

Definition sum_universal {R : commring} (M1 M2 N : module R) (f1 : modulefun M1 N) (f2 : modulefun M2 N) : modulefun (summodule M1 M2) N.
Proof.
  use tpair.
  - intros p.
    induction p as (m1, m2).
    exact (((pr1 f1) m1) * ((pr1 f2) m2)) .
  - red.
    split.
    + red.
      intros p q.
      induction p as (m1, m2).
      induction q as (n1, n2).
      cbn.
      etrans.
      * apply maponpaths.
        apply (binopfunisbinopfun (modulefun_to_binopfun f2)).
      * cbn.
        etrans.
        { apply maponpaths_2.
           apply (binopfunisbinopfun (modulefun_to_binopfun f1)). }
        cbn.
        etrans.
        { apply (assocax N). }
        apply pathsinv0.
        etrans.
        { apply (assocax N). }
        apply maponpaths.
        apply pathsinv0.
        etrans.
        { apply pathsinv0.
        apply (assocax N). }
        apply pathsinv0.
        etrans.
        { apply pathsinv0.
          apply (assocax N). }
        apply maponpaths_2.
        etrans.
        { apply (commax N). }
        apply maponpaths.
        apply maponpaths.
        apply idpath.
    + red.
      intros r x.
      etrans.
      { apply maponpaths.
        apply (modulefun_to_islinear f2). }
      etrans.
      { apply maponpaths_2.
        apply (modulefun_to_islinear f1). }
      apply pathsinv0.
      etrans.
      { apply module_mult_is_ldistr. }
      apply idpath.
Defined.


Definition proj1 {R : commring} (M N : module R) : modulefun (summodule M N) M.
Proof.
  use tpair.
  - exact pr1.
  - red.
    split.
    + red.
      intros p q.
      induction p as (m1, n1).
      induction q as (m2, n2).
      cbn.
      apply idpath.
    + red.
      intros r p.
      cbn.
      apply idpath.
Defined.

Definition proj2 {R : commring} (M N : module R) : modulefun (summodule M N) N.
Proof.
  use tpair.
  - exact pr2.
  - red.
    split.
    + red.
      intros p q.
      cbn.
      apply idpath.
    + red.
      intros r p.
      cbn.
      apply idpath.
Defined.

Definition prod_universal {R : commring} (M1 M2 N : module R) (f1 : modulefun N M1) (f2 : modulefun N M2) : modulefun N (summodule M1 M2).
Proof.
  use tpair.
  - intros x.
    exact ((pr1 f1) x,, (pr1 f2) x).
  - red.
    split.
    + red.
      intros x y.
      etrans.
      { apply maponpaths.
        apply (binopfunisbinopfun (modulefun_to_binopfun f2)). }
      etrans.
      { apply maponpaths_2.
        apply (binopfunisbinopfun (modulefun_to_binopfun f1)). }
      cbn.
      apply idpath.
    + red.
      intros r x.
      etrans.
      { apply maponpaths.
        apply (modulefun_to_islinear f2). }
      etrans.
      { apply maponpaths_2.
        apply (modulefun_to_islinear f1). }
      apply idpath.
Defined.

Definition zeromodule {R : commring} : module R.
Proof.
  use modulepair.
  - exact unitabgr.
  - use (@mult_to_module_struct _ _ (λ _ u, u)); red; intros; reflexivity.
Defined.

(* M ⊕ 0 ≃ M *)

Definition zerosum {R : commring} (M : module R) : moduleiso (summodule M zeromodule) M.
Proof.
  use mk_moduleiso.
  2: cbn.
  Search "iso" "weq" weq.
  - use weq_iso.
    + exact (proj1 M zeromodule).
    + exact (inj1 M zeromodule).
    + intros.
      destruct x.
      cbn.
      use maponpaths.
      apply isapropunit.
    + intros.
      cbn.
      apply idpath.
  - cbn.
    easy.
Defined.

Definition dirsumcommutes {R : commring} (M N : module R) : moduleiso (summodule M N) (summodule N M).
Proof.
  use mk_moduleiso.
  2: cbn.
  - use weq_iso.
    + intros p.
      destruct p.
      exact (pr2,, pr1).
    + intros p.
      destruct p.
      exact (pr2,, pr1).
    + cbn.
      intros p.
      destruct p.
      apply idpath.
    + cbn.
      intros p.
      destruct p.
      apply idpath.
  - easy.
Defined.

Definition dirsumassoc {R : commring} (L M N : module R) : moduleiso (summodule (summodule L M) N) (summodule L (summodule M N)).
Proof.
  use mk_moduleiso.
  2: cbn.
  - use weq_iso.
    + intros q.
      destruct q as [p z].
      destruct p as [x y].
      exact (x,,(y,,z)).
    + intros p.
      destruct p as [x q].
      destruct q as [y z].
      exact ((x,, y),, z).
    + cbn.
      intros p.
      destruct p.
      destruct pr1.
      apply idpath.
    + easy.
  - easy.
Defined.
