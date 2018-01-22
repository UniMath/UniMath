(** * Triangulated categories *)
(** ** Contents
- Triangles, rotations of triangles, and cones
- Pretriangulated data
- Distinguished triangles (DTri) and extensions
- Pretriangulated categories
- Triangulated categories
- Rotations of morphisms and extensions
- Composition of consecutive morphisms in DTri is 0
- Exact sequences associated to a distinguished triangle
- Five lemma for distinguished triangles
- Change of triangles in octahedral axiom
*)

Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.ShortExactSequences.
Require Import UniMath.CategoryTheory.categories.abgrs.

Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Morphisms.
Require Import UniMath.CategoryTheory.AdditiveFunctors.
Require Import UniMath.CategoryTheory.FiveLemma.

Unset Kernel Term Sharing.

(** * Triangulated categories *)
(** ** Introduction
A triangulated category Tr consists of an additive category A together with the following data
- An additive equivalence T : A -> A, called a translation functor.
- A collection of triangles in A, that is, a collection of diagrams of the form
                           X -f-> Y -g-> Z -h-> X[1]
  which are called distinguished triangles. Such a diagram is denoted by (X, Y, Z, f, g, h).
and these data must satisfy the following conditions
(TR1) For all objects X of A the triangle (X, X, 0, Id_X, 0, 0) is distinguished.
(TR2) Any triangle isomorphic to a distinguished triangle is a distinguished triangle.
(TR3) A triangle (X, Y, Z, f, g, h) is distinguished if and only if the rotated triangle
      (Y, Z, T X, g, h, - T f) is distinguished.
(TR4) For any morphism f : X --> Y one has a triangle (X, Y, Z, f, g, h) for some object Z and
      morphisms g and h. The object Z is called the cone of f.
(TR5) Suppose you have two distinguished triangle (X, Y, Z, f, g, h) and (X', Y', Z', f', g', h')
      and morphisms φ1 : X --> X' and φ2 : Y --> Y' such that the following diagram is commutative
                                X  -f-> Y  -g-> Z  -h-> X[1]
                             φ1 |    φ2 |
                                X' -f-> Y' -g-> Z' -h-> X'[1]
      Then there exists a morphism φ3 : Z --> Z' such that the following diagram is commutative
                                X  -f-> Y  -g-> Z   -h->  X[1]
                             φ1 |    φ2 |   φ3 |     φ1[1] |
                                X' -f-> Y' -g-> Z' -h'-> X'[1].
      Such a commutative diagram is called a morphism of triangles.
(TR6) (Octahedral axiom). Suppose you have 3 distinguished triangles (X1, Y1, Z2, f, g, h),
      (Y1, Z1, X2, f', g', h'), and (X1, Z1, Y2, f · f', g'', h''). Then there exists a
      distinguished triangle (Z2, Y2, X2, f''', g''', h'' · g[1]) such that the following diagram
      is commutative

                              X1 ----f----> Y1 ----g----> Z2 ----h----> X1[1]
                              ||            |             |              ||
                              ||         f' |        f''' |              ||
                              ||            |             |              ||
                              X1  -f·f'->  Z1  --g''-->  Y2 ----h''---> X1[1]
                                            |             |              |
                                         g' |        g''' |         f[1] |
                                            |             |              |
                                            X2  ========  X2 ----h'----> Y1[1]
                                            |             |
                                         h' |    h'·g[1] |
                                            |             |
                                         Y1[1] --g[1]-> Z2[1]

     This version of octahedral axiom corresponds to Axiom D of
     http://math-www.uni-paderborn.de/user/hubery/static/Octahedral.pdf


We call the data for triangulated category which satisfies (TR1)-(TR5) a pretriangulated category.
 *)

Local Opaque ishinh.

(** * Basic notions *)
(** ** Introduction
In this section we define

- Triangles. Diagrams of the form
                                X  -f-> Y  -g-> Z  -h-> X[1]

- Morphisms of triangles. Commutative diagrams of the form
                                X  -f-> Y  -g-> Z  -h->  X[1]
                             φ1 |    φ2 |   φ3 |    φ1[1] |
                                X' -f-> Y' -g-> Z' -h-> X'[1].

- Rotations of triangles. Rotation of
                                X  -f-> Y  -g-> Z  -h-> X[1]
  is the triangle
                                Y  -g-> Z  -h-> X[1] -(-f[1])-> Y[1]

- Inverse rotation of triangle. Inverse rotation of
                                X  -f-> Y  -g-> Z  -h-> X[1]
  is the triangle
                                Z[-1] -(-h[-1])-> X -f-> Y -g-> Z

- Rotations of morphisms. Let
                                X  -f-> Y  -g-> Z   -h->  X[1]
                             φ1 |    φ2 |   φ3 |     φ1[1] |
                                X' -f-> Y' -g-> Z' -h'-> X'[1].
  be a morphism of triangles. Then
                                Y  -g-> Z  -h->  X[1] -f[1]->  Y[1]
                             φ2 |   φ3 |    φ1[1] |       φ2[1] |
                                Y' -g-> Z' -h-> X'[1] -f[1]-> Y'[1].
  is the rotation of the morphism. Similarly for inverse rotations of morphisms.

- ConeData to triangles. A ConeData for a morphism f : x --> y consists of
  - An object z
  - A morphism y --> z
  - A morphism z --> x[1]

*)
Section def_triangles.

  Context {A : Additive}.
  Context {T : AddEquiv A A}.


  (** ** Triangles *)

  Definition Tri : UU := ∑ MP : MorphismPair, A⟦Ob3 MP, (AddEquiv1 T) (Ob1 MP)⟧.

  Definition mk_Tri {x y z : ob A} (f : x --> y) (g : y --> z) (h : A⟦z, (AddEquiv1 T x)⟧) : Tri :=
    (mk_MorphismPair f g),,h.

  Definition TriMP (D : Tri) : MorphismPair := pr1 D.
  Coercion TriMP : Tri >-> MorphismPair.

  (** Follows the naming convention Mor1, Mor2, for MorphismPair *)
  Definition Mor3 (D : Tri) : A⟦Ob3 D, (AddEquiv1 T) (Ob1 D)⟧ := pr2 D.


  (** ** Morphisms of triangles *)

  Definition TriMor (D1 D2 : Tri) : UU :=
    ∑ (M : MPMor D1 D2), (MPMor3 M) · (Mor3 D2) = (Mor3 D1) · (# (AddEquiv1 T) (MPMor1 M)).

  Definition mk_TriMor {D1 D2 : Tri} (M : MPMor D1 D2)
             (H : (MPMor3 M) · (Mor3 D2) = (Mor3 D1) · (# (AddEquiv1 T) (MPMor1 M))) :
    TriMor D1 D2 := (M,,H).

  Definition TriMor_Mors {D1 D2 : Tri} (DTM : TriMor D1 D2) : MPMor D1 D2 := pr1 DTM.
  Coercion TriMor_Mors : TriMor >-> MPMor.

  Local Lemma TriMorId_comms {x y : ob A} (f : x --> y) : identity x · f = f · identity y.
  Proof.
    rewrite id_left. rewrite id_right. apply idpath.
  Qed.

  Local Lemma TriMorId_comm3 (D : Tri) :
    identity (Ob3 D) · Mor3 D = Mor3 D · # (AddEquiv1 T) (identity (Ob1 D)).
  Proof.
    rewrite functor_id. rewrite id_left. rewrite id_right. apply idpath.
  Qed.

  Definition TriMorId (D : Tri) : TriMor D D.
  Proof.
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (identity _).
        * exact (identity _).
        * exact (identity _).
      + use mk_MPMorComms.
        * exact (TriMorId_comms _).
        * exact (TriMorId_comms _).
    - exact (TriMorId_comm3 D).
  Defined.

  Definition DComm3 {D1 D2 : Tri} (TM : TriMor D1 D2) :
    (MPMor3 TM) · (Mor3 D2) = (Mor3 D1) · (# (AddEquiv1 T) (MPMor1 TM)) := pr2 TM.

  (** *** Composition of morphisms is a morphism *)

  Local Lemma TriMor_comp_comms {D1 D2 D3 : Tri} (TM1 : TriMor D1 D2) (TM2 : TriMor D2 D3) :
    MPMorComms (mk_MPMorMors (MPMor1 TM1 · MPMor1 TM2) (MPMor2 TM1 · MPMor2 TM2)
                             (MPMor3 TM1 · MPMor3 TM2)).
  Proof.
    use mk_MPMorComms.
    - cbn. rewrite <- assoc. rewrite (MPComm1 TM2). rewrite assoc. rewrite (MPComm1 TM1).
      rewrite assoc. apply idpath.
    - cbn. rewrite <- assoc. rewrite (MPComm2 TM2). rewrite assoc. rewrite (MPComm2 TM1).
      rewrite assoc. apply idpath.
  Qed.

  Local Lemma TriMor_comp_comm3 {D1 D2 D3 : Tri} (TM1 : TriMor D1 D2) (TM2 : TriMor D2 D3) :
    MPMor3 TM1 · MPMor3 TM2 · Mor3 D3 = Mor3 D1 · # (AddEquiv1 T) (MPMor1 TM1 · MPMor1 TM2).
  Proof.
    rewrite <- assoc. rewrite (DComm3 TM2). rewrite assoc. rewrite (DComm3 TM1).
    rewrite <- assoc. rewrite <- functor_comp. apply idpath.
  Qed.

  Definition TriMor_comp {D1 D2 D3 : Tri} (TM1 : TriMor D1 D2) (TM2 : TriMor D2 D3) : TriMor D1 D3.
  Proof.
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (MPMor1 TM1 · MPMor1 TM2).
        * exact (MPMor2 TM1 · MPMor2 TM2).
        * exact (MPMor3 TM1 · MPMor3 TM2).
      + exact (TriMor_comp_comms TM1 TM2).
    - exact (TriMor_comp_comm3 TM1 TM2).
  Defined.


  (** ** is isomorphism *)

  Definition TriMor_is_iso {D1 D2 : Tri} (M : TriMor D1 D2) : UU :=
    (is_z_isomorphism (MPMor1 M)) × (is_z_isomorphism (MPMor2 M))
                                  × (is_z_isomorphism (MPMor3 M)).

  Definition TriMor_is_iso1 {D1 D2 : Tri} {M : TriMor D1 D2} (Ti : TriMor_is_iso M) :
    is_z_isomorphism (MPMor1 M) := dirprod_pr1 Ti.

  Definition TriMor_is_iso2 {D1 D2 : Tri} {M : TriMor D1 D2} (Ti : TriMor_is_iso M) :
    is_z_isomorphism (MPMor2 M) := dirprod_pr1 (dirprod_pr2 Ti).

  Definition TriMor_is_iso3 {D1 D2 : Tri} {M : TriMor D1 D2} (Ti : TriMor_is_iso M) :
    is_z_isomorphism (MPMor3 M) := dirprod_pr2 (dirprod_pr2 Ti).

  Definition mk_TriMor_is_iso {D1 D2 : Tri} {M : TriMor D1 D2}
             (H1 : is_z_isomorphism (MPMor1 M))
             (H2 : is_z_isomorphism (MPMor2 M))
             (H3 : is_z_isomorphism (MPMor3 M)) :
    TriMor_is_iso M := (H1,,(H2,,H3)).

  (** *** Composition of is isomorphism is isomorphism *)

  Definition TriMor_is_iso_comp {D1 D2 D3 : Tri} {M1 : TriMor D1 D2} {M2 : TriMor D2 D3}
             (i1 : TriMor_is_iso M1) (i2 : TriMor_is_iso M2) : TriMor_is_iso (TriMor_comp M1 M2).
  Proof.
    use mk_TriMor_is_iso.
    - use is_z_isomorphism_comp.
      + exact (TriMor_is_iso1 i1).
      + exact (TriMor_is_iso1 i2).
    - use is_z_isomorphism_comp.
      + exact (TriMor_is_iso2 i1).
      + exact (TriMor_is_iso2 i2).
    - use is_z_isomorphism_comp.
      + exact (TriMor_is_iso3 i1).
      + exact (TriMor_is_iso3 i2).
  Defined.

  (** *** Construction of an inverse and the fact that it is isomorphism *)

  Local Lemma TriMor_is_iso_to_inv_Comm {D1 D2 : Tri} {M : TriMor D1 D2} (Ti : TriMor_is_iso M) :
    MPMorComms (mk_MPMorMors (is_z_isomorphism_mor (TriMor_is_iso1 Ti))
                             (is_z_isomorphism_mor (TriMor_is_iso2 Ti))
                             (is_z_isomorphism_mor (TriMor_is_iso3 Ti))).
  Proof.
    use mk_MPMorComms.
    - cbn.
      use (pre_comp_with_z_iso_is_inj (TriMor_is_iso1 Ti)).
      use (post_comp_with_z_iso_is_inj (TriMor_is_iso2 Ti)).
      rewrite assoc.
      rewrite (is_inverse_in_precat1 (TriMor_is_iso1 Ti)). rewrite id_left.
      rewrite <- assoc. rewrite <- assoc.
      rewrite (is_inverse_in_precat2 (TriMor_is_iso2 Ti)).
      rewrite id_right.
      exact (! MPComm1 M).
    - cbn.
      use (pre_comp_with_z_iso_is_inj (TriMor_is_iso2 Ti)).
      use (post_comp_with_z_iso_is_inj (TriMor_is_iso3 Ti)).
      rewrite assoc.
      rewrite (is_inverse_in_precat1 (TriMor_is_iso2 Ti)). rewrite id_left.
      rewrite <- assoc. rewrite <- assoc.
      rewrite (is_inverse_in_precat2 (TriMor_is_iso3 Ti)).
      rewrite id_right.
      exact (! MPComm2 M).
  Qed.

  Lemma TriMor_is_iso_to_inv_Comm3 {D1 D2 : Tri} {M : TriMor D1 D2} (Ti : TriMor_is_iso M) :
    MPMor3
      (mk_MPMor
         (mk_MPMorMors (is_z_isomorphism_mor (TriMor_is_iso1 Ti))
                       (is_z_isomorphism_mor (TriMor_is_iso2 Ti))
                       (is_z_isomorphism_mor (TriMor_is_iso3 Ti)))
         (TriMor_is_iso_to_inv_Comm Ti)) · Mor3 D1 =
    (Mor3 D2)
      · (# (AddEquiv1 T)
            (MPMor1 (mk_MPMor (mk_MPMorMors (is_z_isomorphism_mor (TriMor_is_iso1 Ti))
                                            (is_z_isomorphism_mor (TriMor_is_iso2 Ti))
                                            (is_z_isomorphism_mor (TriMor_is_iso3 Ti)))
                              (TriMor_is_iso_to_inv_Comm Ti)))).
  Proof.
    cbn.
    use (pre_comp_with_z_iso_is_inj (TriMor_is_iso3 Ti)).
    rewrite assoc.
    rewrite (is_inverse_in_precat1 (TriMor_is_iso3 Ti)). rewrite id_left.
    use (post_comp_with_z_iso_is_inj
           (functor_on_is_z_isomorphism _ (TriMor_is_iso1 Ti))).
    rewrite <- assoc. rewrite <- assoc. rewrite <- functor_comp.
    rewrite (is_inverse_in_precat2 (TriMor_is_iso1 Ti)). rewrite functor_id. rewrite id_right.
    rewrite <- (DComm3 M). apply idpath.
  Qed.

  Definition TriMor_is_iso_inv {D1 D2 : Tri} {M : TriMor D1 D2} (Ti : TriMor_is_iso M) :
    TriMor D2 D1.
  Proof.
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (is_z_isomorphism_mor (TriMor_is_iso1 Ti)).
        * exact (is_z_isomorphism_mor (TriMor_is_iso2 Ti)).
        * exact (is_z_isomorphism_mor (TriMor_is_iso3 Ti)).
      + exact (TriMor_is_iso_to_inv_Comm Ti).
    - exact (TriMor_is_iso_to_inv_Comm3 Ti).
  Defined.

  Lemma TriMor_is_iso_inv_is_iso {D1 D2 : Tri} {M : TriMor D1 D2} (Ti : TriMor_is_iso M) :
    TriMor_is_iso (TriMor_is_iso_inv Ti).
  Proof.
    use mk_TriMor_is_iso.
    - cbn. exact (is_z_isomorphism_inv (TriMor_is_iso1 Ti)).
    - cbn. exact (is_z_isomorphism_inv (TriMor_is_iso2 Ti)).
    - cbn. exact (is_z_isomorphism_inv (TriMor_is_iso3 Ti)).
  Defined.


  (** ** Isomorphisms of triangles *)

  Definition TriIso (D1 D2 : Tri) : UU := ∑ M : TriMor D1 D2, TriMor_is_iso M.

  Definition mk_TriIso {D1 D2 : Tri} (M : TriMor D1 D2) (H : TriMor_is_iso M) : TriIso D1 D2 :=
    (M,,H).

  Definition TriIsoMor {D1 D2 : Tri} (I : TriIso D1 D2) : TriMor D1 D2 := pr1 I.
  Coercion TriIsoMor : TriIso >-> TriMor.

  Definition TriIso_is_iso {D1 D2 : Tri} (I : TriIso D1 D2) : TriMor_is_iso I := pr2 I.
  Coercion TriIso_is_iso : TriIso >-> TriMor_is_iso.

  (** *** Composition of isomorphisms *)

  Definition TriIso_comp {D1 D2 D3 : Tri} (M1 : TriIso D1 D2) (M2 : TriIso D2 D3) :
    TriIso D1 D3.
  Proof.
    use mk_TriIso.
    - exact (TriMor_comp M1 M2).
    - exact (TriMor_is_iso_comp (TriIso_is_iso M1) (TriIso_is_iso M2)).
  Defined.

  (** *** Inverse of an isomorphism *)

  Definition TriIsoInv {D1 D2 : Tri} (I : TriIso D1 D2) : TriIso D2 D1.
  Proof.
    use mk_TriIso.
    - exact (TriMor_is_iso_inv (TriIso_is_iso I)).
    - exact (TriMor_is_iso_inv_is_iso (TriIso_is_iso I)).
  Defined.

  (** *** Identity isomorphism *)

  Definition TriIsoId (D : Tri) : TriIso D D.
  Proof.
    use mk_TriIso.
    - exact (TriMorId D).
    - use mk_TriMor_is_iso.
      + exact (is_z_isomorphism_identity _).
      + exact (is_z_isomorphism_identity _).
      + exact (is_z_isomorphism_identity _).
  Defined.


  (** ** Trivial triangle, rotated triangle, and inv rotated triangle *)

  (** *** X -Id-> X -> 0 -> X[1] *)
  Definition TrivialTri (x : ob A) : Tri.
  Proof.
    use mk_Tri.
    - exact x.
    - exact x.
    - exact (to_Zero A).
    - exact (identity _).
    - exact (ZeroArrow (to_Zero A) _ _).
    - exact (ZeroArrow (to_Zero A) _ _).
  Defined.

  (** *** See introduction to this section for the diagram *)
  Definition RotTri (D : Tri) : Tri.
  Proof.
    use mk_Tri.
    - exact (Ob2 D).
    - exact (Ob3 D).
    - exact (AddEquiv1 T (Ob1 D)).
    - exact (Mor2 D).
    - exact (Mor3 D).
    - exact (to_inv (# (AddEquiv1 T) (Mor1 D))).
  Defined.

  Definition InvRotTri (D : Tri) : Tri.
  Proof.
    use mk_Tri.
    - exact (AddEquiv2 T (Ob3 D)).
    - exact (Ob1 D).
    - exact (Ob2 D).
    - exact (to_inv (# (AddEquiv2 T) (Mor3 D)) · (z_iso_inv_mor (AddEquivUnitIso T (Ob1 D)))).
    - exact (Mor1 D).
    - exact (Mor2 D · (z_iso_inv_mor (AddEquivCounitIso T (Ob3 D)))).
  Defined.


  (** ** Rotation and inverse rotation of a morphism *)
  (** *** See the diagram in the introduction *)

  Local Lemma RotTriMor_Comm3 {D1 D2 : Tri} (M : TriMor D1 D2)  :
    # (AddEquiv1 T) (MPMor1 M) · to_inv (# (AddEquiv1 T) (Mor1 D2)) =
    to_inv (# (AddEquiv1 T) (Mor1 D1)) · # (AddEquiv1 T) (MPMor2 M).
  Proof.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp. apply maponpaths.
    rewrite <- functor_comp. rewrite <- functor_comp. apply maponpaths.
    exact (MPComm1 M).
  Qed.

  Definition RotTriMor {D1 D2 : Tri} (M : TriMor D1 D2) : TriMor (RotTri D1) (RotTri D2).
  Proof.
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (MPMor2 M).
        * exact (MPMor3 M).
        * exact (# (AddEquiv1 T) (MPMor1 M)).
      + use mk_MPMorComms.
        * exact (MPComm2 M).
        * exact (DComm3 M).
    - exact (RotTriMor_Comm3 M).
  Defined.

  Local Lemma InvRotTriMor_Comm1 {D1 D2 : Tri} (M : TriMor D1 D2) :
    (# (AddEquiv2 T) (MPMor3 M))
      · ((to_inv (# (AddEquiv2 T) (Mor3 D2)))
            · z_iso_inv_mor (AddEquivUnitIso T (Ob1 D2))) =
    (to_inv (# (AddEquiv2 T) (Mor3 D1)))
      · z_iso_inv_mor (AddEquivUnitIso T (Ob1 D1)) · MPMor1 M.
  Proof.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    apply maponpaths. rewrite assoc. rewrite <- functor_comp.
    set (tmp := maponpaths (# (AddEquiv2 T)) (DComm3 M)). rewrite tmp. clear tmp.
    rewrite functor_comp. rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    set (tmp := AddEquivUnitComm T _ _ (MPMor1 M)). cbn in tmp.
    use (! AddEquivUnitInv T (MPMor1 M)).
  Qed.

  Local Lemma InvRotTriMor_Comm3 {D1 D2 : Tri} (M : TriMor D1 D2)  :
    MPMor2 M · (Mor2 D2 · z_iso_inv_mor (AddEquivCounitIso T (Ob3 D2))) =
    Mor2 D1 · z_iso_inv_mor (AddEquivCounitIso T (Ob3 D1))
         · # (AddEquiv1 T) (# (AddEquiv2 T) (MPMor3 M)).
  Proof.
    set (tmp := MPComm2 M). rewrite assoc. rewrite tmp. clear tmp.
    rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    use (! AddEquivCounitInv T (MPMor3 M)).
  Qed.

  Definition InvRotTriMor {D1 D2 : Tri} (M : TriMor D1 D2) :
    TriMor (InvRotTri D1) (InvRotTri D2).
  Proof.
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (# (AddEquiv2 T) (MPMor3 M)).
        * exact (MPMor1 M).
        * exact (MPMor2 M).
      + use mk_MPMorComms.
        * exact (InvRotTriMor_Comm1 M).
        * exact (MPComm1 M).
    - exact (InvRotTriMor_Comm3 M).
  Defined.

  Definition RotTriMor_is_iso {D1 D2 : Tri} {M : TriMor D1 D2} (H : TriMor_is_iso M) :
    TriMor_is_iso (RotTriMor M).
  Proof.
    use mk_TriMor_is_iso.
    - exact (TriMor_is_iso2 H).
    - exact (TriMor_is_iso3 H).
    - exact (functor_on_is_z_isomorphism (AddEquiv1 T) (TriMor_is_iso1 H)).
  Defined.

  Definition RotTriIso {D1 D2 : Tri} (M : TriIso D1 D2) :
    TriIso (RotTri D1) (RotTri D2).
  Proof.
    use mk_TriIso.
    - exact (RotTriMor M).
    - exact (RotTriMor_is_iso (TriIso_is_iso M)).
  Defined.

  Definition InvRotTriMor_is_iso {D1 D2 : Tri} {M : TriMor D1 D2} (H : TriMor_is_iso M) :
    TriMor_is_iso (InvRotTriMor M).
  Proof.
    use mk_TriMor_is_iso.
    - exact (functor_on_is_z_isomorphism (AddEquiv2 T) (TriMor_is_iso3 H)).
    - exact (TriMor_is_iso1 H).
    - exact (TriMor_is_iso2 H).
  Defined.

  Definition InvRotTriIso {D1 D2 : Tri} (M : TriIso D1 D2) :
    TriIso (InvRotTri D1) (InvRotTri D2).
  Proof.
    use mk_TriIso.
    - exact (InvRotTriMor M).
    - exact (InvRotTriMor_is_iso (TriIso_is_iso M)).
  Defined.


  (** ** Cone data *)

  Definition ConeData {A : Additive} (T : AddEquiv A A) (x y : ob A) : UU :=
    ∑ (z : ob A), A⟦y, z⟧ × A⟦z, (AddEquiv1 T x)⟧.

  Definition mk_ConeData {A : Additive} (T : AddEquiv A A) {x y z : ob A} (g : y --> z)
             (h : z --> (AddEquiv1 T x)) : ConeData T x y := (z,,(g,,h)).

  Definition ConeDataOb {A : Additive} {T : AddEquiv A A} {x y : ob A} (C : ConeData T x y) :
    ob A := pr1 C.
  Coercion ConeDataOb : ConeData >-> ob.

  Definition ConeData1 {A : Additive} {T : AddEquiv A A} {x y : ob A} (C : ConeData T x y) :
    A⟦y, C⟧ := dirprod_pr1 (pr2 C).

  Definition ConeData2 {A : Additive} {T : AddEquiv A A} {x y : ob A} (C : ConeData T x y) :
    A⟦C, (AddEquiv1 T x)⟧ := dirprod_pr2 (pr2 C).

End def_triangles.


(** * Data for pretriangulated categories *)
Section def_pretriang_data.

  (** ** PreTriangData *)

  (** Data for pretriangulated category consists of
   - An additive category A
   - An additive equivalence T : A -> A
   - A subtype for triangles in (A, T), called the distinguished triangles.
   *)
  Definition PreTriangData : UU :=
    ∑ D : (∑ A : (Additive), (AddEquiv A A)), hsubtype (@Tri (pr1 D) (pr2 D)).

  Definition mk_PreTriangData (A : Additive) (T : AddEquiv A A) (H : hsubtype (@Tri A T)) :
    PreTriangData.
  Proof.
    use tpair.
    - use tpair.
      + exact A.
      + exact T.
    - exact H.
  Defined.

  Definition PreTriangData_Additive (PTD : PreTriangData) : Additive := pr1 (pr1 PTD).
  Coercion PreTriangData_Additive : PreTriangData >-> Additive.

  Definition Trans {PTD : PreTriangData} : AddEquiv PTD PTD := pr2 (pr1 PTD).

  Definition isDTri {PTD : PreTriangData} (T : @Tri PTD Trans) : hProp := (pr2 PTD) T.

  (** Construction of a triangle in PTD from ConeData *)
  Definition ConeTri {PTD : PreTriangData} {x y : ob PTD} (f : x --> y) (D : ConeData Trans x y) :
    @Tri _ (@Trans PTD).
  Proof.
    use mk_Tri.
    - exact x.
    - exact y.
    - exact D.
    - exact f.
    - exact (ConeData1 D).
    - exact (ConeData2 D).
  Defined.

End def_pretriang_data.


(** * Distinguished triangles and extentions *)
(** ** Inroduction
In this section we define data for
- Distinguished triangles
- Extentions of morphisms
*)
Section def_pretriangulated_data.

  Context {PTD : PreTriangData}.

  (** ** Distinguished triangles *)

  Definition DTri : UU := ∑ (T : @Tri _ (@Trans PTD)), isDTri T.

  Definition mk_DTri {x y z : ob PTD} (f : x --> y) (g : y --> z)
             (h : z --> (AddEquiv1 Trans x)) (H : isDTri (mk_Tri f g h)) :
    DTri := ((mk_Tri f g h),,H).

  Definition mk_DTri' (T : @Tri _ (@Trans PTD)) (H : isDTri T) :
    DTri := (T,,H).

  Definition DTriTri (D : DTri) : Tri := pr1 D.
  Coercion DTriTri : DTri >-> Tri.

  Definition DTriisDTri (D : DTri) : isDTri D := pr2 D.


  (** ** Extensions *)

  Definition TExt {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             (H : f1 · Mor1 D2 = Mor1 D1 · f2) : UU :=
    ∑ f3 : Ob3 D1 --> Ob3 D2, (Mor2 D1 · f3 = f2 · Mor2 D2)
                              × (Mor3 D1 · (# (AddEquiv1 (@Trans PTD)) f1) = f3 · Mor3 D2).

  Definition mk_TExt {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             {H : f1 · Mor1 D2 = Mor1 D1 · f2} (f3 : Ob3 D1 --> Ob3 D2)
             (H2 : Mor2 D1 · f3 = f2 · Mor2 D2)
             (H3 : Mor3 D1 · (# (AddEquiv1 (@Trans PTD)) f1) = f3 · Mor3 D2) :
    TExt H := (f3,,(H2,,H3)).

  Definition TExt_Mor {D1 D2 : DTri} {f1 : Ob1 (DTriTri D1) --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             {H : f1 · Mor1 D2 = Mor1 D1 · f2} (TE : TExt H) : PTD⟦Ob3 D1, Ob3 D2⟧ := pr1 TE.
  Coercion TExt_Mor : TExt >-> precategory_morphisms.

  Definition TExtComm1 {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             {H : f1 · Mor1 D2 = Mor1 D1 · f2} (TE : TExt H) :
    Mor2 D1 · TE = f2 · Mor2 D2 := dirprod_pr1 (pr2 TE).

  Definition TExtComm2 {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             {H : f1 · Mor1 D2 = Mor1 D1 · f2} (TE : TExt H) :
    (Mor3 D1 · (# (AddEquiv1 Trans) f1) = TE · Mor3 D2) := dirprod_pr2 (pr2 TE).

  Definition TExtMor {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             {H : f1 · Mor1 D2 = Mor1 D1 · f2} (TE : TExt H) : TriMor D1 D2.
  Proof.
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact f1.
        * exact f2.
        * exact TE.
      + use mk_MPMorComms.
        * exact H.
        * exact (! TExtComm1 TE).
    - exact (! TExtComm2 TE).
  Defined.

End def_pretriangulated_data.


(** * PreTriangulated categories *)
Section def_pretrangulated.

  (** *** isPreTriang
   - Trivial triangles are distinguished
   - Distinguished triangles are closed under isomorphism
   - Rotation of a distinguished triangle is distinguished
   - Inverse rotation of a distinguished triangle is distinguished
   - For every morphism f, there exists a completion to distinguished triangle
   - Commutative squares to morphisms of distinguished triangles
   *)
  Definition isPreTriang (PTD : PreTriangData) : UU :=
    (∏ (x : ob PTD), isDTri (TrivialTri x))
      × (∏ (T1 T2 : @Tri PTD Trans) (I : ∥ TriIso T1 T2 ∥), isDTri T1 -> isDTri T2)
      × (∏ (D : DTri), @isDTri PTD (RotTri D))
      × (∏ (D : DTri), @isDTri PTD (InvRotTri D))
      × (∏ (x y : ob PTD) (f : x --> y), ∥ ∑ D : ConeData Trans x y, isDTri (ConeTri f D) ∥)
      × (∏ (D1 D2 : DTri) (f1 : Ob1 D1 --> Ob1 D2) (f2 : Ob2 D1 --> Ob2 D2)
           (H : f1 · Mor1 D2 = Mor1 D1 · f2), ∥ @TExt PTD _ _ _ _ H ∥).

  Definition mk_isPreTriang {PTD : PreTriangData}
             (H1 : (∏ (x : ob PTD), isDTri (TrivialTri x)))
             (H2 : ∏ (T1 T2 : @Tri PTD Trans) (I : ∥ TriIso T1 T2 ∥), isDTri T1 -> isDTri T2)
             (H3 : ∏ (D : DTri), isDTri (RotTri D))
             (H4 : ∏ (D : DTri), isDTri (InvRotTri D))
             (H5 : ∏ (x y : ob PTD) (f : x --> y),
                   ∥ ∑ D : ConeData Trans x y, isDTri (ConeTri f D) ∥)
             (H6 : ∏ (D1 D2 : DTri) (f1 : Ob1 D1 --> Ob1 D2) (f2 : Ob2 D1 --> Ob2 D2)
                     (H : f1 · Mor1 D2 = Mor1 D1 · f2), ∥ (@TExt PTD _ _ _ _ H) ∥) :
    isPreTriang PTD := (H1,,(H2,,(H3,,(H4,,(H5,,H6))))).

  (** *** Accessor functions *)
  Definition TrivialDTrisData {PTD : PreTriangData} (iPT : isPreTriang PTD) :
    ∏ (x : ob PTD), isDTri (TrivialTri x) := dirprod_pr1 iPT.

  Definition TrivialDTri {PTD : PreTriangData} (iPT : isPreTriang PTD) (x : ob PTD) : @DTri PTD.
  Proof.
    set (TDT := TrivialDTrisData iPT x).
    exact (mk_DTri (identity x) (ZeroArrow (to_Zero PTD) _ (to_Zero PTD))
                   (ZeroArrow (to_Zero PTD) _ (AddEquiv1 Trans x)) TDT).
  Defined.

  Definition DTrisUnderIso {PTD : PreTriangData} (iPT : isPreTriang PTD) :
    ∏ (T1 T2 : @Tri PTD Trans) (I : ∥ TriIso T1 T2 ∥), isDTri T1 -> isDTri T2 :=
    dirprod_pr1 (dirprod_pr2 iPT).

  Definition RotDTris {PTD : PreTriangData} (iPT : isPreTriang PTD) (D : @DTri PTD) :
    isDTri (RotTri D) := dirprod_pr1 (dirprod_pr2 (dirprod_pr2 iPT)) D.

  Definition RotDTri {PTD : PreTriangData} (iPT : isPreTriang PTD) (D : @DTri PTD) : @DTri PTD.
  Proof.
    set (D' := RotDTris iPT D).
    exact (mk_DTri' (RotTri D) D').
  Defined.

  Definition InvRotDTris {PTD : PreTriangData} (iPT : isPreTriang PTD) (D : @DTri PTD) :
    isDTri (InvRotTri D) := dirprod_pr1 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 iPT))) D.

  Definition InvRotDTri {PTD : PreTriangData} (iPT : isPreTriang PTD) (D : @DTri PTD) : @DTri PTD.
  Proof.
    set (D' := InvRotDTris iPT D).
    exact (mk_DTri' (InvRotTri D) D').
  Defined.

  Definition DCompletion {PTD : PreTriangData} (iPT : isPreTriang PTD) :
    ∏ (x y : ob PTD) (f : x --> y), ∥ ∑ D : ConeData Trans x y, isDTri (ConeTri f D) ∥ :=
    dirprod_pr1 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 iPT)))).

  Definition DExts {PTD : PreTriangData} (iPT : isPreTriang PTD) :
    ∏ (D1 D2 : DTri) (f1 : Ob1 D1 --> Ob1 D2) (f2 : Ob2 D1 --> Ob2 D2)
      (H : f1 · Mor1 D2 = Mor1 D1 · f2), ∥ @TExt PTD _ _ _ _ H ∥ :=
    dirprod_pr2 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 iPT)))).

  Definition DExt {PTD : PreTriangData} (iPT : isPreTriang PTD) (D1 D2 : DTri)
             (f1 : Ob1 D1 --> Ob1 D2) (f2 : Ob2 D1 --> Ob2 D2) (H : f1 · Mor1 D2 = Mor1 D1 · f2) :
    ∥ TExt H ∥ := DExts iPT D1 D2 f1 f2 H.

  (** ** Pretriangulated category *)

  Definition PreTriang : UU := ∑ PTD : PreTriangData, isPreTriang PTD.

  Definition mk_PreTriang (PTD : PreTriangData) (H : isPreTriang PTD) := (PTD,,H).

  (** Accessor functions for pretriangulated categories *)
  Definition PreTriang_PreTriangData (PT : PreTriang) : PreTriangData := pr1 PT.
  Coercion PreTriang_PreTriangData : PreTriang >-> PreTriangData.

  Definition PreTriang_isPreTriang (PT : PreTriang) : isPreTriang PT := pr2 PT.
  Coercion PreTriang_isPreTriang : PreTriang >-> isPreTriang.

End def_pretrangulated.
Arguments Trans [PTD] : simpl never.


(** * Triangulated categories **)
Section def_triangulated.

  (** ** Octahedral data *)

  (** (Octahedral axiom). Suppose you have 3 distinguished triangles (X1, Y1, Z2, f1, f2, f3),
      (Y1, Z1, X2, g1, g2, g3), and (X1, Z1, Y2, f1 · g1, h2, h3). Then there exists a
      distinguished triangle (Z2, Y2, X2, φ1, φ2, g3 · f2[1]) such that the following diagram
      is commutative

                              X1 ----f1----> Y1 ----f2----> Z2 ----f3----> X1[1]
                              ||            |             |              ||
                              ||         g1 |          φ1 |              ||
                              ||            |             |              ||
                              X1 -f1·g1->  Z1  ---h2-->  Y2 ----h3---> X1[1]
                                            |             |              |
                                         g2 |          φ2 |         f[1] |
                                            |             |              |
                                            X2  ========  X2 ----h''---> Y1[1]
                                            |             |
                                         g3 |   g3·f2[1] |
                                            |             |
                                         Y1[1] --f2[1]-> Z2[1]
   *)
  Definition Octa {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
             (H3 : isDTri (mk_Tri (f1 · g1) h2 h3)) : UU :=
    ∑ D : ((z2 --> y2) × (y2 --> x2)),
          (isDTri (mk_Tri (dirprod_pr1 D) (dirprod_pr2 D) (g3 · (# (AddEquiv1 Trans) f2))))
            × (dirprod_pr1 D · h3 = f3)
            × (h2 · dirprod_pr2 D = g2)
            × (f2 · dirprod_pr1 D = g1 · h2)
            × (dirprod_pr2 D · g3 = h3 · (# (AddEquiv1 Trans) f1)).

  Definition mk_Octa {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
             (H3 : isDTri (mk_Tri (f1 · g1) h2 h3))
             (φ1 : z2 --> y2) (φ2 : y2 --> x2)
             (H4 : isDTri (mk_Tri φ1 φ2 (g3 · (# (AddEquiv1 Trans) f2))))
             (Comm1 : φ1 · h3 = f3) (Comm2 : h2 · φ2 = g2)
             (Comm3 : f2 · φ1 = g1 · h2)
             (Comm4 : φ2 · g3 = h3 · (# (AddEquiv1 Trans) f1)) : Octa H1 H2 H3 :=
    ((φ1,,φ2),,(H4,,(Comm1,,(Comm2,,(Comm3,,Comm4))))).

  (** Accessor functions *)

  Definition OctaMor1 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : isDTri (mk_Tri f1 f2 f3)} {H2 : isDTri (mk_Tri g1 g2 g3)}
             {H3 : isDTri (mk_Tri (f1 · g1) h2 h3)}
             (O : Octa H1 H2 H3) : PT⟦z2, y2⟧ := dirprod_pr1 (pr1 O).

  Definition OctaMor2 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : isDTri (mk_Tri f1 f2 f3)} {H2 : isDTri (mk_Tri g1 g2 g3)}
             {H3 : isDTri (mk_Tri (f1 · g1) h2 h3)}
             (O : Octa H1 H2 H3) : PT⟦y2, x2⟧ := dirprod_pr2 (pr1 O).

  Definition OctaDTri {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : isDTri (mk_Tri f1 f2 f3)} {H2 : isDTri (mk_Tri g1 g2 g3)}
             {H3 : isDTri (mk_Tri (f1 · g1) h2 h3)}
             (O : Octa H1 H2 H3) : @DTri PT := mk_DTri' _ (dirprod_pr1 (pr2 O)).

  Definition OctaComm1 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : isDTri (mk_Tri f1 f2 f3)} {H2 : isDTri (mk_Tri g1 g2 g3)}
             {H3 : isDTri (mk_Tri (f1 · g1) h2 h3)}
             (O : Octa H1 H2 H3) : (OctaMor1 O) · h3 = f3 :=
    dirprod_pr1 (dirprod_pr2 (pr2 O)).

  Definition OctaComm2 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : isDTri (mk_Tri f1 f2 f3)} {H2 : isDTri (mk_Tri g1 g2 g3)}
             {H3 : isDTri (mk_Tri (f1 · g1) h2 h3)}
             (O : Octa H1 H2 H3) : h2 · (OctaMor2 O) = g2 :=
    dirprod_pr1 (dirprod_pr2 (dirprod_pr2 (pr2 O))).

  Definition OctaComm3 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : isDTri (mk_Tri f1 f2 f3)} {H2 : isDTri (mk_Tri g1 g2 g3)}
             {H3 : isDTri (mk_Tri (f1 · g1) h2 h3)}
             (O : Octa H1 H2 H3) : f2 · (OctaMor1 O) = g1 · h2 :=
    dirprod_pr1 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 (pr2 O)))).

  Definition OctaComm4 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : isDTri (mk_Tri f1 f2 f3)} {H2 : isDTri (mk_Tri g1 g2 g3)}
             {H3 : isDTri (mk_Tri (f1 · g1) h2 h3)}
             (O : Octa H1 H2 H3) : (OctaMor2 O) · g3 = h3 · (# (AddEquiv1 Trans) f1) :=
    dirprod_pr2 (dirprod_pr2 (dirprod_pr2 (dirprod_pr2 (pr2 O)))).

  (** ** Triangulated category *)
  Definition Triang : UU :=
    ∑ PT : PreTriang,
           (∏ (x1 x2 y1 y2 z1 z2 : ob PT)
              (f1 : x1 --> y1) (f2 : y1 --> z2) (f3 : z2 --> (AddEquiv1 Trans x1))
              (g1 : y1 --> z1) (g2 : z1 --> x2) (g3 : x2 --> (AddEquiv1 Trans y1))
              (h2 : z1 --> y2) (h3 : y2 --> (AddEquiv1 Trans x1))
              (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
              (H3 : isDTri (mk_Tri (f1 · g1) h2 h3)), ∥ Octa H1 H2 H3 ∥).

  Definition mk_Triang {PT : PreTriang} (H : ∏ (x1 x2 y1 y2 z1 z2 : ob PT)
              (f1 : x1 --> y1) (f2 : y1 --> z2) (f3 : z2 --> (AddEquiv1 Trans x1))
              (g1 : y1 --> z1) (g2 : z1 --> x2) (g3 : x2 --> (AddEquiv1 Trans y1))
              (h2 : z1 --> y2) (h3 : y2 --> (AddEquiv1 Trans x1))
              (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
              (H3 : isDTri (mk_Tri (f1 · g1) h2 h3)), ∥ Octa H1 H2 H3 ∥) : Triang := (PT,,H).

  Definition Triang_PreTriang (TR : Triang) : PreTriang := pr1 TR.
  Coercion Triang_PreTriang : Triang >-> PreTriang.

  Definition Octahedral {TR : Triang} {x1 x2 y1 y2 z1 z2 : ob TR}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : isDTri (mk_Tri f1 f2 f3)} {H2 : isDTri (mk_Tri g1 g2 g3)}
             {H3 : isDTri (mk_Tri (f1 · g1) h2 h3)} :
    ∥ Octa H1 H2 H3 ∥ := (pr2 TR) x1 x2 y1 y2 z1 z2 f1 f2 f3 g1 g2 g3 h2 h3 H1 H2 H3.

End def_triangulated.


(** * Rotations and inverse rotations of morphisms, Extensions, and DTris *)
Section rotation_isos.

  Context {PT : PreTriang}.


  (** ** iso D InvRot (Rot D) and iso D Rot (InvRot D) *)

  Local Lemma RotInvIso_Mor_Comm1 (D : DTri) :
    ((AddEquivUnitIso Trans (Ob1 D)) : PT⟦_, _⟧)
      · ((to_inv (# (AddEquiv2 Trans) (to_inv (# (AddEquiv1 Trans) (Mor1 D)))))
            · (z_iso_inv_mor (AddEquivUnitIso (@Trans PT) (Ob2 D)))) =
    Mor1 D · identity (Ob2 D).
  Proof.
    rewrite AdditiveFunctorInv. rewrite inv_inv_eq. rewrite id_right.
    use (post_comp_with_z_iso_is_inj (AddEquivUnitIso Trans (Ob2 D))).
    rewrite <- assoc. rewrite <- assoc.
    rewrite (is_inverse_in_precat2 (AddEquivUnitIso Trans (Ob2 D))).
    rewrite id_right.
    use (! (AddEquivUnitComm (@Trans PT) _ _ (Mor1 D))).
  Qed.

  Local Lemma RotInvIso_Mor_Comm2 (D : @DTri PT) :
    identity (Ob2 D) · Mor2 D = Mor2 D · identity (Ob3 D).
  Proof.
    rewrite id_right. apply id_left.
  Qed.

  Local Lemma RotInvIso_Mor_Comm3 (D : DTri) :
    (identity (Ob3 D))
      · ((Mor3 D) · (z_iso_inv_mor (AddEquivCounitIso Trans ((AddEquiv1 Trans) (Ob1 D))))) =
    Mor3 D · # (AddEquiv1 (@Trans PT)) (AddEquivUnitIso Trans (Ob1 D)).
  Proof.
    rewrite id_left. apply cancel_precomposition. use AddEquivCounitUnit.
  Qed.

  Definition RotInvIso_Mor (D : DTri) : TriMor D (InvRotDTri PT (RotDTri PT D)).
  Proof.
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (AddEquivUnitIso Trans (Ob1 D)).
        * exact (identity _).
        * exact (identity _).
      + use mk_MPMorComms.
        * exact (RotInvIso_Mor_Comm1 D).
        * exact (RotInvIso_Mor_Comm2 D).
    - exact (RotInvIso_Mor_Comm3 D).
  Defined.

  Definition RotInvIso_is_iso (D : DTri) : TriMor_is_iso (RotInvIso_Mor D).
  Proof.
    use mk_TriMor_is_iso.
    - exact (AddEquivUnitInvMor_is_iso_with_inv_data Trans (Ob1 D)).
    - exact (is_z_isomorphism_identity (Ob2 D)).
    - exact (is_z_isomorphism_identity (Ob3 D)).
  Qed.

  Local Lemma InvRotIso_Mor_Comm1 (D : @DTri PT) :
    identity (Ob1 D) · Mor1 D = Mor1 D · identity (Ob2 D).
  Proof.
    rewrite id_right. apply id_left.
  Qed.

  Local Lemma InvRotIso_Mor_Comm2 (D : @DTri PT) :
    (identity (Ob2 D))
      · (Mor2 D · z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D))) =
    Mor2 D · z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D)).
  Proof.
    rewrite id_left. apply idpath.
  Qed.

  Local Lemma InvRotIso_Mor_Comm3 (D : @DTri PT) :
    (z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D)))
      · (to_inv (# (AddEquiv1 Trans) ((to_inv (# (AddEquiv2 Trans) (Mor3 D)))
                                         · z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D))))) =
    Mor3 D · # (AddEquiv1 Trans) (identity (Ob1 D)).
  Proof.
    rewrite functor_id. rewrite id_right. rewrite <- PreAdditive_invlcomp.
    rewrite AdditiveFunctorInv. rewrite inv_inv_eq. rewrite functor_comp.
    set (tmp := AddEquivCounitUnit' Trans (Ob1 D)). cbn in tmp. rewrite assoc. cbn.
    apply (maponpaths (λ g : _, (z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D)))
                                   · (# (AddEquiv1 Trans) (# (AddEquiv2 Trans) (Mor3 D)))
                                   · g)) in tmp.
    use (pathscomp0 (! tmp)). clear tmp.
    use (pre_comp_with_z_iso_is_inj (AddEquivCounitIso Trans (Ob3 D))).
    rewrite assoc. rewrite assoc. cbn.
    set (tmp := is_inverse_in_precat1 (AddEquivCounitIso Trans (Ob3 D))). cbn in tmp.
    rewrite tmp. clear tmp. rewrite id_left.
    exact (AddEquivCounitComm Trans _ _ (Mor3 D)).
  Qed.

  Definition InvRotIso_Mor (D : @DTri PT) : TriMor D (RotDTri PT (InvRotDTri PT D)).
  Proof.
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (identity _).
        * exact (identity _).
        * exact (z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D))).
      + use mk_MPMorComms.
        * exact (InvRotIso_Mor_Comm1 D).
        * exact (InvRotIso_Mor_Comm2 D).
    - exact (InvRotIso_Mor_Comm3 D).
  Defined.

  Definition InvRotIso_is_iso (D : @DTri PT) : TriMor_is_iso (InvRotIso_Mor D).
  Proof.
    use mk_TriMor_is_iso.
    - exact (is_z_isomorphism_identity (Ob1 D)).
    - exact (is_z_isomorphism_identity (Ob2 D)).
    - exact (z_iso_is_z_isomorphism2 (AddEquivCounitIso Trans (Ob3 D))).
  Defined.


  (** ** Extension of morphisms at 2 and 1 *)

  Local Lemma ExtMor'_Comm1 (D1 D2 : @DTri PT) (Mor : TriMor (RotDTri PT D1) (RotDTri PT D2)) :
    (AddEquivUnit Trans) (Ob1 D1) · # (AddEquiv2 Trans) (MPMor3 Mor)
                         · z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D2))
                         · Mor1 D2 = Mor1 D1 · MPMor1 Mor.
  Proof.
    set (tmp := DComm3 Mor). cbn in tmp.
    rewrite <- PreAdditive_invlcomp in tmp. rewrite <- PreAdditive_invrcomp in tmp.
    apply cancel_inv in tmp. rewrite <- functor_comp in tmp.
    use (AddEquiv1Inj Trans). use (pathscomp0 _ tmp). clear tmp.
    rewrite functor_comp. apply cancel_postcomposition.
    set (tmp := AddEquivCounitMorComm Trans (MPMor3 Mor)).
    use (pathscomp0 _ (! tmp)). clear tmp. cbn. rewrite functor_comp. rewrite functor_comp.
    set (tmp := AddEquivCounitUnit Trans (Ob1 D1)).
    apply (maponpaths
             (λ gg : _, gg · # (AddEquiv1 Trans) (# (AddEquiv2 Trans) (MPMor3 Mor)) ·
                            # (AddEquiv1 Trans)
                            (z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D2))))) in tmp.
    use (pathscomp0 (! tmp)). clear tmp. rewrite <- assoc. rewrite <- assoc.
    apply cancel_precomposition. apply cancel_precomposition.
    use (! AddEquivCounitUnit' Trans (Ob1 D2)).
  Qed.

  Local Lemma ExtMor'_Comm3 (D1 D2 : @DTri PT) (Mor : TriMor (RotDTri PT D1) (RotDTri PT D2)):
    MPMor2 Mor · Mor3 D2 =
    Mor3 D1 · # (AddEquiv1 Trans)
         ((AddEquivUnit Trans) (Ob1 D1) · # (AddEquiv2 Trans) (MPMor3 Mor) ·
                               z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D2))).
  Proof.
    set (tmp := MPComm2 Mor). cbn in tmp. cbn. rewrite tmp. clear tmp.
    apply cancel_precomposition.
    use (pathscomp0 (AddEquivCounitMorComm Trans (MPMor3 Mor))).
    set (tmp := AddEquivCounitUnit Trans (Ob1 D1)).
    apply (maponpaths
             (λ gg : _, gg · (# (functor_composite (AddEquiv2 Trans) (AddEquiv1 Trans))
                                  (MPMor3 Mor))
                            · (AddEquivCounit Trans) ((AddEquiv1 Trans) (Ob1 D2)))) in tmp.
    use (pathscomp0 tmp). clear tmp. rewrite <- assoc. rewrite <- assoc. rewrite functor_comp.
    apply cancel_precomposition. rewrite functor_comp. apply cancel_precomposition.
    exact (AddEquivCounitUnit' Trans (Ob1 D2)).
  Qed.

  Definition ExtMor1 (D1 D2 : @DTri PT) (f2 : Ob2 D1 --> Ob2 D2) (f3 : Ob3 D1 --> Ob3 D2)
             (H : f2 · Mor2 D2 = Mor2 D1 · f3)
             (Ext : @TExt _ (RotDTri PT D1) (RotDTri PT D2) f2 f3 H) : TriMor D1 D2.
  Proof.
    set (Mor := TExtMor Ext).
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (((AddEquivUnitIso Trans (Ob1 D1)) : PT⟦_, _⟧)
                   · (# (AddEquiv2 Trans) (MPMor3 Mor))
                   · (z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D2)))).
        * exact (MPMor1 Mor).
        * exact (MPMor2 Mor).
      + use mk_MPMorComms.
        * exact (ExtMor'_Comm1 D1 D2 Mor).
        * exact (MPComm1 Mor).
    - exact (ExtMor'_Comm3 D1 D2 Mor).
  Defined.

  Local Lemma ExtMor2_Comm (D1 D2 : @DTri PT) (f3 : Ob3 D1 --> Ob3 D2)
             (f4 : (AddEquiv1 Trans (Ob1 D1)) --> (AddEquiv1 Trans (Ob1 D2)))
             (H : f3 · Mor3 D2 = Mor3 D1 · f4) :
    let D1' := InvRotDTri PT D1 in
    let D2' := InvRotDTri PT D2 in
    (# (AddEquiv2 Trans) f3)
      · (to_inv (# (AddEquiv2 Trans) (Mor3 D2)) · AddEquivUnitInvMor Trans (Ob1 D2)) =
    (to_inv (# (AddEquiv2 Trans) (Mor3 D1)))
      · AddEquivUnitInvMor Trans (Ob1 D1)
      · (((AddEquivUnit Trans) (Ob1 D1))
            · # (AddEquiv2 Trans) f4 · AddEquivUnitInvMor Trans (Ob1 D2)).
  Proof.
    intros D1' D2'. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp.
    apply maponpaths. apply cancel_postcomposition.
    rewrite <- functor_comp. apply (maponpaths (# (AddEquiv2 Trans))) in H. use (pathscomp0 H).
    rewrite functor_comp. apply cancel_postcomposition. rewrite <- assoc.
    set (tmp := is_inverse_in_precat2 (AddEquivUnitIso Trans (Ob1 D1))).
    apply (maponpaths (compose (# (AddEquiv2 Trans) (Mor3 D1)))) in tmp.
    use (pathscomp0 _ (! tmp)). rewrite id_right. apply idpath.
  Qed.

  Local Lemma ExtMor2_Comm2 (D1 D2 : @DTri PT)
        (Mor : TriMor (InvRotDTri PT D1) (InvRotDTri PT D2)) :
    MPMor3 Mor · Mor2 D2 =
    Mor2 D1 · (AddEquivCounitInvMor Trans (Ob3 D1) · # (AddEquiv1 Trans) (MPMor1 Mor) ·
                                     (AddEquivCounit Trans) (Ob3 D2)).
  Proof.
    use (post_comp_with_z_iso_inv_is_inj (AddEquivCounitIso Trans (Ob3 D2))).
    rewrite <- assoc. use (pathscomp0 (DComm3 Mor)). rewrite <- assoc. rewrite <- assoc.
    cbn. rewrite <- assoc. apply cancel_precomposition. rewrite <- assoc.
    apply cancel_precomposition.
    set (tmp := is_inverse_in_precat1 (AddEquivCounitIso Trans (Ob3 D2))).
    apply (maponpaths (compose (# (AddEquiv1 Trans) (MPMor1 Mor)))) in tmp.
    use (pathscomp0 _ (! tmp)). clear tmp. rewrite id_right. apply idpath.
  Qed.

  Local Lemma ExtMor2_Comm3 (D1 D2 : @DTri PT)
        (Mor : TriMor (InvRotDTri PT D1) (InvRotDTri PT D2)) :
    (AddEquivCounitInvMor Trans (Ob3 D1))
      · # (AddEquiv1 Trans) (MPMor1 Mor) · (AddEquivCounit Trans) (Ob3 D2) ·  Mor3 D2 =
    Mor3 D1 · # (AddEquiv1 Trans) (MPMor2 Mor).
  Proof.
    use (pre_comp_with_z_iso_is_inj (AddEquivCounitIso Trans (Ob3 D1))).
    rewrite assoc. rewrite assoc. rewrite assoc.
    set (tmp' := is_inverse_in_precat1 (AddEquivCounitIso Trans (Ob3 D1))). cbn in tmp'.
    apply (maponpaths
             (postcompose ((# (AddEquiv1 Trans) (MPMor1 Mor))
                             · (AddEquivCounit Trans) (Ob3 D2) · Mor3 D2))) in tmp'.
    unfold postcompose in tmp'. rewrite assoc in tmp'. rewrite assoc in tmp'.
    use (pathscomp0 tmp'). clear tmp'. rewrite id_left. rewrite <- assoc.
    set (tmp' := AddEquivCounitComm Trans _ _ (Mor3 D2)).
    apply (maponpaths (compose (# (AddEquiv1 Trans) (MPMor1 Mor)))) in tmp'.
    use (pathscomp0 (! tmp')). clear tmp'.
    set (tmp' := AddEquivCounitUnit' Trans (Ob1 D2)).
    apply (maponpaths (λ gg : _, # (AddEquiv1 Trans) (MPMor1 Mor)
                                    · (# (AddEquiv1 Trans) (# (AddEquiv2 Trans) (Mor3 D2))
                                          · gg))) in tmp'.
    use (pathscomp0 tmp'). clear tmp'.
    rewrite <- functor_comp. rewrite <- functor_comp. rewrite assoc. rewrite assoc.
    set (tmp' := AddEquivCounitComm Trans _ _ (Mor3 D1)).
    apply (maponpaths (postcompose (# (AddEquiv1 Trans) (MPMor2 Mor)))) in tmp'.
    use (pathscomp0 _ tmp'). clear tmp'. unfold postcompose.
    set (tmp' := AddEquivCounitUnit' Trans (Ob1 D1)).
    apply (maponpaths (λ gg : _, # (AddEquiv1 Trans) (# (AddEquiv2 Trans) (Mor3 D1))
                                    · gg · # (AddEquiv1 Trans) (MPMor2 Mor))) in tmp'.
    use (pathscomp0 _ (! tmp')). clear tmp'.
    rewrite <- functor_comp. rewrite <- functor_comp. apply maponpaths.
    set (tmp := MPComm1 Mor).
    apply cancel_inv. rewrite PreAdditive_invlcomp. rewrite PreAdditive_invrcomp.
    rewrite <- assoc. use (pathscomp0 tmp). clear tmp.
    rewrite PreAdditive_invlcomp. rewrite PreAdditive_invlcomp. apply idpath.
  Qed.

  Definition ExtMor2 (D1 D2 : @DTri PT) (f3 : Ob3 D1 --> Ob3 D2)
             (f4 : (AddEquiv1 Trans (Ob1 D1)) --> (AddEquiv1 Trans (Ob1 D2)))
             (H : f3 · Mor3 D2 = Mor3 D1 · f4) : ∥ TriMor D1 D2 ∥.
  Proof.
    set (D1' := InvRotDTri PT D1). set (D2' := InvRotDTri PT D2).
    set (Ext' := DExt PT D1' D2' (# (AddEquiv2 Trans) f3)
                      (((AddEquivUnitIso Trans (Ob1 D1)) : PT⟦_, _⟧)
                         · (# (AddEquiv2 Trans) f4)
                         · z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D2)))
                      (ExtMor2_Comm D1 D2 f3 f4 H)).
    use (squash_to_prop Ext' (propproperty _)). intros Ext.
    set (Mor := TExtMor Ext).
    use hinhpr.
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (MPMor2 Mor).
        * exact (MPMor3 Mor).
        * exact ((z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D1)))
                   · (# (AddEquiv1 Trans) (MPMor1 Mor))
                   · (AddEquivCounitIso Trans (Ob3 D2))).
      + use mk_MPMorComms.
        * exact (MPComm2 Mor).
        * exact (ExtMor2_Comm2 D1 D2 Mor).
    - exact (ExtMor2_Comm3 D1 D2 Mor).
  Defined.


  (** ** Rotations of DTris *)

  Definition RotDTriMor {D1 D2 : @DTri PT} (M : TriMor D1 D2) :
    TriMor (@RotDTri PT PT D1) (@RotDTri PT PT D2) := RotTriMor M.

  Definition InvRotDTriMor {D1 D2 : @DTri PT} (M : TriMor D1 D2) :
    TriMor (@InvRotDTri PT PT D1) (@InvRotDTri PT PT D2) := InvRotTriMor M.

End rotation_isos.


(** * Composition is zero *)
(** ** Introduction
Composition of consecutive morphisms of a distinguished triangle is 0.
 *)
Section comp_zero.

  Context {PT : PreTriang}.

  Lemma DTriCompZero (D : @DTri PT) : Mor1 D · Mor2 D = ZeroArrow (to_Zero PT) _ _.
  Proof.
    set (D2 := TrivialDTri PT (Ob1 D)).
    set (Ext' := DExt PT D2 D (identity (Ob1 D)) (Mor1 D) (idpath _)).
    use (squash_to_prop Ext'). apply to_has_homsets. intros Ext. clear Ext'.
    set (M := TExtMor Ext). use (pathscomp0 (MPComm2 M)). cbn. apply ZeroArrow_comp_left.
  Qed.

  Lemma DTriCompZero' (D : @DTri PT) : Mor2 D · Mor3 D = ZeroArrow (to_Zero PT) _ _.
  Proof.
    exact (DTriCompZero (RotDTri PT D)).
  Qed.

  Lemma DTriCompZero'' (D : @DTri PT) :
    Mor3 D · to_inv (# (AddEquiv1 Trans) (Mor1 D)) = ZeroArrow (to_Zero PT) _ _.
  Proof.
    exact (DTriCompZero (RotDTri PT (RotDTri PT D))).
  Qed.

End comp_zero.


(** ** Introduction
We construct the short exact sequences out from distinguished triangles. These can be used to define
the long exact sequences associated to a distinguished triangle. Suppose (X, Y, Z, f, g, h) is a
distinguished triangle. Then for every object W we have shortshortexact sequences
      Mor(W, X) --> Mor(W, Y) --> Mor(W, Z)    and    Mor(Z, W) --> Mor(Y, W) --> Mor(X, W)
These shortshortexact sequences are constructed in  [DTriSSE1_ShortShortExact_from_object] and
[DTriSSE1_ShortShortExact_to_object].
 *)
Section short_short_exact_sequences.

  Context {PT : PreTriang}.

  Local Opaque ZeroArrow.

  Definition MorphismPair_from_object (D : @DTri PT) (X : ob PT) :
    @MorphismPair abgr_Abelian.
  Proof.
    use mk_MorphismPair.
    - exact (@to_abgrop PT X (Ob1 D)).
    - exact (@to_abgrop PT X (Ob2 D)).
    - exact (@to_abgrop PT X (Ob3 D)).
    - exact (to_postmor_monoidfun PT X (Ob1 D) (Ob2 D) (Mor1 D)).
    - exact (to_postmor_monoidfun PT X (Ob2 D) (Ob3 D) (Mor2 D)).
  Defined.

  Local Lemma ShortShortExactData_Eq_from_object (D : @DTri PT) (X : ob PT):
    monoidfuncomp (to_postmor_monoidfun PT X (Ob1 D) (Ob2 D) (Mor1 D))
                  (to_postmor_monoidfun PT X (Ob2 D) (Ob3 D) (Mor2 D)) =
    ZeroArrow abgr_Zero (to_abgrop X (Ob1 D)) (to_abgrop X (Ob3 D)).
  Proof.
    cbn. rewrite <- (@AdditiveZeroArrow_postmor_Abelian PT).
    use monoidfun_paths. use funextfun. intros x. cbn. unfold to_postmor.
    rewrite <- assoc. apply cancel_precomposition. exact (DTriCompZero D).
  Qed.

  Definition ShortShortExactData_from_object (D : @DTri PT) (X : ob PT) :
    @ShortShortExactData abgr_Abelian abgr_Zero.
  Proof.
    use mk_ShortShortExactData.
    - exact (MorphismPair_from_object D X).
    - exact (ShortShortExactData_Eq_from_object D X).
  Defined.

  Lemma ShortShortExact_isKernel_from_object (D : @DTri PT) (X : ob PT) :
    isKernel (Abelian.to_Zero abgr_Abelian)
             (KernelArrow (Image (ShortShortExactData_from_object D X)))
             (Mor2 (ShortShortExactData_from_object D X))
             (@Image_Eq abgr_Abelian has_homsets_abgr (ShortShortExactData_from_object D X)).
  Proof.
    use abgr_isKernel_Criteria.
    - intros D0. induction D0 as [y yH].
      set (D' := TrivialDTri PT X).
      assert (e : y · Mor2 D =
                  ZeroArrow (to_Zero PT) _ (to_Zero PT) · ZeroArrow (to_Zero PT) _ _).
      {
        cbn in yH. unfold to_postmor in yH. rewrite yH.
        rewrite ZeroArrow_comp_left. set (tmp := PreAdditive_unel_zero PT (to_Zero PT) X (Ob3 D)).
        unfold to_unel in tmp. exact tmp.
      }
      set (Ext' := @DExt _ PT (RotDTri PT D') (RotDTri PT D) y
                         (ZeroArrow (Additive.to_Zero PT) _ _) e).
      use (squash_to_prop Ext' (propproperty _)). intros Ext. clear Ext'.
      set (Mor := ExtMor1 D' D y (ZeroArrow (Additive.to_Zero PT) _ _) e Ext).
      use hinhpr.
      use tpair.
      + exact (((factorization1_epi
                   abgr_Abelian has_homsets_abgr
                   (Mor1 (ShortShortExactData_from_object D X)) : abgr_Abelian⟦_, _⟧) :
                  monoidfun _ _)
                 (MPMor1 Mor)).
      + cbn beta. set (comm1 := MPComm1 Mor). rewrite id_left in comm1.
        use (pathscomp0 _ comm1). clear comm1.
        set (tmp := @factorization1 abgr_Abelian has_homsets_abgr _ _
                                    (Mor1 (ShortShortExactData_from_object D X))).
        apply base_paths in tmp.
        exact (! (toforallpaths _ _ _ tmp (MPMor1 Mor))).
    - use KernelArrowisMonic.
  Qed.

  Definition ShortShortExact_from_object (D : @DTri PT) (X : ob PT) :
    @ShortShortExact abgr_Abelian has_homsets_abgr.
  Proof.
    use mk_ShortShortExact.
    - exact (ShortShortExactData_from_object D X).
    - exact (ShortShortExact_isKernel_from_object D X).
  Defined.

  (** ShortShortExacts to X *)
  Definition MorphismPair_to_object (D : @DTri PT) (X : ob PT) : @MorphismPair abgr_Abelian.
  Proof.
    use mk_MorphismPair.
    - exact (@to_abgrop PT (Ob3 D) X).
    - exact (@to_abgrop PT (Ob2 D) X).
    - exact (@to_abgrop PT (Ob1 D) X).
    - exact (to_premor_monoidfun PT (Ob2 D) (Ob3 D) X (Mor2 D)).
    - exact (to_premor_monoidfun PT (Ob1 D) (Ob2 D) X (Mor1 D)).
  Defined.

  Local Lemma ShortShortExactData_Eq_to_object (D : @DTri PT) (X : ob PT) :
    monoidfuncomp (to_premor_monoidfun PT (Ob2 D) (Ob3 D) X (Mor2 D))
                  (to_premor_monoidfun PT (Ob1 D) (Ob2 D) X (Mor1 D)) =
    ZeroArrow (Abelian.to_Zero abgr_Abelian) (to_abgrop (Ob3 D) X) (to_abgrop (Ob1 D) X).
  Proof.
    rewrite <- (@AdditiveZeroArrow_premor_Abelian PT).
    use monoidfun_paths. use funextfun. intros x. cbn. unfold to_premor. rewrite assoc.
    apply cancel_postcomposition. exact (DTriCompZero D).
  Qed.

  Definition ShortShortExactData_to_object (D : @DTri PT) (X : ob PT) :
    @ShortShortExactData abgr_Abelian abgr_Zero.
  Proof.
    use mk_ShortShortExactData.
    - exact (MorphismPair_to_object D X).
    - exact (ShortShortExactData_Eq_to_object D X).
  Defined.

  Lemma ShortShortExact_isKernel_to_object (D : @DTri PT) (X : ob PT) :
    isKernel (Abelian.to_Zero abgr_Abelian)
             (KernelArrow (Image (ShortShortExactData_to_object D X)))
             (Mor2 (ShortShortExactData_to_object D X))
             (@Image_Eq abgr_Abelian has_homsets_abgr
                       (ShortShortExactData_to_object D X)).
  Proof.
    use abgr_isKernel_Criteria.
    - intros D0. induction D0 as [y yH].
      set (D' := InvRotDTri PT (TrivialDTri PT X)).
      assert (e : ZeroArrow (to_Zero PT) (Ob1 D) (Ob1 D') · Mor1 D' = Mor1 D · y).
      {
        rewrite ZeroArrow_comp_left.
        cbn in yH. unfold to_premor in yH. use (pathscomp0 _ (! yH)).
        set (tmp := PreAdditive_unel_zero PT (to_Zero PT) (Ob1 D) (Ob2 D')).
        unfold to_unel in tmp. exact (! tmp).
      }
      set (Ext' := DExt PT D D' (ZeroArrow (Additive.to_Zero PT) _ _) y e).
      use (squash_to_prop Ext' (propproperty _)). intros Ext. clear Ext'.
      set (Mor := TExtMor Ext).
      use hinhpr.
      use tpair.
      + exact (((factorization1_epi
                   abgr_Abelian has_homsets_abgr
                   (Mor1 (ShortShortExactData_to_object D X)) : abgr_Abelian⟦_, _⟧) : monoidfun _ _)
                 (MPMor3 Mor)).
      + cbn beta. set (comm2 := MPComm2 Mor). rewrite id_right in comm2.
        use (pathscomp0 _ (! comm2)). clear comm2.
        set (tmp := @factorization1 abgr_Abelian has_homsets_abgr _ _
                                    (Mor1 (ShortShortExactData_to_object D X))).
        apply base_paths in tmp.
        exact (! (toforallpaths _ _ _ tmp (MPMor3 Mor))).
    - use KernelArrowisMonic.
  Qed.

  Definition ShortShortExact_to_object (D : @DTri PT) (X : ob PT) :
    @ShortShortExact abgr_Abelian has_homsets_abgr.
  Proof.
    use mk_ShortShortExact.
    - exact (ShortShortExactData_to_object D X).
    - exact (ShortShortExact_isKernel_to_object D X).
  Defined.

End short_short_exact_sequences.


(** ** Introduction
Suppose you have a morphism of distinguished triangles represented by the following diagram
                                X  -f-> Y  -g-> Z  -h->  X[1]
                             φ1 |    φ2 |    φ3 |    φ1[1] |
                                X' -f-> Y' -g-> Z' -h-> X'[1].
The five lemma for triangulated categories says that if φ1 and φ2 are isomorphisms, then so is φ3.
Using rotations we show also the following versions: if φ1 and φ3 are isomorphisms, then so is φ2,
and if φ2 and φ3 are isomorphisms, then so is φ1. These are proved in [TriangulatedFiveLemma],
TriangulatedFiveLemma2], and [TriangulatedFiveLemma1], respectively.
 *)
Section triangulated_five_lemma.

  Context {PT : PreTriang}.

  Local Opaque ZeroArrow.

  Definition TriangulatedRowObs_from_object (D : @DTri PT) (X : ob PT) :
    @FiveRowObs abgr_Abelian.
  Proof.
    use mk_FiveRowObs.
    - exact (to_abgrop X (Ob1 D)).
    - exact (to_abgrop X (Ob2 D)).
    - exact (to_abgrop X (Ob3 D)).
    - exact (to_abgrop X (AddEquiv1 Trans (Ob1 D))).
    - exact (to_abgrop X (AddEquiv1 Trans (Ob2 D))).
  Defined.

  Definition TriangulatedRowDiffs_from_object (D : @DTri PT) (X : ob PT) :
    @FiveRowDiffs abgr_Abelian (TriangulatedRowObs_from_object D X).
  Proof.
    use mk_FiveRowDiffs.
    - exact (to_postmor_monoidfun PT _ _ _ (Mor1 D)).
    - exact (to_postmor_monoidfun PT _ _ _ (Mor2 D)).
    - exact (to_postmor_monoidfun PT _ _ _ (Mor3 D)).
    - exact (to_postmor_monoidfun PT _ _ _ (to_inv (# (AddEquiv1 Trans) (Mor1 D)))).
  Defined.

  Definition TriangulatedRowDiffsEq_from_object (D : @DTri PT) (X : ob PT) :
    @FiveRowDiffsEq abgr_Abelian _ (TriangulatedRowDiffs_from_object D X).
  Proof.
    use mk_FiveRowDiffsEq.
    - use monoidfun_paths. use funextfun. intros x. cbn. unfold to_postmor. rewrite <- assoc.
      set (tmp := DTriCompZero D). apply (maponpaths (compose x)) in tmp.
      use (pathscomp0 tmp). clear tmp. rewrite ZeroArrow_comp_right.
      rewrite <- PreAdditive_unel_zero. unfold to_unel. apply idpath.
    - use monoidfun_paths. use funextfun. intros x. cbn. unfold to_postmor. rewrite <- assoc.
      set (tmp := DTriCompZero' D). apply (maponpaths (compose x)) in tmp.
      use (pathscomp0 tmp). clear tmp. rewrite ZeroArrow_comp_right.
      rewrite <- PreAdditive_unel_zero. unfold to_unel. apply idpath.
    - use monoidfun_paths. use funextfun. intros x. cbn. unfold to_postmor. rewrite <- assoc.
      set (tmp := DTriCompZero' (RotDTri PT D)). apply (maponpaths (compose x)) in tmp.
      cbn in tmp. use (pathscomp0 tmp). clear tmp. rewrite ZeroArrow_comp_right.
      rewrite <- PreAdditive_unel_zero. unfold to_unel. apply idpath.
  Qed.

  Definition TriangulatedRowExacts_from_object (D : @DTri PT) (X : ob PT) :
    @FiveRowExacts abgr_Abelian has_homsets_abgr _ _ (TriangulatedRowDiffsEq_from_object D X).
  Proof.
    use mk_FiveRowExacts.
    - unfold isExact. exact_op (@ShortShortExact_isKernel_from_object PT D X).
    - unfold isExact. exact_op (@ShortShortExact_isKernel_from_object PT (RotDTri PT D) X).
    - unfold isExact.
      exact_op (@ShortShortExact_isKernel_from_object PT (RotDTri PT (RotDTri PT D)) X).
  Qed.

  Definition TriangulatedRow_from_object (D : @DTri PT) (X : ob PT) :
    @FiveRow abgr_Abelian has_homsets_abgr.
  Proof.
    use mk_FiveRow.
    - exact (TriangulatedRowObs_from_object D X).
    - exact (TriangulatedRowDiffs_from_object D X).
    - exact (TriangulatedRowDiffsEq_from_object D X).
    - exact (TriangulatedRowExacts_from_object D X).
  Defined.

  Definition TriangulatedRowMors_from_object {D1 D2 : @DTri PT} (M : TriMor D1 D2) (X : ob PT) :
    @FiveRowMors abgr_Abelian has_homsets_abgr
                 (TriangulatedRow_from_object D1 X) (TriangulatedRow_from_object D2 X).
  Proof.
    use mk_FiveRowMors.
    - exact (to_postmor_monoidfun PT _ _ _ (MPMor1 M)).
    - exact (to_postmor_monoidfun PT _ _ _ (MPMor2 M)).
    - exact (to_postmor_monoidfun PT _ _ _ (MPMor3 M)).
    - exact (to_postmor_monoidfun PT _ _ _ (# (AddEquiv1 Trans) (MPMor1 M))).
    - exact (to_postmor_monoidfun PT _ _ _ (# (AddEquiv1 Trans) (MPMor2 M))).
  Defined.

  Definition TriangulatedMorsComm_from_object {D1 D2 : @DTri PT} (M : TriMor D1 D2) (X : ob PT) :
    @FiveRowMorsComm abgr_Abelian has_homsets_abgr _ _ (TriangulatedRowMors_from_object M X).
  Proof.
    use mk_FiveRowMorsComm.
    - use monoidfun_paths. use funextfun. intros x. cbn. unfold to_postmor.
      rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition. exact (! MPComm1 M).
    - use monoidfun_paths. use funextfun. intros x. cbn. unfold to_postmor.
      rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition. exact (! MPComm2 M).
    - use monoidfun_paths. use funextfun. intros x. cbn. unfold to_postmor.
      rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition. exact (! DComm3 M).
    - use monoidfun_paths. use funextfun. intros x. cbn. unfold to_postmor.
      rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
      apply maponpaths. rewrite <- functor_comp. rewrite <- functor_comp.
      apply maponpaths. exact (! MPComm1 M).
  Qed.

  Definition TriangulatedMorphism_from_object {D1 D2 : @DTri PT} (M : TriMor D1 D2) (X : ob PT) :
    @FiveRowMorphism abgr_Abelian has_homsets_abgr
                     (TriangulatedRow_from_object D1 X) (TriangulatedRow_from_object D2 X).
  Proof.
    use mk_FiveRowMorphism.
    - exact (TriangulatedRowMors_from_object M X).
    - exact (TriangulatedMorsComm_from_object M X).
  Defined.

  Definition TriangulatedRowObs_to_object (D : @DTri PT) (X : ob PT) : @FiveRowObs abgr_Abelian.
  Proof.
    use mk_FiveRowObs.
    - exact (to_abgrop (AddEquiv1 Trans (Ob2 D)) X).
    - exact (to_abgrop (AddEquiv1 Trans (Ob1 D)) X).
    - exact (to_abgrop (Ob3 D) X).
    - exact (to_abgrop (Ob2 D) X).
    - exact (to_abgrop (Ob1 D) X).
  Defined.

  Definition TriangulatedRowDiffs_to_object (D : @DTri PT) (X : ob PT) :
    @FiveRowDiffs abgr_Abelian (TriangulatedRowObs_to_object D X).
  Proof.
    use mk_FiveRowDiffs.
    - exact (to_premor_monoidfun PT _ _ _ (to_inv (# (AddEquiv1 Trans) (Mor1 D)))).
    - exact (to_premor_monoidfun PT _ _ _ (Mor3 D)).
    - exact (to_premor_monoidfun PT _ _ _ (Mor2 D)).
    - exact (to_premor_monoidfun PT _ _ _ (Mor1 D)).
  Defined.

  Definition TriangulatedRowDiffsEq_to_object (D : @DTri PT) (X : ob PT) :
    @FiveRowDiffsEq abgr_Abelian _ (TriangulatedRowDiffs_to_object D X).
  Proof.
    use mk_FiveRowDiffsEq.
    - use monoidfun_paths. use funextfun. intros x. cbn. unfold to_premor. rewrite assoc.
      set (tmp := DTriCompZero (RotDTri PT (RotDTri PT D))). cbn in tmp. cbn.
      apply (maponpaths (postcompose x)) in tmp. unfold postcompose in tmp.
      use (pathscomp0 tmp). clear tmp. rewrite ZeroArrow_comp_left.
      rewrite <- PreAdditive_unel_zero. unfold to_unel. apply idpath.
    - use monoidfun_paths. use funextfun. intros x. cbn. unfold to_premor. rewrite assoc.
      set (tmp := DTriCompZero (RotDTri PT D)). cbn in tmp. cbn.
      apply (maponpaths (postcompose x)) in tmp. unfold postcompose in tmp.
      use (pathscomp0 tmp). clear tmp. rewrite ZeroArrow_comp_left.
      rewrite <- PreAdditive_unel_zero. unfold to_unel. apply idpath.
    - use monoidfun_paths. use funextfun. intros x. cbn. unfold to_premor. rewrite assoc.
      set (tmp := DTriCompZero D). cbn in tmp. cbn.
      apply (maponpaths (postcompose x)) in tmp. unfold postcompose in tmp.
      cbn in tmp. use (pathscomp0 tmp). clear tmp. rewrite ZeroArrow_comp_left.
      rewrite <- PreAdditive_unel_zero. unfold to_unel. apply idpath.
  Qed.

  Definition TriangulatedRowExacts_to_object (D : @DTri PT) (X : ob PT) :
    @FiveRowExacts abgr_Abelian has_homsets_abgr _ _ (TriangulatedRowDiffsEq_to_object D X).
  Proof.
    use mk_FiveRowExacts.
    - unfold isExact.
      exact_op (@ShortShortExact_isKernel_to_object PT (RotDTri PT (RotDTri PT D)) X).
    - unfold isExact. exact_op (@ShortShortExact_isKernel_to_object PT (RotDTri PT D) X).
    - unfold isExact. exact_op (@ShortShortExact_isKernel_to_object PT D X).
  Qed.

  Definition TriangulatedRow_to_object (D : @DTri PT) (X : ob PT) :
    @FiveRow abgr_Abelian has_homsets_abgr.
  Proof.
    use mk_FiveRow.
    - exact (TriangulatedRowObs_to_object D X).
    - exact (TriangulatedRowDiffs_to_object D X).
    - exact (TriangulatedRowDiffsEq_to_object D X).
    - exact (TriangulatedRowExacts_to_object D X).
  Defined.

  Definition TriangulatedRowMors_to_object {D1 D2 : @DTri PT} (M : TriMor D1 D2) (X : ob PT) :
    @FiveRowMors abgr_Abelian has_homsets_abgr
                 (TriangulatedRow_to_object D2 X) (TriangulatedRow_to_object D1 X).
  Proof.
    use mk_FiveRowMors.
    - exact (to_premor_monoidfun PT _ _ _ (# (AddEquiv1 Trans) (MPMor2 M))).
    - exact (to_premor_monoidfun PT _ _ _ (# (AddEquiv1 Trans) (MPMor1 M))).
    - exact (to_premor_monoidfun PT _ _ _ (MPMor3 M)).
    - exact (to_premor_monoidfun PT _ _ _ (MPMor2 M)).
    - exact (to_premor_monoidfun PT _ _ _ (MPMor1 M)).
  Defined.

  Definition TriangulatedMorsComm_to_object {D1 D2 : @DTri PT} (M : TriMor D1 D2) (X : ob PT) :
    @FiveRowMorsComm abgr_Abelian has_homsets_abgr _ _ (TriangulatedRowMors_to_object M X).
  Proof.
    use mk_FiveRowMorsComm.
    - use monoidfun_paths. use funextfun. intros x. cbn. unfold to_premor.
      rewrite assoc. rewrite assoc.
      apply cancel_postcomposition. rewrite <- PreAdditive_invlcomp.
      rewrite <- PreAdditive_invrcomp.
      apply maponpaths. rewrite <- functor_comp. rewrite <- functor_comp.
      apply maponpaths. exact (MPComm1 M).
    - use monoidfun_paths. use funextfun.
      intros x. cbn. unfold to_premor. rewrite assoc. rewrite assoc.
      apply cancel_postcomposition. exact (DComm3 M).
    - use monoidfun_paths. use funextfun. intros x. cbn. unfold to_premor.
      rewrite assoc. rewrite assoc.
      apply cancel_postcomposition. exact (MPComm2 M).
    - use monoidfun_paths. use funextfun.
      intros x. cbn. unfold to_premor. rewrite assoc. rewrite assoc.
      apply cancel_postcomposition. exact (MPComm1 M).
  Qed.

  Definition TriangulatedMorphism_to_object {D1 D2 : @DTri PT} (M : TriMor D1 D2) (X : ob PT) :
    @FiveRowMorphism abgr_Abelian has_homsets_abgr
                     (TriangulatedRow_to_object D2 X) (TriangulatedRow_to_object D1 X) .
  Proof.
    use mk_FiveRowMorphism.
    - exact (TriangulatedRowMors_to_object M X).
    - exact (TriangulatedMorsComm_to_object M X).
  Defined.

  Lemma TriangulatedFiveLemma {D1 D2 : @DTri PT} (M : TriMor D1 D2)
        (H1 : is_z_isomorphism (MPMor1 M)) (H2 : is_z_isomorphism (MPMor2 M)) :
    is_z_isomorphism (MPMor3 M).
  Proof.
    set (Mor1 := TriangulatedMorphism_from_object M (Ob3 D2)).
    set (Mor2 := TriangulatedMorphism_to_object M (Ob3 D1)).
    assert (e1 : is_z_isomorphism (@FMor3 abgr_Abelian has_homsets_abgr _ _ Mor1)).
    {
      use FiveLemma.
      - exact (@abgr_Additive_is_iso_postmor PT _ _ _ _ H1).
      - exact (@abgr_Additive_is_iso_postmor PT _ _ _ _ H2).
      - exact (abgr_Additive_is_iso_postmor
                 (Ob3 D2) _ _ (functor_on_is_z_isomorphism (AddEquiv1 (@Trans PT)) H1)).
      - exact (abgr_Additive_is_iso_postmor
                 (Ob3 D2) _ _ (functor_on_is_z_isomorphism (AddEquiv1 (@Trans PT)) H2)).
    }
    assert (e2 : is_z_isomorphism (@FMor3 abgr_Abelian has_homsets_abgr _ _ Mor2)).
    {
      use FiveLemma.
      - exact (abgr_Additive_is_iso_premor
                 _ _ (Ob3 D1) (functor_on_is_z_isomorphism (AddEquiv1 (@Trans PT)) H2)).
      - exact (abgr_Additive_is_iso_premor
                 _ _ (Ob3 D1) (functor_on_is_z_isomorphism (AddEquiv1 (@Trans PT)) H1)).
      - exact (@abgr_Additive_is_iso_premor PT _ _ _ _ H2).
      - exact (@abgr_Additive_is_iso_premor PT _ _ _ _ H1).
    }
    exact (@abgr_Additive_premor_postmor_is_iso PT _ _ (MPMor3 M) e2 e1).
  Qed.

  Lemma TriangulatedFiveLemma2 {D1 D2 : @DTri PT} (M : TriMor D1 D2)
        (H1 : is_z_isomorphism (MPMor1 M)) (H2 : is_z_isomorphism (MPMor3 M)) :
    is_z_isomorphism (MPMor2 M).
  Proof.
    exact (TriangulatedFiveLemma
             (InvRotDTriMor M) (functor_on_is_z_isomorphism (AddEquiv2 Trans) H2) H1).
  Qed.

  Lemma TriangulatedFiveLemma1 {D1 D2 : @DTri PT} (M : TriMor D1 D2)
        (H1 : is_z_isomorphism (MPMor2 M)) (H2 : is_z_isomorphism (MPMor3 M)) :
    is_z_isomorphism (MPMor1 M).
  Proof.
    exact (TriangulatedFiveLemma
             (InvRotDTriMor (InvRotDTriMor M))
             (functor_on_is_z_isomorphism (AddEquiv2 Trans) H1)
             (functor_on_is_z_isomorphism (AddEquiv2 Trans) H2)).
  Qed.

End triangulated_five_lemma.


(** ** Change triangles in extension using isomorphisms *)
Section Ext_isomorphisms.

  Lemma DExtIso_Comm1 {PT : PreTriangData} {D1 D2 : DTri} (D1' D2' : Tri)
        (I1 : TriIso D1 D1') (I2 : TriIso D2 D2')
        {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2} (H : f1 · Mor1 D2 = Mor1 D1 · f2)
        (h : Ob3 D1' --> Ob3 D2')
        (comm1 : Mor2 D1' · h = MPMor2 (TriIsoInv I1) · f2 · MPMor2 I2 · Mor2 D2')
        (comm2 : Mor3 D1' · (# (AddEquiv1 (@Trans PT))
                                (MPMor1 (TriIsoInv I1) · f1 · MPMor1 I2)) = h · Mor3 D2') :
    Mor2 D1 · (MPMor3 I1 · h · MPMor3 (TriIsoInv I2)) = f2 · Mor2 D2.
  Proof.
    rewrite assoc. rewrite assoc. rewrite <- (MPComm2 I1).
    rewrite <- (assoc _ (Mor2 D1')). rewrite comm1. rewrite assoc. rewrite assoc.
    rewrite assoc. cbn. rewrite (is_inverse_in_precat1 (TriMor_is_iso2 I1)).
    rewrite id_left. rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    rewrite assoc. rewrite (MPComm2 I2). rewrite <- assoc.
    rewrite (is_inverse_in_precat1 (TriMor_is_iso3 I2)). apply id_right.
  Qed.

  Lemma DExtIso_Comm2 {PT : PreTriangData} {D1 D2 : DTri} (D1' D2' : Tri)
        (I1 : TriIso D1 D1') (I2 : TriIso D2 D2')
        {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2} (H : f1 · Mor1 D2 = Mor1 D1 · f2)
        (h : Ob3 D1' --> Ob3 D2')
        (comm1 : Mor2 D1' · h = MPMor2 (TriIsoInv I1) · f2 · MPMor2 I2 · Mor2 D2')
        (comm2 : Mor3 D1' · (# (AddEquiv1 (@Trans PT))
                                (MPMor1 (TriIsoInv I1) · f1 · MPMor1 I2)) = h · Mor3 D2') :
    Mor3 D1 · # (AddEquiv1 Trans) f1 = MPMor3 I1 · h · MPMor3 (TriIsoInv I2) · Mor3 D2.
  Proof.
    rewrite functor_comp in comm2. rewrite functor_comp in comm2. rewrite assoc in comm2.
    rewrite assoc in comm2. rewrite <- (DComm3 (TriIsoInv I1)) in comm2.
    rewrite <- assoc. rewrite (DComm3 (TriIsoInv I2)).
    use (pre_comp_with_z_iso_inv_is_inj (TriMor_is_iso3 I1)).
    use (post_comp_with_z_iso_is_inj
           (functor_on_is_z_isomorphism (AddEquiv1 Trans) (TriMor_is_iso1 I2))).
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    rewrite <- assoc. rewrite <- functor_comp. rewrite <- functor_comp.
    cbn. rewrite (is_inverse_in_precat2 (TriMor_is_iso1 I2)). rewrite functor_id.
    rewrite id_right. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite (is_inverse_in_precat2 (TriMor_is_iso3 I1)). rewrite id_left.
    rewrite <- comm2. rewrite functor_comp. rewrite assoc. apply idpath.
  Qed.

  Definition DExtIso {PT : PreTriangData} {D1 D2 : DTri} (D1' D2' : Tri)
             (I1 : TriIso D1 D1') (I2 : TriIso D2 D2')
             {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2} (H : f1 · Mor1 D2 = Mor1 D1 · f2)
             (h : Ob3 D1' --> Ob3 D2')
             (comm1 : Mor2 D1' · h = MPMor2 (TriIsoInv I1) · f2 · MPMor2 I2 · Mor2 D2')
             (comm2 : Mor3 D1' · (# (AddEquiv1 (@Trans PT))
                                     (MPMor1 (TriIsoInv I1) · f1 · MPMor1 I2)) = h · Mor3 D2') :
    TExt H.
  Proof.
    use mk_TExt.
    - exact (MPMor3 I1 · h · MPMor3 (TriIsoInv I2)).
    - exact (DExtIso_Comm1 D1' D2' I1 I2 H h comm1 comm2).
    - exact (DExtIso_Comm2 D1' D2' I1 I2 H h comm1 comm2).
  Defined.

End Ext_isomorphisms.


(** ** Change triangles in octa using isomorphisms *)
Section Octa_isomorphisms.

  Lemma OctaIsoMPMorMors {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
             (H3 : isDTri (mk_Tri (f1 · g1) h2 h3))
             {x1' x2' y1' y2' z1' z2' : ob PT}
             {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
             {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
             {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
             (H1' : isDTri (mk_Tri f1' f2' f3')) (H2' : isDTri (mk_Tri g1' g2' g3'))
             (H3' : isDTri (mk_Tri (f1' · g1') h2' h3'))
             (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
             (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
             (I3 : TriIso (mk_Tri (f1 · g1) h2 h3) (mk_Tri (f1' · g1') h2' h3'))
             (II12 : MPMor1 I2 = MPMor2 I1) (II13 : MPMor1 I1 = MPMor1 I3)
             (II23 : MPMor2 I2 = MPMor2 I3) (O : Octa H1' H2' H3') :
    MPMorMors
      (mk_MorphismPair (MPMor3 I1 · OctaMor1 O · is_z_isomorphism_mor (TriMor_is_iso3 I3))
                       (MPMor3 I3 · OctaMor2 O · is_z_isomorphism_mor (TriMor_is_iso3 I2)))
      (mk_MorphismPair (dirprod_pr1 (pr1 O)) (dirprod_pr2 (pr1 O))).
  Proof.
    use mk_MPMorMors.
    - exact (MPMor3 I1).
    - exact (MPMor3 I3).
    - exact (MPMor3 I2).
  Defined.

  Lemma OctaIsoMorComms {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
        {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
        {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
        {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
        (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
        (H3 : isDTri (mk_Tri (f1 · g1) h2 h3))
        {x1' x2' y1' y2' z1' z2' : ob PT}
        {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
        {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
        {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
        (H1' : isDTri (mk_Tri f1' f2' f3')) (H2' : isDTri (mk_Tri g1' g2' g3'))
        (H3' : isDTri (mk_Tri (f1' · g1') h2' h3'))
        (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
        (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
        (I3 : TriIso (mk_Tri (f1 · g1) h2 h3) (mk_Tri (f1' · g1') h2' h3'))
        (II12 : MPMor1 I2 = MPMor2 I1) (II13 : MPMor1 I1 = MPMor1 I3)
        (II23 : MPMor2 I2 = MPMor2 I3) (O : Octa H1' H2' H3') :
    MPMorComms (OctaIsoMPMorMors H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 II13 II23 O).
  Proof.
    use mk_MPMorComms.
    - cbn. rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition.
      set (tmp := is_inverse_in_precat2 (TriMor_is_iso3 I3)).
      apply (maponpaths (compose (OctaMor1 O))) in tmp.
      use (pathscomp0 _ (! tmp)). clear tmp.
      rewrite id_right. apply idpath.
    - cbn. rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition.
      set (tmp := is_inverse_in_precat2 (TriMor_is_iso3 I2)).
      apply (maponpaths (compose (OctaMor2 O))) in tmp.
      use (pathscomp0 _ (! tmp)). clear tmp.
      rewrite id_right. apply idpath.
  Qed.

  Lemma OctaIsoMorComm3 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
        {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
        {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
        {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
        (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
        (H3 : isDTri (mk_Tri (f1 · g1) h2 h3))
        {x1' x2' y1' y2' z1' z2' : ob PT}
        {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
        {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
        {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
        (H1' : isDTri (mk_Tri f1' f2' f3')) (H2' : isDTri (mk_Tri g1' g2' g3'))
        (H3' : isDTri (mk_Tri (f1' · g1') h2' h3'))
        (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
        (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
        (I3 : TriIso (mk_Tri (f1 · g1) h2 h3) (mk_Tri (f1' · g1') h2' h3'))
        (II12 : MPMor1 I2 = MPMor2 I1) (II13 : MPMor1 I1 = MPMor1 I3)
        (II23 : MPMor2 I2 = MPMor2 I3) (O : Octa H1' H2' H3') :
    MPMor3 I2 · (g3' · # (AddEquiv1 Trans) f2') =
    g3 · # (AddEquiv1 Trans) f2 · # (AddEquiv1 Trans) (MPMor3 I1).
  Proof.
    cbn. rewrite assoc.
    set (tmp := DComm3 I2). cbn in tmp. rewrite tmp. clear tmp.
    rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    rewrite <- functor_comp. rewrite <- functor_comp. apply maponpaths.
    set (tmp := MPComm2 I1). cbn in tmp. rewrite <- tmp. apply cancel_postcomposition.
    exact II12.
  Qed.

  Definition OctaIsoComm1 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
             (H3 : isDTri (mk_Tri (f1 · g1) h2 h3))
             {x1' x2' y1' y2' z1' z2' : ob PT}
             {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
             {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
             {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
             (H1' : isDTri (mk_Tri f1' f2' f3')) (H2' : isDTri (mk_Tri g1' g2' g3'))
             (H3' : isDTri (mk_Tri (f1' · g1') h2' h3'))
             (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
             (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
             (I3 : TriIso (mk_Tri (f1 · g1) h2 h3) (mk_Tri (f1' · g1') h2' h3'))
             (II12 : MPMor1 I2 = MPMor2 I1) (II13 : MPMor1 I1 = MPMor1 I3)
             (II23 : MPMor2 I2 = MPMor2 I3) (O : Octa H1' H2' H3') :
    MPMor3 I1 · OctaMor1 O · is_z_isomorphism_mor (TriMor_is_iso3 I3) · h3 = f3.
  Proof.
    set (tmp := DComm3 (TriIsoInv I3)). cbn in tmp. rewrite <- assoc.
    cbn. rewrite tmp. clear tmp.
    rewrite assoc. rewrite <- (assoc _ (OctaMor1 O)). rewrite (OctaComm1 O).
    set (tmp := DComm3 I1). cbn in tmp. rewrite tmp. clear tmp.
    rewrite <- assoc. rewrite <- functor_comp. cbn in II13. rewrite II13.
    set (tmp := is_inverse_in_precat1 (TriMor_is_iso1 I3)). cbn in tmp.
    rewrite tmp. clear tmp. rewrite functor_id. apply id_right.
  Qed.

  Definition OctaIsoComm2 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
             (H3 : isDTri (mk_Tri (f1 · g1) h2 h3))
             {x1' x2' y1' y2' z1' z2' : ob PT}
             {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
             {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
             {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
             (H1' : isDTri (mk_Tri f1' f2' f3')) (H2' : isDTri (mk_Tri g1' g2' g3'))
             (H3' : isDTri (mk_Tri (f1' · g1') h2' h3'))
             (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
             (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
             (I3 : TriIso (mk_Tri (f1 · g1) h2 h3) (mk_Tri (f1' · g1') h2' h3'))
             (II12 : MPMor1 I2 = MPMor2 I1) (II13 : MPMor1 I1 = MPMor1 I3)
             (II23 : MPMor2 I2 = MPMor2 I3) (O : Octa H1' H2' H3') :
    h2 · (MPMor3 I3 · OctaMor2 O · is_z_isomorphism_mor (TriMor_is_iso3 I2)) = g2.
  Proof.
    rewrite assoc. rewrite assoc. set (tmp := MPComm2 I3). cbn in tmp.
    cbn. rewrite <- tmp. clear tmp. rewrite <- (assoc _ h2'). rewrite (OctaComm2 O).
    set (tmp := MPComm2 (TriIsoInv I2)). cbn in tmp.
    rewrite <- (assoc _ g2'). rewrite <- tmp. clear tmp. rewrite assoc.
    cbn in II23. rewrite <- II23.
    set (tmp := is_inverse_in_precat1 (TriMor_is_iso2 I2)). cbn in tmp.
    rewrite tmp. clear tmp. apply id_left.
  Qed.

  Definition OctaIsoComm3 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
             (H3 : isDTri (mk_Tri (f1 · g1) h2 h3))
             {x1' x2' y1' y2' z1' z2' : ob PT}
             {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
             {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
             {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
             (H1' : isDTri (mk_Tri f1' f2' f3')) (H2' : isDTri (mk_Tri g1' g2' g3'))
             (H3' : isDTri (mk_Tri (f1' · g1') h2' h3'))
             (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
             (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
             (I3 : TriIso (mk_Tri (f1 · g1) h2 h3) (mk_Tri (f1' · g1') h2' h3'))
             (II12 : MPMor1 I2 = MPMor2 I1) (II13 : MPMor1 I1 = MPMor1 I3)
             (II23 : MPMor2 I2 = MPMor2 I3) (O : Octa H1' H2' H3') :
    f2 · (MPMor3 I1 · OctaMor1 O · is_z_isomorphism_mor (TriMor_is_iso3 I3)) = g1 · h2.
  Proof.
    cbn. rewrite assoc. rewrite assoc.
    set (tmp := MPComm2 I1). cbn in tmp. rewrite <- tmp. clear tmp.
    set (tmp := OctaComm3 O). rewrite <- (assoc _ f2'). rewrite tmp. clear tmp.
    rewrite assoc.
    set (tmp := MPComm1 I2). cbn in tmp. cbn in II12. rewrite <- II12. rewrite tmp. clear tmp.
    rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    cbn in II23. rewrite II23. rewrite assoc.
    set (tmp := MPComm2 I3). cbn in tmp. rewrite tmp. clear tmp.
    rewrite <- assoc. set (tmp := is_inverse_in_precat1 (TriMor_is_iso3 I3)). cbn in tmp.
    rewrite tmp. apply id_right.
  Qed.

  Definition OctaIsoComm4 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
             (H3 : isDTri (mk_Tri (f1 · g1) h2 h3))
             {x1' x2' y1' y2' z1' z2' : ob PT}
             {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
             {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
             {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
             (H1' : isDTri (mk_Tri f1' f2' f3')) (H2' : isDTri (mk_Tri g1' g2' g3'))
             (H3' : isDTri (mk_Tri (f1' · g1') h2' h3'))
             (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
             (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
             (I3 : TriIso (mk_Tri (f1 · g1) h2 h3) (mk_Tri (f1' · g1') h2' h3'))
             (II12 : MPMor1 I2 = MPMor2 I1) (II13 : MPMor1 I1 = MPMor1 I3)
             (II23 : MPMor2 I2 = MPMor2 I3) (O : Octa H1' H2' H3') :
    MPMor3 I3 · OctaMor2 O · is_z_isomorphism_mor (TriMor_is_iso3 I2) · g3 =
    h3 · # (AddEquiv1 Trans) f1.
  Proof.
    rewrite <- assoc.
    set (tmp := DComm3 (TriIsoInv I2)). cbn in tmp. cbn. rewrite tmp. clear tmp.
    set (tmp := OctaComm4 O). rewrite <- (assoc _ (OctaMor2 O)). rewrite (assoc (OctaMor2 O)).
    rewrite tmp. clear tmp. rewrite <- assoc. rewrite <- functor_comp.
    set (tmp := MPComm1 (TriIsoInv I1)). cbn in tmp.
    assert (e : is_z_isomorphism_mor (TriMor_is_iso1 I2) =
                is_z_isomorphism_mor (TriMor_is_iso2 I1)).
    {
      use is_z_isomorphism_mor_eq. exact II12.
    }
    cbn in e. rewrite e. clear e. rewrite <- tmp. clear tmp.
    rewrite functor_comp. rewrite assoc. rewrite assoc. apply cancel_postcomposition.
    set (tmp := DComm3 I3). cbn in tmp. rewrite tmp. clear tmp.
    cbn. use (pathscomp0 _ (id_right _)). rewrite <- assoc. apply cancel_precomposition.
    rewrite <- functor_id.
    use (pathscomp0 (! (functor_comp (AddEquiv1 Trans) _ _))). apply maponpaths.
    cbn in II13. rewrite <- II13.
    exact (is_inverse_in_precat1 (TriMor_is_iso1 I1)).
  Qed.

  Definition OctaIso {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
             (H3 : isDTri (mk_Tri (f1 · g1) h2 h3))
             {x1' x2' y1' y2' z1' z2' : ob PT}
             {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
             {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
             {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
             (H1' : isDTri (mk_Tri f1' f2' f3')) (H2' : isDTri (mk_Tri g1' g2' g3'))
             (H3' : isDTri (mk_Tri (f1' · g1') h2' h3'))
             (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
             (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
             (I3 : TriIso (mk_Tri (f1 · g1) h2 h3) (mk_Tri (f1' · g1') h2' h3'))
             (II12 : MPMor1 I2 = MPMor2 I1) (II13 : MPMor1 I1 = MPMor1 I3)
             (II23 : MPMor2 I2 = MPMor2 I3) (O : Octa H1' H2' H3') :
    Octa H1 H2 H3.
  Proof.
    use mk_Octa.
    - exact (MPMor3 I1 · OctaMor1 O · is_z_isomorphism_mor (TriMor_is_iso3 (TriIso_is_iso I3))).
    - exact (MPMor3 I3 · OctaMor2 O · is_z_isomorphism_mor (TriMor_is_iso3 (TriIso_is_iso I2))).
    - use (DTrisUnderIso PT (OctaDTri O) _ _ (DTriisDTri (OctaDTri O))).
      use hinhpr.
      use TriIsoInv.
      use mk_TriIso.
      + use mk_TriMor.
        * use mk_MPMor.
          -- exact (OctaIsoMPMorMors H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 II13 II23 O).
          -- exact (OctaIsoMorComms H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 II13 II23 O).
        * exact (OctaIsoMorComm3 H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 II13 II23 O).
      + use mk_TriMor_is_iso.
        * exact (TriMor_is_iso3 I1).
        * exact (TriMor_is_iso3 I3).
        * exact (TriMor_is_iso3 I2).
    - exact (OctaIsoComm1 H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 II13 II23 O).
    - exact (OctaIsoComm2 H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 II13 II23 O).
    - exact (OctaIsoComm3 H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 II13 II23 O).
    - exact (OctaIsoComm4 H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 II13 II23 O).
  Defined.

End Octa_isomorphisms.
