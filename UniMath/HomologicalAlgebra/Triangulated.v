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
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

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
Require Import UniMath.CategoryTheory.category_abgr.

Require Import UniMath.CategoryTheory.precategoriesWithBinOps.
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
                                X  -f-> Y  -g-> Z  -h->  X[1]
                             φ1 |    φ2 |   φ3 |    φ1[1] |
                                X' -f-> Y' -g-> Z' -h-> X'[1].
      Such a commutative diagram is called a morphism of triangles.
(TR6) (Octahedral axiom). Suppose you have 3 distinguished triangles (X1, Y1, Z2, f, g, h),
      (Y1, Z1, X2, f', g', h'), and (X1, Z1, Y2, f ;; f', g'', h''). Then there exists a
      distinguished triangle (Z2, Y2, X2, f''', g''', h' ;; g[1]) such that g ;; g''' = f' ;; g''
      and h''' ;; h' = h'' ;; f.

We call the data for triangulated category which satisfies (TR1)-(TR5) a pretriangulated category.

We formulate triangulated categories as follows. To every morphisms f in the underlying additive
category A we associate a mapping cone C(f). This corresponds the axiom (TR4). Next, we define
a distinguished triangle to be a triangle such that there exists an isomorphism to a triangle
of the form (f, in2, pr1, X, Y, C(f)). This is equivalent to TR2 by using (TR5) and the five lemma
for triangulated categories. Thus, our definition of pretriangulated category says that
- Rotations and inverse rotations of distinguished triangles are distinguished. (TR3)
- Every commutative square of distinguished triangles can be completed to a morphism of
  distinguished triangle. (TR5)

Formalization of (TR6), the octahedral axiom, is the same as above.
 *)


(** * Basic notions *)
(** ** Introduction
We define triangles, morphisms of triangles, rotations, inverse rotations, and cones of morphisms.
*)
Section def_triangles.

  Context {A : Additive}.
  Context {T : AddEquiv A A}.

  (** ** Triangles *)
  Definition Tri : UU := Σ MP : MorphismPair, A⟦Ob3 MP, (AddEquiv1 T) (Ob1 MP)⟧.

  Definition mk_Tri {x y z : ob A} (f : x --> y) (g : y --> z) (h : A⟦z, (AddEquiv1 T x)⟧) : Tri :=
    (mk_MorphismPair f g),,h.

  Definition TriMP (D : Tri) : MorphismPair := pr1 D.
  Coercion TriMP : Tri >-> MorphismPair.

  (** Follows the naming convention Mor1, Mor2, for MorphismPair *)
  Definition Mor3 (D : Tri) : A⟦Ob3 D, (AddEquiv1 T) (Ob1 D)⟧ := pr2 D.

  Definition TriMor (D1 D2 : Tri) : UU :=
    Σ (M : MPMor D1 D2), (MPMor3 M) ;; (Mor3 D2) = (Mor3 D1) ;; (# (AddEquiv1 T) (MPMor1 M)).

  Definition mk_TriMor {D1 D2 : Tri} (M : MPMor D1 D2)
             (H : (MPMor3 M) ;; (Mor3 D2) = (Mor3 D1) ;; (# (AddEquiv1 T) (MPMor1 M))) :
    TriMor D1 D2 := (M,,H).

  Definition TriMor_Mors {D1 D2 : Tri} (DTM : TriMor D1 D2) : MPMor D1 D2 := pr1 DTM.
  Coercion TriMor_Mors : TriMor >-> MPMor.

  Local Lemma TriMorId_comms {x y : ob A} (f : x --> y) : identity x ;; f = f ;; identity y.
  Proof.
    rewrite id_left. rewrite id_right. apply idpath.
  Qed.

  Local Lemma TriMorId_comm3 (D : Tri) :
    identity (Ob3 D) ;; Mor3 D = Mor3 D ;; # (AddEquiv1 T) (identity (Ob1 D)).
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
    (MPMor3 TM) ;; (Mor3 D2) = (Mor3 D1) ;; (# (AddEquiv1 T) (MPMor1 TM)) := pr2 TM.

  (** The fourth morphism is automatically an ismorphism because functors preserve isomorphisms *)
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
         (TriMor_is_iso_to_inv_Comm Ti)) ;; Mor3 D1 =
    (Mor3 D2)
      ;; (# (AddEquiv1 T)
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

  Definition TriIso (D1 D2 : Tri) : UU := Σ M : TriMor D1 D2, TriMor_is_iso M.

  Definition mk_TriIso {D1 D2 : Tri} (M : TriMor D1 D2) (H : TriMor_is_iso M) : TriIso D1 D2 :=
    (M,,H).

  Definition TriIsoMor {D1 D2 : Tri} (I : TriIso D1 D2) : TriMor D1 D2 := pr1 I.
  Coercion TriIsoMor : TriIso >-> TriMor.

  Definition TriIso_is_iso {D1 D2 : Tri} (I : TriIso D1 D2) : TriMor_is_iso I := pr2 I.


  (** ** Trivial triangle, rotated triangle, and inv rotated triangle *)

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
    - exact (to_inv (# (AddEquiv2 T) (Mor3 D)) ;; (z_iso_inv_mor (AddEquivUnitIso T (Ob1 D)))).
    - exact (Mor1 D).
    - exact (Mor2 D ;; (z_iso_inv_mor (AddEquivCounitIso T (Ob3 D)))).
  Defined.

  (** ** Mapping Cones *)

  Definition MCone {A : Additive} (T : AddEquiv A A) (x y : ob A) : UU :=
    Σ (z : ob A), A⟦y, z⟧ × A⟦z, (AddEquiv1 T x)⟧.

  Definition mk_MCone {A : Additive} (T : AddEquiv A A) {x y z : ob A} (g : y --> z)
             (h : z --> (AddEquiv1 T x)) : MCone T x y := (z,,(g,,h)).

  Definition MConeOb {A : Additive} {T : AddEquiv A A} {x y : ob A} (C : MCone T x y) :
    ob A := pr1 C.
  Coercion MConeOb : MCone >-> ob.

  Definition MCone1 {A : Additive} {T : AddEquiv A A} {x y : ob A} (C : MCone T x y) :
    A⟦y, C⟧ := dirprod_pr1 (pr2 C).

  Definition MCone2 {A : Additive} {T : AddEquiv A A} {x y : ob A} (C : MCone T x y) :
    A⟦C, (AddEquiv1 T x)⟧ := dirprod_pr2 (pr2 C).

End def_triangles.


(** * Data for pretriangulated *)
(** ** Introduction
We define data needed to define pretriangulated categories.
*)
Section def_pretriang_data.

  (** ** PreTriangData *)

  Definition PreTriangData : UU :=
    Σ D : (Σ D' : (Σ A : (Additive), (AddEquiv A A) × (Π (x y : ob A) (f : x --> y), UU)),
                  Π (x y : ob (pr1 D')) (f : x --> y), ishinh (dirprod_pr2 (pr2 D') x y f)),
          Π (x y : ob (pr1 (pr1 D))) (f : x --> y) (f' : dirprod_pr2 (pr2 (pr1 D)) x y f),
          MCone (dirprod_pr1 (pr2 (pr1 D))) x y.

  Definition mk_PreTriangData (A : Additive) (T : AddEquiv A A)
             (P : Π (x y : ob A) (f : x --> y), UU)
             (H1 : Π (x y : ob A) (f : x --> y), ishinh (P x y f))
             (H2 : Π (x y : ob A) (f : x --> y) (f' : P x y f), MCone T x y) : PreTriangData.
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * exact A.
        * use tpair.
          -- exact T.
          -- exact P.
      + exact H1.
    - exact H2.
  Defined.

  Definition PreTriangData_Additive (PTD : PreTriangData) : Additive := pr1 (pr1 (pr1 PTD)).
  Coercion PreTriangData_Additive : PreTriangData >-> Additive.

  Definition Trans {PTD : PreTriangData} : AddEquiv PTD PTD := dirprod_pr1 (pr2 (pr1 (pr1 PTD))).

  Definition ConePropType {PTD : PreTriangData} :
    Π (x y : ob PTD) (f : x --> y), UU := dirprod_pr2 (pr2 (pr1 (pr1 PTD))).

  Definition ConeProp {PTD : PreTriangData} :
    Π (x y : ob PTD) (f : x --> y), ishinh (ConePropType x y f) := pr2 (pr1 (PTD)).

  Definition MConeOf {PTD : PreTriangData} {x y : ob PTD} (f : x --> y) (f' : ConePropType x y f) :
    MCone Trans x y := (pr2 PTD) x y f f'.

End def_pretriang_data.


(** * Distinguished triangles *)
(** ** Inroduction
We define distinguished triangles, extensions of morphisms, and lemmas which are used to prove that
K(A) is pretriangulated.
*)
Section def_pretriangulated_data.

  Definition ConeTri {PTD : PreTriangData} {x y : ob PTD} (f : x --> y) (Cf : MCone Trans x y) :
    @Tri _ (@Trans PTD).
  Proof.
    use mk_Tri.
    - exact x.
    - exact y.
    - exact Cf.
    - exact f.
    - exact (MCone1 Cf).
    - exact (MCone2 Cf).
  Defined.

  (** Isomorphism to a cone triangle *)
  Definition ConeIso {PTD : PreTriangData} (T : Tri) (M : Morphism) : UU :=
    Σ D : (Σ (f' : ConePropType (Source M) (Target M) M),
           TriMor T (ConeTri M (@MConeOf PTD _ _ M f'))), TriMor_is_iso (pr2 D).

  Definition mk_ConeIso {PTD : PreTriangData} {T : Tri} {x y : ob PTD} {f : x --> y}
             (f' : ConePropType x y f) (M : TriMor T (ConeTri f (@MConeOf PTD _ _ f f')))
             (I : TriMor_is_iso M) : ConeIso T (mk_Morphism f) := ((f',,M),,I).

  Definition ConeIsoFiber {PTD : PreTriangData} {T : Tri} {M : Morphism} (CI : ConeIso T M) :
    @ConePropType PTD (Source M) (Target M) M := pr1 (pr1 CI).

  Definition ConeIsoTri {PTD : PreTriangData} {T : Tri} {M : Morphism} (CI : ConeIso T M) :
    Tri := ConeTri M (@MConeOf PTD _ _ M (ConeIsoFiber CI)).

  Definition ConeIsoMor {PTD : PreTriangData} {T : Tri} {M : Morphism} (CI : ConeIso T M) :
    TriMor T (ConeTri M (@MConeOf PTD _ _ M (ConeIsoFiber CI))) := pr2 (pr1 CI).

  Definition ConeIsoMor_is_iso {PTD : PreTriangData} {T : Tri} {M : Morphism} (CI : ConeIso T M) :
    TriMor_is_iso (@ConeIsoMor PTD _ _ CI) := pr2 CI.

  Definition ConeIsoMorInv {PTD : PreTriangData} {T : Tri} {M : Morphism} (CI : ConeIso T M) :
    TriMor (ConeTri M (@MConeOf PTD _ _ M (ConeIsoFiber CI))) T :=
    TriMor_is_iso_inv (ConeIsoMor_is_iso CI).

  Definition ConeIsoMorInv_is_iso {PTD : PreTriangData} {T : Tri} {M : Morphism} (CI : ConeIso T M) :
    TriMor_is_iso (ConeIsoMorInv CI) := TriMor_is_iso_inv_is_iso (@ConeIsoMor_is_iso PTD _ _ CI).

  (** ** Distinguished triangles *)

  Definition DTri {PTD : PreTriangData} : UU :=
    Σ (T : @Tri _ (@Trans PTD)), ∥ Σ M : Morphism, ∥ ConeIso T M ∥ ∥.

  Definition mk_DTri {PTD : PreTriangData} {x y z : ob PTD} (f : x --> y) (g : y --> z)
             (h : z --> (AddEquiv1 Trans x))
             (H : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f g h) M ∥ ∥) : DTri := ((mk_Tri f g h),,H).

  Definition mk_DTri' {PTD : PreTriangData} (T : @Tri _ (@Trans PTD))
             (H : ∥ Σ M : Morphism, ∥ ConeIso T M ∥ ∥) : DTri := (T,,H).

  Definition DTriTri {PTD : PreTriangData} (D : @DTri PTD) : Tri := pr1 D.
  Coercion DTriTri : DTri >-> Tri.

  Definition DTriIso {PTD : PreTriangData} (D : @DTri PTD) :
    ∥ Σ M : Morphism, ∥ ConeIso D M ∥ ∥ := pr2 D.

  Definition ConeDTri {PTD : PreTriangData} {x y : ob PTD} (f : x --> y) (f' : ConePropType x y f)
             (Cf : MCone Trans x y) :
    @DTri PTD.
  Proof.
    use mk_DTri'.
    - exact (ConeTri f (MConeOf f f')).
    - intros P X. apply X. clear P X.
      use tpair.
      + exact (Morphisms.mk_Morphism f).
      + intros P X. apply X. clear P X.
        use mk_ConeIso.
        * exact f'.
        * exact (TriMorId _).
        * use mk_TriMor_is_iso.
          -- exact (is_z_isomorphism_identity _).
          -- exact (is_z_isomorphism_identity _).
          -- exact (is_z_isomorphism_identity _).
  Defined.

  Context {PTD : PreTriangData}.

  (** **  Extension of a commutative square of distinguished triangles to morphism *)

  Definition TExt {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             (H : f1 ;; Mor1 D2 = Mor1 D1 ;; f2) : UU :=
    Σ f3 : Ob3 D1 --> Ob3 D2, (Mor2 D1 ;; f3 = f2 ;; Mor2 D2)
                              × (Mor3 D1 ;; (# (AddEquiv1 (@Trans PTD)) f1) = f3 ;; Mor3 D2).

  Definition mk_TExt {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             {H : f1 ;; Mor1 D2 = Mor1 D1 ;; f2} (f3 : Ob3 D1 --> Ob3 D2)
             (H2 : Mor2 D1 ;; f3 = f2 ;; Mor2 D2)
             (H3 : Mor3 D1 ;; (# (AddEquiv1 (@Trans PTD)) f1) = f3 ;; Mor3 D2) :
    TExt H := (f3,,(H2,,H3)).

  Definition TExt_Mor {D1 D2 : DTri} {f1 : Ob1 (DTriTri D1) --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             {H : f1 ;; Mor1 D2 = Mor1 D1 ;; f2} (TE : TExt H) : PTD⟦Ob3 D1, Ob3 D2⟧ := pr1 TE.
  Coercion TExt_Mor : TExt >-> precategory_morphisms.

  Definition TExtComm1 {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             {H : f1 ;; Mor1 D2 = Mor1 D1 ;; f2} (TE : TExt H) :
    Mor2 D1 ;; TE = f2 ;; Mor2 D2 := dirprod_pr1 (pr2 TE).

  Definition TExtComm2 {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             {H : f1 ;; Mor1 D2 = Mor1 D1 ;; f2} (TE : TExt H) :
    (Mor3 D1 ;; (# (AddEquiv1 Trans) f1) = TE ;; Mor3 D2) := dirprod_pr2 (pr2 TE).

  Definition TExtMor {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             {H : f1 ;; Mor1 D2 = Mor1 D1 ;; f2} (TE : TExt H) : TriMor D1 D2.
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


  (** ** The following is used to prove rotations of DTris in K(A) *)
  Definition mk_RotDTris_MPMorMors (D : DTri) (M1 : Morphism) (I1 : ConeIso D M1)
             (M2 : Morphism) (M2' : ConePropType (Source M2) (Target M2) M2)
             (f1 : PTD⟦Ob1 (RotTri (ConeIsoTri I1)), Source M2⟧)
             (f2 : PTD⟦Ob2 (RotTri (ConeIsoTri I1)), Target M2⟧)
             (f3 : PTD⟦Ob3 (RotTri (ConeIsoTri I1)), (MConeOf M2 M2')⟧) :
    MPMorMors (RotTri D) (ConeTri M2 (MConeOf M2 M2')).
  Proof.
    use mk_MPMorMors.
    - exact ((MPMor2 (ConeIsoMor I1)) ;; f1).
    - exact ((MPMor3 (ConeIsoMor I1)) ;; f2).
    - exact (# (AddEquiv1 Trans) (MPMor1 (ConeIsoMor I1)) ;; f3).
  Defined.

  Lemma mk_RotDTris_MPMorComms (D : DTri) (M1 : Morphism) (I1 : ConeIso D M1)
        (M2 : Morphism) (M2' : ConePropType (Source M2) (Target M2) M2)
        (f1 : PTD⟦Ob1 (RotTri (ConeIsoTri I1)), Source M2⟧)
        (f2 : PTD⟦Ob2 (RotTri (ConeIsoTri I1)), Target M2⟧)
        (f3 : PTD⟦Ob3 (RotTri (ConeIsoTri I1)), (MConeOf M2 M2')⟧)
        (is1 : is_z_isomorphism f1) (is2 : is_z_isomorphism f2)
        (is3 : is_z_isomorphism f3)
        (H1 : Mor1 (RotTri (ConeIsoTri I1)) ;; f2 = f1 ;; M2)
        (H2 : Mor2 (RotTri (ConeIsoTri I1)) ;; f3 = f2 ;; MCone1 (MConeOf M2 M2'))
        (H3 : Mor3 (RotTri (ConeIsoTri I1)) ;; (# (AddEquiv1 Trans) f1) =
              f3 ;; MCone2 (MConeOf M2 M2')) :
    MPMorComms (mk_RotDTris_MPMorMors D M1 I1 M2 M2' f1 f2 f3).
  Proof.
    use mk_MPMorComms.
    - apply (maponpaths (compose (MPMor2 (ConeIsoMor I1)))) in H1.
      rewrite assoc in H1. rewrite assoc in H1. use (pathscomp0 (! H1)). clear H1.
      cbn. rewrite assoc. apply cancel_postcomposition. exact (MPComm2 (ConeIsoMor I1)).
    - apply (maponpaths (compose (MPMor3 (ConeIsoMor I1)))) in H2.
      rewrite assoc in H2. rewrite assoc in H2. use (pathscomp0 (! H2)). clear H2.
      cbn. rewrite assoc. apply cancel_postcomposition. exact (DComm3 (ConeIsoMor I1)).
  Qed.

  Lemma mk_RotDTris_DComm3 (D : DTri) (M1 : Morphism) (I1 : ConeIso D M1)
        (M2 : Morphism) (M2' : ConePropType (Source M2) (Target M2) M2)
        (f1 : PTD⟦Ob1 (RotTri (ConeIsoTri I1)), Source M2⟧)
        (f2 : PTD⟦Ob2 (RotTri (ConeIsoTri I1)), Target M2⟧)
        (f3 : PTD⟦Ob3 (RotTri (ConeIsoTri I1)), (MConeOf M2 M2')⟧)
        (is1 : is_z_isomorphism f1) (is2 : is_z_isomorphism f2)
        (is3 : is_z_isomorphism f3)
        (H1 : Mor1 (RotTri (ConeIsoTri I1)) ;; f2 = f1 ;; M2)
        (H2 : Mor2 (RotTri (ConeIsoTri I1)) ;; f3 = f2 ;; MCone1 (MConeOf M2 M2'))
        (H3 : Mor3 (RotTri (ConeIsoTri I1)) ;; (# (AddEquiv1 Trans) f1) =
              f3 ;; MCone2 (MConeOf M2 M2')) :
    # (AddEquiv1 Trans) (MPMor1 (ConeIsoMor I1)) ;; f3 ;; MCone2 (MConeOf M2 M2') =
    to_inv (# (AddEquiv1 Trans) (Mor1 D)) ;; # (AddEquiv1 Trans) (MPMor2 (ConeIsoMor I1) ;; f1).
  Proof.
    apply (maponpaths (fun gg : _ => # (AddEquiv1 Trans) (MPMor1 (ConeIsoMor I1)) ;; gg)) in H3.
    rewrite assoc in H3. rewrite assoc in H3. use (pathscomp0 (! H3)). clear H3.
    rewrite functor_comp. rewrite assoc. apply cancel_postcomposition.
    cbn. rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp. apply maponpaths.
    rewrite <- functor_comp. rewrite <- functor_comp. apply maponpaths.
    exact (MPComm1 (ConeIsoMor I1)).
  Qed.

  Lemma mk_RotDTris (D : DTri) (M1 : Morphism) (I1 : ConeIso D M1)
        (M2 : Morphism) (M2' : ConePropType (Source M2) (Target M2) M2)
        (f1 : PTD⟦Ob1 (RotTri (ConeIsoTri I1)), Source M2⟧)
        (f2 : PTD⟦Ob2 (RotTri (ConeIsoTri I1)), Target M2⟧)
        (f3 : PTD⟦Ob3 (RotTri (ConeIsoTri I1)), (MConeOf M2 M2')⟧)
        (is1 : is_z_isomorphism f1) (is2 : is_z_isomorphism f2)
        (is3 : is_z_isomorphism f3)
        (H1 : Mor1 (RotTri (ConeIsoTri I1)) ;; f2 = f1 ;; M2)
        (H2 : Mor2 (RotTri (ConeIsoTri I1)) ;; f3 = f2 ;; MCone1 (MConeOf M2 M2'))
        (H3 : Mor3 (RotTri (ConeIsoTri I1)) ;; (# (AddEquiv1 Trans) f1) =
              f3 ;; MCone2 (MConeOf M2 M2')) :
    ∥ Σ M : Morphisms.Morphism, ∥ @ConeIso PTD (RotTri D) M ∥ ∥.
  Proof.
    intros P X. apply X. clear P X.
    use tpair.
    - exact M2.
    - intros P X. apply X. clear P X.
      use mk_ConeIso.
      + exact M2'.
      + use mk_TriMor.
        * use mk_MPMor.
          -- exact (mk_RotDTris_MPMorMors D M1 I1 M2 M2' f1 f2 f3).
          -- exact (mk_RotDTris_MPMorComms D M1 I1 M2 M2' f1 f2 f3 is1 is2 is3 H1 H2 H3).
        * exact (mk_RotDTris_DComm3 D M1 I1 M2 M2' f1 f2 f3 is1 is2 is3 H1 H2 H3).
      + use mk_TriMor_is_iso.
        * use is_z_isomorphism_comp.
          -- exact (TriMor_is_iso2 (ConeIsoMor_is_iso I1)).
          -- exact is1.
        * use is_z_isomorphism_comp.
          -- exact (TriMor_is_iso3 (ConeIsoMor_is_iso I1)).
          -- exact is2.
        * use is_z_isomorphism_comp.
          -- exact (functor_on_is_z_isomorphism
                      (AddEquiv1 Trans) (TriMor_is_iso1 (ConeIsoMor_is_iso I1))).
          -- exact is3.
  Qed.

  (** ** The following is used to prove inverse rotations of DTris in K(A) *)

  Definition mk_InvRotDTris_MPMorMors (D : DTri) (M1 : Morphism) (I1 : ConeIso D M1)
        (M2 : Morphism) (M2' : ConePropType (Source M2) (Target M2) M2)
        (f1 : PTD⟦Ob1 (InvRotTri (ConeIsoTri I1)), Source M2⟧)
        (f2 : PTD⟦Ob2 (InvRotTri (ConeIsoTri I1)), Target M2⟧)
        (f3 : PTD⟦Ob3 (InvRotTri (ConeIsoTri I1)), (MConeOf M2 M2')⟧) :
    MPMorMors (InvRotTri D) (ConeTri M2 (MConeOf M2 M2')).
  Proof.
    use mk_MPMorMors.
    - exact (# (AddEquiv2 Trans) (MPMor3 (ConeIsoMor I1)) ;; f1).
    - exact ((MPMor1 (ConeIsoMor I1)) ;; f2).
    - exact ((MPMor2 (ConeIsoMor I1)) ;; f3).
  Defined.

  Lemma mk_InvRotDTris_MPMorComms (D : DTri) (M1 : Morphism) (I1 : ConeIso D M1)
        (M2 : Morphism) (M2' : ConePropType (Source M2) (Target M2) M2)
        (f1 : PTD⟦Ob1 (InvRotTri (ConeIsoTri I1)), Source M2⟧)
        (f2 : PTD⟦Ob2 (InvRotTri (ConeIsoTri I1)), Target M2⟧)
        (f3 : PTD⟦Ob3 (InvRotTri (ConeIsoTri I1)), (MConeOf M2 M2')⟧)
        (is1 : is_z_isomorphism f1) (is2 : is_z_isomorphism f2)
        (is3 : is_z_isomorphism f3)
        (H1 : Mor1 (InvRotTri (ConeIsoTri I1)) ;; f2 = f1 ;; M2)
        (H2 : Mor2 (InvRotTri (ConeIsoTri I1)) ;; f3 = f2 ;; MCone1 (MConeOf M2 M2'))
        (H3 : Mor3 (InvRotTri (ConeIsoTri I1)) ;; (# (AddEquiv1 Trans) f1) =
              f3 ;; MCone2 (MConeOf M2 M2')) :
    MPMorComms (mk_InvRotDTris_MPMorMors D M1 I1 M2 M2' f1 f2 f3).
  Proof.
    use mk_MPMorComms.
    - cbn. rewrite <- assoc.
      apply (maponpaths (compose (# (AddEquiv2 Trans) (MPMor3 (ConeIsoMor I1))))) in H1.
      use (pathscomp0 (! H1)). clear H1. rewrite assoc. rewrite assoc.
      apply cancel_postcomposition. cbn.
      rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
      rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp. apply maponpaths.
      rewrite assoc. rewrite <- functor_comp.
      set (tmp := DComm3 (ConeIsoMor I1)).
      apply (maponpaths (fun gg : _ => (# (AddEquiv2 Trans) gg)
                                      ;; (AddEquivUnitInvMor Trans (Source M1)))) in tmp.
      use (pathscomp0 tmp). clear tmp. rewrite functor_comp. rewrite <- assoc.
      rewrite <- assoc. apply cancel_precomposition.
      exact (! (AddEquivUnitInv Trans (MPMor1 (ConeIsoMor I1)))).
    - cbn. rewrite assoc. set (tmp := MPComm1 (ConeIsoMor I1)).
      apply (maponpaths (fun gg : _ => gg ;; f3)) in tmp.
      use (pathscomp0 _ tmp). rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. exact (! H2).
  Qed.

  Lemma InvRotDTrisComm3 (D : DTri) (M1 : Morphism) (I1 : ConeIso D M1)
        (M2 : Morphism) (M2' : ConePropType (Source M2) (Target M2) M2)
        (f1 : PTD⟦Ob1 (InvRotTri (ConeIsoTri I1)), Source M2⟧)
        (f2 : PTD⟦Ob2 (InvRotTri (ConeIsoTri I1)), Target M2⟧)
        (f3 : PTD⟦Ob3 (InvRotTri (ConeIsoTri I1)), (MConeOf M2 M2')⟧)
        (is1 : is_z_isomorphism f1) (is2 : is_z_isomorphism f2)
        (is3 : is_z_isomorphism f3)
        (H1 : Mor1 (InvRotTri (ConeIsoTri I1)) ;; f2 = f1 ;; M2)
        (H2 : Mor2 (InvRotTri (ConeIsoTri I1)) ;; f3 = f2 ;; MCone1 (MConeOf M2 M2'))
        (H3 : Mor3 (InvRotTri (ConeIsoTri I1)) ;; (# (AddEquiv1 Trans) f1) =
              f3 ;; MCone2 (MConeOf M2 M2')) :
    MPMor2 (ConeIsoMor I1) ;; f3 ;; MCone2 (MConeOf _ M2') =
    (Mor2 D)
      ;; AddEquivCounitInvMor Trans (Ob3 D)
      ;; # (AddEquiv1 Trans) (# (AddEquiv2 Trans) (MPMor3 (ConeIsoMor I1)) ;; f1).
  Proof.
    apply (maponpaths (compose (MPMor2 (ConeIsoMor I1)))) in H3.
    rewrite <- assoc. use (pathscomp0 (! H3)). clear H3.
    set (tmp := MPComm2 (ConeIsoMor I1)). cbn.
    cbn in tmp. rewrite assoc. rewrite assoc. rewrite tmp. clear tmp.
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    apply cancel_precomposition. rewrite functor_comp. rewrite assoc. rewrite assoc.
    apply cancel_postcomposition.
    exact (! (AddEquivCounitInv Trans (MPMor3 (ConeIsoMor I1)))).
  Qed.

  Lemma mk_InvRotDTris (D : DTri) (M1 : Morphism) (I1 : ConeIso D M1)
        (M2 : Morphism) (M2' : ConePropType (Source M2) (Target M2) M2)
        (f1 : PTD⟦Ob1 (InvRotTri (ConeIsoTri I1)), Source M2⟧)
        (f2 : PTD⟦Ob2 (InvRotTri (ConeIsoTri I1)), Target M2⟧)
        (f3 : PTD⟦Ob3 (InvRotTri (ConeIsoTri I1)), (MConeOf M2 M2')⟧)
        (is1 : is_z_isomorphism f1) (is2 : is_z_isomorphism f2)
        (is3 : is_z_isomorphism f3)
        (H1 : Mor1 (InvRotTri (ConeIsoTri I1)) ;; f2 = f1 ;; M2)
        (H2 : Mor2 (InvRotTri (ConeIsoTri I1)) ;; f3 = f2 ;; MCone1 (MConeOf M2 M2'))
        (H3 : Mor3 (InvRotTri (ConeIsoTri I1)) ;; (# (AddEquiv1 Trans) f1) =
              f3 ;; MCone2 (MConeOf M2 M2')) :
    ∥ Σ M : Morphism, ∥ @ConeIso PTD (InvRotTri D) M ∥ ∥.
  Proof.
    intros P X. apply X. clear P X.
    use tpair.
    - exact M2.
    - intros P X. apply X. clear P X.
      use mk_ConeIso.
      + exact M2'.
      + use mk_TriMor.
        * use mk_MPMor.
          -- exact (mk_InvRotDTris_MPMorMors D M1 I1 M2 M2' f1 f2 f3).
          -- exact (mk_InvRotDTris_MPMorComms D M1 I1 M2 M2' f1 f2 f3 is1 is2 is3 H1 H2 H3).
        * exact (InvRotDTrisComm3 D M1 I1 M2 M2' f1 f2 f3 is1 is2 is3 H1 H2 H3).
      + use mk_TriMor_is_iso.
        * use is_z_isomorphism_comp.
          -- exact (functor_on_is_z_isomorphism
                      (AddEquiv2 Trans) (TriMor_is_iso3 (ConeIsoMor_is_iso I1))).
          -- exact is1.
        * use is_z_isomorphism_comp.
          -- exact (TriMor_is_iso1 (ConeIsoMor_is_iso I1)).
          -- exact is2.
        * use is_z_isomorphism_comp.
          -- exact (TriMor_is_iso2 (ConeIsoMor_is_iso I1)).
          -- exact is3.
  Qed.

  (** ** The following is used to construct TExt in K(A) *)

  Local Lemma mk_TExts_comm1 {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             (M1 : Morphism) (I1 : ConeIso D1 M1) (M2 : Morphism) (I2 : ConeIso D2 M2)
             (E : PTD⟦Ob3 (ConeIsoTri I1), Ob3 (ConeIsoTri I2)⟧)
             (Comm1 : Mor2 (ConeIsoTri I1) ;; E =
                      MPMor2 (ConeIsoMorInv I1) ;; f2 ;; MPMor2 (ConeIsoMor I2)
                             ;; Mor2 (ConeIsoTri I2))
             (Comm2 : E ;; Mor3 (ConeIsoTri I2) =
                      (Mor3 (ConeIsoTri I1))
                        ;; (# (AddEquiv1 Trans) ((MPMor1 (ConeIsoMorInv I1))
                                                   ;; f1 ;; MPMor1 (ConeIsoMor I2)))) :
    Mor2 D1 ;; (MPMor3 (ConeIsoMor I1) ;; E ;; MPMor3 (ConeIsoMorInv I2)) = f2 ;; Mor2 D2.
  Proof.
    use (pre_comp_with_z_iso_is_inj (TriMor_is_iso2 (ConeIsoMorInv_is_iso I1))).
    use (post_comp_with_z_iso_is_inj (TriMor_is_iso3 (ConeIsoMor_is_iso I2))).
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    set (comm2 := MPComm2 (ConeIsoMor I2)). rewrite <- (assoc _ (Mor2 D2)).
    rewrite <- comm2. clear comm2. rewrite assoc. unfold ConeIsoTri in Comm1. rewrite <- Comm1.
    clear Comm1.
    use (post_comp_with_z_iso_is_inj (TriMor_is_iso3 (ConeIsoMorInv_is_iso I2))).
    rewrite <- (assoc _ (MPMor3 (ConeIsoMor I2))). cbn.
    set (tmp := is_inverse_in_precat1 (TriMor_is_iso3 (ConeIsoMor_is_iso I2))). cbn in tmp.
    rewrite tmp. clear tmp. rewrite id_right. apply cancel_postcomposition.
    apply cancel_postcomposition.
    set (comm2 := MPComm2 (ConeIsoMor I1)). rewrite <- assoc. cbn. cbn in comm2. rewrite <- comm2.
    clear comm2. rewrite assoc.
    set (tmp := is_inverse_in_precat2 (TriMor_is_iso2 (ConeIsoMor_is_iso I1))). cbn in tmp.
    rewrite tmp. clear tmp. apply id_left.
  Qed.

  Local Lemma mk_TExts_comm2 {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             (M1 : Morphism) (I1 : ConeIso D1 M1) (M2 : Morphism) (I2 : ConeIso D2 M2)
             (E : PTD⟦Ob3 (ConeIsoTri I1), Ob3 (ConeIsoTri I2)⟧)
             (Comm1 : Mor2 (ConeIsoTri I1) ;; E =
                      MPMor2 (ConeIsoMorInv I1) ;; f2 ;; MPMor2 (ConeIsoMor I2)
                             ;; Mor2 (ConeIsoTri I2))
             (Comm2 : E ;; Mor3 (ConeIsoTri I2) =
                      (Mor3 (ConeIsoTri I1))
                        ;; (# (AddEquiv1 Trans) ((MPMor1 (ConeIsoMorInv I1))
                                                   ;; f1 ;; MPMor1 (ConeIsoMor I2)))) :
    Mor3 D1 ;; # (AddEquiv1 Trans) f1 =
    MPMor3 (ConeIsoMor I1) ;; E ;; MPMor3 (ConeIsoMorInv I2) ;; Mor3 D2.
  Proof.
    use (post_comp_with_z_iso_is_inj
           (functor_on_is_z_isomorphism
              (AddEquiv1 Trans) (TriMor_is_iso1 (ConeIsoMor_is_iso I2)))).
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    rewrite <- (DComm3 (ConeIsoMor I2)).
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (MPMor3 (ConeIsoMor I2))).
    set (tmp := (is_inverse_in_precat2 (TriMor_is_iso3 (ConeIsoMor_is_iso I2)))).
    cbn. cbn in tmp. rewrite tmp. clear tmp. rewrite id_right. cbn in Comm2.
    rewrite <- assoc. rewrite <- assoc. rewrite Comm2. rewrite assoc. rewrite assoc.
    rewrite functor_comp. rewrite functor_comp. rewrite assoc. rewrite assoc.
    apply cancel_postcomposition. apply cancel_postcomposition.
    set (comm3 := DComm3 (ConeIsoMor I1)). cbn in comm3. rewrite comm3. clear comm3.
    rewrite <- assoc. rewrite <- functor_comp.
    set (tmp := (is_inverse_in_precat1 (TriMor_is_iso1 (ConeIsoMor_is_iso I1)))). cbn in tmp.
    rewrite tmp. clear tmp. rewrite functor_id. rewrite id_right. apply idpath.
  Qed.

  Definition mk_TExts {D1 D2 : DTri} {f1 : Ob1 D1 --> Ob1 D2} {f2 : Ob2 D1 --> Ob2 D2}
             (H : f1 ;; Mor1 D2 = Mor1 D1 ;; f2)
             (M1 : Morphism) (I1 : ConeIso D1 M1) (M2 : Morphism) (I2 : ConeIso D2 M2)
             (E : PTD⟦Ob3 (ConeIsoTri I1), Ob3 (ConeIsoTri I2)⟧)
             (Comm1 : Mor2 (ConeIsoTri I1) ;; E =
                      MPMor2 (ConeIsoMorInv I1) ;; f2 ;; MPMor2 (ConeIsoMor I2)
                             ;; Mor2 (ConeIsoTri I2))
             (Comm2 : E ;; Mor3 (ConeIsoTri I2) =
                      (Mor3 (ConeIsoTri I1))
                        ;; (# (AddEquiv1 Trans) ((MPMor1 (ConeIsoMorInv I1))
                                                   ;; f1 ;; MPMor1 (ConeIsoMor I2)))) : TExt H.
  Proof.
    use mk_TExt.
    - exact (MPMor3 (ConeIsoMor I1) ;; E ;; MPMor3 (ConeIsoMorInv I2)).
    - exact (mk_TExts_comm1 M1 I1 M2 I2 E Comm1 Comm2).
    - exact (mk_TExts_comm2 M1 I1 M2 I2 E Comm1 Comm2).
  Defined.

End def_pretriangulated_data.


(** * PreTriangulated categories *)
Section def_pretrangulated.

  Definition isPreTriang (PTD : PreTriangData) : UU :=
    (Π (x : ob PTD), ∥ Σ M : Morphism, ∥ ConeIso (TrivialTri x) M ∥ ∥)
      × (Π (D : DTri), ∥ Σ M : Morphism, ∥ @ConeIso PTD (RotTri D) M ∥ ∥)
      × (Π (D : DTri), ∥ Σ M : Morphism, ∥ @ConeIso PTD (InvRotTri D) M ∥ ∥)
      × (Π (D1 D2 : DTri) (f1 : Ob1 D1 --> Ob1 D2) (f2 : Ob2 D1 --> Ob2 D2)
           (H : f1 ;; Mor1 D2 = Mor1 D1 ;; f2), ∥ @TExt PTD _ _ _ _ H ∥).

  Definition mk_isPreTriang {PTD : PreTriangData}
             (H1 : (Π (x : ob PTD), ∥ Σ M : Morphism, ∥ ConeIso (TrivialTri x) M ∥ ∥))
             (H2 : Π (D : DTri), ∥ Σ M : Morphism, ∥ @ConeIso PTD (RotTri D) M ∥ ∥ )
             (H3 : Π (D : DTri), ∥ Σ M : Morphism, ∥ @ConeIso PTD (InvRotTri D) M ∥ ∥)
             (H4 : Π (D1 D2 : DTri) (f1 : Ob1 D1 --> Ob1 D2) (f2 : Ob2 D1 --> Ob2 D2)
                     (H : f1 ;; Mor1 D2 = Mor1 D1 ;; f2), ∥ (@TExt PTD _ _ _ _ H) ∥) :
    isPreTriang PTD := (H1,,(H2,,(H3,,H4))).

  Definition TrivialDTrisData {PTD : PreTriangData} (iPT : isPreTriang PTD) :
    Π (x : ob PTD), ∥ Σ M : Morphism, ∥ ConeIso (TrivialTri x) M ∥ ∥ := dirprod_pr1 iPT.

  (** Accessor functions *)
  Definition TrivialDTri {PTD : PreTriangData} (iPT : isPreTriang PTD) (x : ob PTD) : @DTri PTD.
  Proof.
    set (TDT := TrivialDTrisData iPT x).
    exact (mk_DTri (identity x) (ZeroArrow (to_Zero PTD) _ (to_Zero PTD))
                   (ZeroArrow (to_Zero PTD) _ (AddEquiv1 Trans x)) TDT).
  Defined.

  Definition RotDTris {PTD : PreTriangData} (iPT : isPreTriang PTD) (D : @DTri PTD) :
    ∥ Σ M : Morphism, ∥ @ConeIso PTD (RotTri D) M ∥ ∥ := dirprod_pr1 (dirprod_pr2 iPT) D.

  Definition RotDTri {PTD : PreTriangData} (iPT : isPreTriang PTD) (D : @DTri PTD) : @DTri PTD.
  Proof.
    set (D' := RotDTris iPT D).
    exact (mk_DTri' (RotTri D) D').
  Defined.

  Definition InvRotDTris {PTD : PreTriangData} (iPT : isPreTriang PTD) (D : @DTri PTD) :
    ∥ Σ M : Morphism, ∥ @ConeIso PTD (InvRotTri D) M ∥ ∥ :=
    dirprod_pr1 (dirprod_pr2 (dirprod_pr2 iPT)) D.

  Definition InvRotDTri {PTD : PreTriangData} (iPT : isPreTriang PTD) (D : @DTri PTD) : @DTri PTD.
  Proof.
    set (D' := InvRotDTris iPT D).
    exact (mk_DTri' (InvRotTri D) D').
  Defined.

  Definition DExts {PTD : PreTriangData} (iPT : isPreTriang PTD) :
    Π (D1 D2 : DTri) (f1 : Ob1 D1 --> Ob1 D2) (f2 : Ob2 D1 --> Ob2 D2)
      (H : f1 ;; Mor1 D2 = Mor1 D1 ;; f2), ∥ @TExt PTD _ _ _ _ H ∥ :=
    dirprod_pr2 (dirprod_pr2 (dirprod_pr2 iPT)).

  Definition DExt {PTD : PreTriangData} (iPT : isPreTriang PTD) (D1 D2 : DTri)
             (f1 : Ob1 D1 --> Ob1 D2) (f2 : Ob2 D1 --> Ob2 D2) (H : f1 ;; Mor1 D2 = Mor1 D1 ;; f2) :
    ∥ TExt H ∥ := DExts iPT D1 D2 f1 f2 H.

  (** ** Pretriangulated category *)

  Definition PreTriang : UU := Σ PTD : PreTriangData, isPreTriang PTD.

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

  (** Octahedral axiom *)
  Definition Octa {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥)
             (H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥)
             (H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥) : UU :=
    Σ D : ((z2 --> y2) × (y2 --> x2)),
          (∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (dirprod_pr1 D) (dirprod_pr2 D)
                                               (g3 ;; (# (AddEquiv1 Trans) f2))) M ∥ ∥)
            × (f2 ;; dirprod_pr1 D = g1 ;; h2)
            × (dirprod_pr2 D ;; g3 = h3 ;; (# (AddEquiv1 Trans) f1)).

  Definition mk_Octa {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥)
             (H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥)
             (H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥)
             (φ1 : z2 --> y2) (φ2 : y2 --> x2)
             (H4 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri φ1 φ2 (g3 ;; (# (AddEquiv1 Trans) f2))) M ∥ ∥)
             (Comm1 : f2 ;; φ1 = g1 ;; h2)
             (Comm2 : φ2 ;; g3 = h3 ;; (# (AddEquiv1 Trans) f1)) : Octa H1 H2 H3 :=
    ((φ1,,φ2),,(H4,,(Comm1,,Comm2))).

  (** Accessor functions *)

  Definition OctaMor1 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥}
             {H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥}
             {H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥}
             (O : Octa H1 H2 H3) : PT⟦z2, y2⟧ := dirprod_pr1 (pr1 O).

  Definition OctaMor2 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥}
             {H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥}
             {H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥}
             (O : Octa H1 H2 H3) : PT⟦y2, x2⟧ := dirprod_pr2 (pr1 O).

  Definition OctaDTri {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥}
             {H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥}
             {H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥}
             (O : Octa H1 H2 H3) : @DTri PT := mk_DTri' _ (dirprod_pr1 (pr2 O)).

  Definition OctaComm1 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥}
             {H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥}
             {H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥}
             (O : Octa H1 H2 H3) : f2 ;; (OctaMor1 O) = g1 ;; h2 :=
    dirprod_pr1 (dirprod_pr2 (pr2 O)).

  Definition OctaComm2 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥}
             {H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥}
             {H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥}
             (O : Octa H1 H2 H3) : (OctaMor2 O) ;; g3 = h3 ;; (# (AddEquiv1 Trans) f1) :=
    dirprod_pr2 (dirprod_pr2 (pr2 O)).

  (** Triangulated category *)
  Definition Triang : UU :=
    Σ PT : PreTriang,
           (Π (x1 x2 y1 y2 z1 z2 : ob PT)
              (f1 : x1 --> y1) (f2 : y1 --> z2) (f3 : z2 --> (AddEquiv1 Trans x1))
              (g1 : y1 --> z1) (g2 : z1 --> x2) (g3 : x2 --> (AddEquiv1 Trans y1))
              (h2 : z1 --> y2) (h3 : y2 --> (AddEquiv1 Trans x1))
              (H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥)
              (H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥)
              (H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥),
            ∥ Octa H1 H2 H3 ∥).

  Definition mk_Triang {PT : PreTriang} (H : Π (x1 x2 y1 y2 z1 z2 : ob PT)
              (f1 : x1 --> y1) (f2 : y1 --> z2) (f3 : z2 --> (AddEquiv1 Trans x1))
              (g1 : y1 --> z1) (g2 : z1 --> x2) (g3 : x2 --> (AddEquiv1 Trans y1))
              (h2 : z1 --> y2) (h3 : y2 --> (AddEquiv1 Trans x1))
              (H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥)
              (H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥)
              (H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥),
                                             ∥ Octa H1 H2 H3 ∥) : Triang := (PT,,H).

  Definition Triang_PreTriang (TR : Triang) : PreTriang := pr1 TR.
  Coercion Triang_PreTriang : Triang >-> PreTriang.

  Definition Octahedral {TR : Triang} {x1 x2 y1 y2 z1 z2 : ob TR}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             {H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥}
             {H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥}
             {H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥} :
    ∥ Octa H1 H2 H3 ∥ := (pr2 TR) x1 x2 y1 y2 z1 z2 f1 f2 f3 g1 g2 g3 h2 h3 H1 H2 H3.

End def_triangulated.


(** ** Rotations, Extensions, and ... *)
Section rotation_isos.

  Context {PT : PreTriang}.

  (** ** iso D InvRot (Rot D) and iso D Rot (InvRot D) *)

  Local Lemma RotInvIso_Mor_Comm1 (D : DTri) :
    ((AddEquivUnitIso Trans (Ob1 D)) : PT⟦_, _⟧)
      ;; ((to_inv (# (AddEquiv2 Trans) (to_inv (# (AddEquiv1 Trans) (Mor1 D)))))
            ;; (z_iso_inv_mor (AddEquivUnitIso (@Trans PT) (Ob2 D)))) =
    Mor1 D ;; identity (Ob2 D).
  Proof.
    rewrite AdditiveFunctorInv. rewrite inv_inv_eq. rewrite id_right.
    use (post_comp_with_z_iso_is_inj (AddEquivUnitIso Trans (Ob2 D))).
    rewrite <- assoc. rewrite <- assoc.
    rewrite (is_inverse_in_precat2 (AddEquivUnitIso Trans (Ob2 D))).
    rewrite id_right.
    use (! (AddEquivUnitComm (@Trans PT) _ _ (Mor1 D))).
  Qed.

  Local Lemma RotInvIso_Mor_Comm2 (D : @DTri PT) :
    identity (Ob2 D) ;; Mor2 D = Mor2 D ;; identity (Ob3 D).
  Proof.
    rewrite id_right. apply id_left.
  Qed.

  Local Lemma RotInvIso_Mor_Comm3 (D : DTri) :
    (identity (Ob3 D))
      ;; ((Mor3 D) ;; (z_iso_inv_mor (AddEquivCounitIso Trans ((AddEquiv1 Trans) (Ob1 D))))) =
    Mor3 D ;; # (AddEquiv1 (@Trans PT)) (AddEquivUnitIso Trans (Ob1 D)).
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
    identity (Ob1 D) ;; Mor1 D = Mor1 D ;; identity (Ob2 D).
  Proof.
    rewrite id_right. apply id_left.
  Qed.

  Local Lemma InvRotIso_Mor_Comm2 (D : @DTri PT) :
    (identity (Ob2 D))
      ;; (Mor2 D ;; z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D))) =
    Mor2 D ;; z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D)).
  Proof.
    rewrite id_left. apply idpath.
  Qed.

  Local Lemma InvRotIso_Mor_Comm3 (D : @DTri PT) :
    (z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D)))
      ;; (to_inv (# (AddEquiv1 Trans) ((to_inv (# (AddEquiv2 Trans) (Mor3 D)))
                                         ;; z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D))))) =
    Mor3 D ;; # (AddEquiv1 Trans) (identity (Ob1 D)).
  Proof.
    rewrite functor_id. rewrite id_right. rewrite <- PreAdditive_invlcomp.
    rewrite AdditiveFunctorInv. rewrite inv_inv_eq. rewrite functor_comp.
    set (tmp := AddEquivCounitUnit' Trans (Ob1 D)). cbn in tmp. rewrite assoc. cbn.
    apply (maponpaths (fun g : _ => (z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D)))
                                   ;; (# (AddEquiv1 Trans) (# (AddEquiv2 Trans) (Mor3 D)))
                                   ;; g)) in tmp.
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
    (AddEquivUnit Trans) (Ob1 D1) ;; # (AddEquiv2 Trans) (MPMor3 Mor)
                         ;; z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D2))
                         ;; Mor1 D2 = Mor1 D1 ;; MPMor1 Mor.
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
             (fun gg : _ => gg ;; # (AddEquiv1 Trans) (# (AddEquiv2 Trans) (MPMor3 Mor)) ;;
                            # (AddEquiv1 Trans)
                            (z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D2))))) in tmp.
    use (pathscomp0 (! tmp)). clear tmp. rewrite <- assoc. rewrite <- assoc.
    apply cancel_precomposition. apply cancel_precomposition.
    use (! AddEquivCounitUnit' Trans (Ob1 D2)).
  Qed.

  Local Lemma ExtMor'_Comm3 (D1 D2 : @DTri PT) (Mor : TriMor (RotDTri PT D1) (RotDTri PT D2)):
    MPMor2 Mor ;; Mor3 D2 =
    Mor3 D1 ;; # (AddEquiv1 Trans)
         ((AddEquivUnit Trans) (Ob1 D1) ;; # (AddEquiv2 Trans) (MPMor3 Mor) ;;
                               z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D2))).
  Proof.
    set (tmp := MPComm2 Mor). cbn in tmp. cbn. rewrite tmp. clear tmp.
    apply cancel_precomposition.
    use (pathscomp0 (AddEquivCounitMorComm Trans (MPMor3 Mor))).
    set (tmp := AddEquivCounitUnit Trans (Ob1 D1)).
    apply (maponpaths
             (fun gg : _ => (gg) ;; (# (functor_composite (AddEquiv2 Trans) (AddEquiv1 Trans)) (MPMor3 Mor))
                              ;; (AddEquivCounit Trans) ((AddEquiv1 Trans) (Ob1 D2)))) in tmp.
    use (pathscomp0 tmp). clear tmp. rewrite <- assoc. rewrite <- assoc. rewrite functor_comp.
    apply cancel_precomposition. rewrite functor_comp. apply cancel_precomposition.
    exact (AddEquivCounitUnit' Trans (Ob1 D2)).
  Qed.

  Definition ExtMor1 (D1 D2 : @DTri PT) (f2 : Ob2 D1 --> Ob2 D2) (f3 : Ob3 D1 --> Ob3 D2)
             (H : f2 ;; Mor2 D2 = Mor2 D1 ;; f3)
             (Ext : @TExt _ (RotDTri PT D1) (RotDTri PT D2) f2 f3 H) : TriMor D1 D2.
  Proof.
    set (Mor := TExtMor Ext).
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (((AddEquivUnitIso Trans (Ob1 D1)) : PT⟦_, _⟧)
                   ;; (# (AddEquiv2 Trans) (MPMor3 Mor))
                   ;; (z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D2)))).
        * exact (MPMor1 Mor).
        * exact (MPMor2 Mor).
      + use mk_MPMorComms.
        * exact (ExtMor'_Comm1 D1 D2 Mor).
        * exact (MPComm1 Mor).
    - exact (ExtMor'_Comm3 D1 D2 Mor).
  Defined.

  Local Lemma ExtMor2_Comm (D1 D2 : @DTri PT) (f3 : Ob3 D1 --> Ob3 D2)
             (f4 : (AddEquiv1 Trans (Ob1 D1)) --> (AddEquiv1 Trans (Ob1 D2)))
             (H : f3 ;; Mor3 D2 = Mor3 D1 ;; f4) :
    let D1' := InvRotDTri PT D1 in
    let D2' := InvRotDTri PT D2 in
    (# (AddEquiv2 Trans) f3)
      ;; (to_inv (# (AddEquiv2 Trans) (Mor3 D2)) ;; AddEquivUnitInvMor Trans (Ob1 D2)) =
    (to_inv (# (AddEquiv2 Trans) (Mor3 D1)))
      ;; AddEquivUnitInvMor Trans (Ob1 D1)
      ;; (((AddEquivUnit Trans) (Ob1 D1))
            ;; # (AddEquiv2 Trans) f4 ;; AddEquivUnitInvMor Trans (Ob1 D2)).
  Proof.
    intros D1' D2'. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    apply maponpaths. apply cancel_postcomposition.
    rewrite <- functor_comp. apply (maponpaths (# (AddEquiv2 Trans))) in H. use (pathscomp0 H).
    rewrite functor_comp. apply cancel_postcomposition. rewrite <- assoc.
    set (tmp := is_inverse_in_precat2 (AddEquivUnitIso Trans (Ob1 D1))).
    apply (maponpaths (compose (# (AddEquiv2 Trans) (Mor3 D1)))) in tmp.
    use (pathscomp0 _ (! tmp)). rewrite id_right. apply idpath.
  Qed.

  Local Lemma ExtMor2_Comm2 (D1 D2 : @DTri PT) (Mor : TriMor (InvRotDTri PT D1) (InvRotDTri PT D2)) :
    MPMor3 Mor ;; Mor2 D2 =
    Mor2 D1 ;; (AddEquivCounitInvMor Trans (Ob3 D1) ;; # (AddEquiv1 Trans) (MPMor1 Mor) ;;
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

  Local Lemma ExtMor2_Comm3 (D1 D2 : @DTri PT) (Mor : TriMor (InvRotDTri PT D1) (InvRotDTri PT D2)) :
    (AddEquivCounitInvMor Trans (Ob3 D1))
      ;; # (AddEquiv1 Trans) (MPMor1 Mor) ;; (AddEquivCounit Trans) (Ob3 D2) ;;  Mor3 D2 =
    Mor3 D1 ;; # (AddEquiv1 Trans) (MPMor2 Mor).
  Proof.
    use (pre_comp_with_z_iso_is_inj (AddEquivCounitIso Trans (Ob3 D1))).
    rewrite assoc. rewrite assoc. rewrite assoc.
    set (tmp' := is_inverse_in_precat1 (AddEquivCounitIso Trans (Ob3 D1))). cbn in tmp'.
    apply (maponpaths
             (postcompose ((# (AddEquiv1 Trans) (MPMor1 Mor))
                             ;; (AddEquivCounit Trans) (Ob3 D2) ;; Mor3 D2))) in tmp'.
    unfold postcompose in tmp'. rewrite assoc in tmp'. rewrite assoc in tmp'.
    use (pathscomp0 tmp'). clear tmp'. rewrite id_left. rewrite <- assoc.
    set (tmp' := AddEquivCounitComm Trans _ _ (Mor3 D2)).
    apply (maponpaths (compose (# (AddEquiv1 Trans) (MPMor1 Mor)))) in tmp'.
    use (pathscomp0 (! tmp')). clear tmp'.
    set (tmp' := AddEquivCounitUnit' Trans (Ob1 D2)).
    apply (maponpaths (fun gg : _ => # (AddEquiv1 Trans) (MPMor1 Mor)
                                    ;; (# (AddEquiv1 Trans) (# (AddEquiv2 Trans) (Mor3 D2))
                                          ;; gg))) in tmp'.
    use (pathscomp0 tmp'). clear tmp'.
    rewrite <- functor_comp. rewrite <- functor_comp. rewrite assoc. rewrite assoc.
    set (tmp' := AddEquivCounitComm Trans _ _ (Mor3 D1)).
    apply (maponpaths (postcompose (# (AddEquiv1 Trans) (MPMor2 Mor)))) in tmp'.
    use (pathscomp0 _ tmp'). clear tmp'. unfold postcompose.
    set (tmp' := AddEquivCounitUnit' Trans (Ob1 D1)).
    apply (maponpaths (fun gg : _ => # (AddEquiv1 Trans) (# (AddEquiv2 Trans) (Mor3 D1))
                                    ;; gg ;; # (AddEquiv1 Trans) (MPMor2 Mor))) in tmp'.
    use (pathscomp0 _ (! tmp')). clear tmp'.
    rewrite <- functor_comp. rewrite <- functor_comp. apply maponpaths.
    set (tmp := MPComm1 Mor).
    apply cancel_inv. rewrite PreAdditive_invlcomp. rewrite PreAdditive_invrcomp.
    rewrite <- assoc. use (pathscomp0 tmp). clear tmp.
    rewrite PreAdditive_invlcomp. rewrite PreAdditive_invlcomp. apply idpath.
  Qed.

  Definition ExtMor2 (D1 D2 : @DTri PT) (f3 : Ob3 D1 --> Ob3 D2)
             (f4 : (AddEquiv1 Trans (Ob1 D1)) --> (AddEquiv1 Trans (Ob1 D2)))
             (H : f3 ;; Mor3 D2 = Mor3 D1 ;; f4) : ∥ TriMor D1 D2 ∥.
  Proof.
    set (D1' := InvRotDTri PT D1). set (D2' := InvRotDTri PT D2).
    set (Ext' := DExt PT D1' D2' (# (AddEquiv2 Trans) f3)
                      (((AddEquivUnitIso Trans (Ob1 D1)) : PT⟦_, _⟧)
                         ;; (# (AddEquiv2 Trans) f4)
                         ;; z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D2)))
                      (ExtMor2_Comm D1 D2 f3 f4 H)).
    use (squash_to_prop Ext' (propproperty _)). intros Ext.
    set (Mor := TExtMor Ext). intros P X. apply X. clear X P.
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (MPMor2 Mor).
        * exact (MPMor3 Mor).
        * exact ((z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D1)))
                   ;; (# (AddEquiv1 Trans) (MPMor1 Mor))
                   ;; (AddEquivCounitIso Trans (Ob3 D2))).
      + use mk_MPMorComms.
        * exact (MPComm2 Mor).
        * exact (ExtMor2_Comm2 D1 D2 Mor).
    - exact (ExtMor2_Comm3 D1 D2 Mor).
  Defined.

  (** ** Rotation of morphisms *)

  Local Lemma RotTriMor_Comm3 {D1 D2 : @DTri PT} (M : TriMor D1 D2)  :
    # (AddEquiv1 Trans) (MPMor1 M) ;; to_inv (# (AddEquiv1 Trans) (Mor1 D2)) =
    to_inv (# (AddEquiv1 Trans) (Mor1 D1)) ;; # (AddEquiv1 Trans) (MPMor2 M).
  Proof.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp. apply maponpaths.
    rewrite <- functor_comp. rewrite <- functor_comp. apply maponpaths.
    exact (MPComm1 M).
  Qed.

  Definition RotTriMor {D1 D2 : @DTri PT} (M : TriMor D1 D2) :
    TriMor (RotDTri PT D1) (RotDTri PT D2).
  Proof.
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (MPMor2 M).
        * exact (MPMor3 M).
        * exact (# (AddEquiv1 Trans) (MPMor1 M)).
      + use mk_MPMorComms.
        * exact (MPComm2 M).
        * exact (DComm3 M).
    - exact (RotTriMor_Comm3 M).
  Defined.

  Local Lemma InvRotTriMor_Comm1 {D1 D2 : @DTri PT} (M : TriMor D1 D2) :
    (# (AddEquiv2 Trans) (MPMor3 M))
      ;; ((to_inv (# (AddEquiv2 Trans) (Mor3 D2)))
            ;; z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D2))) =
    (to_inv (# (AddEquiv2 Trans) (Mor3 D1)))
      ;; z_iso_inv_mor (AddEquivUnitIso Trans (Ob1 D1)) ;; MPMor1 M.
  Proof.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    apply maponpaths. rewrite assoc. rewrite <- functor_comp.
    set (tmp := maponpaths (# (AddEquiv2 Trans)) (DComm3 M)). rewrite tmp. clear tmp.
    rewrite functor_comp. rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    set (tmp := AddEquivUnitComm Trans _ _ (MPMor1 M)). cbn in tmp.
    use (! AddEquivUnitInv Trans (MPMor1 M)).
  Qed.

  Local Lemma InvRotTriMor_Comm3 {D1 D2 : @DTri PT} (M : TriMor D1 D2)  :
    MPMor2 M ;; (Mor2 D2 ;; z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D2))) =
    Mor2 D1 ;; z_iso_inv_mor (AddEquivCounitIso Trans (Ob3 D1))
         ;; # (AddEquiv1 Trans) (# (AddEquiv2 Trans) (MPMor3 M)).
  Proof.
    set (tmp := MPComm2 M). rewrite assoc. rewrite tmp. clear tmp.
    rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    use (! AddEquivCounitInv Trans (MPMor3 M)).
  Qed.

  Definition InvRotTriMor {D1 D2 : @DTri PT} (M : TriMor D1 D2) :
    TriMor (InvRotDTri PT D1) (InvRotDTri PT D2).
  Proof.
    use mk_TriMor.
    - use mk_MPMor.
      + use mk_MPMorMors.
        * exact (# (AddEquiv2 Trans) (MPMor3 M)).
        * exact (MPMor1 M).
        * exact (MPMor2 M).
      + use mk_MPMorComms.
        * exact (InvRotTriMor_Comm1 M).
        * exact (MPComm1 M).
    - exact (InvRotTriMor_Comm3 M).
  Defined.

End rotation_isos.


(** ** Introduction
Composition of consecutive morphisms of a distinguished triangle is 0.
 *)
Section comp_zero.

  Context {PT : PreTriang}.

  Lemma DTriCompZero (D : @DTri PT) : Mor1 D ;; Mor2 D = ZeroArrow (to_Zero PT) _ _.
  Proof.
    set (D2 := TrivialDTri PT (Ob1 D)).
    set (Ext' := DExt PT D2 D (identity (Ob1 D)) (Mor1 D) (idpath _)).
    use (squash_to_prop Ext'). apply to_has_homsets. intros Ext. clear Ext'.
    set (M := TExtMor Ext). use (pathscomp0 (MPComm2 M)). cbn. apply ZeroArrow_comp_left.
  Qed.

  Lemma DTriCompZero' (D : @DTri PT) : Mor2 D ;; Mor3 D = ZeroArrow (to_Zero PT) _ _.
  Proof.
    set (D' := RotDTri PT D). exact (DTriCompZero D').
  Qed.

End comp_zero.


(** ** Introduction
We construct the short exact sequences out from distinguished triangles. These can be used to define
the long exact sequences associated to a distinguished triangle. Suppose (X, Y, Z, f, g, h) is a
distinguished triangle. Then for every object W we have shortshortexact sequences
      Mor(W, X) --> Mor(W, Y) --> Mor(W, Z)    and    Mor(Z, W) --> Mor(Y, W) --> Mor(X, W)
These shortshortexact sequences are constructed in  [DTriSSE1_ShortShortExact_from_X] and
[DTriSSE1_ShortShortExact_to_X].
 *)
Section short_short_exact_sequences.

  Context {PT : PreTriang}.

  Local Opaque ZeroArrow.

  Definition MorphismPair_from_X (D : @DTri PT) (X : ob PT) :
    @MorphismPair ABGR_AbelianPreCat.
  Proof.
    use mk_MorphismPair.
    - exact (@to_abgrop PT X (Ob1 D)).
    - exact (@to_abgrop PT X (Ob2 D)).
    - exact (@to_abgrop PT X (Ob3 D)).
    - exact (to_postmor_monoidfun PT X (Ob1 D) (Ob2 D) (Mor1 D)).
    - exact (to_postmor_monoidfun PT X (Ob2 D) (Ob3 D) (Mor2 D)).
  Defined.

  Local Lemma ShortShortExactData_Eq_from_X (D : @DTri PT) (X : ob PT):
    monoidfuncomp (to_postmor_monoidfun PT X (Ob1 D) (Ob2 D) (Mor1 D))
                  (to_postmor_monoidfun PT X (Ob2 D) (Ob3 D) (Mor2 D)) =
    ZeroArrow ABGR_has_zero (to_abgrop X (Ob1 D)) (to_abgrop X (Ob3 D)).
  Proof.
    cbn. rewrite <- (@AdditiveZeroArrow_postmor_Abelian PT).
    use monoidfun_eq. intros x. cbn. unfold to_postmor. rewrite <- assoc.
    apply cancel_precomposition. exact (DTriCompZero D).
  Qed.

  Definition ShortShortExactData_from_X (D : @DTri PT) (X : ob PT) :
    @ShortShortExactData ABGR_AbelianPreCat ABGR_has_zero.
  Proof.
    use mk_ShortShortExactData.
    - exact (MorphismPair_from_X D X).
    - exact (ShortShortExactData_Eq_from_X D X).
  Defined.

  Lemma ShortShortExact_isKernel_from_X (D : @DTri PT) (X : ob PT) :
    isKernel Abelian.to_Zero (KernelArrow (Image (ShortShortExactData_from_X D X)))
             (Mor2 (ShortShortExactData_from_X D X))
             (@Image_Eq ABGR_AbelianPreCat has_homsets_ABGR (ShortShortExactData_from_X D X)).
  Proof.
    use ABGR_isKernel.
    - intros D0. induction D0 as [y yH].
      set (D' := TrivialDTri PT X).
      assert (e : y ;; Mor2 D =
                  ZeroArrow (to_Zero PT) _ (to_Zero PT) ;; ZeroArrow (to_Zero PT) _ _).
      {
        cbn in yH. unfold to_postmor in yH. rewrite yH.
        rewrite ZeroArrow_comp_left. set (tmp := PreAdditive_unel_zero PT (to_Zero PT) X (Ob3 D)).
        unfold to_unel in tmp. exact tmp.
      }
      set (Ext' := @DExt _ PT (RotDTri PT D') (RotDTri PT D) y
                         (ZeroArrow (Additive.to_Zero PT) _ _) e).
      use (squash_to_prop Ext' (propproperty _)). intros Ext. clear Ext'.
      set (Mor := ExtMor1 D' D y (ZeroArrow (Additive.to_Zero PT) _ _) e Ext).
      intros P X'. apply X'. clear P X'.
      use tpair.
      + exact (((factorization1_epi
                   ABGR_AbelianPreCat has_homsets_ABGR
                   (Mor1 (ShortShortExactData_from_X D X)) : ABGR⟦_, _⟧) : monoidfun _ _)
                 (MPMor1 Mor)).
      + cbn beta. set (φ := MPMor1 Mor). cbn in φ.
        set (comm1 := MPComm1 Mor). cbn in comm1. fold φ in comm1. rewrite id_left in comm1.
        use (pathscomp0 _ comm1). clear comm1.
        set (tmp := @factorization1 ABGR_AbelianPreCat has_homsets_ABGR _ _
                                    (Mor1 (ShortShortExactData_from_X D X))).
        apply base_paths in tmp. set (tmp' := funeqpaths tmp φ). cbn in tmp'.
        unfold to_postmor in tmp'. use (pathscomp0 _ (! tmp')). clear tmp'. clear tmp.
        cbn. apply idpath.
    - use KernelArrowisMonic.
  Qed.

  Definition ShortShortExact_from_X (D : @DTri PT) (X : ob PT) :
    @ShortShortExact ABGR_AbelianPreCat has_homsets_ABGR.
  Proof.
    use mk_ShortShortExact.
    - exact (ShortShortExactData_from_X D X).
    - exact (ShortShortExact_isKernel_from_X D X).
  Defined.

  (** ShortShortExacts to X *)
  Definition MorphismPair_to_X (D : @DTri PT) (X : ob PT) :
    @MorphismPair ABGR_AbelianPreCat.
  Proof.
    use mk_MorphismPair.
    - exact (@to_abgrop PT (Ob3 D) X).
    - exact (@to_abgrop PT (Ob2 D) X).
    - exact (@to_abgrop PT (Ob1 D) X).
    - exact (to_premor_monoidfun PT (Ob2 D) (Ob3 D) X (Mor2 D)).
    - exact (to_premor_monoidfun PT (Ob1 D) (Ob2 D) X (Mor1 D)).
  Defined.

  Local Lemma ShortShortExactData_Eq_to_X (D : @DTri PT) (X : ob PT) :
    monoidfuncomp (to_premor_monoidfun PT (Ob2 D) (Ob3 D) X (Mor2 D))
                  (to_premor_monoidfun PT (Ob1 D) (Ob2 D) X (Mor1 D)) =
    ZeroArrow (@Abelian.to_Zero ABGR_AbelianPreCat) (to_abgrop (Ob3 D) X) (to_abgrop (Ob1 D) X).
  Proof.
    rewrite <- (@AdditiveZeroArrow_premor_Abelian PT).
    use monoidfun_eq. intros x. cbn. unfold to_premor. rewrite assoc.
    apply cancel_postcomposition. exact (DTriCompZero D).
  Qed.

  Definition ShortShortExactData_to_X (D : @DTri PT) (X : ob PT) :
    @ShortShortExactData ABGR_AbelianPreCat ABGR_has_zero.
  Proof.
    use mk_ShortShortExactData.
    - exact (MorphismPair_to_X D X).
    - exact (ShortShortExactData_Eq_to_X D X).
  Defined.

  Lemma ShortShortExact_isKernel_to_X (D : @DTri PT) (X : ob PT) :
    isKernel Abelian.to_Zero (KernelArrow (Image (ShortShortExactData_to_X D X)))
             (Mor2 (ShortShortExactData_to_X D X))
             (@Image_Eq ABGR_AbelianPreCat has_homsets_ABGR
                       (ShortShortExactData_to_X D X)).
  Proof.
    use ABGR_isKernel.
    - intros D0. induction D0 as [y yH].
      set (D' := InvRotDTri PT (TrivialDTri PT X)).
      assert (e : ZeroArrow (to_Zero PT) (Ob1 D) (Ob1 D') ;; Mor1 D' = Mor1 D ;; y).
      {
        rewrite ZeroArrow_comp_left.
        cbn in yH. unfold to_premor in yH. use (pathscomp0 _ (! yH)).
        set (tmp := PreAdditive_unel_zero PT (to_Zero PT) (Ob1 D) (Ob2 D')).
        unfold to_unel in tmp. exact (! tmp).
      }
      set (Ext' := DExt PT D D' (ZeroArrow (Additive.to_Zero PT) _ _) y e).
      use (squash_to_prop Ext' (propproperty _)). intros Ext. clear Ext'.
      set (Mor := TExtMor Ext).
      intros P X'. apply X'. clear X' P.
      use tpair.
      + exact (((factorization1_epi
                   ABGR_AbelianPreCat has_homsets_ABGR
                   (Mor1 (ShortShortExactData_to_X D X)) : ABGR⟦_, _⟧) : monoidfun _ _)
                 (MPMor3 Mor)).
      + cbn beta. set (φ := MPMor3 Mor). cbn in φ.
        set (comm2 := MPComm2 Mor). cbn in comm2. fold φ in comm2. rewrite id_right in comm2.
        use (pathscomp0 _ (! comm2)). clear comm2.
        set (tmp := @factorization1 ABGR_AbelianPreCat has_homsets_ABGR _ _
                                    (Mor1 (ShortShortExactData_to_X D X))).
        apply base_paths in tmp. set (tmp' := funeqpaths tmp φ). cbn in tmp'.
        unfold to_premor in tmp'. use (pathscomp0 _ (! tmp')). clear tmp'. clear tmp.
        cbn. apply idpath.
    - use KernelArrowisMonic.
  Qed.

  Definition ShortShortExact_to_X (D : @DTri PT) (X : ob PT) :
    @ShortShortExact ABGR_AbelianPreCat has_homsets_ABGR.
  Proof.
    use mk_ShortShortExact.
    - exact (ShortShortExactData_to_X D X).
    - exact (ShortShortExact_isKernel_to_X D X).
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

  Definition TriangulatedRowObs_from_X (D : @DTri PT) (X : ob PT) : @FiveRowObs ABGR_AbelianPreCat.
  Proof.
    use mk_FiveRowObs.
    - exact (to_abgrop X (Ob1 D)).
    - exact (to_abgrop X (Ob2 D)).
    - exact (to_abgrop X (Ob3 D)).
    - exact (to_abgrop X (AddEquiv1 Trans (Ob1 D))).
    - exact (to_abgrop X (AddEquiv1 Trans (Ob2 D))).
  Defined.

  Definition TriangulatedRowDiffs_from_X (D : @DTri PT) (X : ob PT) :
    @FiveRowDiffs ABGR_AbelianPreCat (TriangulatedRowObs_from_X D X).
  Proof.
    use mk_FiveRowDiffs.
    - exact (to_postmor_monoidfun PT _ _ _ (Mor1 D)).
    - exact (to_postmor_monoidfun PT _ _ _ (Mor2 D)).
    - exact (to_postmor_monoidfun PT _ _ _ (Mor3 D)).
    - exact (to_postmor_monoidfun PT _ _ _ (to_inv (# (AddEquiv1 Trans) (Mor1 D)))).
  Defined.

  Definition TriangulatedRowDiffsEq_from_X (D : @DTri PT) (X : ob PT) :
    @FiveRowDiffsEq ABGR_AbelianPreCat _ (TriangulatedRowDiffs_from_X D X).
  Proof.
    use mk_FiveRowDiffsEq.
    - use monoidfun_eq. rewrite ABGR_has_zero_arrow_eq.
      intros x. cbn. unfold to_postmor. rewrite <- assoc.
      set (tmp := DTriCompZero D). apply (maponpaths (compose x)) in tmp.
      use (pathscomp0 tmp). clear tmp. rewrite ZeroArrow_comp_right.
      rewrite <- PreAdditive_unel_zero. unfold to_unel. apply idpath.
    - use monoidfun_eq. rewrite ABGR_has_zero_arrow_eq.
      intros x. cbn. unfold to_postmor. rewrite <- assoc.
      set (tmp := DTriCompZero' D). apply (maponpaths (compose x)) in tmp.
      use (pathscomp0 tmp). clear tmp. rewrite ZeroArrow_comp_right.
      rewrite <- PreAdditive_unel_zero. unfold to_unel. apply idpath.
    - use monoidfun_eq. rewrite ABGR_has_zero_arrow_eq.
      intros x. cbn. unfold to_postmor. rewrite <- assoc.
      set (tmp := DTriCompZero' (RotDTri PT D)). apply (maponpaths (compose x)) in tmp.
      cbn in tmp. use (pathscomp0 tmp). clear tmp. rewrite ZeroArrow_comp_right.
      rewrite <- PreAdditive_unel_zero. unfold to_unel. apply idpath.
  Qed.

  Local Opaque ABGR_AbelianPreCat ishinh.
  Definition TriangulatedRowExacts_from_X (D : @DTri PT) (X : ob PT) :
    @FiveRowExacts ABGR_AbelianPreCat has_homsets_ABGR _ _ (TriangulatedRowDiffsEq_from_X D X).
  Proof.
    use mk_FiveRowExacts.
    - unfold isExact. exact (@ShortShortExact_isKernel_from_X PT D X).
    - unfold isExact. exact (@ShortShortExact_isKernel_from_X PT (RotDTri PT D) X).
    - unfold isExact. exact (@ShortShortExact_isKernel_from_X PT (RotDTri PT (RotDTri PT D)) X).
  Qed.
  Local Transparent ABGR_AbelianPreCat ishinh.

  Definition TriangulatedRow_from_X (D : @DTri PT) (X : ob PT) :
    @FiveRow ABGR_AbelianPreCat has_homsets_ABGR.
  Proof.
    use mk_FiveRow.
    - exact (TriangulatedRowObs_from_X D X).
    - exact (TriangulatedRowDiffs_from_X D X).
    - exact (TriangulatedRowDiffsEq_from_X D X).
    - exact (TriangulatedRowExacts_from_X D X).
  Defined.

  Definition TriangulatedRowMors_from_X {D1 D2 : @DTri PT} (M : TriMor D1 D2) (X : ob PT) :
    @FiveRowMors ABGR_AbelianPreCat has_homsets_ABGR
                 (TriangulatedRow_from_X D1 X) (TriangulatedRow_from_X D2 X).
  Proof.
    use mk_FiveRowMors.
    - exact (to_postmor_monoidfun PT _ _ _ (MPMor1 M)).
    - exact (to_postmor_monoidfun PT _ _ _ (MPMor2 M)).
    - exact (to_postmor_monoidfun PT _ _ _ (MPMor3 M)).
    - exact (to_postmor_monoidfun PT _ _ _ (# (AddEquiv1 Trans) (MPMor1 M))).
    - exact (to_postmor_monoidfun PT _ _ _ (# (AddEquiv1 Trans) (MPMor2 M))).
  Defined.

  Definition TriangulatedMorsComm_from_X {D1 D2 : @DTri PT} (M : TriMor D1 D2) (X : ob PT) :
    @FiveRowMorsComm ABGR_AbelianPreCat has_homsets_ABGR _ _ (TriangulatedRowMors_from_X M X).
  Proof.
    use mk_FiveRowMorsComm.
    - use monoidfun_eq.
      intros x. cbn. unfold to_postmor. rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. exact (! MPComm1 M).
    - use monoidfun_eq.
      intros x. cbn. unfold to_postmor. rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. exact (! MPComm2 M).
    - use monoidfun_eq.
      intros x. cbn. unfold to_postmor. rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. exact (! DComm3 M).
    - use monoidfun_eq.
      intros x. cbn. unfold to_postmor. rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
      apply maponpaths. rewrite <- functor_comp. rewrite <- functor_comp.
      apply maponpaths. exact (! MPComm1 M).
  Qed.

  Definition TriangulatedMorphism_from_X {D1 D2 : @DTri PT} (M : TriMor D1 D2) (X : ob PT) :
    @FiveRowMorphism ABGR_AbelianPreCat has_homsets_ABGR
                     (TriangulatedRow_from_X D1 X) (TriangulatedRow_from_X D2 X).
  Proof.
    use mk_FiveRowMorphism.
    - exact (TriangulatedRowMors_from_X M X).
    - exact (TriangulatedMorsComm_from_X M X).
  Defined.

  Definition TriangulatedRowObs_to_X (D : @DTri PT) (X : ob PT) : @FiveRowObs ABGR_AbelianPreCat.
  Proof.
    use mk_FiveRowObs.
    - exact (to_abgrop (AddEquiv1 Trans (Ob2 D)) X).
    - exact (to_abgrop (AddEquiv1 Trans (Ob1 D)) X).
    - exact (to_abgrop (Ob3 D) X).
    - exact (to_abgrop (Ob2 D) X).
    - exact (to_abgrop (Ob1 D) X).
  Defined.

  Definition TriangulatedRowDiffs_to_X (D : @DTri PT) (X : ob PT) :
    @FiveRowDiffs ABGR_AbelianPreCat (TriangulatedRowObs_to_X D X).
  Proof.
    use mk_FiveRowDiffs.
    - exact (to_premor_monoidfun PT _ _ _ (to_inv (# (AddEquiv1 Trans) (Mor1 D)))).
    - exact (to_premor_monoidfun PT _ _ _ (Mor3 D)).
    - exact (to_premor_monoidfun PT _ _ _ (Mor2 D)).
    - exact (to_premor_monoidfun PT _ _ _ (Mor1 D)).
  Defined.

  Definition TriangulatedRowDiffsEq_to_X (D : @DTri PT) (X : ob PT) :
    @FiveRowDiffsEq ABGR_AbelianPreCat _ (TriangulatedRowDiffs_to_X D X).
  Proof.
    use mk_FiveRowDiffsEq.
    - use monoidfun_eq. rewrite ABGR_has_zero_arrow_eq.
      intros x. cbn. unfold to_premor. rewrite assoc.
      set (tmp := DTriCompZero (RotDTri PT (RotDTri PT D))). cbn in tmp. cbn.
      apply (maponpaths (postcompose x)) in tmp. unfold postcompose in tmp.
      use (pathscomp0 tmp). clear tmp. rewrite ZeroArrow_comp_left.
      rewrite <- PreAdditive_unel_zero. unfold to_unel. apply idpath.
    - use monoidfun_eq. rewrite ABGR_has_zero_arrow_eq.
      intros x. cbn. unfold to_premor. rewrite assoc.
      set (tmp := DTriCompZero (RotDTri PT D)). cbn in tmp. cbn.
      apply (maponpaths (postcompose x)) in tmp. unfold postcompose in tmp.
      use (pathscomp0 tmp). clear tmp. rewrite ZeroArrow_comp_left.
      rewrite <- PreAdditive_unel_zero. unfold to_unel. apply idpath.
    - use monoidfun_eq. rewrite ABGR_has_zero_arrow_eq.
      intros x. cbn. unfold to_premor. rewrite assoc.
      set (tmp := DTriCompZero D). cbn in tmp. cbn.
      apply (maponpaths (postcompose x)) in tmp. unfold postcompose in tmp.
      cbn in tmp. use (pathscomp0 tmp). clear tmp. rewrite ZeroArrow_comp_left.
      rewrite <- PreAdditive_unel_zero. unfold to_unel. apply idpath.
  Qed.

  Local Opaque ABGR_AbelianPreCat ishinh.
  Definition TriangulatedRowExacts_to_X (D : @DTri PT) (X : ob PT) :
    @FiveRowExacts ABGR_AbelianPreCat has_homsets_ABGR _ _ (TriangulatedRowDiffsEq_to_X D X).
  Proof.
    use mk_FiveRowExacts.
    - unfold isExact. exact (@ShortShortExact_isKernel_to_X PT (RotDTri PT (RotDTri PT D)) X).
    - unfold isExact. exact (@ShortShortExact_isKernel_to_X PT (RotDTri PT D) X).
    - unfold isExact. exact (@ShortShortExact_isKernel_to_X PT D X).
  Qed.
  Local Transparent ABGR_AbelianPreCat ishinh.

  Definition TriangulatedRow_to_X (D : @DTri PT) (X : ob PT) :
    @FiveRow ABGR_AbelianPreCat has_homsets_ABGR.
  Proof.
    use mk_FiveRow.
    - exact (TriangulatedRowObs_to_X D X).
    - exact (TriangulatedRowDiffs_to_X D X).
    - exact (TriangulatedRowDiffsEq_to_X D X).
    - exact (TriangulatedRowExacts_to_X D X).
  Defined.

  Definition TriangulatedRowMors_to_X {D1 D2 : @DTri PT} (M : TriMor D1 D2) (X : ob PT) :
    @FiveRowMors ABGR_AbelianPreCat has_homsets_ABGR
                 (TriangulatedRow_to_X D2 X) (TriangulatedRow_to_X D1 X).
  Proof.
    use mk_FiveRowMors.
    - exact (to_premor_monoidfun PT _ _ _ (# (AddEquiv1 Trans) (MPMor2 M))).
    - exact (to_premor_monoidfun PT _ _ _ (# (AddEquiv1 Trans) (MPMor1 M))).
    - exact (to_premor_monoidfun PT _ _ _ (MPMor3 M)).
    - exact (to_premor_monoidfun PT _ _ _ (MPMor2 M)).
    - exact (to_premor_monoidfun PT _ _ _ (MPMor1 M)).
  Defined.

  Definition TriangulatedMorsComm_to_X {D1 D2 : @DTri PT} (M : TriMor D1 D2) (X : ob PT) :
    @FiveRowMorsComm ABGR_AbelianPreCat has_homsets_ABGR _ _ (TriangulatedRowMors_to_X M X).
  Proof.
    use mk_FiveRowMorsComm.
    - use monoidfun_eq.
      intros x. cbn. unfold to_premor. rewrite assoc. rewrite assoc.
      apply cancel_postcomposition. rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
      apply maponpaths. rewrite <- functor_comp. rewrite <- functor_comp.
      apply maponpaths. exact (MPComm1 M).
    - use monoidfun_eq.
      intros x. cbn. unfold to_premor. rewrite assoc. rewrite assoc.
      apply cancel_postcomposition. exact (DComm3 M).
    - use monoidfun_eq.
      intros x. cbn. unfold to_premor. rewrite assoc. rewrite assoc.
      apply cancel_postcomposition. exact (MPComm2 M).
    - use monoidfun_eq.
      intros x. cbn. unfold to_premor. rewrite assoc. rewrite assoc.
      apply cancel_postcomposition. exact (MPComm1 M).
  Qed.

  Definition TriangulatedMorphism_to_X {D1 D2 : @DTri PT} (M : TriMor D1 D2) (X : ob PT) :
    @FiveRowMorphism ABGR_AbelianPreCat has_homsets_ABGR
                     (TriangulatedRow_to_X D2 X) (TriangulatedRow_to_X D1 X) .
  Proof.
    use mk_FiveRowMorphism.
    - exact (TriangulatedRowMors_to_X M X).
    - exact (TriangulatedMorsComm_to_X M X).
  Defined.

  Lemma TriangulatedFiveLemma {D1 D2 : @DTri PT} (M : TriMor D1 D2)
        (H1 : is_z_isomorphism (MPMor1 M)) (H2 : is_z_isomorphism (MPMor2 M)) :
    is_z_isomorphism (MPMor3 M).
  Proof.
    set (Mor1 := TriangulatedMorphism_from_X M (Ob3 D2)).
    set (Mor2 := TriangulatedMorphism_to_X M (Ob3 D1)).
    assert (e1 : is_z_isomorphism (@FMor3 ABGR_AbelianPreCat has_homsets_ABGR _ _ Mor1)).
    {
      use FiveLemma.
      - exact (@ABGR_Additive_is_iso_postmor PT _ _ _ _ H1).
      - exact (@ABGR_Additive_is_iso_postmor PT _ _ _ _ H2).
      - exact (ABGR_Additive_is_iso_postmor
                 (Ob3 D2) _ _ (functor_on_is_z_isomorphism (AddEquiv1 (@Trans PT)) H1)).
      - exact (ABGR_Additive_is_iso_postmor
                 (Ob3 D2) _ _ (functor_on_is_z_isomorphism (AddEquiv1 (@Trans PT)) H2)).
    }
    assert (e2 : is_z_isomorphism (@FMor3 ABGR_AbelianPreCat has_homsets_ABGR _ _ Mor2)).
    {
      use FiveLemma.
      - exact (ABGR_Additive_is_iso_premor
                 _ _ (Ob3 D1) (functor_on_is_z_isomorphism (AddEquiv1 (@Trans PT)) H2)).
      - exact (ABGR_Additive_is_iso_premor
                 _ _ (Ob3 D1) (functor_on_is_z_isomorphism (AddEquiv1 (@Trans PT)) H1)).
      - exact (@ABGR_Additive_is_iso_premor PT _ _ _ _ H2).
      - exact (@ABGR_Additive_is_iso_premor PT _ _ _ _ H1).
    }
    exact (@ABGR_Additive_premor_postmor_is_iso PT _ _ (MPMor3 M) e2 e1).
  Qed.

  Lemma TriangulatedFiveLemma2 {D1 D2 : @DTri PT} (M : TriMor D1 D2)
        (H1 : is_z_isomorphism (MPMor1 M)) (H2 : is_z_isomorphism (MPMor3 M)) :
    is_z_isomorphism (MPMor2 M).
  Proof.
    exact (TriangulatedFiveLemma
             (InvRotTriMor M) (functor_on_is_z_isomorphism (AddEquiv2 Trans) H2) H1).
  Qed.

  Lemma TriangulatedFiveLemma1 {D1 D2 : @DTri PT} (M : TriMor D1 D2)
        (H1 : is_z_isomorphism (MPMor2 M)) (H2 : is_z_isomorphism (MPMor3 M)) :
    is_z_isomorphism (MPMor1 M).
  Proof.
    exact (TriangulatedFiveLemma
             (InvRotTriMor (InvRotTriMor M))
             (functor_on_is_z_isomorphism (AddEquiv2 Trans) H1)
             (functor_on_is_z_isomorphism (AddEquiv2 Trans) H2)).
  Qed.

End triangulated_five_lemma.


(** ** The following is used to prove octahedral axiom in K(A) *)
Section KA_Octa.

  Definition OctaConeIsoMPMorMors {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥)
             (H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥)
             (H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥)
             {x1' x2' y1' y2' z1' z2' : ob PT}
             {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
             {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
             {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
             (H1' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1' f2' f3') M ∥ ∥)
             (H2' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1' g2' g3') M ∥ ∥)
             (H3' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1' ;; g1') h2' h3') M ∥ ∥)
             (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
             (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
             (I3 : TriIso (mk_Tri (f1 ;; g1) h2 h3) (mk_Tri (f1' ;; g1') h2' h3'))
             (II12 : MPMor1 I2 = MPMor2 I1) (O : Octa H1' H2' H3')
             (M : Morphism) (II' : ConeIso (OctaDTri O) M) :
    MPMorMors
      (mk_Tri (MPMor3 I1 ;; OctaMor1 O ;; is_z_isomorphism_mor (TriMor_is_iso3 (TriIso_is_iso I3)))
              (MPMor3 I3 ;; OctaMor2 O ;; is_z_isomorphism_mor (TriMor_is_iso3 (TriIso_is_iso I2)))
              (g3 ;; # (AddEquiv1 Trans) f2))
      (ConeTri M (MConeOf _ (ConeIsoFiber II'))).
  Proof.
    use mk_MPMorMors.
    - exact (MPMor3 I1 ;; MPMor1 (ConeIsoMor II')).
    - exact (MPMor3 I3 ;; MPMor2 (ConeIsoMor II')).
    - exact (MPMor3 I2 ;; MPMor3 (ConeIsoMor II')).
  Defined.

  Definition OctaConeIsoMPMorMorsComm {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥)
             (H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥)
             (H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥)
             {x1' x2' y1' y2' z1' z2' : ob PT}
             {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
             {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
             {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
             (H1' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1' f2' f3') M ∥ ∥)
             (H2' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1' g2' g3') M ∥ ∥)
             (H3' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1' ;; g1') h2' h3') M ∥ ∥)
             (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
             (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
             (I3 : TriIso (mk_Tri (f1 ;; g1) h2 h3) (mk_Tri (f1' ;; g1') h2' h3'))
             (II12 : MPMor1 I2 = MPMor2 I1) (O : Octa H1' H2' H3')
             (M : Morphism) (II' : ConeIso (OctaDTri O) M) :
    MPMorComms (OctaConeIsoMPMorMors H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 O M II').
  Proof.
    use mk_MPMorComms.
    - cbn. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. use (pathscomp0 (MPComm1 (ConeIsoMor II'))).
      apply cancel_precomposition. rewrite assoc.
      set (tmp := is_inverse_in_precat2 (TriMor_is_iso3 (TriIso_is_iso I3))).
      apply (maponpaths (postcompose (MPMor2 (ConeIsoMor II')))) in tmp.
      use (pathscomp0 _ (! tmp)). clear tmp. unfold postcompose. rewrite id_left.
      apply idpath.
    - cbn. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. use (pathscomp0 (MPComm2 (ConeIsoMor II'))).
      apply cancel_precomposition. rewrite assoc.
      set (tmp := is_inverse_in_precat2 (TriMor_is_iso3 (TriIso_is_iso I2))).
      apply (maponpaths (postcompose (MPMor3 (ConeIsoMor II')))) in tmp.
      use (pathscomp0 _ (! tmp)). clear tmp. unfold postcompose. rewrite id_left.
      apply idpath.
  Qed.

  Local Lemma OctaConeIsoComm3 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥)
             (H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥)
             (H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥)
             {x1' x2' y1' y2' z1' z2' : ob PT}
             {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
             {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
             {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
             (H1' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1' f2' f3') M ∥ ∥)
             (H2' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1' g2' g3') M ∥ ∥)
             (H3' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1' ;; g1') h2' h3') M ∥ ∥)
             (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
             (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
             (I3 : TriIso (mk_Tri (f1 ;; g1) h2 h3) (mk_Tri (f1' ;; g1') h2' h3'))
             (II12 : MPMor1 I2 = MPMor2 I1) (O : Octa H1' H2' H3')
             (M : Morphism) (II' : ConeIso (OctaDTri O) M) :
    MPMor3 I2 ;; MPMor3 (ConeIsoMor II') ;; MCone2 (MConeOf _ (ConeIsoFiber II')) =
    g3 ;; # (AddEquiv1 Trans) f2 ;; # (AddEquiv1 Trans) (MPMor3 I1 ;; MPMor1 (ConeIsoMor II')).
  Proof.
    set (tmp := DComm3 (ConeIsoMor II')).
    rewrite <- assoc. apply (maponpaths (compose (MPMor3 I2))) in tmp.
    use (pathscomp0 tmp). clear tmp. rewrite functor_comp.
    rewrite assoc. rewrite assoc. apply cancel_postcomposition.
    set (tmp := DComm3 I2).
    apply (maponpaths (postcompose (# (AddEquiv1 Trans) f2'))) in tmp.
    unfold postcompose in tmp.
    cbn. rewrite assoc. use (pathscomp0 tmp). clear tmp.
    rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    rewrite <- functor_comp. rewrite <- functor_comp.
    set (tmp := MPComm2 I1). cbn in tmp. rewrite <- tmp. clear tmp.
    rewrite functor_comp. rewrite functor_comp. apply cancel_postcomposition.
    cbn. apply maponpaths. exact II12.
  Qed.

  Lemma OctaConeIsoOctaComm1 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥)
             (H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥)
             (H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥)
             {x1' x2' y1' y2' z1' z2' : ob PT}
             {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
             {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
             {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
             (H1' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1' f2' f3') M ∥ ∥)
             (H2' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1' g2' g3') M ∥ ∥)
             (H3' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1' ;; g1') h2' h3') M ∥ ∥)
             (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
             (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
             (I3 : TriIso (mk_Tri (f1 ;; g1) h2 h3) (mk_Tri (f1' ;; g1') h2' h3'))
             (II12 : MPMor1 I2 = MPMor2 I1) (II13 : MPMor1 I1 = MPMor1 I3)
             (II23 : MPMor2 I2 = MPMor2 I3) (O : Octa H1' H2' H3') :
    f2 ;; (MPMor3 I1 ;; OctaMor1 O ;; is_z_isomorphism_mor (TriMor_is_iso3 (TriIso_is_iso I3))) =
    g1 ;; h2.
  Proof.
    set (tmp := OctaComm1 O). cbn. cbn in tmp.
    rewrite assoc. rewrite assoc.
    set (tmp' := MPComm2 I1). cbn in tmp'. rewrite <- tmp'. clear tmp'.
    rewrite <- (assoc _ f2'). rewrite tmp. clear tmp. rewrite assoc.
    cbn in II12. rewrite <- II12.
    set (tmp := MPComm1 I2). cbn in tmp. rewrite tmp. clear tmp.
    rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    rewrite assoc. set (tmp := MPComm2 I3). cbn in tmp. cbn in II23. rewrite II23. rewrite tmp.
    clear tmp. set (tmp := is_inverse_in_precat1 (TriMor_is_iso3 (TriIso_is_iso I3))).
    rewrite <- assoc. cbn in tmp. rewrite tmp. clear tmp. rewrite id_right. apply idpath.
  Qed.

  Lemma OcataConeIsoOctaComm2 {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥)
             (H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥)
             (H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥)
             {x1' x2' y1' y2' z1' z2' : ob PT}
             {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
             {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
             {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
             (H1' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1' f2' f3') M ∥ ∥)
             (H2' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1' g2' g3') M ∥ ∥)
             (H3' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1' ;; g1') h2' h3') M ∥ ∥)
             (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
             (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
             (I3 : TriIso (mk_Tri (f1 ;; g1) h2 h3) (mk_Tri (f1' ;; g1') h2' h3'))
             (II12 : MPMor1 I2 = MPMor2 I1) (II13 : MPMor1 I1 = MPMor1 I3)
             (II23 : MPMor2 I2 = MPMor2 I3) (O : Octa H1' H2' H3') :
    MPMor3 I3 ;; OctaMor2 O ;; is_z_isomorphism_mor (TriMor_is_iso3 (TriIso_is_iso I2)) ;; g3 =
    h3 ;; # (AddEquiv1 Trans) f1.
  Proof.
    set (tmp := OctaComm2 O).
    rewrite <- assoc. rewrite <- assoc.
    set (tmp' := DComm3 I2). cbn in tmp'.
    apply (maponpaths (compose (is_z_isomorphism_mor (TriMor_is_iso3 (TriIso_is_iso I2)))))
      in tmp'.
    set (tmp'' := functor_on_is_z_isomorphism
                    (AddEquiv1 Trans) (TriMor_is_iso1 (TriIso_is_iso I2))).
    use (post_comp_with_z_iso_is_inj tmp''). clear tmp''.
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. cbn. cbn in tmp'. rewrite <- tmp'.
    clear tmp'. set (tmp'' := is_inverse_in_precat2 (TriMor_is_iso3 (TriIso_is_iso I2))).
    rewrite (assoc _ (MPMor3 I2)). cbn in tmp''. cbn. rewrite tmp''. clear tmp''.
    rewrite id_left. rewrite tmp. clear tmp.
    set (tmp := DComm3 I3). cbn in tmp. rewrite assoc. rewrite tmp. clear tmp.
    rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    cbn in II13. rewrite <- II13. rewrite <- functor_comp. rewrite <- functor_comp.
    apply maponpaths. set (tmp := MPComm1 I1). cbn in tmp. cbn in II12. rewrite II12. exact tmp.
  Qed.

  Definition OctaConeIso {PT : PreTriang} {x1 x2 y1 y2 z1 z2 : ob PT}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥)
             (H2 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥)
             (H3 : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥)
             {x1' x2' y1' y2' z1' z2' : ob PT}
             {f1' : x1' --> y1'} {f2' : y1' --> z2'} {f3' : z2' --> (AddEquiv1 Trans x1')}
             {g1' : y1' --> z1'} {g2' : z1' --> x2'} {g3' : x2' --> (AddEquiv1 Trans y1')}
             {h2' : z1' --> y2'} {h3' : y2' --> (AddEquiv1 Trans x1')}
             (H1' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri f1' f2' f3') M ∥ ∥)
             (H2' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri g1' g2' g3') M ∥ ∥)
             (H3' : ∥ Σ M : Morphism, ∥ ConeIso (mk_Tri (f1' ;; g1') h2' h3') M ∥ ∥)
             (I1 : TriIso (mk_Tri f1 f2 f3) (mk_Tri f1' f2' f3'))
             (I2 : TriIso (mk_Tri g1 g2 g3) (mk_Tri g1' g2' g3'))
             (I3 : TriIso (mk_Tri (f1 ;; g1) h2 h3) (mk_Tri (f1' ;; g1') h2' h3'))
             (II12 : MPMor1 I2 = MPMor2 I1) (II13 : MPMor1 I1 = MPMor1 I3)
             (II23 : MPMor2 I2 = MPMor2 I3) :
    Octa H1' H2' H3' -> Octa H1 H2 H3.
  Proof.
    intros O.
    use mk_Octa.
    - exact (MPMor3 I1 ;; OctaMor1 O ;; is_z_isomorphism_mor (TriMor_is_iso3 (TriIso_is_iso I3))).
    - exact (MPMor3 I3 ;; OctaMor2 O ;; is_z_isomorphism_mor (TriMor_is_iso3 (TriIso_is_iso I2))).
    - use (squash_to_prop (DTriIso (OctaDTri O)) (propproperty _)). intros MM.
      induction MM as [M II].
      intros P X. apply X. clear X P.
      use tpair.
      + exact M.
      + use (squash_to_prop II (propproperty _)). intros II'.
        intros P X. apply X. clear X P.
        use mk_ConeIso.
        * exact (ConeIsoFiber II').
        * use mk_TriMor.
          -- use mk_MPMor.
             ++ exact (OctaConeIsoMPMorMors H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 O M II').
             ++ exact (OctaConeIsoMPMorMorsComm H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 O M II').
          -- exact (OctaConeIsoComm3 H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 O M II').
        * use mk_TriMor_is_iso.
          -- use is_z_isomorphism_comp.
             ++ exact (TriMor_is_iso3 (TriIso_is_iso I1)).
             ++ exact (TriMor_is_iso1 (ConeIsoMor_is_iso II')).
          -- use is_z_isomorphism_comp.
             ++ exact (TriMor_is_iso3 (TriIso_is_iso I3)).
             ++ exact (TriMor_is_iso2 (ConeIsoMor_is_iso II')).
          -- use is_z_isomorphism_comp.
             ++ exact (TriMor_is_iso3 (TriIso_is_iso I2)).
             ++ exact (TriMor_is_iso3 (ConeIsoMor_is_iso II')).
    - exact (OctaConeIsoOctaComm1 H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 II13 II23 O).
    - exact (OcataConeIsoOctaComm2 H1 H2 H3 H1' H2' H3' I1 I2 I3 II12 II13 II23 O).
  Defined.

End KA_Octa.
