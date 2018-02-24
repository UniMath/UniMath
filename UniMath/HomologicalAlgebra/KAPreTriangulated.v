(** * K(A) is a pretriangulated category *)
(** Contents
- K(A) pretriangulated
 - Pretriangulated data
 - Trivial triangle is distinguished
 - Rotations of triangles
 - Every morphism can be completed to a distinguished triangle
 - Extension of triangles
 - Distinguished triangles are closed under isomorphism
 - K(A) pretriangulated
*)

Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.MonoidsAndGroups.

Require Import UniMath.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.Total2Paths.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.Limits.Zero.
Require Import UniMath.CategoryTheory.Limits.Binproducts.
Require Import UniMath.CategoryTheory.Limits.Bincoproducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Kernels.
Require Import UniMath.CategoryTheory.Limits.Cokernels.
Require Import UniMath.CategoryTheory.Limits.Pushouts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.BinDirectSums.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.FunctorCategories.
Require Import UniMath.CategoryTheory.Equivalences.

Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.ShortExactSequences.
Require Import UniMath.CategoryTheory.Categories.Abgrs.

Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Morphisms.
Require Import UniMath.CategoryTheory.AdditiveFunctors.

Require Import UniMath.HomologicalAlgebra.Complexes.
Require Import UniMath.HomologicalAlgebra.Triangulated.
Require Import UniMath.HomologicalAlgebra.KA.
Require Import UniMath.HomologicalAlgebra.TranslationFunctors.
Require Import UniMath.HomologicalAlgebra.MappingCone.

Unset Kernel Term Sharing.
Opaque hz isdecrelhzeq hzplus hzminus hzone hzzero iscommrngops ZeroArrow.


(** * K(A) with a structure of a pretriangulated category *)
(** ** Introduction
Let f : X --> Y be a morphism in K(A). We use [squash_to_prop] to obtain a morphism f' : X --> Y
which maps to f by the natural functor C(A) -> K(A). To f' we associate a cone given by C(f'),
the mapping cone of f' in C(A). The translation functors give the natural equivalence
T : K(A) -> K(A). A distinguished triangle in K(A) is a triangle (X,Y,Z,u,v,w) such that there
exists a morphism M of K(A), and a fiber M' of M, such that we have the following isomorphism of
triangles
                             X --u--> Y --v-->   Z  --w-->  X[1]
                             |        |          |            |
                             X' -M'-> Y -in2-> C(M') -pr1-> X[1]

To show that K(A) is pretriangulated, it suffices to show that
- Trivial triangle is distinguished
- Distinguished triangles are closed under isomorphism
- Rotation of a distinguished triangle is distinguished
- Inverse rotation of a distinguished triangle is distinguished
- Any morphism can be completed to a distinguished triangle
- Any commutative square coming from distinguished triangles can be completed to a morphism
  of distinguished triangles.

To show that trivial triangle is distinguished, we construct the following isomorphism of triangles
                         X --> X -->    0    -->  Y[1]
                         |     |        |          |
                         X --> X --> C(Id_X) -->  Y[1]
To prove rotation of distinguished triangles, we construct the following isomorphism of triangles
                         Y --> C(f') --> C(i2)-->  Y[1]
                         |       |         |         |
                         Y --> C(f') -->  X[1] --> Y[1]
To prove inverse rotation of distinguished triangles, we construct the following isomorphism of
triangles
                      C(f)[-1] -->  X   -->   Y   -->  C(f)
                         |          |         |          |
                      C(f)[-1]  --> X -->C(-p1[-1])--> C(f)
Extension of triangles is given by the following morphism of triangles
                         X   -g->  Y   -->  C(g) --> Y[1]
                         |         |          |        |
                         X' -g'->  Y'  --> C(g') --> Y[1]
*)
Section KAPreTriangulated.

  Context {A : Additive}.

  Local Opaque ComplexHomotFunctor ComplexHomotSubset Quotcategory identity
        MappingConePr1 MappingConeIn2 RotMorphism RotMorphismInv InvRotMorphism InvRotMorphismInv
        to_inv compose pathsinv0 pathscomp0 ishinh to_abgrop.

  Definition MappingConeTri {x y : ob (ComplexHomot_Additive A)} (f : x --> y)
             (f' : hfiber (# (ComplexHomotFunctor A)) f) :
    @Tri (ComplexHomot_Additive A) (TranslationHEquiv A).
  Proof.
    use mk_Tri.
    - exact x.
    - exact y.
    - exact (MappingCone A (hfiberpr1 _ _ f')).
    - exact f.
    - exact (# (ComplexHomotFunctor A) (MappingConeIn2 A (hfiberpr1 _ _ f'))).
    - exact (# (ComplexHomotFunctor A) (MappingConePr1 A (hfiberpr1 _ _ f'))).
  Defined.

  Definition KADTriData (T : @Tri (ComplexHomot_Additive A) (TranslationHEquiv A)) : UU :=
    ∑ D : (∑ M : @Morphisms.Morphism (ComplexHomot_Additive A),
                 hfiber (# (ComplexHomotFunctor A)) M),
          TriIso T (MappingConeTri (pr1 D) (pr2 D)).

  Definition mk_KADTriData {T : @Tri (ComplexHomot_Additive A) (TranslationHEquiv A)}
             (M : @Morphisms.Morphism (ComplexHomot_Additive A))
             (M' : hfiber (# (ComplexHomotFunctor A)) M)
             (I : TriIso T (MappingConeTri M M')) : KADTriData T :=
    ((M,,M'),,I).

  Definition KADTriDataMor {T : @Tri (ComplexHomot_Additive A) (TranslationHEquiv A)}
    (D : KADTriData T) : @Morphisms.Morphism (ComplexHomot_Additive A) := pr1 (pr1 D).

  Definition KADTriDataFiber {T : @Tri (ComplexHomot_Additive A) (TranslationHEquiv A)}
             (D : KADTriData T) : hfiber (# (ComplexHomotFunctor A)) (KADTriDataMor D) :=
    pr2 (pr1 D).

  Definition KADTriDataIso {T : @Tri (ComplexHomot_Additive A) (TranslationHEquiv A)}
             (D : KADTriData T) : TriIso T (MappingConeTri (KADTriDataMor D) (KADTriDataFiber D)) :=
    pr2 D.

  Definition KAisDTri (T : @Tri (ComplexHomot_Additive A) (TranslationHEquiv A)) : hProp :=
    ∥ KADTriData T ∥.

  Definition KAPreTriangData : PreTriangData.
  Proof.
    use mk_PreTriangData.
    - exact (ComplexHomot_Additive A).
    - exact (TranslationHEquiv A).
    - intros T. exact (KAisDTri T).
  Defined.

  Lemma KAFiberisDTri (M : @Morphisms.Morphism (ComplexHomot_Additive A))
        (M' : hfiber (# (ComplexHomotFunctor A)) M) :
    @isDTri KAPreTriangData (MappingConeTri M M').
  Proof.
    use hinhpr.
    use mk_KADTriData.
    - exact M.
    - exact M'.
    - exact (TriIsoId _).
  Qed.

  Definition KADTriDataDTri {T : @Tri (ComplexHomot_Additive A) (TranslationHEquiv A)}
             (D : KADTriData T) : @DTri KAPreTriangData.
  Proof.
    use mk_DTri'.
    - exact (MappingConeTri (KADTriDataMor D) (KADTriDataFiber D)).
    - exact (KAFiberisDTri (KADTriDataMor D) (KADTriDataFiber D)).
  Defined.

  (** Different fibers of a same morphism induce an isomorphism *)

  Lemma KAIdComml {x y : ob KAPreTriangData} (f g : x --> y) (e : f = g) :
    identity _ · f =  g.
  Proof.
    rewrite id_left. exact e.
  Qed.

  Lemma KAIdCommr {x y : ob KAPreTriangData} (f g : x --> y) (e : f = g) :
    f · identity _ =  g.
  Proof.
    rewrite id_right. exact e.
  Qed.

  Lemma KAIdComm {x y : ob KAPreTriangData} (f g : x --> y) (e : f = g) :
    f · identity _ = identity _ · g.
  Proof.
    rewrite id_left. rewrite id_right. exact e.
  Qed.

  Definition KAFiber {x y : ob (ComplexPreCat_Additive A)} (f : x --> y) :
    hfiber (# (ComplexHomotFunctor A)) (# (ComplexHomotFunctor A) f) :=
    hfiberpair (# (ComplexHomotFunctor A)) f (idpath _).

  Definition KAFiberIsoMor {x y : KAPreTriangData} {f : x --> y}
             (f' f'' : hfiber (# (ComplexHomotFunctor A)) f)
             (f1 := hfiberpr1 _ _ f') (f2 := hfiberpr1 _ _ f'')
             (Ho : ComplexHomot A x y)
             (e : to_binop _ _ f1 (to_inv f2) = ComplexHomotMorphism A Ho) :
    MPMorMors (MappingConeTri f f') (MappingConeTri f f'').
  Proof.
    use mk_MPMorMors.
    - exact (identity _).
    - exact (identity _).
    - exact (# (ComplexHomotFunctor A) (FiberExt A f1 f2 Ho e)).
  Defined.

  Lemma KAFiberIsoMorComms {x y : KAPreTriangData} {f : x --> y}
             (f' f'' : hfiber (# (ComplexHomotFunctor A)) f)
             (f1 := hfiberpr1 _ _ f') (f2 := hfiberpr1 _ _ f'')
             (Ho : ComplexHomot A x y)
             (e : to_binop _ _ f1 (to_inv f2) = ComplexHomotMorphism A Ho) :
    MPMorComms (KAFiberIsoMor f' f'' Ho e).
  Proof.
    use mk_MPMorComms.
    - exact (! (KAIdComm _ _ (idpath _))).
    - use KAIdComml.
      exact (! (FiberExt_Comm2H A f1 f2 Ho e)).
  Qed.

  Lemma KAFiberIsoMorComm3 {x y : KAPreTriangData} {f : x --> y}
        (f' f'' : hfiber (# (ComplexHomotFunctor A)) f)
        (f1 := hfiberpr1 _ _ f') (f2 := hfiberpr1 _ _ f'')
        (Ho : ComplexHomot A x y)
        (e : to_binop _ _ f1 (to_inv f2) = ComplexHomotMorphism A Ho) :
    (MPMor3 (mk_MPMor (KAFiberIsoMor f' f'' Ho e) (KAFiberIsoMorComms f' f'' Ho e)))
      · Mor3 (MappingConeTri f f'') =
    (Mor3 (MappingConeTri f f'))
      · (# (AddEquiv1 (@Trans KAPreTriangData))
            (MPMor1 (mk_MPMor (KAFiberIsoMor f' f'' Ho e) (KAFiberIsoMorComms f' f'' Ho e)))).
  Proof.
    cbn. rewrite functor_id. use (! (KAIdCommr _ _ _)).
    exact (FiberExt_Comm3H A f1 f2 Ho e).
  Qed.

  Definition KAFiberIso {x y : KAPreTriangData} {f : x --> y}
             (f' f'' : hfiber (# (ComplexHomotFunctor A)) f)
             (f1 := hfiberpr1 _ _ f') (f2 := hfiberpr1 _ _ f'')
             (Ho : ComplexHomot A x y)
             (e : to_binop _ _ f1 (to_inv f2) = ComplexHomotMorphism A Ho) :
    TriIso (MappingConeTri f f') (MappingConeTri f f'').
  Proof.
    use mk_TriIso.
    - use mk_TriMor.
      + use mk_MPMor.
        * exact (KAFiberIsoMor f' f'' Ho e).
        * exact (KAFiberIsoMorComms f' f'' Ho e).
      + exact (KAFiberIsoMorComm3 f' f'' Ho e).
    - use mk_TriMor_is_iso.
      + exact (is_z_isomorphism_identity _).
      + exact (is_z_isomorphism_identity _).
      + exact (FiberExt_is_z_isomorphism A f1 f2 Ho e).
  Defined.


  (** ** Trivial triangle is distinguished *)

  Definition KATrivialDistinguished_MPMorMors (x : ob KAPreTriangData)
             (i' := @hfiberpair _ _ (# (ComplexHomotFunctor A)) _ _
                                (functor_id (ComplexHomotFunctor A) x)) :
    @MPMorMors KAPreTriangData (@TrivialTri _ (@Trans KAPreTriangData) x)
               (MappingConeTri (identity x) i').
  Proof.
    use mk_MPMorMors.
    - exact (# (ComplexHomotFunctor A) (identity _)).
    - exact (# (ComplexHomotFunctor A) (identity _)).
    - exact (ZeroArrow (to_Zero _) _ _).
  Defined.

  Local Lemma KATrivialDistinguished_MPMorsComm (x : ob (ComplexPreCat_Additive A)) :
    MPMorComms (KATrivialDistinguished_MPMorMors x).
  Proof.
    use mk_MPMorComms.
    - apply idpath.
    - cbn. rewrite (functor_id (ComplexHomotFunctor A)).
      rewrite (@id_left (ComplexHomot_Additive A)).
      rewrite (@ZeroArrow_comp_right (ComplexHomot_Additive A)).
      use (pathscomp0 _ (AdditiveFunctorZeroArrow (ComplexHomotFunctor A) _ _)).
      exact (MappingConeIn2Eq A x).
  Qed.

  Definition KATrivialDistinguished_TriMor (x : ob KAPreTriangData)
             (i' := @hfiberpair _ _ (# (ComplexHomotFunctor A)) _ _
                                (functor_id (ComplexHomotFunctor A) x)) :
    TriMor (TrivialTri x) (MappingConeTri (identity x) i').
  Proof.
    use mk_TriMor.
    - exact (mk_MPMor (KATrivialDistinguished_MPMorMors x)
                      (KATrivialDistinguished_MPMorsComm x)).
    - cbn. rewrite (@ZeroArrow_comp_left (ComplexHomot_Additive A)).
      rewrite (@ZeroArrow_comp_left (ComplexHomot_Additive A)). apply idpath.
  Defined.

  Lemma KATrivialDistinguished : ∏ x : KAPreTriangData, isDTri (TrivialTri x).
  Proof.
    intros x.
    set (i' := @hfiberpair _ _ (# (ComplexHomotFunctor A)) _ _
                           (functor_id (ComplexHomotFunctor A) x)).
    use hinhpr.
    use mk_KADTriData.
    - exact (Morphisms.mk_Morphism (identity x)).
    - exact i'.
    - use mk_TriIso.
      + exact (KATrivialDistinguished_TriMor x).
      + use mk_TriMor_is_iso.
        * exact (functor_on_is_z_isomorphism
                   (ComplexHomotFunctor A)
                   (@is_z_isomorphism_identity (ComplexPreCat_Additive A) (x : Complex A))).
        * exact (functor_on_is_z_isomorphism
                   (ComplexHomotFunctor A)
                   (@is_z_isomorphism_identity (ComplexPreCat_Additive A) (x : Complex A))).
        * exact (IDMappingCone_is_z_isomorphism A x).
  Qed.


  (** ** Rotation of distinguished triangles *)

  Local Lemma KARotDTris_Comm2 (D : @DTri KAPreTriangData) (I : KADTriData D)
    (I' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I) (KADTriDataFiber I)) :
    identity _ · # (ComplexHomotFunctor A) (MappingConeIn2 A (MappingConeIn2 A I')) =
    # (ComplexHomotFunctor A) (MappingConePr1 A I') · # (ComplexHomotFunctor A) (RotMorphism A I').
  Proof.
    use (pathscomp0 (id_left _)).
    use (pathscomp0 _ ((functor_comp (ComplexHomotFunctor A)
                                     (MappingConePr1 A I') (RotMorphism A I')))).
    exact (! (RotMorphism_comm A I')).
  Qed.

  Local Lemma KARotDTris_Comm3 (D : @DTri KAPreTriangData) (I : KADTriData D)
    (I' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I) (KADTriDataFiber I)) :
    # (ComplexHomotFunctor A) (RotMorphism A I')
      · # (ComplexHomotFunctor A) (MappingConePr1 A (MappingConeIn2 A I')) =
    to_inv (# (AddEquiv1 (TranslationHEquiv A)) (KADTriDataMor I))
           · # (AddEquiv1 (TranslationHEquiv A)) (identity (Target (KADTriDataMor I))).
  Proof.
    use (pathscomp0
           (! (functor_comp (ComplexHomotFunctor A) (RotMorphism A I')
                            (MappingConePr1 A (MappingConeIn2 A I'))))).
    use (pathscomp0 (! (maponpaths (# (ComplexHomotFunctor A)) (RotMorphism_comm2 A I')))).
    rewrite functor_id. rewrite id_right.
    rewrite (AdditiveFunctorInv (ComplexHomotFunctor A)). apply maponpaths.
    apply pathsinv0. apply TranslationFunctorHImEq. exact (hfiberpr2 _ _ (KADTriDataFiber I)).
  Qed.

  Definition KARotDTris_Iso (D : @DTri KAPreTriangData) (I : KADTriData D)
             (I' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I) (KADTriDataFiber I)) :
    TriIso (RotTri D)
           (MappingConeTri
              (Morphisms.mk_Morphism (Mor2 (MappingConeTri (KADTriDataMor I) (KADTriDataFiber I))))
              (KAFiber (MappingConeIn2 A I'))).
  Proof.
    use (TriIso_comp (RotTriIso (KADTriDataIso I))).
    use mk_TriIso.
    - use mk_TriMor.
      + use mk_MPMor.
        * use mk_MPMorMors.
          -- exact (identity _).
          -- exact (identity _).
          -- exact (# (ComplexHomotFunctor A) (RotMorphism A I')).
        * use mk_MPMorComms.
          -- exact (! (KAIdComm _ _ (idpath _))).
          -- exact (KARotDTris_Comm2 D I).
      + exact (KARotDTris_Comm3 D I).
    - use mk_TriMor_is_iso.
      + exact (is_z_isomorphism_identity _).
      + exact (is_z_isomorphism_identity _).
      + exact (RotMorphism_is_z_isomorphism A _).
  Defined.

  Lemma KARotDTris : ∏ D : DTri, @isDTri KAPreTriangData (RotTri D).
  Proof.
    intros D.
    use (squash_to_prop (DTriisDTri D) (propproperty _)). intros I.
    use hinhpr.
    use mk_KADTriData.
    - exact (Morphisms.mk_Morphism (Mor2 (MappingConeTri (KADTriDataMor I) (KADTriDataFiber I)))).
    - exact (KAFiber (MappingConeIn2 A (hfiberpr1 _ _ (KADTriDataFiber I)))).
    - exact (KARotDTris_Iso D I).
  Qed.

  (** ** Inverse rotation of distinguished triangles *)

  Lemma KAInvRotDTris_Comm1 (D : @DTri KAPreTriangData) (I : KADTriData D)
        (I' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I) (KADTriDataFiber I)) :
    (identity _) · (# (ComplexHomotFunctor A)
                       ((to_inv (# (InvTranslationFunctor A) (MappingConePr1 A I')))
                          · TranslationEquivUnitInv A (Source (KADTriDataMor I)))) =
    (to_inv (# (AddEquiv2 (TranslationHEquiv A)) (# (ComplexHomotFunctor A) (MappingConePr1 A I'))))
      · # (ComplexHomotFunctor A) (TranslationEquivUnitInv A (Source (KADTriDataMor I)))
      · identity (Source (KADTriDataMor I)).
  Proof.
    use (! (KAIdComm _ _ _)).
    use (pathscomp0 _ (! (functor_comp
                            (ComplexHomotFunctor A)
                            (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A I')))
                            (z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A)
                                                            (Source (KADTriDataMor I))))))).
    set (tmp''' := @AdditiveFunctorInv
                     _ _ (ComplexHomotFunctor A)
                     _ _ (# (InvTranslationFunctor A) (MappingConePr1 A I'))).
    apply (maponpaths
             (postcompose
                (# (ComplexHomotFunctor A)
                   (z_iso_inv_mor
                      (AddEquivUnitIso (TranslationEquiv A) (Source (KADTriDataMor I)))))))
      in tmp'''.
    use (pathscomp0 _ (! tmp''')). clear tmp'''. unfold postcompose.
    apply cancel_postcomposition. apply maponpaths.
    use InvTranslationFunctorHImEq. apply idpath.
  Qed.

  Lemma KAInvRotDTris_Comm2 (D : @DTri KAPreTriangData) (I : KADTriData D)
        (I' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I) (KADTriDataFiber I)) :
    (identity (Source (KADTriDataMor I)))
      · (# (ComplexHomotFunctor A)
            (MappingConeIn2 A ((to_inv (# (InvTranslationFunctor A) (MappingConePr1 A I')))
                                 · TranslationEquivUnitInv A (Source (KADTriDataMor I))))) =
    KADTriDataMor I · # (ComplexHomotFunctor A) (InvRotMorphismInv A I').
  Proof.
    rewrite id_left. use (pathscomp0 (! (InvRotMorphismInvComm1 A I'))).
    use (pathscomp0 (functor_comp (ComplexHomotFunctor A) _ _)).
    use cancel_postcomposition.
    exact (hfiberpr2 _ _ (KADTriDataFiber I)).
  Qed.

  Lemma KAInvRotDTris_Comm3 (D : @DTri KAPreTriangData) (I : KADTriData D)
        (I' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I) (KADTriDataFiber I)) :
    (# (ComplexHomotFunctor A) (InvRotMorphismInv A I'))
      · (# (ComplexHomotFunctor A)
            (MappingConePr1
               A ((to_inv (# (InvTranslationFunctor A) (MappingConePr1 A I')))
                    · TranslationEquivUnitInv A (Source (KADTriDataMor I))))) =
    (# (ComplexHomotFunctor A) (MappingConeIn2 A I'))
      · # (ComplexHomotFunctor A) (TranslationEquivCounitInv A (MappingCone A I'))
      · (# (AddEquiv1 (TranslationHEquiv A))
            (identity ((AddEquiv2 (TranslationHEquiv A)) (MappingCone A I')))).
  Proof.
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A) _ _))).
    use (pathscomp0 (maponpaths # (ComplexHomotFunctor A) (! (InvRotMorphismInvComm2 A I')))).
    rewrite functor_id. use (pathscomp0 _ (! (id_right _))).
    exact (functor_comp (ComplexHomotFunctor A) _ _).
  Qed.

  Local Opaque AddEquiv1 AddEquiv2.

  Definition KAInvRotDTris_Iso (D : @DTri KAPreTriangData) (I : KADTriData D)
             (I' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I) (KADTriDataFiber I)) :
    TriIso (InvRotTri D)
           (MappingConeTri
              (# (ComplexHomotFunctor A)
                 ((to_inv (# (InvTranslationFunctor A) (MappingConePr1 A I')))
                    · z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A)
                                                      (Source (KADTriDataMor I)))))
              (KAFiber
                 ((to_inv (# (InvTranslationFunctor A) (MappingConePr1 A I')))
                    · z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A)
                                                      (Source (KADTriDataMor I)))))).
  Proof.
    use (TriIso_comp (InvRotTriIso (KADTriDataIso I))).
    use mk_TriIso.
    - use mk_TriMor.
      + use mk_MPMor.
        * use mk_MPMorMors.
          -- exact (identity _).
          -- exact (identity _).
          -- exact (# (ComplexHomotFunctor A) (InvRotMorphismInv A I')).
        * use mk_MPMorComms.
          -- exact (KAInvRotDTris_Comm1 D I).
          -- exact (KAInvRotDTris_Comm2 D I).
      + exact (KAInvRotDTris_Comm3 D I).
    - use mk_TriMor_is_iso.
      + exact (is_z_isomorphism_identity _).
      + exact (is_z_isomorphism_identity _).
      + exact (InvRotMorphism_is_z_isomorphism A _).
  Defined.

  Lemma KAInvRotDTris : ∏ D : DTri, @isDTri KAPreTriangData (InvRotTri D).
  Proof.
    intros D.
    use (squash_to_prop (DTriisDTri D) (propproperty _)). intros I.
    set (i' := hfiberpr1 _ _ (KADTriDataFiber I)).
    use hinhpr.
    use mk_KADTriData.
    - exact (Morphisms.mk_Morphism
               (# (ComplexHomotFunctor A)
                  (to_inv (# (InvTranslationFunctor A)
                             (MappingConePr1 A i')) ·
                          z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A)
                                                         (Source (KADTriDataMor I)))))).
    - exact (KAFiber (to_inv (# (InvTranslationFunctor A)
                             (MappingConePr1 A i')) ·
                             z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A)
                                                            (Source (KADTriDataMor I))))).
    - exact (KAInvRotDTris_Iso D I).
  Qed.

  (** ** Completion to distinguished triangle *)

  Local Opaque TranslationFunctor TranslationFunctorH.

  Lemma KAConeDTri :
    ∏ (x y : KAPreTriangData) (f : KAPreTriangData ⟦ x, y ⟧),
    ∃ D : ConeData Trans x y, isDTri (ConeTri f D).
  Proof.
    intros x y f.
    use (squash_to_prop (ComplexHomotFunctor_issurj A f) (propproperty _)). intros f'.
    set (f'' := hfiberpr1 _ _ f').
    use hinhpr.
    use tpair.
    - use mk_ConeData.
      + exact ((ComplexHomotFunctor A) (MappingCone A f'')).
      + exact (# (ComplexHomotFunctor A) (MappingConeIn2 A f'')).
      + exact (# (ComplexHomotFunctor A) (MappingConePr1 A f'')).
    - use hinhpr.
      use mk_KADTriData.
      + exact (Morphisms.mk_Morphism f).
      + exact f'.
      + use mk_TriIso.
        * use mk_TriMor.
          -- use mk_MPMor.
             ++ use mk_MPMorMors.
                ** exact (identity _).
                ** exact (identity _).
                ** exact (identity _).
             ++ use mk_MPMorComms.
                ** exact (! (KAIdComm _ _ (idpath _))).
                ** exact (! (KAIdComm _ _ (idpath _))).
          -- cbn. rewrite id_left.
             use (pathscomp0 (! (id_right _))). apply cancel_precomposition.
             apply (! (functor_id _ _)).
        * use mk_TriMor_is_iso.
          -- exact (is_z_isomorphism_identity _).
          -- exact (is_z_isomorphism_identity _).
          -- exact (is_z_isomorphism_identity _).
  Qed.

  (** ** Extension of squares *)

  Lemma KAExt_Comm1 (D1 D2 : DTri) (g1 : KAPreTriangData ⟦ Ob1 D1, Ob1 D2 ⟧)
        (g2 : KAPreTriangData ⟦ Ob2 D1, Ob2 D2 ⟧) (H : g1 · Mor1 D2 = Mor1 D1 · g2)
        (I1 : KADTriData D1) (I2 : KADTriData D2) :
    (MPMor1 (TriIsoInv (KADTriDataIso I1)))
       · g1 · (MPMor1 (KADTriDataIso I2)) · (KADTriDataMor I2) =
    (KADTriDataMor I1)
      · (MPMor2 (TriIsoInv (KADTriDataIso I1))) · g2 · (MPMor2 (KADTriDataIso I2)).
  Proof.
    set (tmp := MPComm1 (TriIsoInv (KADTriDataIso I1))).
    apply (maponpaths (postcompose (g2 · MPMor2 (KADTriDataIso I2)))) in tmp.
    unfold postcompose in tmp. rewrite assoc in tmp. rewrite assoc in tmp. use (pathscomp0 _ tmp).
    clear tmp.
    rewrite <- (assoc (MPMor1 (TriIsoInv (KADTriDataIso I1)))).
    rewrite <- (assoc (MPMor1 (TriIsoInv (KADTriDataIso I1)))).
    rewrite <- (assoc (MPMor1 (TriIsoInv (KADTriDataIso I1)))).
    rewrite <- (assoc (MPMor1 (TriIsoInv (KADTriDataIso I1)))).
    apply cancel_precomposition.
    apply (maponpaths (postcompose (MPMor2 (KADTriDataIso I2)))) in H.
    unfold postcompose in H. use (pathscomp0 _ H). clear H.
    rewrite <- (assoc g1). rewrite <- (assoc g1). apply cancel_precomposition.
    exact (MPComm1 (KADTriDataIso I2)).
  Qed.

  Lemma KAExt_MorEq (D1 D2 : DTri) (g1 : KAPreTriangData ⟦ Ob1 D1, Ob1 D2 ⟧)
             (g2 : KAPreTriangData ⟦ Ob2 D1, Ob2 D2 ⟧) (H : g1 · Mor1 D2 = Mor1 D1 · g2)
             (I1 : KADTriData D1) (I2 : KADTriData D2)
             (h1 : hfiber # (ComplexHomotFunctor A)
                          (MPMor1 (TriIsoInv (KADTriDataIso I1))
                                  · g1 · MPMor1 (KADTriDataIso I2)))
             (h2 : hfiber # (ComplexHomotFunctor A)
                          (MPMor2 (TriIsoInv (KADTriDataIso I1))
                                  · g2 · MPMor2 (KADTriDataIso I2)))
             (I1' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I1) (KADTriDataFiber I1))
             (I2' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I2) (KADTriDataFiber I2))
             (h1' := hfiberpr1 _ _ h1) (h2' := hfiberpr1 _ _ h2) :
    # (ComplexHomotFunctor A) (I1' · h2') = # (ComplexHomotFunctor A) (h1' · I2').
  Proof.
    use ComplexHomotComm2. rewrite assoc. rewrite assoc.
    exact (! (KAExt_Comm1 D1 D2 g1 g2 H I1 I2)).
  Qed.

  Lemma KAExt_Comm2 (D1 D2 : DTri) (g1 : KAPreTriangData ⟦ Ob1 D1, Ob1 D2 ⟧)
        (g2 : KAPreTriangData ⟦ Ob2 D1, Ob2 D2 ⟧) (H : g1 · Mor1 D2 = Mor1 D1 · g2)
        (I1 : KADTriData D1) (I2 : KADTriData D2)
        (h1 : hfiber # (ComplexHomotFunctor A)
                     (MPMor1 (TriIsoInv (KADTriDataIso I1)) · g1 · MPMor1 (KADTriDataIso I2)))
        (h2 : hfiber # (ComplexHomotFunctor A)
                     (MPMor2 (TriIsoInv (KADTriDataIso I1)) · g2 · MPMor2 (KADTriDataIso I2)))
        (I1' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I1) (KADTriDataFiber I1))
        (I2' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I2) (KADTriDataFiber I2))
        (h1' := hfiberpr1 # (ComplexHomotFunctor A)
                          (is_z_isomorphism_mor (TriMor_is_iso1 (KADTriDataIso I1))
                                                · g1 · MPMor1 (KADTriDataIso I2)) h1)
        (h2' := hfiberpr1 # (ComplexHomotFunctor A)
                          (is_z_isomorphism_mor (TriMor_is_iso2 (KADTriDataIso I1))
                                                · g2 · MPMor2 (KADTriDataIso I2)) h2)
        (HH1 : ComplexHomot A (Source (KADTriDataMor I1))
                            (Ob2 (MappingConeTri (KADTriDataMor I2) (KADTriDataFiber I2))))
        (HH2 : ComplexHomotMorphism A HH1 =
               @to_binop (ComplexPreCat_Additive A) (Source (KADTriDataMor I1))
                         (Ob2 (MappingConeTri (KADTriDataMor I2) (KADTriDataFiber I2)))
                         (I1' · h2') (to_inv (h1' · I2'))) :
    # (ComplexHomotFunctor A) (MappingConeIn2 A I1')
      · # (ComplexHomotFunctor A) (MappingConeMorExt A I1' I2' h1' h2' HH1 (! HH2)) =
    (is_z_isomorphism_mor (TriMor_is_iso2 (KADTriDataIso I1)))
      · g2 · MPMor2 (KADTriDataIso I2)
      · # (ComplexHomotFunctor A) (MappingConeIn2 A I2').
  Proof.
    set (tmp := hfiberpr2 _ _ h2).
    apply (maponpaths (postcompose (Mor2 (MappingConeTri (KADTriDataMor I2) (KADTriDataFiber I2)))))
      in tmp.
    use (pathscomp0 _ tmp). clear tmp. cbn. unfold postcompose.
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A) _ _))).
    use (pathscomp0 _ (functor_comp (ComplexHomotFunctor A) _ _)).
    apply maponpaths.
    exact (MappingConeMorExtComm1 A I1' I2' h1' h2' HH1 (! HH2)).
  Qed.

  Lemma KAExt_Comm3 (D1 D2 : DTri) (g1 : KAPreTriangData ⟦ Ob1 D1, Ob1 D2 ⟧)
        (g2 : KAPreTriangData ⟦ Ob2 D1, Ob2 D2 ⟧) (H : g1 · Mor1 D2 = Mor1 D1 · g2)
        (I1 : KADTriData D1) (I2 : KADTriData D2)
        (h1 : hfiber # (ComplexHomotFunctor A)
                     (MPMor1 (TriIsoInv (KADTriDataIso I1)) · g1 · MPMor1 (KADTriDataIso I2)))
        (h2 : hfiber # (ComplexHomotFunctor A)
                     (MPMor2 (TriIsoInv (KADTriDataIso I1)) · g2 · MPMor2 (KADTriDataIso I2)))
        (I1' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I1) (KADTriDataFiber I1))
        (I2' := hfiberpr1 # (ComplexHomotFunctor A) (KADTriDataMor I2) (KADTriDataFiber I2))
        (h1' := hfiberpr1 # (ComplexHomotFunctor A)
                          (is_z_isomorphism_mor (TriMor_is_iso1 (KADTriDataIso I1))
                                                · g1 · MPMor1 (KADTriDataIso I2)) h1)
        (h2' := hfiberpr1 # (ComplexHomotFunctor A)
                          (is_z_isomorphism_mor (TriMor_is_iso2 (KADTriDataIso I1))
                                                · g2 · MPMor2 (KADTriDataIso I2)) h2)
        (HH1 : ComplexHomot A (Source (KADTriDataMor I1))
                            (Ob2 (MappingConeTri (KADTriDataMor I2) (KADTriDataFiber I2))))
        (HH2 : ComplexHomotMorphism A HH1 =
               @to_binop (ComplexPreCat_Additive A) (Source (KADTriDataMor I1))
                         (Ob2 (MappingConeTri (KADTriDataMor I2) (KADTriDataFiber I2)))
                         (I1' · h2') (to_inv (h1' · I2'))) :
    # (ComplexHomotFunctor A) (MappingConePr1 A I1')
      · (# (AddEquiv1 (@Trans KAPreTriangData))
            (is_z_isomorphism_mor (TriMor_is_iso1 (KADTriDataIso I1))
                                  · g1 · MPMor1 (KADTriDataIso I2))) =
    # (ComplexHomotFunctor A) (MappingConeMorExt A I1' I2' h1' h2' HH1 (! HH2))
      · # (ComplexHomotFunctor A) (MappingConePr1 A I2').
  Proof.
    use (pathscomp0 _ (functor_comp (ComplexHomotFunctor A) _ _)).
    use (pathscomp0
           _ (maponpaths # (ComplexHomotFunctor A)
                         (MappingConeMorExtComm2 A I1' I2' h1' h2' HH1 (! HH2)))).
    use (pathscomp0 _ (! (functor_comp (ComplexHomotFunctor A) _ _))).
    apply cancel_precomposition. use TranslationFunctorHImEq.
    exact (hfiberpr2 _ _ h1).
  Qed.

  Lemma KAExt :
    ∏ (D1 D2 : DTri) (g1 : KAPreTriangData ⟦ Ob1 D1, Ob1 D2 ⟧)
      (g2 : KAPreTriangData ⟦ Ob2 D1, Ob2 D2 ⟧) (H : g1 · Mor1 D2 = Mor1 D1 · g2), ∥ TExt H ∥.
  Proof.
    intros D1 D2 g1 g2 H.
    use (squash_to_prop (DTriisDTri D1) (propproperty _)). intros I1.
    set (I1' := hfiberpr1 _ _ (KADTriDataFiber I1)).
    use (squash_to_prop (DTriisDTri D2) (propproperty _)). intros I2.
    set (I2' := hfiberpr1 _ _ (KADTriDataFiber I2)).
    set (φ1 := (MPMor1 (TriIsoInv (KADTriDataIso I1)) · g1 · MPMor1 (KADTriDataIso I2))).
    set (φ2 := (MPMor2 (TriIsoInv (KADTriDataIso I1)) · g2 · MPMor2 (KADTriDataIso I2))).
    use (squash_to_prop (ComplexHomotFunctor_issurj A φ1) (propproperty _)). intros φ1'.
    use (squash_to_prop (ComplexHomotFunctor_issurj A φ2) (propproperty _)). intros φ2'.
    use (squash_to_prop
           (ComplexHomotFunctor_im_to_homot A _ _ (KAExt_MorEq D1 D2 g1 g2 H I1 I2 φ1' φ2'))
           (propproperty _ )). intros HH.
    use hinhpr.
    use (@DExtIso KAPreTriangData _ _ _ _ (KADTriDataIso I1) (KADTriDataIso I2)).
    - exact (# (ComplexHomotFunctor A)
               (MappingConeMorExt A I1' I2' (hfiberpr1 _ _ φ1') (hfiberpr1 _ _ φ2')
                                  (pr1 HH) (! (pr2 HH)))).
    - exact (KAExt_Comm2 D1 D2 g1 g2 H I1 I2 φ1' φ2' (pr1 HH) (pr2 HH)).
    - exact (KAExt_Comm3 D1 D2 g1 g2 H I1 I2 φ1' φ2' (pr1 HH) (pr2 HH)).
  Defined.

  (** ** Closed under isomorphisms *)

  Definition KADTrisIsos :
    ∏ T1 T2 : Tri, ∥ TriIso T1 T2 ∥ → @isDTri KAPreTriangData T1 → @isDTri KAPreTriangData T2.
  Proof.
    intros T1 T2 I X0.
    use (squash_to_prop I (propproperty _)). intros I'.
    use (squash_to_prop X0 (propproperty _)). intros I1. clear X0.
    use hinhpr.
    use mk_KADTriData.
    - exact (KADTriDataMor I1).
    - exact (KADTriDataFiber I1).
    - exact (TriIso_comp (TriIsoInv I') (KADTriDataIso I1)).
  Qed.

  Definition KAPreTriang : PreTriang.
  Proof.
    use mk_PreTriang.
    - exact KAPreTriangData.
    - use mk_isPreTriang.
      + exact KATrivialDistinguished.
      + exact KADTrisIsos.
      + exact KARotDTris.
      + exact KAInvRotDTris.
      + exact KAConeDTri.
      + exact KAExt.
  Defined.

End KAPreTriangulated.
