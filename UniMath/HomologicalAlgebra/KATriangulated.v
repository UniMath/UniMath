(** * K(A) is a triangulated category *)
(** Contents
- K(A) pretriangulated
 - Pretriangulated data
 - Trivial triangle is distinguished
 - Rotations of triangles
 - Extension of triangles
 - K(A) pretriangulated
- K(A) triangulated
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
Require Import UniMath.CategoryTheory.equivalences.

Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.ShortExactSequences.
Require Import UniMath.CategoryTheory.category_abgr.

Require Import UniMath.CategoryTheory.precategoriesWithBinOps.
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
- Rotation of a distinguished triangle is distinguished
- Inverse rotation of a distinguished triangle is distinguished
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

  Definition MappingConeData {x y : ob (ComplexPreCat_Additive A)} (f : x --> y) :
    @MCone (ComplexHomot_Additive A) (TranslationHEquiv A) x y.
  Proof.
    use mk_MCone.
    - exact (MappingCone A f).
    - exact (# (ComplexHomotFunctor A) (MappingConeIn2 A f)).
    - exact (# (ComplexHomotFunctor A) (MappingConePr1 A f)).
  Defined.

  Definition KAPreTriangData : PreTriangData.
  Proof.
    use mk_PreTriangData.
    - exact (ComplexHomot_Additive A).
    - exact (TranslationHEquiv A).
    - intros x y f. exact (hfiber (# (ComplexHomotFunctor A)) f).
    - intros x y f.
      use (squash_to_prop (ComplexHomotFunctor_issurj A f) (propproperty _)).
      intros f'. intros P X. apply X. exact f'.
    - intros x y f f'. exact (MappingConeData (hfiberpr1 _ _ f')).
  Defined.

  (** ** Trivial triangle is distinguished *)

  Local Opaque ComplexHomotFunctor ComplexHomotSubset QuotPrecategory identity ZeroArrow
        MappingConePr1 MappingConeIn2 RotMorphism RotMorphismInv InvRotMorphism InvRotMorphismInv
        to_inv compose.

  Definition KAPreTriang1_MPMorMors (x : ob KAPreTriangData)
             (i' := @hfiberpair _ _ (# (ComplexHomotFunctor A)) _ _
                                (functor_id (ComplexHomotFunctor A) x)) :
    @MPMorMors KAPreTriangData (@TrivialTri _ (@Trans KAPreTriangData) x)
              (ConeTri (identity x) (@MConeOf KAPreTriangData _ _ (identity x) i')).
  Proof.
    use mk_MPMorMors.
    - exact (# (ComplexHomotFunctor A) (identity _)).
    - exact (# (ComplexHomotFunctor A) (identity _)).
    - exact (ZeroArrow (to_Zero _) _ _).
  Defined.

  Local Lemma KAPreTriang1_MPMorsComm (x : ob (ComplexPreCat_Additive A)) :
    MPMorComms (KAPreTriang1_MPMorMors x).
  Proof.
    use mk_MPMorComms.
    - apply idpath.
    - cbn. rewrite (functor_id (ComplexHomotFunctor A)).
      rewrite (@id_left (ComplexHomot_Additive A)).
      rewrite (@ZeroArrow_comp_right (ComplexHomot_Additive A)).
      use (pathscomp0 _ (AdditiveFunctorZeroArrow (ComplexHomotFunctor A) _ _)).
      exact (MappingConeIn2Eq A x).
  Qed.

  Definition KAPreTriang1_TriMor (x : ob KAPreTriangData)
             (i' := @hfiberpair _ _ (# (ComplexHomotFunctor A)) _ _
                                (functor_id (ComplexHomotFunctor A) x)) :
    TriMor (TrivialTri x) (ConeTri (identity x) (MConeOf (identity x) i')).
  Proof.
    use mk_TriMor.
    - exact (mk_MPMor (KAPreTriang1_MPMorMors x) (KAPreTriang1_MPMorsComm x)).
    - cbn. rewrite (@ZeroArrow_comp_left (ComplexHomot_Additive A)).
      rewrite (@ZeroArrow_comp_left (ComplexHomot_Additive A)). apply idpath.
  Defined.

  Lemma KAPreTriang1 :
    Π x : KAPreTriangData, ∥ Σ M : Morphisms.Morphism, ∥ ConeIso (TrivialTri x) M ∥ ∥.
  Proof.
    intros x. intros P X. apply X. clear X P.
    use tpair.
    - exact (Morphisms.mk_Morphism (identity x)).
    - set (i' := @hfiberpair _ _ (# (ComplexHomotFunctor A)) _ _
                             (functor_id (ComplexHomotFunctor A) x)).
      intros P X. apply X. clear X P.
      use mk_ConeIso.
      + exact i'.
      + exact (KAPreTriang1_TriMor x).
      + use mk_TriMor_is_iso.
        * cbn. rewrite (@functor_id _ _ (ComplexHomotFunctor A)).
          exact (is_z_isomorphism_identity ((ComplexHomotFunctor A) x)).
        * cbn. rewrite (@functor_id _ _ (ComplexHomotFunctor A)).
          exact (is_z_isomorphism_identity ((ComplexHomotFunctor A) x)).
        * cbn. exact (IDMappingCone_is_iso_with_inv_data A x).
  Qed.


  (** ** Rotation of distinguished triangles *)

  Local Lemma KAPreTriang2_Comm1 {x y : ob KAPreTriangData} (f : x --> y) :
    f ;; identity _ = identity _ ;; f.
  Proof.
    rewrite id_left. rewrite id_right. apply idpath.
  Qed.

  Local Lemma KAPreTriang2_Comm2 (D : DTri) (M : @Morphisms.Morphism KAPreTriangData)
        (I' : ConeIso D M) (M' := hfiberpr1 _ _ (ConeIsoFiber I')) :
    (# (ComplexHomotFunctor A) (MappingConePr1 A M'))
      ;; (# (ComplexHomotFunctor A) (RotMorphism A M')) =
    (identity _) ;; (# (ComplexHomotFunctor A) (MappingConeIn2 A (MappingConeIn2 A M'))).
  Proof.
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A) _ _ _
                                       (MappingConePr1 A M') (RotMorphism A M')))).
    use (pathscomp0 (RotMorphism_comm A M')).
    apply pathsinv0. apply id_left.
  Qed.

  Local Lemma KAPreTriang2_Comm3 (D : DTri) (M : @Morphisms.Morphism KAPreTriangData)
        (I' : ConeIso D M) (M' := hfiberpr1 _ _ (ConeIsoFiber I')) :
    to_inv (# (AddEquiv1 Trans) M) ;; # (AddEquiv1 Trans) (identity (Target M)) =
    (# (ComplexHomotFunctor A) (RotMorphism A M'))
      ;; (# (ComplexHomotFunctor A) (MappingConePr1 A (MappingConeIn2 A M'))).
  Proof.
    use (pathscomp0 _ (functor_comp (ComplexHomotFunctor A) _ _ _
                                    (RotMorphism A M')
                                    (MappingConePr1 A (MappingConeIn2 A M')))).
    set (tmp' := RotMorphism_comm2 A M').
    apply (maponpaths (# (ComplexHomotFunctor A))) in tmp'. use (pathscomp0 _ tmp'). clear tmp'.
    rewrite functor_id. rewrite id_right.
    rewrite (AdditiveFunctorInv (ComplexHomotFunctor A)). apply maponpaths.
    apply TranslationFunctorHImEq. exact (hfiberpr2 _ _ (ConeIsoFiber I')).
  Qed.

  Lemma KAPreTriang2 :
    Π D : DTri, ∥ Σ M : Morphisms.Morphism, ∥ @ConeIso KAPreTriangData (RotTri D) M ∥ ∥.
  Proof.
    intros D.
    use (squash_to_prop (DTriIso D) (propproperty _)). intros I.
    use (squash_to_prop (pr2 I) (propproperty _)). intros I'.
    exact (@mk_RotDTris
           KAPreTriangData
           D (pr1 I) I' (Morphisms.mk_Morphism
                           (# (ComplexHomotFunctor A)
                              (MappingConeIn2 A (hfiberpr1 _ _ (ConeIsoFiber I')))))
           (hfiberpair (# (ComplexHomotFunctor A))
                       (MappingConeIn2 A (hfiberpr1 _ _ (ConeIsoFiber I'))) (idpath _))
           (identity _) (identity _)
           (# (ComplexHomotFunctor A) (RotMorphism A (hfiberpr1 _ _ (ConeIsoFiber I'))))
           (is_z_isomorphism_identity _) (is_z_isomorphism_identity _)
           (RotMorphism_is_iso_with_inv_data _ _)
           (KAPreTriang2_Comm1 (# (ComplexHomotFunctor A)
                                  (MappingConeIn2 A (hfiberpr1 _ _ (ConeIsoFiber I')))))
           (KAPreTriang2_Comm2 D (pr1 I) I') (KAPreTriang2_Comm3 D (pr1 I) I')).
  Qed.

  (** ** Inverse rotation of distinguished triangles *)

  Local Lemma KAPreTriang3_1' {x y : ob KAPreTriangData} (f g : x --> y) (e : f = g) :
    f ;; identity _ = identity _ ;; g.
  Proof.
    rewrite id_left. rewrite id_right. exact e.
  Qed.

  Lemma KAPreTriang3_1 (D : DTri) (M : @Morphisms.Morphism KAPreTriangData) (I' : ConeIso D M)
        (M' := hfiberpr1 _ _ (ConeIsoFiber I')) :
    (@to_inv (ComplexHomot_Additive A) _ _
             (# (AddEquiv2 (TranslationHEquiv A))
                (# (ComplexHomotFunctor A) (MappingConePr1 A M'))))
      ;; AddEquivUnitInvMor (TranslationHEquiv A) (Source M) ;; identity (Source M) =
    (identity _)
      ;; (# (ComplexHomotFunctor A)
            ((to_inv (# (InvTranslationFunctor A) (MappingConePr1 A M')))
               ;; z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) (Source M)))).
  Proof.
    use KAPreTriang3_1'.
    set (tmp''' := functor_comp
                     (ComplexHomotFunctor A) _ _ _
                     (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A M')))
                     (z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) (Source M)))).
    use (pathscomp0 _ (! tmp''')). clear tmp'''.
    set (tmp''' := @AdditiveFunctorInv
                     _ _ (ComplexHomotFunctor A)
                     _ _ (# (InvTranslationFunctor A) (MappingConePr1 A M'))).
    apply (maponpaths
             (postcompose
                (# (ComplexHomotFunctor A)
                   (z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) (Source M)))))) in tmp'''.
    use (pathscomp0 _ (! tmp''')). clear tmp'''. unfold postcompose.
    assert (e : z_iso_inv_mor (AddEquivUnitIso Trans (Source M)) =
                # (ComplexHomotFunctor A)
                  (z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) (Source M)))).
    {
      apply idpath.
    }
    apply (maponpaths
             (compose (to_inv (# (ComplexHomotFunctor A)
                                 (# (InvTranslationFunctor A) (MappingConePr1 A M')))))) in e.
    use (pathscomp0 _ e). clear e. apply cancel_postcomposition.
    apply maponpaths. use InvTranslationFunctorHImEq. apply idpath.
  Qed.

  Local Lemma KAPreTriang3_2' {x y : ob KAPreTriangData} (f g : x --> y) (e : f = g) :
    f = identity _ ;; g.
  Proof.
    rewrite id_left. exact e.
  Qed.

  Lemma KAPreTriang3_2 (D : DTri) (M : @Morphisms.Morphism KAPreTriangData) (I' : ConeIso D M)
    (M' := hfiberpr1 _ _ (ConeIsoFiber I')) :
    M ;; # (ComplexHomotFunctor A) (InvRotMorphismInv A M') =
    (identity (Source M))
      ;; (# (ComplexHomotFunctor A)
            (MappingConeIn2
               A ((to_inv (# (InvTranslationFunctor A) (MappingConePr1 A M')))
                    ;; z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) (Source M))))).
  Proof.
    use KAPreTriang3_2'.
    set (tmp''' := hfiberpr2 _ _ (ConeIsoFiber I')).
    apply (maponpaths
             (postcompose (# (ComplexHomotFunctor A)
                             (InvRotMorphismInv A M')))) in tmp'''.
    use (pathscomp0 (! tmp''')). clear tmp'''. unfold postcompose.
    set (tmp''' := functor_comp (ComplexHomotFunctor A) _ _ _ M'
                                (InvRotMorphismInv A M')).
    use (pathscomp0 (! tmp''')). clear tmp'''.
    exact (InvRotMorphismInvComm1 A M').
  Qed.

  Lemma KAPreTriang3_3 (D : DTri) (M : @Morphisms.Morphism KAPreTriangData) (I' : ConeIso D M)
    (M' := hfiberpr1 _ _ (ConeIsoFiber I')) :
    (# (ComplexHomotFunctor A) (MappingConeIn2 A M'))
      ;; (AddEquivCounitInvMor
            (TranslationHEquiv A) (MappingCone A M'))
      ;; (# (AddEquiv1 (TranslationHEquiv A))
            (identity ((AddEquiv2 (TranslationHEquiv A)) (MappingCone A M')))) =
    (# (ComplexHomotFunctor A) (InvRotMorphismInv A M'))
      ;; (# (ComplexHomotFunctor A)
            (MappingConePr1
               A (to_inv (# (InvTranslationFunctor A)
                            (MappingConePr1 A M'))
                         ;; z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) (Source M))))).
  Proof.
    rewrite functor_id. rewrite id_right.
    set (tmp''' := functor_comp (ComplexHomotFunctor A) _ _ _
                                (InvRotMorphismInv A M')
                                (MappingConePr1
                                   A ((to_inv (# (InvTranslationFunctor A)
                                                 (MappingConePr1 A M'))
                                              ;; z_iso_inv_mor
                                              (AddEquivUnitIso (TranslationEquiv A) (Source M)))))).
    use (pathscomp0 _ tmp'''). clear tmp'''.
    set (tmp''' := functor_comp (ComplexHomotFunctor A) _ _ _
                                (MappingConeIn2 A M')
                                (TranslationEquivCounitInv
                                   A (MappingCone A M'))).
    use (pathscomp0 (! tmp''')). clear tmp'''. apply maponpaths.
    exact (InvRotMorphismInvComm2 A M').
  Qed.

  Lemma KAPreTriang3 :
    Π D : DTri, ∃ M : Morphisms.Morphism, ∥ @ConeIso KAPreTriangData (InvRotTri D) M ∥.
  Proof.
    intros D.
    use (squash_to_prop (DTriIso D) (propproperty _)). intros I.
    induction I as [M I].
    use (squash_to_prop I (propproperty _)). intros I'.
    set (M' := hfiberpr1 _ _ (ConeIsoFiber I')).
    set (MM1 := to_inv (# (InvTranslationFunctor A)
                          (MappingConePr1 A M')) ;;
                       z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) (Source M))).
    set (MM1' := hfiberpair (# (ComplexHomotFunctor A)) MM1 (idpath _)).
    exact (@mk_InvRotDTris KAPreTriangData
                           D M I' (Morphisms.mk_Morphism (# (ComplexHomotFunctor A) MM1)) MM1'
                           (identity _) (identity _)
                           (# (ComplexHomotFunctor A) (InvRotMorphismInv A M'))
                           (is_z_isomorphism_identity (Ob1 (InvRotTri (ConeIsoTri I'))))
                           (is_z_isomorphism_identity (Ob2 (InvRotTri (ConeIsoTri I'))))
                           (InvRotMorphism_is_iso_with_inv_data _ _) (KAPreTriang3_1 D M I')
                           (KAPreTriang3_2 D M I') (KAPreTriang3_3 D M I')).
  Qed.

  (** ** Extension of squares *)

  Local Opaque binopeqrel_subgr_eqrel.

  Lemma KAPreTriang4_1 (D1 D2 : DTri) (g1 : KAPreTriangData ⟦ Ob1 D1, Ob1 D2 ⟧)
        (g2 : KAPreTriangData ⟦ Ob2 D1, Ob2 D2 ⟧) (H : g1 ;; Mor1 D2 = Mor1 D1 ;; g2)
        (M1 : Morphisms.Morphism) (M2 : Morphisms.Morphism)
        (I1' : ConeIso D1 M1) (I2' : ConeIso D2 M2)
        (k1' : hfiber # (ComplexHomotFunctor A) (MPMor1 (ConeIsoMor I2')))
        (k2' : hfiber # (ComplexHomotFunctor A) (MPMor2 (ConeIsoMor I2')))
        (g1' : hfiber # (ComplexHomotFunctor A) g1)
        (g2' : hfiber # (ComplexHomotFunctor A) g2)
        (invh1' : hfiber # (ComplexHomotFunctor A) (MPMor1 (ConeIsoMorInv I1')))
        (invh2' : hfiber # (ComplexHomotFunctor A) (MPMor2 (ConeIsoMorInv I1')))
        (M1' := hfiberpr1 _ _ (ConeIsoFiber I1')) (M2' := hfiberpr1 _ _ (ConeIsoFiber I2')) :
    # (ComplexHomotFunctor A)
      ((hfiberpr1 _ _ invh1') ;; (hfiberpr1 _ _ g1') ;; (hfiberpr1 _ _  k1') ;; M2') =
    # (ComplexHomotFunctor A)
      (M1' ;; (hfiberpr1 _ _ invh2') ;; (hfiberpr1 _ _ g2') ;; (hfiberpr1 _ _ k2')).
  Proof.
    use (ComplexHomotComm4 A invh1' g1' k1' (ConeIsoFiber I2') (ConeIsoFiber I1') invh2' g2' k2').
    apply pathsinv0. set (comm1 := ! (MPComm1 (ConeIsoMorInv I1'))).
    apply (maponpaths (fun gg : _ => gg ;; g2 ;; MPMor2 (ConeIsoMor I2'))) in comm1.
    use (pathscomp0 comm1). clear comm1.
    apply pathsinv0 in H.
    apply (maponpaths
             (fun gg : _ => is_z_isomorphism_mor (TriMor_is_iso1 (ConeIsoMor_is_iso I1')) ;;
                                              gg ;; MPMor2 (ConeIsoMor I2'))) in H.
    rewrite assoc in H. rewrite assoc in H. use (pathscomp0 H).
    set (comm3 := MPComm1 (ConeIsoMor I2')).
    apply pathsinv0 in comm3.
    apply (maponpaths
             (fun gg : _ => is_z_isomorphism_mor (TriMor_is_iso1 (ConeIsoMor_is_iso I1'))
                                              ;; g1 ;; gg)) in comm3.
    rewrite assoc in comm3. rewrite assoc in comm3.
    exact comm3.
  Qed.

  Lemma KAPreTriang4_2 (D1 D2 : DTri) (g1 : KAPreTriangData ⟦ Ob1 D1, Ob1 D2 ⟧)
        (g2 : KAPreTriangData ⟦ Ob2 D1, Ob2 D2 ⟧) (H : g1 ;; Mor1 D2 = Mor1 D1 ;; g2)
        (M1 : Morphisms.Morphism) (M2 : Morphisms.Morphism)
        (I1' : ConeIso D1 M1) (I2' : ConeIso D2 M2)
        (M1' := hfiberpr1 _ _ (ConeIsoFiber I1')) (M2' := hfiberpr1 _ _ (ConeIsoFiber I2'))
        (k1' : hfiber # (ComplexHomotFunctor A) (MPMor1 (ConeIsoMor I2')))
        (k2' : hfiber # (ComplexHomotFunctor A) (MPMor2 (ConeIsoMor I2')))
        (g1' : hfiber # (ComplexHomotFunctor A) g1)
        (g2' : hfiber # (ComplexHomotFunctor A) g2)
        (invh1' : hfiber # (ComplexHomotFunctor A) (MPMor1 (ConeIsoMorInv I1')))
        (invh2' : hfiber # (ComplexHomotFunctor A) (MPMor2 (ConeIsoMorInv I1')))
        (HH1 : ComplexHomot A (Ob1 (ConeTri M1 (MConeOf M1 (ConeIsoFiber I1')))) (Target M2))
        (HH2 : MorphismOp
                 A (hfiberpr1 # (ComplexHomotFunctor A) M1 (ConeIsoFiber I1')
                              ;; (hfiberpr1 # (ComplexHomotFunctor A)
                                            (is_z_isomorphism_mor
                                               (TriMor_is_iso2 (ConeIsoMor_is_iso I1')))
                                            invh2'
                                            ;; hfiberpr1 # (ComplexHomotFunctor A) g2 g2'
                                            ;; hfiberpr1 # (ComplexHomotFunctor A)
                                            (MPMor2 (ConeIsoMor I2')) k2'))
                 (to_inv
                    (hfiberpr1
                       # (ComplexHomotFunctor A)
                       (is_z_isomorphism_mor (TriMor_is_iso1 (ConeIsoMor_is_iso I1'))) invh1'
                       ;; hfiberpr1 # (ComplexHomotFunctor A) g1 g1'
                       ;; hfiberpr1 # (ComplexHomotFunctor A) (MPMor1 (ConeIsoMor I2')) k1'
                       ;; hfiberpr1 # (ComplexHomotFunctor A) M2 (ConeIsoFiber I2'))) =
               ComplexHomotMorphism A HH1) :
    # (ComplexHomotFunctor A) (MappingConeIn2 A M1') ;;
      # (ComplexHomotFunctor A)
      (MappingConeMorExt
         A M1' M2'
         ((hfiberpr1 _ _ invh1') ;; (hfiberpr1 _ _ g1') ;; (hfiberpr1 _ _ k1'))
         ((hfiberpr1 _ _ invh2') ;; (hfiberpr1 _ _ g2') ;; (hfiberpr1 _ _ k2'))
         HH1 HH2) =
    (is_z_isomorphism_mor (TriMor_is_iso2 (ConeIsoMor_is_iso I1')))
      ;; g2 ;; MPMor2 (ConeIsoMor I2')
      ;; # (ComplexHomotFunctor A) (MappingConeIn2 A M2').
  Proof.
    set (tmp'' := MappingConeMorExt
                    A M1' M2'
                    ((hfiberpr1 _ _ invh1') ;; (hfiberpr1 _ _ g1') ;; (hfiberpr1 _ _ k1'))
                    ((hfiberpr1 _ _ invh2') ;; (hfiberpr1 _ _ g2') ;; (hfiberpr1 _ _ k2'))
                    HH1 HH2).
    set (comm1 := MappingConeMorExtComm1
                    A M1' M2'
                    ((hfiberpr1 _ _ invh1') ;; (hfiberpr1 _ _ g1') ;; (hfiberpr1 _ _ k1'))
                    ((hfiberpr1 _ _ invh2') ;; (hfiberpr1 _ _ g2') ;; (hfiberpr1 _ _ k2'))
                    HH1 HH2).
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A) _ _ _ (MappingConeIn2 A M1') tmp''))).
    apply (maponpaths (# (ComplexHomotFunctor A))) in comm1.
    use (pathscomp0 comm1). clear comm1.
    rewrite functor_comp. rewrite functor_comp. rewrite functor_comp.
    apply cancel_postcomposition.
    set (tmp''' := hfiberpr2 _ _ k2').
    apply (maponpaths
             (compose
                (is_z_isomorphism_mor
                   (TriMor_is_iso2 (ConeIsoMor_is_iso I1')) ;; g2))) in tmp'''.
    use (pathscomp0 _ tmp'''). clear tmp'''. apply cancel_postcomposition.
    set (tmp''' := hfiberpr2 _ _ g2').
    apply (maponpaths
             (compose
                (is_z_isomorphism_mor
                   (TriMor_is_iso2 (ConeIsoMor_is_iso I1'))))) in tmp'''.
    use (pathscomp0 _ tmp'''). clear tmp'''. apply cancel_postcomposition.
    exact (hfiberpr2 _ _ invh2').
  Qed.

  Lemma KAPreTriang4_3 (D1 D2 : DTri) (g1 : KAPreTriangData ⟦ Ob1 D1, Ob1 D2 ⟧)
        (g2 : KAPreTriangData ⟦ Ob2 D1, Ob2 D2 ⟧) (H : g1 ;; Mor1 D2 = Mor1 D1 ;; g2)
        (M1 : Morphisms.Morphism) (M2 : Morphisms.Morphism)
        (I1' : ConeIso D1 M1) (I2' : ConeIso D2 M2)
        (M1' := hfiberpr1 _ _ (ConeIsoFiber I1')) (M2' := hfiberpr1 _ _ (ConeIsoFiber I2'))
        (k1' : hfiber # (ComplexHomotFunctor A) (MPMor1 (ConeIsoMor I2')))
        (k2' : hfiber # (ComplexHomotFunctor A) (MPMor2 (ConeIsoMor I2')))
        (g1' : hfiber # (ComplexHomotFunctor A) g1)
        (g2' : hfiber # (ComplexHomotFunctor A) g2)
        (invh1' : hfiber # (ComplexHomotFunctor A) (MPMor1 (ConeIsoMorInv I1')))
        (invh2' : hfiber # (ComplexHomotFunctor A) (MPMor2 (ConeIsoMorInv I1')))
        (HH1 : ComplexHomot A (Ob1 (ConeTri M1 (MConeOf M1 (ConeIsoFiber I1')))) (Target M2))
        (HH2 : MorphismOp
                 A (hfiberpr1 # (ComplexHomotFunctor A) M1 (ConeIsoFiber I1')
                              ;; (hfiberpr1 # (ComplexHomotFunctor A)
                                            (is_z_isomorphism_mor
                                               (TriMor_is_iso2 (ConeIsoMor_is_iso I1')))
                                            invh2' ;; hfiberpr1
                                            # (ComplexHomotFunctor A) g2 g2'
                                            ;; hfiberpr1 # (ComplexHomotFunctor A)
                                            (MPMor2 (ConeIsoMor I2')) k2'))
                 (to_inv
                    (hfiberpr1 # (ComplexHomotFunctor A)
                               (is_z_isomorphism_mor
                                  (TriMor_is_iso1 (ConeIsoMor_is_iso I1'))) invh1' ;;
                               hfiberpr1 # (ComplexHomotFunctor A) g1 g1'
                               ;; hfiberpr1 # (ComplexHomotFunctor A)
                               (MPMor1 (ConeIsoMor I2')) k1'
                               ;; hfiberpr1 # (ComplexHomotFunctor A) M2 (ConeIsoFiber I2'))) =
               ComplexHomotMorphism A HH1) :
    (# (ComplexHomotFunctor A)
       (MappingConeMorExt
          A M1' M2'
          ((hfiberpr1 _ _ invh1') ;; (hfiberpr1 _ _ g1') ;; (hfiberpr1 _ _ k1'))
          ((hfiberpr1 _ _ invh2') ;; (hfiberpr1 _ _ g2') ;; (hfiberpr1 _ _ k2'))
          HH1 HH2))
      ;; (# (ComplexHomotFunctor A) (MappingConePr1 A M2')) =
    (# (ComplexHomotFunctor A) (MappingConePr1 A M1'))
      ;; (# (AddEquiv1 Trans)
            ((is_z_isomorphism_mor (TriMor_is_iso1 (ConeIsoMor_is_iso I1')))
               ;; g1 ;; MPMor1 (ConeIsoMor I2'))).
  Proof.
    set (tmp'' := MappingConeMorExt
                    A M1' M2'
                    ((hfiberpr1 _ _ invh1') ;; (hfiberpr1 _ _ g1') ;; (hfiberpr1 _ _ k1'))
                    ((hfiberpr1 _ _ invh2') ;; (hfiberpr1 _ _ g2') ;; (hfiberpr1 _ _ k2'))
                    HH1 HH2).
    set (comm2 := MappingConeMorExtComm2
                    A M1' M2'
                    ((hfiberpr1 _ _ invh1') ;; (hfiberpr1 _ _ g1') ;; (hfiberpr1 _ _ k1'))
                    ((hfiberpr1 _ _ invh2') ;; (hfiberpr1 _ _ g2') ;; (hfiberpr1 _ _ k2'))
                    HH1 HH2).
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A) _ _ _
                                     tmp'' (MappingConePr1 A M2')))).
    apply (maponpaths (# (ComplexHomotFunctor A))) in comm2.
    use (pathscomp0 (! comm2)). clear comm2.
    rewrite functor_comp. apply cancel_precomposition.
    apply pathsinv0. use TranslationFunctorHImEq.
    set (tmp''' := functor_comp (ComplexHomotFunctor A) _ _ _
                                ((hfiberpr1 _ _ invh1') ;; (hfiberpr1 _ _ g1'))
                                (hfiberpr1 _ _ k1')).
    use (pathscomp0 tmp'''). clear tmp'''.
    set (tmp''' := hfiberpr2 _ _ k1').
    apply (maponpaths (compose (is_z_isomorphism_mor
                                  (TriMor_is_iso1 (ConeIsoMor_is_iso I1')) ;; g1))) in tmp'''.
    use (pathscomp0 _ tmp'''). clear tmp'''. apply cancel_postcomposition.
    set (tmp''' := functor_comp (ComplexHomotFunctor A) _ _ _
                                (hfiberpr1 _ _ invh1') (hfiberpr1 _ _ g1')).
    use (pathscomp0 tmp'''). clear tmp'''.
    set (tmp''' := hfiberpr2 _ _ g1').
    apply (maponpaths (compose (is_z_isomorphism_mor
                                  (TriMor_is_iso1 (ConeIsoMor_is_iso I1'))))) in tmp'''.
    use (pathscomp0 _ tmp'''). clear tmp'''. apply cancel_postcomposition.
    exact (hfiberpr2 _ _ invh1').
  Qed.

  Lemma KAPreTriang4 :
    Π (D1 D2 : DTri) (g1 : KAPreTriangData ⟦ Ob1 D1, Ob1 D2 ⟧)
      (g2 : KAPreTriangData ⟦ Ob2 D1, Ob2 D2 ⟧) (H : g1 ;; Mor1 D2 = Mor1 D1 ;; g2), ∥ TExt H ∥.
  Proof.
    intros D1 D2 g1 g2 H.
    use (squash_to_prop (ComplexHomotFunctor_issurj A (Mor2 D1)) (propproperty _)). intros ii1'.
    use (squash_to_prop (ComplexHomotFunctor_issurj A (Mor2 D2)) (propproperty _)). intros ii2'.
    use (squash_to_prop (ComplexHomotFunctor_issurj A g1) (propproperty _)). intros g1'.
    use (squash_to_prop (ComplexHomotFunctor_issurj A g2) (propproperty _)). intros g2'.
    use (squash_to_prop (DTriIso D1) (propproperty _)). intros I1.
    induction I1 as [M1 I1].
    use (squash_to_prop I1 (propproperty _)). intros I1'.
    set (M1' := hfiberpr1 _ _ (ConeIsoFiber I1')). cbn in M1'.
    set (I1'' := ConeIsoMorInv I1').
    use (squash_to_prop (DTriIso D2) (propproperty _)). intros I2.
    induction I2 as [M2 I2].
    use (squash_to_prop I2 (propproperty _)). intros I2'.
    set (M2' := hfiberpr1 _ _ (ConeIsoFiber I2')). cbn in M2'.
    set (I2'' := ConeIsoMorInv I2').
    use (squash_to_prop
           (ComplexHomotFunctor_issurj A (MPMor1 (ConeIsoMor I1'))) (propproperty _)). intros h1'.
    use (squash_to_prop
           (ComplexHomotFunctor_issurj A (MPMor2 (ConeIsoMor I1'))) (propproperty _)). intros h2'.
    use (squash_to_prop
           (ComplexHomotFunctor_issurj A (MPMor3 (ConeIsoMor I1'))) (propproperty _)). intros h3'.
    use (squash_to_prop
           (ComplexHomotFunctor_issurj A (MPMor1 I1'')) (propproperty _)). intros invh1'.
    use (squash_to_prop
           (ComplexHomotFunctor_issurj A (MPMor2 I1'')) (propproperty _)). intros invh2'.
    use (squash_to_prop
           (ComplexHomotFunctor_issurj A (MPMor3 I1'')) (propproperty _)). intros invh3'.
    use (squash_to_prop
           (ComplexHomotFunctor_issurj A (MPMor1 (ConeIsoMor I2'))) (propproperty _)). intros k1'.
    use (squash_to_prop
           (ComplexHomotFunctor_issurj A (MPMor2 (ConeIsoMor I2'))) (propproperty _)). intros k2'.
    use (squash_to_prop
           (ComplexHomotFunctor_issurj A (MPMor3 (ConeIsoMor I2'))) (propproperty _)). intros k3'.
    use (squash_to_prop
           (ComplexHomotFunctor_issurj A (MPMor1 I2'')) (propproperty _)). intros invk1'.
    use (squash_to_prop
           (ComplexHomotFunctor_issurj A (MPMor2 I2'')) (propproperty _)). intros invk2'.
    use (squash_to_prop
           (ComplexHomotFunctor_issurj A (MPMor3 I2'')) (propproperty _)). intros invk3'.
    set (e := KAPreTriang4_1 D1 D2 g1 g2 H M1 M2 I1' I2' k1' k2' g1' g2' invh1' invh2').
    set (tmp := ComplexHomotFunctor_im_to_homot A _ _ (! e)).
    use (squash_to_prop tmp (propproperty _ )). intros HH.
    induction HH as [HH1 HH2].
    rewrite <- (assoc (hfiberpr1 _ _ (ConeIsoFiber I1'))) in HH2.
    rewrite <- (assoc _ _ (hfiberpr1 # (ComplexHomotFunctor A) (MPMor2 (ConeIsoMor I2')) k2'))
      in HH2.
    intros P X. apply X. clear P X.
    use mk_TExts.
    - exact M1.
    - exact I1'.
    - exact M2.
    - exact I2'.
    - exact (# (ComplexHomotFunctor A)
               (MappingConeMorExt
                  A M1' M2'
                  ((hfiberpr1 _ _ invh1') ;; (hfiberpr1 _ _ g1') ;; (hfiberpr1 _ _ k1'))
                  ((hfiberpr1 _ _ invh2') ;; (hfiberpr1 _ _ g2') ;; (hfiberpr1 _ _ k2'))
                  HH1 (! HH2))).
    - exact (KAPreTriang4_2 D1 D2 g1 g2 H M1 M2 I1' I2' k1' k2' g1' g2' invh1' invh2' HH1 (! HH2)).
    - exact (KAPreTriang4_3 D1 D2 g1 g2 H M1 M2 I1' I2' k1' k2' g1' g2' invh1' invh2' HH1 (! HH2)).
  Qed.

  Definition KAPreTriang : PreTriang.
  Proof.
    use mk_PreTriang.
    - exact KAPreTriangData.
    - use mk_isPreTriang.
      + exact KAPreTriang1.
      + exact KAPreTriang2.
      + exact KAPreTriang3.
      + exact KAPreTriang4.
  Defined.

End KAPreTriangulated.


(** * K(A) as a triangulated category *)
Section KATriangulated.

  Context {A : Additive}.

  Definition KATriangOctaTriIsoTri {x y z : ob (ComplexPreCat_Additive A)} (f1 : Morphism x y)
             (f2 : Morphism y z) :
    @Tri (@KAPreTriang A) Trans.
  Proof.
    use mk_Tri.
    - exact (MappingCone _ f1).
    - exact (MappingCone _ (MorphismComp f1 f2)).
    - exact (MappingCone _ f2).
    - exact (# (ComplexHomotFunctor A) (KAOctaMor1 f1 f2)).
    - exact (# (ComplexHomotFunctor A) (KAOctaMor2 f1 f2)).
    - exact (# (ComplexHomotFunctor A)
               (MorphismComp (MappingConePr1 _ f2)
                             (# (TranslationFunctor A) (MappingConeIn2 _ f1)))).
  Defined.

  Definition KAFiberTri {x y : @KAPreTriang A} (f : Morphism x y) : @Tri (@KAPreTriang A) Trans.
  Proof.
    use (@ConeTri (@KAPreTriang A) _ _ (# (ComplexHomotFunctor A) f)).
    use MConeOf.
    - exact (# (ComplexHomotFunctor A) f).
    - use hfiberpair.
      + exact f.
      + exact (idpath _).
  Defined.

  Local Opaque ComplexHomotFunctor ComplexHomotSubset QuotPrecategory identity ZeroArrow
        MappingConePr1 MappingConeIn2 RotMorphism RotMorphismInv InvRotMorphism InvRotMorphismInv
        to_inv compose to_abgrop.

  Local Lemma KAFiberDTriIsoMPComms {x y : @KAPreTriang A} (f : Morphism x y) :
    MPMorComms
      (mk_MPMorMors (identity (Ob1 (KAFiberTri f))) (identity (Ob2 (KAFiberTri f)))
                    (identity (Ob3 (KAFiberTri f)))).
  Proof.
    use mk_MPMorComms.
    - cbn. rewrite id_left. rewrite id_right. apply idpath.
    - cbn. rewrite id_left. rewrite id_right. apply idpath.
  Qed.

  Local Lemma KAFiberDTriIsoComm3 {x y : @KAPreTriang A} (f : Morphism x y) :
    @identity
      (QuotPrecategory (ComplexPreCat_PreAdditive A)
                       (λ C1 C2 : Complex A, ComplexHomotSubgrp A C1 C2)
                       (KA.ComplexHomot_Additive_Comp A))
      (@MappingCone A ((ComplexHomotFunctor A) x) ((ComplexHomotFunctor A) y) f)
      ;; (# (ComplexHomotFunctor A)
            (@MappingConePr1 A ((ComplexHomotFunctor A) x) ((ComplexHomotFunctor A) y) f)) =
    # (ComplexHomotFunctor A)
      (@MappingConePr1 A ((ComplexHomotFunctor A) x) ((ComplexHomotFunctor A) y) f)
      ;; # (@AddEquiv1 (ComplexHomot_Additive A) (ComplexHomot_Additive A)
                       (@Trans (@KAPreTriangData A)))
      (@identity
         (QuotPrecategory (ComplexPreCat_PreAdditive A)
                          (λ C1 C2 : Complex A, ComplexHomotSubgrp A C1 C2)
                          (KA.ComplexHomot_Additive_Comp A)) ((ComplexHomotFunctor A) x)).
  Proof.
    rewrite id_left. rewrite functor_id. rewrite id_right. apply idpath.
  Qed.

  Lemma KAFiberDTriIso {x y : @KAPreTriang A} (f : Morphism x y) :
    ∃ M : Morphisms.Morphism, ∥ ConeIso (KAFiberTri f) M ∥.
  Proof.
    intros P X. apply X. clear P X.
    use tpair.
    - exact (Morphisms.mk_Morphism (# (ComplexHomotFunctor A) f)).
    - intros P X. apply X. clear P X.
      use mk_ConeIso.
      + use hfiberpair.
        * exact f.
        * exact (idpath _).
      + use mk_TriMor.
        * use mk_MPMor.
          -- use mk_MPMorMors.
             ++ exact (identity _).
             ++ exact (identity _).
             ++ exact (identity _).
          -- exact (KAFiberDTriIsoMPComms f).
        * exact (KAFiberDTriIsoComm3 f).
      + use mk_TriMor_is_iso.
        * exact (is_z_isomorphism_identity _).
        * exact (is_z_isomorphism_identity _).
        * exact (is_z_isomorphism_identity _).
  Qed.

  Definition KAFiberDTri {x y : @KAPreTriang A} (f : Morphism x y) : @DTri (@KAPreTriang A).
  Proof.
    use mk_DTri'.
    - exact (KAFiberTri f).
    - exact (KAFiberDTriIso f).
  Defined.

  Definition KATriangOctaTriIso1MPMors {x y z : ob (ComplexPreCat_Additive A)} (f1 : Morphism x y)
             (f2 : Morphism y z) :
    MPMorMors (KATriangOctaTriIsoTri f1 f2) (KAFiberTri (KAOctaMor1 f1 f2)).
  Proof.
    use mk_MPMorMors.
    - exact (identity _).
    - exact (identity _).
    - exact (# (ComplexHomotFunctor A) (KAOctaMor3 f1 f2)).
  Defined.

  Local Lemma KATriangOctaTriIso1MPMorsComm {x y z : ob (ComplexPreCat_Additive A)}
        (f1 : Morphism x y) (f2 : Morphism y z) : MPMorComms (KATriangOctaTriIso1MPMors f1 f2).
  Proof.
    use mk_MPMorComms.
    - exact (! (KAPreTriang2_Comm1 _)).
    - exact (KAOctaComm2' f1 f2).
  Qed.

  Local Lemma KATriangOctaTriIso1MPMorsComm3 {x y z : ob (ComplexPreCat_Additive A)}
        (f1 : Morphism x y) (f2 : Morphism y z) :
    # (ComplexHomotFunctor A) (KAOctaMor3 f1 f2) ;;
      # (ComplexHomotFunctor A) (MappingConePr1 A (KAOctaMor1 f1 f2)) =
    # (ComplexHomotFunctor A)
      (MorphismComp (MappingConePr1 A f2)
                    (TranslationMorphism A y (MappingCone A f1) (MappingConeIn2 A f1)))
      ;; # (AddEquiv1 Trans) (identity ((MappingCone A f1) : KAPreTriang)).
  Proof.
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A) _ _ _ _ _))).
    set (tmp := KAOctaComm3 f1 f2).
    apply (maponpaths (# (ComplexHomotFunctor A))) in tmp.
    use (pathscomp0 tmp). clear tmp. rewrite functor_id. rewrite id_right.
    apply idpath.
  Qed.

  Definition KATriangOctaTriIso1 {x y z : KAPreTriang} (f1 : x --> y) (f2 : y --> z)
             (f1' : hfiber # (ComplexHomotFunctor A) f1) (f2' : hfiber # (ComplexHomotFunctor A) f2)
             (f1'' := (hfiberpr1 _ _ f1')) (f2'' := (hfiberpr1 _ _ f2')) :
    TriIso (KATriangOctaTriIsoTri f1'' f2'') (KAFiberTri (KAOctaMor1 f1'' f2'')).
  Proof.
    use mk_TriIso.
    - use mk_TriMor.
      + use mk_MPMor.
        * exact (KATriangOctaTriIso1MPMors f1'' f2'').
        * exact (KATriangOctaTriIso1MPMorsComm f1'' f2'').
      + exact (KATriangOctaTriIso1MPMorsComm3 f1'' f2'').
    - use mk_TriMor_is_iso.
      + exact (is_z_isomorphism_identity _).
      + exact (is_z_isomorphism_identity _).
      + exact (KAOctaMor3Iso f1'' f2'').
  Defined.

  Definition KATriangOctaFiberIso {x y z : KAPreTriang} {f1 : x --> y} {f2 : y --> z}
             {f3 : z --> (AddEquiv1 Trans x)} (f1' : hfiber # (ComplexHomotFunctor A) f1)
             (H : ∥ Σ M : Morphisms.Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥)
             (f1'' := (hfiberpr1 _ _ f1'))
             (e : identity x ;; # (ComplexHomotFunctor A) f1'' = f1 ;; identity y)
             (T : @TExt KAPreTriang (mk_DTri' _ H) (KAFiberDTri f1'') _ _ e) :
    TriIso (mk_Tri f1 f2 f3) (KAFiberTri f1'').
  Proof.
    use mk_TriIso.
    - use mk_TriMor.
      + use mk_MPMor.
        * use mk_MPMorMors.
          -- exact (identity _).
          -- exact (identity _).
          -- exact T.
        * use mk_MPMorComms.
          -- exact e.
          -- exact (! (TExtComm1 T)).
      + exact (! (TExtComm2 T)).
    - use mk_TriMor_is_iso.
      + exact (is_z_isomorphism_identity _).
      + exact (is_z_isomorphism_identity _).
      + use (@TriangulatedFiveLemma KAPreTriang (mk_DTri' _ H) (KAFiberDTri f1'')).
        * exact (is_z_isomorphism_identity _).
        * exact (is_z_isomorphism_identity _).
  Defined.

  Local Definition KATriangOctaFiberComp {x y z : ob (ComplexPreCat_Additive A)}
        (f1 : Morphism x y) (f2 : Morphism y z) :
    MPMorMors
      (mk_MorphismPair (# (ComplexHomotFunctor A) f1 ;; # (ComplexHomotFunctor A) f2)
                       (# (ComplexHomotFunctor A) (MappingConeIn2 A (MorphismComp f1 f2))))
      (mk_MorphismPair (# (ComplexHomotFunctor A) (MorphismComp f1 f2))
                       (# (ComplexHomotFunctor A) (MappingConeIn2 A (MorphismComp f1 f2)))).
  Proof.
    use mk_MPMorMors.
    - exact (identity _).
    - exact (identity _).
    - exact (identity _).
  Defined.

  Local Lemma KATriangOctaFiberCompConeComms {x y z : ob (ComplexPreCat_Additive A)}
        (f1 : Morphism x y) (f2 : Morphism y z) :
    @MPMorComms KAPreTriang _ _ (KATriangOctaFiberComp f1 f2).
  Proof.
    use mk_MPMorComms.
    - exact (! (KAPreTriang3_1' _ _ (! (functor_comp
                                          (ComplexHomotFunctor A) _ _ _ f1 f2)))).
    - exact (! (KAPreTriang2_Comm1 _)).
  Qed.

  Local Lemma KATriangOctaFiberCompCone {x y z : ob (ComplexPreCat_Additive A)}
        (f1 : Morphism x y) (f2 : Morphism y z)  :
    ∃ M : @Morphisms.Morphism (@KAPreTriang A),
      ∥ @ConeIso (@KAPreTriang A)
        (@mk_Tri (@KAPreTriang A) (@Trans (@KAPreTriang A)) x z
                 (@MappingCone A x z (MorphismComp f1 f2))
                 (# (ComplexHomotFunctor A) f1 ;; # (ComplexHomotFunctor A) f2)
                 (# (ComplexHomotFunctor A) (@MappingConeIn2 A x z (MorphismComp f1 f2)))
                 (# (ComplexHomotFunctor A) (@MappingConePr1 A x z (MorphismComp f1 f2)))) M ∥.
  Proof.
    intros P X. apply X. clear P X.
    use tpair.
    - exact (Morphisms.mk_Morphism (# (ComplexHomotFunctor A) (MorphismComp f1 f2))).
    - intros P X. apply X. clear P X. use mk_ConeIso.
      + cbn. use hfiberpair.
        * exact (MorphismComp f1 f2).
        * apply idpath.
      + use mk_TriMor.
        * use mk_MPMor.
          -- exact (KATriangOctaFiberComp f1 f2).
          -- exact (KATriangOctaFiberCompConeComms f1 f2).
        * cbn. rewrite functor_id. exact (! (KAPreTriang2_Comm1 _)).
      + use mk_TriMor_is_iso.
        * exact (is_z_isomorphism_identity _).
        * exact (is_z_isomorphism_identity _).
        * exact (is_z_isomorphism_identity _).
  Qed.

  Definition KATriangOctaFiberIso'Mor {x y y' z : KAPreTriang} {f1 : x --> y'} {g1 : y' --> y}
             {h2 : y --> z} {h3 : z --> (AddEquiv1 Trans x)}
             (f1' : hfiber # (ComplexHomotFunctor A) f1) (g1' : hfiber # (ComplexHomotFunctor A) g1)
             (H : ∥ Σ M : Morphisms.Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥)
             (f1'' := (hfiberpr1 _ _ f1')) (g1'' := (hfiberpr1 _ _ g1'))
             (e : identity x ;; # (ComplexHomotFunctor A) (f1'' ;; g1'') = f1 ;; g1 ;; identity y)
             (T : @TExt KAPreTriang (mk_DTri' _ H) (KAFiberDTri (f1'' ;; g1'')) _ _ e) :
    TriMor (mk_Tri (f1 ;; g1) h2 h3)
           (@mk_Tri (@KAPreTriang A) (@Trans (@KAPreTriang A)) _ _ _
                    (# (ComplexHomotFunctor A) f1'' ;; # (ComplexHomotFunctor A) g1'')
                    (# (ComplexHomotFunctor A) (MappingConeIn2 A (f1'' ;; g1'')))
                    (# (ComplexHomotFunctor A) (MappingConePr1 A (f1'' ;; g1'')))).
  Proof.
    use mk_TriMor.
      + use mk_MPMor.
        * use mk_MPMorMors.
          -- exact (identity _).
          -- exact (identity _).
          -- exact T.
        * use mk_MPMorComms.
          -- cbn. rewrite <- (functor_comp (ComplexHomotFunctor A)). exact e.
          -- exact (! (TExtComm1 T)).
      + exact (! (TExtComm2 T)).
  Defined.

  Definition KATriangOctaFiberIso' {x y y' z : KAPreTriang} {f1 : x --> y'} {g1 : y' --> y}
             {h2 : y --> z} {h3 : z --> (AddEquiv1 Trans x)}
             (f1' : hfiber # (ComplexHomotFunctor A) f1) (g1' : hfiber # (ComplexHomotFunctor A) g1)
             (H : ∥ Σ M : Morphisms.Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥)
             (f1'' := (hfiberpr1 _ _ f1')) (g1'' := (hfiberpr1 _ _ g1'))
             (e : identity x ;; # (ComplexHomotFunctor A) (f1'' ;; g1'') = f1 ;; g1 ;; identity y)
             (T : @TExt KAPreTriang (mk_DTri' _ H) (KAFiberDTri (f1'' ;; g1'')) _ _ e) :
    TriIso (mk_Tri (f1 ;; g1) h2 h3)
           (@mk_Tri (@KAPreTriang A) (@Trans (@KAPreTriang A)) _ _ _
                    (# (ComplexHomotFunctor A) f1'' ;; # (ComplexHomotFunctor A) g1'')
                    (# (ComplexHomotFunctor A) (MappingConeIn2 A (f1'' ;; g1'')))
                    (# (ComplexHomotFunctor A) (MappingConePr1 A (f1'' ;; g1'')))).
  Proof.
    use mk_TriIso.
    - exact (KATriangOctaFiberIso'Mor f1' g1' H e T).
    - use mk_TriMor_is_iso.
      + exact (is_z_isomorphism_identity _).
      + exact (is_z_isomorphism_identity _).
      + use (@TriangulatedFiveLemma
               KAPreTriang (mk_DTri' _ H) (mk_DTri' _ (KATriangOctaFiberCompCone f1'' g1''))
               (KATriangOctaFiberIso'Mor f1' g1' H e T)).
        * exact (is_z_isomorphism_identity _).
        * exact (is_z_isomorphism_identity _).
  Defined.

  Definition KATriangOctaMPMors {x y z : ob (ComplexPreCat_Additive A)}
             (f : Morphism x y) (g : Morphism y z) :
    MPMorMors
      (mk_MorphismPair (# (ComplexHomotFunctor A) (KAOctaMor1 f g))
                       (# (ComplexHomotFunctor A) (KAOctaMor2 f g)))
      (mk_MorphismPair (# (ComplexHomotFunctor A) (KAOctaMor1 f g))
                       (# (ComplexHomotFunctor A) (MappingConeIn2 A (KAOctaMor1 f g)))).
  Proof.
    use mk_MPMorMors.
    - exact (identity _).
    - exact (identity _).
    - exact (# (ComplexHomotFunctor A) (KAOctaMor3 f g)).
  Defined.

  Lemma KATriangOctaMPMorsComm {x y z : ob (ComplexPreCat_Additive A)}
             (f : Morphism x y) (g : Morphism y z) :
    @MPMorComms (ComplexHomot_Additive A) _ _ (KATriangOctaMPMors f g).
  Proof.
    use mk_MPMorComms.
    - exact (! (KAPreTriang2_Comm1 _)).
    - exact (KAOctaComm2' f g).
  Qed.

  Lemma KATriangOcta {x1 x2 y1 y2 z1 z2 : ob (@KAPreTriang A)}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : ∥ Σ M : Morphisms.Morphism, ∥ ConeIso (mk_Tri f1 f2 f3) M ∥ ∥)
             (H2 : ∥ Σ M : Morphisms.Morphism, ∥ ConeIso (mk_Tri g1 g2 g3) M ∥ ∥)
             (H3 : ∥ Σ M : Morphisms.Morphism, ∥ ConeIso (mk_Tri (f1 ;; g1) h2 h3) M ∥ ∥) :
    ∥ Octa H1 H2 H3 ∥.
  Proof.
    use (squash_to_prop H1 (propproperty _)). intros H1'.
    use (squash_to_prop H2 (propproperty _)). intros H2'.
    use (squash_to_prop H3 (propproperty _)). intros H3'.
    induction H1' as [M1 I1']. induction H2' as [M2 I2']. induction H3' as [M3 I3'].
    use (squash_to_prop I1' (propproperty _)). intros I1.
    use (squash_to_prop I2' (propproperty _)). intros I2.
    use (squash_to_prop I3' (propproperty _)). intros I3.
    use (squash_to_prop (ComplexHomotFunctor_issurj A f1) (propproperty _)). intros f1'.
    set (f1'' := hfiberpr1 _ _ f1').
    use (squash_to_prop (ComplexHomotFunctor_issurj A g1) (propproperty _)). intros g1'.
    set (g1'' := hfiberpr1 _ _ g1').
    set (Ext1 := DExt KAPreTriang
                      (mk_DTri' _ H1) (KAFiberDTri f1'') (identity _) (identity _)
                      (! (KAPreTriang3_1' _ _ (! (hfiberpr2 _ _ f1'))))).
    set (Ext2 := DExt KAPreTriang
                      (mk_DTri' _ H2) (KAFiberDTri g1'') (identity _) (identity _)
                      (! (KAPreTriang3_1' _ _ (! (hfiberpr2 _ _ g1'))))).
    assert (ee : # (ComplexHomotFunctor A) (f1'' ;; g1'') = f1 ;; g1).
    {
      rewrite functor_comp. unfold f1''. rewrite (hfiberpr2 _ _ f1').
      unfold g1''. rewrite (hfiberpr2 _ _ g1'). apply idpath.
    }
    set (Ext3 := DExt KAPreTriang
                      (mk_DTri' _ H3) (KAFiberDTri (f1'' ;; g1'')) (identity _) (identity _)
                      (! (KAPreTriang3_1' _ _ (! ee)))).
    use (squash_to_prop Ext1 (propproperty _)). intros Ext1'.
    use (squash_to_prop Ext2 (propproperty _)). intros Ext2'.
    use (squash_to_prop Ext3 (propproperty _)). intros Ext3'.
    intros P PX. apply PX. clear P PX.
    use (@OctaConeIso
           (@KAPreTriang A) x1 x2 y1 y2 z1 z2 f1 f2 f3 g1 g2 g3 h2 h3 H1 H2 H3 x1
           (MappingCone A g1'') y1 (MappingCone A (f1'' ;; g1'')) z1
           (MappingCone A f1'') (# (ComplexHomotFunctor A) f1'')
           (# (ComplexHomotFunctor A) (MappingConeIn2 A f1''))
           (# (ComplexHomotFunctor A) (MappingConePr1 A f1''))
           (# (ComplexHomotFunctor A) g1'')
           (# (ComplexHomotFunctor A) (MappingConeIn2 A g1''))
           (# (ComplexHomotFunctor A) (MappingConePr1 A g1''))
           (# (ComplexHomotFunctor A) (MappingConeIn2 A (f1'' ;; g1'')))
           (# (ComplexHomotFunctor A) (MappingConePr1 A (f1'' ;; g1'')))
           (KAFiberDTriIso f1'') (KAFiberDTriIso g1'')
           (KATriangOctaFiberCompCone f1'' g1'')
           (KATriangOctaFiberIso f1' H1 (! (KAPreTriang3_1' _ _ (! (hfiberpr2 _ _ f1')))) Ext1')
           (KATriangOctaFiberIso g1' H2 (! (KAPreTriang3_1' _ _ (! (hfiberpr2 _ _ g1')))) Ext2')
           (KATriangOctaFiberIso' f1' g1' H3 (! (KAPreTriang3_1' _ _ (! ee))) Ext3')
           (idpath _) (idpath _) (idpath _)).
    clear Ext1' Ext2' Ext3' Ext3 ee Ext2 Ext1.
    use mk_Octa.
    - exact (# (ComplexHomotFunctor A) (KAOctaMor1 f1'' g1'')).
    - exact (# (ComplexHomotFunctor A) (KAOctaMor2 f1'' g1'')).
    - intros P PX. apply PX. clear P PX.
      use tpair.
      + exact (Morphisms.mk_Morphism (# (ComplexHomotFunctor A) (KAOctaMor1 f1'' g1''))).
      + intros P PX. apply PX. clear P PX.
        * use mk_ConeIso.
          -- use hfiberpair.
             ++ exact (KAOctaMor1 f1'' g1'').
             ++ apply idpath.
          -- use mk_TriMor.
             ++ use mk_MPMor.
                ** exact (KATriangOctaMPMors f1'' g1'').
                ** exact (KATriangOctaMPMorsComm f1'' g1'').
             ++ exact (KAOctaComm3' f1'' g1'').
          -- use mk_TriMor_is_iso.
             ++ exact (is_z_isomorphism_identity _).
             ++ exact (is_z_isomorphism_identity _).
             ++ exact (KAOctaMor3Iso f1'' g1'').
    - exact (KAOctaComm5' f1'' g1'').
    - exact (KAOctaComm4' f1'' g1'').
  Qed.

  Definition KATriang : Triang.
  Proof.
    use mk_Triang.
    - exact (@KAPreTriang A).
    - intros x1 x2 y1 y2 z1 z2 f1 f2 f3 g1 g2 g3 h2 h3 H1 H2 H3.
      exact(KATriangOcta H1 H2 H3).
  Defined.

End KATriangulated.
