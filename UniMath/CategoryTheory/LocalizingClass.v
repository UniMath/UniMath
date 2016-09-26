(** * Localizing class *)
Require Import UniMath.Foundations.Basics.UnivalenceAxiom.
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.BinProductPrecategory.

(** * Localizing class and localization of categories.
    In this section we define localization of categories when the collection of morphisms forms
    so called localizing class. The axioms of localizing class S are the following
    - every identity morphism must be in the collection
    - if f and g are in S, then so is f ;; g
    - Suppose we morphisms s : X --> Y and f : Z --> Y such that s in in S. Then we can find a
      square, that is morphisms, s' : W --> Z and f' : W --> X, such that s' in in S and we have
      s' ;; f = f' ;; s.
    - Dual version of the previous. Suppose s : X --> Y and f : X --> Z such that s in in S. Then
      we can find a square, that is morphisms, s' : Z --> W and f' : Y --> W, such that s' is in S
      and we have s' ;; f = f' ;; s.
    - Suppose we have a morphism s : X --> Y contained in S and two morphisms f g : Y --> Z such
      that s ;; f = s ;; g. Then S contains a morphism s' such that f ;; s' = f ;; s'.
    - Dual of the above. Suppose we have a morphism s : Z --> W in S and two morphisms
      f g : Y --> Z such that f ;; s = g ;; s. Then we can find a morphism s' in S such that
      s' ;; f = s' ;; g.
*)

Section def_roofs.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Definition SubsetsOfMors : UU := Π (x y : ob C), hsubtypes (hSetpair (C⟦x, y⟧) (hs x y)).

  (** ** Localizing classes *)

  (** *** Identities and compositions are in the subset of morphisms *)
  Definition isLocalizingClass1 (SOM : SubsetsOfMors) : UU :=
    (Π (x : ob C), SOM x x (identity x))
      × (Π (x y z : ob C) (f : x --> y) (e1 : SOM x y f) (g : y --> z) (e2 : SOM y z g),
         SOM x z (f ;; g)).

  Definition isLocClassIs {SOM : SubsetsOfMors} (H : isLocalizingClass1 SOM) :
    Π (x : ob C), SOM x x (identity x) := pr1 H.

  Definition isLocClassComp {SOM : SubsetsOfMors} (H : isLocalizingClass1 SOM) :
    Π (x y z : ob C) (f : x --> y) (e1 : SOM x y f) (g : y --> z) (e2 : SOM y z g),
    SOM x z (f ;; g) := pr2 H.

  (** **** Squares *)
  Definition LocSqr1 (SOM : SubsetsOfMors) {x y z : ob C} (s : x --> y) (e1 : SOM x y s)
             (f : x --> z) : UU :=
    Σ D : (Σ (w : ob C), C⟦y, w⟧ × C⟦z, w⟧),
          (SOM z (pr1 D) (dirprod_pr2 (pr2 D)))
            × (s ;; (dirprod_pr1 (pr2 D)) = f ;; (dirprod_pr2 (pr2 D))).

  Definition LocSqr1Ob {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e1 : SOM x y s}
             {f : x --> z} (LS1 : LocSqr1 SOM s e1 f) : ob C := pr1 (pr1 LS1).
  Coercion LocSqr1Ob : LocSqr1 >-> ob.

  Definition LocSqr1Mor1 {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e1 : SOM x y s}
             {f : x --> z} (LS1 : LocSqr1 SOM s e1 f) : C⟦y, LS1⟧ := dirprod_pr1 (pr2 (pr1 LS1)).

  Definition LocSqr1Mor2 {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e1 : SOM x y s}
             {f : x --> z} (LS1 : LocSqr1 SOM s e1 f) : C⟦z, LS1⟧ := dirprod_pr2 (pr2 (pr1 LS1)).

  Definition LocSqr1Mor2Is {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e1 : SOM x y s}
             {f : x --> z} (LS1 : LocSqr1 SOM s e1 f) : SOM z LS1 (LocSqr1Mor2 LS1) :=
    pr1 (pr2 LS1).

  Definition LocSqr1Comm {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e1 : SOM x y s}
             {f : x --> z} (LS1 : LocSqr1 SOM s e1 f) :
    s ;; (LocSqr1Mor1 LS1) = f ;; (LocSqr1Mor2 LS1) := dirprod_pr2 (pr2 LS1).

  Definition LocSqr2 (SOM : SubsetsOfMors) {y z w : ob C} (s : y --> w) (e1 : SOM y w s)
             (f : z --> w) : UU :=
    Σ D : (Σ (x : ob C), C⟦x, y⟧ × C⟦x, z⟧),
          (SOM (pr1 D) z (dirprod_pr2 (pr2 D)))
            × ((dirprod_pr1 (pr2 D)) ;; s = (dirprod_pr2 (pr2 D)) ;; f).

  Definition LocSqr2Ob {SOM : SubsetsOfMors} {y z w : ob C} {s : y --> w} {e1 : SOM y w s}
             {f : z --> w} (LS2 : LocSqr2 SOM s e1 f) : ob C := pr1 (pr1 LS2).
  Coercion LocSqr2Ob : LocSqr2 >-> ob.

  Definition LocSqr2Mor1 {SOM : SubsetsOfMors} {y z w : ob C} {s : y --> w} {e1 : SOM y w s}
             {f : z --> w} (LS2 : LocSqr2 SOM s e1 f) : C⟦LS2, y⟧ := dirprod_pr1 (pr2 (pr1 LS2)).

  Definition LocSqr2Mor2 {SOM : SubsetsOfMors} {y z w : ob C} {s : y --> w} {e1 : SOM y w s}
             {f : z --> w} (LS2 : LocSqr2 SOM s e1 f) : C⟦LS2, z⟧ := dirprod_pr2 (pr2 (pr1 LS2)).

  Definition LocSqr2Mor2Is {SOM : SubsetsOfMors} {y z w : ob C} {s : y --> w} {e1 : SOM y w s}
             {f : z --> w} (LS2 : LocSqr2 SOM s e1 f) : SOM LS2 z (LocSqr2Mor2 LS2) :=
    dirprod_pr1 (pr2 LS2).

  Definition LocSqr2Comm {SOM : SubsetsOfMors} {y z w : ob C} {s : y --> w} {e1 : SOM y w s}
             {f : z --> w} (LS2 : LocSqr2 SOM s e1 f) :
    (LocSqr2Mor1 LS2) ;; s = (LocSqr2Mor2 LS2) ;; f := dirprod_pr2 (pr2 LS2).

  (** *** Completion to squares *)
  Definition isLocalizingClass2 (SOM : SubsetsOfMors) : UU :=
    (Π (x y z : ob C) (s : x --> y) (e1 : SOM x y s) (f : x --> z), (LocSqr1 SOM s e1 f))
      × (Π (y z w : ob C) (s : y --> w) (e1 : SOM y w s) (f : z --> w), (LocSqr2 SOM s e1 f)).

  Definition isLocClassSqr1 {SOM : SubsetsOfMors} (H : isLocalizingClass2 SOM) :
    Π (x y z : ob C) (s : x --> y) (e1 : SOM x y s) (f : x --> z), LocSqr1 SOM s e1 f :=
    dirprod_pr1 H.

  Definition isLocClassSqr2 {SOM : SubsetsOfMors} (H : isLocalizingClass2 SOM) :
    Π (y z w : ob C) (s : y --> w) (e1 : SOM y w s) (f : z --> w), LocSqr2 SOM s e1 f :=
    dirprod_pr2 H.

  (** **** Pre- and post switch *)
  Definition PreSwitch (SOM : SubsetsOfMors) {x y z : ob C} (s : x --> y) (e : SOM x y s)
             (f g : y --> z) (H : s ;; f = s ;; g) : UU :=
    Σ D : (Σ (w : ob C), C⟦z, w⟧), (SOM z (pr1 D) (pr2 D)) × (f ;; (pr2 D) = g ;; (pr2 D)).

  Definition PreSwitchOb {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e : SOM x y s}
             {f g : y --> z} {H : s ;; f = s ;; g} (PreS : PreSwitch SOM s e f g H) : ob C :=
    pr1 (pr1 PreS).
  Coercion PreSwitchOb : PreSwitch >-> ob.

  Definition PreSwitchMor {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e : SOM x y s}
             {f g : y --> z} {H : s ;; f = s ;; g} (PreS : PreSwitch SOM s e f g H) :
    C⟦z, PreS⟧ := pr2 (pr1 PreS).

  Definition PreSwitchMorIs {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e : SOM x y s}
             {f g : y --> z} {H : s ;; f = s ;; g} (PreS : PreSwitch SOM s e f g H) :
    SOM z PreS (PreSwitchMor PreS) := dirprod_pr1 (pr2 PreS).

  Definition PreSwitchEq {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e : SOM x y s}
             {f g : y --> z} {H : s ;; f = s ;; g} (PreS : PreSwitch SOM s e f g H) :
    f ;; (PreSwitchMor PreS) = g ;; (PreSwitchMor PreS) := dirprod_pr2 (pr2 PreS).

  (** **** Post switch *)

  Definition PostSwitch (SOM : SubsetsOfMors) {y z w : ob C} (f g : y --> z) (s : z --> w)
             (e : SOM z w s) (H : f ;; s = g ;; s) : UU :=
    Σ D : (Σ (x : ob C), C⟦x, y⟧), (SOM (pr1 D) y (pr2 D)) × ((pr2 D) ;; f = (pr2 D) ;; g).

  Definition PostSwitchOb {SOM : SubsetsOfMors} {y z w : ob C} {f g : y --> z} {s : z --> w}
             {e : SOM z w s} {H : f ;; s = g ;; s} (PostS : PostSwitch SOM f g s e H) : ob C :=
    pr1 (pr1 PostS).
  Coercion PostSwitchOb : PostSwitch >-> ob.

  Definition PostSwitchMor {SOM : SubsetsOfMors} {y z w : ob C} {f g : y --> z} {s : z --> w}
             {e : SOM z w s} {H : f ;; s = g ;; s} (PostS : PostSwitch SOM f g s e H) :
    C⟦PostS, y⟧ := pr2 (pr1 PostS).

  Definition PostSwitchMorIs {SOM : SubsetsOfMors} {y z w : ob C} {f g : y --> z} {s : z --> w}
             {e : SOM z w s} {H : f ;; s = g ;; s} (PostS : PostSwitch SOM f g s e H) :
    SOM PostS y (PostSwitchMor PostS) := dirprod_pr1 (pr2 PostS).

  Definition PostSwitchEq {SOM : SubsetsOfMors} {y z w : ob C} {f g : y --> z} {s : z --> w}
             {e : SOM z w s} {H : f ;; s = g ;; s} (PostS : PostSwitch SOM f g s e H) :
    (PostSwitchMor PostS) ;; f = (PostSwitchMor PostS) ;; g := dirprod_pr2 (pr2 PostS).

  (** *** Pre- and postcomposition with morphisms in the subset *)
  Definition isLocalizingClass3 (SOM : SubsetsOfMors) : UU :=
    (Π (x y z : ob C) (s : x --> y) (e : SOM x y s) (f g : y --> z) (H : s ;; f = s ;; g),
     PreSwitch SOM s e f g H)
      × (Π (y z w : ob C) (f g : y --> z) (s : z --> w) (e : SOM z w s) (H : f ;; s = g ;; s),
         PostSwitch SOM f g s e H).

  Definition isLocClassPre {SOM : SubsetsOfMors} (H : isLocalizingClass3 SOM) :
    Π (x y z : ob C) (s : x --> y) (e : SOM x y s) (f g : y --> z) (H : s ;; f = s ;; g),
    PreSwitch SOM s e f g H := dirprod_pr1 H.

  Definition isLocClassPost {SOM : SubsetsOfMors} (H : isLocalizingClass3 SOM) :
    Π (y z w : ob C) (f g : y --> z) (s : z --> w) (e : SOM z w s) (H : f ;; s = g ;; s),
    PostSwitch SOM f g s e H := dirprod_pr2 H.

  (** *** Localizing class *)
  Definition isLocalizingClass (SOM : SubsetsOfMors) : UU :=
    (isLocalizingClass1 SOM) × (isLocalizingClass2 SOM) × (isLocalizingClass3 SOM).

  Definition isLocalizingClass_isLocalizingClass1 {SOM : SubsetsOfMors}
             (H : isLocalizingClass SOM) : isLocalizingClass1 SOM := dirprod_pr1 H.
  Coercion isLocalizingClass_isLocalizingClass1 : isLocalizingClass >-> isLocalizingClass1.

  Definition isLocalizingClass_isLocalizingClass2 {SOM : SubsetsOfMors}
             (H : isLocalizingClass SOM) : isLocalizingClass2 SOM :=
    dirprod_pr1 (dirprod_pr2 H).
  Coercion isLocalizingClass_isLocalizingClass2 : isLocalizingClass >-> isLocalizingClass2.

  Definition isLocalizingClass_isLocalizingClass3 {SOM : SubsetsOfMors}
             (H : isLocalizingClass SOM) : isLocalizingClass3 SOM :=
    dirprod_pr2 (dirprod_pr2 H).
  Coercion isLocalizingClass_isLocalizingClass3 : isLocalizingClass >-> isLocalizingClass3.

  (** Collection of morphisms in C *)
  Variable SOM : SubsetsOfMors.

  (** The above collection satisfies the conditions of localizin class. See the comment on top
      of this section. *)
  Hypothesis iLC : isLocalizingClass SOM.

  (** ** Roofs *)
  Definition Roof (x y : ob C) : UU :=
    Σ D : (Σ z : ob C, C⟦z, x⟧ × C⟦z, y⟧), (SOM (pr1 D) x (dirprod_pr1 (pr2 D))).

  Definition mk_Roof (x y z : ob C) (s : z --> x) (f : z --> y) (e : SOM z x s) : Roof x y :=
    tpair _ (tpair _ z (s,,f)) e.

  Definition RoofOb {x y : ob C} (R : Roof x y) : ob C := pr1 (pr1 R).
  Coercion RoofOb : Roof >-> ob.

  Definition RoofMor1 {x y : ob C} (R : Roof x y) : C⟦R, x⟧ := dirprod_pr1 (pr2 (pr1 R)).

  Definition RoofMor1Is {x y : ob C} (R : Roof x y) : SOM R x (RoofMor1 R) := pr2 R.

  Definition RoofMor2 {x y : ob C} (R : Roof x y) : C⟦R, y⟧ := dirprod_pr2 (pr2 (pr1 R)).

  (** ** Coroofs *)
  Definition Coroof (x y : ob C) : UU :=
    Σ D : (Σ z : ob C, C⟦x, z⟧ × C⟦y, z⟧), (SOM y (pr1 D) (dirprod_pr2 (pr2 D))).

  Definition mk_Coroof (x y z : ob C) (f : x --> z) (s : y --> z) (e : SOM y z s) : Coroof x y :=
    tpair _ (tpair _ z (f,,s)) e.

  Definition CoroofOb {x y : ob C} (CR : Coroof x y) : ob C := pr1 (pr1 CR).
  Coercion CoroofOb : Coroof >-> ob.

  Definition CoroofMor1 {x y : ob C} (CR : Coroof x y) : C⟦x, CR⟧ := dirprod_pr1 (pr2 (pr1 CR)).

  Definition CoroofMor2 {x y : ob C} (CR : Coroof x y) : C⟦y, CR⟧ := dirprod_pr2 (pr2 (pr1 CR)).

  Definition CoroofMor2Is {x y : ob C} (CR : Coroof x y) : SOM y CR (CoroofMor2 CR) := pr2 CR.

  Definition RoofToCoroof {x y : ob C} (R : Roof x y) : Coroof x y.
  Proof.
    set (sqr := isLocClassSqr1 iLC _ _ _ (RoofMor1 R) (RoofMor1Is R) (RoofMor2 R)).
    use mk_Coroof.
    - exact sqr.
    - exact (LocSqr1Mor1 sqr).
    - exact (LocSqr1Mor2 sqr).
    - exact (LocSqr1Mor2Is sqr).
  Defined.

  (** ** RoofTop *)
  (** These are used to define an equivalence relation between roofs *)
  Definition RoofTop {x y : ob C} (R1 R2 : Roof x y) : UU :=
    Σ D : (Σ w : ob C, C⟦w, R1⟧ × C⟦w, R2⟧),
          (SOM (pr1 D) x ((dirprod_pr1 (pr2 D)) ;; (RoofMor1 R1)))
            × ((dirprod_pr1 (pr2 D)) ;; (RoofMor1 R1) = (dirprod_pr2 (pr2 D)) ;; (RoofMor1 R2))
            × ((dirprod_pr1 (pr2 D)) ;; (RoofMor2 R1) = (dirprod_pr2 (pr2 D)) ;; (RoofMor2 R2)).

  Definition mk_RoofTop {x y : ob C} {R1 R2 : Roof x y} (w : ob C) (s : w --> R1) (f : w --> R2)
             (e : SOM w x (s ;; RoofMor1 R1))
             (H1 : s ;; (RoofMor1 R1) = f ;; (RoofMor1 R2))
             (H2 : s ;; (RoofMor2 R1) = f ;; (RoofMor2 R2)) : RoofTop R1 R2 :=
    tpair _ (tpair _ w (s,,f)) (e,,(H1,,H2)).

  Definition RoofTopOb {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) : ob C := pr1 (pr1 T).
  Coercion RoofTopOb : RoofTop >-> ob.

  Definition RoofTopMor1 {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) : C⟦T, R1⟧ :=
    dirprod_pr1 (pr2 (pr1 T)).

  Definition RoofTopMor1Is {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) :
    (SOM T x ((RoofTopMor1 T) ;; (RoofMor1 R1))) := (dirprod_pr1 (pr2 T)).

  Definition RoofTopMor2 {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) : C⟦T, R2⟧ :=
    dirprod_pr2 (pr2 (pr1 T)).

  Definition RoofTopEq1 {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) :
    (RoofTopMor1 T) ;; (RoofMor1 R1) = (RoofTopMor2 T) ;; (RoofMor1 R2) :=
    dirprod_pr1 (dirprod_pr2 (pr2 T)).

  Definition RoofTopEq2 {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) :
    (RoofTopMor1 T) ;; (RoofMor2 R1) = (RoofTopMor2 T) ;; (RoofMor2 R2) :=
    dirprod_pr2 (dirprod_pr2 (pr2 T)).

  (** We define an equivalence relation between the roofs *)
  Definition RoofHrel' {x y : ob C} (R1 R2 : Roof x y) : hProp := ishinh (RoofTop R1 R2).

  Definition RoofHrel (x y : ob C) : hrel (Roof x y) :=
    (fun R1 : Roof x y => fun R2 : Roof x y => RoofHrel' R1 R2).

  Lemma RoofEqrel (x y : ob C) : iseqrel (RoofHrel x y).
  Proof.
    use iseqrelconstr.
    (* is trans *)
    - intros R1 R2 R3 T1' T2'.
      use (squash_to_prop T1'). apply isapropishinh. intros T1. clear T1'.
      use (squash_to_prop T2'). apply isapropishinh. intros T2. clear T2'.
      set (tmp := isLocClassSqr2 iLC T2 T1 x (RoofTopMor1 T2 ;; RoofMor1 R2) (RoofTopMor1Is T2)
                                 (RoofTopMor2 T1 ;; RoofMor1 R2)).
      induction tmp as [D1 D2]. induction D1 as [w m]. induction m as [m1 m2].
      induction D2 as [D1 D2]. cbn in D1, D2. repeat rewrite assoc in D2.
      set (tmp := isLocClassPost iLC w R2 x (m1 ;; RoofTopMor1 T2) (m2 ;; RoofTopMor2 T1)
                                 (RoofMor1 R2) (RoofMor1Is R2) D2).
      induction tmp as [t p].
      intros P X. apply X. clear X P.
      use mk_RoofTop.
      + exact (pr1 t).
      + exact ((pr2 t) ;; m2 ;; RoofTopMor1 T1).
      + exact ((pr2 t) ;; m1 ;; RoofTopMor2 T2).
      + repeat rewrite <- assoc. use (isLocClassComp iLC).
        * exact (dirprod_pr1 p).
        * use (isLocClassComp iLC).
          -- exact D1.
          -- exact (RoofTopMor1Is T1).
      + induction p as [p1 p2]. repeat rewrite assoc in p2.
        set (tmp := RoofTopEq1 T2). repeat rewrite <- assoc. rewrite <- tmp. clear tmp.
        repeat rewrite assoc. repeat rewrite <- (assoc (pr2 t)). rewrite D2.
        repeat rewrite <- assoc.
        apply cancel_precomposition. apply cancel_precomposition.
        exact (RoofTopEq1 T1).
      + induction p as [p1 p2]. repeat rewrite assoc in p2.
        set (tmp := RoofTopEq2 T2). repeat rewrite <- assoc. rewrite <- tmp. clear tmp.
        repeat rewrite assoc. rewrite p2. repeat rewrite <- assoc.
        apply cancel_precomposition. apply cancel_precomposition.
        exact (RoofTopEq2 T1).
    (* isrefl *)
    - intros R1.
      intros P X. apply X. clear X P.
      use mk_RoofTop.
      + exact R1.
      + exact (identity R1).
      + exact (identity R1).
      + rewrite id_left. exact (RoofMor1Is R1).
      + apply idpath.
      + apply idpath.
    (* issymm *)
    - intros R1 R2 T'.
      use (squash_to_prop T'). apply isapropishinh. intros T. clear T'.
      intros P X. apply X. clear X P.
      use mk_RoofTop.
      + exact T.
      + exact (RoofTopMor2 T).
      + exact (RoofTopMor1 T).
      + rewrite <- (RoofTopEq1 T). exact (RoofTopMor1Is T).
      + exact (! (RoofTopEq1 T)).
      + exact (! (RoofTopEq2 T)).
  Qed.

  (** We are interested in the equivalence classes of roofs. *)
  (* Definition eqclass {X : UU} {r : eqrel X} : UU := Σ A : hsubtypes X, iseqclass r A. *)

  Definition RoofEqclass (x y : ob C) : UU :=
    Σ A : hsubtypes (Roof x y), iseqclass (eqrelpair _ (RoofEqrel x y)) A.

  Lemma isasetRoofEqclass (x y : ob C) : isaset (RoofEqclass x y).
  Proof.
    apply isaset_total2.
    - apply isasethsubtypes.
    - intros x0.
      apply isasetaprop.
      apply isapropiseqclass.
  Defined.

  Definition mk_RoofEqclass {x y : ob C} (A : hsubtypes (Roof x y))
             (H : iseqclass (eqrelpair _ (RoofEqrel x y)) A) : RoofEqclass x y := tpair _ A H.

  Definition RoofEqclassIn {x y : ob C} (RE : RoofEqclass x y) : hsubtypes (Roof x y) := pr1 RE.

  Definition RoofEqclassIs {x y : ob C} (RE : RoofEqclass x y) :
    iseqclass (eqrelpair _ (RoofEqrel x y)) (RoofEqclassIn RE) := pr2 RE.

  Definition RoofEqclassEq {x y : ob C} (RE1 RE2 : RoofEqclass x y)
             (H1 : Π (R : Roof x y) (H : (pr1 RE1) R), (pr1 RE2) R)
             (H2 : Π (R : Roof x y) (H : (pr1 RE2) R), (pr1 RE1) R) : RE1 = RE2.
  Proof.
    use total2_paths.
    - use funextfun. intros g.
      apply hPropUnivalence.
      + apply H1.
      + apply H2.
    - apply proofirrelevance. apply isapropiseqclass.
  Qed.

  Definition RoofEqclassDisjoint {x y : ob C} (RE1 RE2 : RoofEqclass x y)
             (R1 R2 : Roof x y) (H1 : RoofEqclassIn RE1 R1) (H2 : RoofEqclassIn RE2 R2)
             (H : (eqrelpair _ (RoofEqrel x y)) R1 R2) : RE1 = RE2.
  Proof.
    use RoofEqclassEq.
    - intros R H'.
      set (tmp := eqax1 (pr2 RE1) R1 R2 H H1).
      set (tmp' := eqax2 (pr2 RE1) R R2 H' tmp).
      apply eqrelsymm in tmp'.
      apply (eqax1 (pr2 RE2) R2 R tmp' H2).
    - intros R H'.
      apply eqrelsymm in H.
      set (tmp := eqax1 (pr2 RE2) R2 R1 H H2).
      set (tmp' := eqax2 (pr2 RE2) R1 R tmp H').
      apply (eqax1 (pr2 RE1) R1 R tmp' H1).
  Qed.

  Definition RoofEqclassFromRoof {x y : ob C} (R : Roof x y) : RoofEqclass x y.
  Proof.
    use tpair.
    - exact (fun RR : Roof x y => (eqrelpair _ (RoofEqrel x y)) RR R).
    - use tpair.
      + intros P X. apply X. clear X P.
        use tpair.
        * exact R.
        * apply eqrelrefl.
      + split.
        * intros x1 x2 X X0.
          use eqreltrans.
          -- exact x1.
          -- apply eqrelsymm. apply X.
          -- apply X0.
        * intros x1 x2 X X0.
          use eqreltrans.
          -- exact R.
          -- exact X.
          -- apply eqrelsymm. apply X0.
  Defined.

  Definition RoofEqclassFromRoofIn {x y : ob C} (R : Roof x y) :
    RoofEqclassIn (RoofEqclassFromRoof R) R.
  Proof.
    intros P X. apply X. clear X P.
    use mk_RoofTop.
    - exact R.
    - exact (identity R).
    - exact (identity R).
    - use (isLocClassComp iLC).
      + apply (isLocClassIs iLC).
      + apply (RoofMor1Is R).
    - apply idpath.
    - apply idpath.
  Qed.

  Definition RoofEqClassIn {x y : ob C} (R1 R2 R3 : Roof x y)
             (H1 : RoofEqclassIn (RoofEqclassFromRoof R1) R2)
             (H2 : (eqrelpair _ (RoofEqrel x y)) R2 R3) :
    RoofEqclassIn (RoofEqclassFromRoof R1) R3.
  Proof.
    exact (eqax1 (RoofEqclassIs (RoofEqclassFromRoof R1)) R2 R3 H2 H1).
  Qed.

  Definition RoofEqClassIn2 {x y : ob C} (RE : RoofEqclass x y) (R2 R3 : Roof x y)
             (H1 : RoofEqclassIn RE R2) (H2 : (eqrelpair _ (RoofEqrel x y)) R2 R3) :
    RoofEqclassIn RE R3.
  Proof.
    use (squash_to_prop (pr1 (RoofEqclassIs RE))). apply propproperty. intros RE1.
    induction RE1 as [RE1 RE2].
    apply (eqax1 (RoofEqclassIs RE) RE1 R3).
    - use eqreltrans.
      + exact R2.
      + apply (eqax2 (RoofEqclassIs RE) RE1 R2 RE2 H1).
      + apply H2.
    - apply RE2.
  Qed.

  Definition roof_comp {x y z : ob C} (R1 : Roof x y) (R2 : Roof y z) : Roof x z.
  Proof.
    set (LS2 := isLocClassSqr2 iLC R2 R1 y (RoofMor1 R2) (RoofMor1Is R2) (RoofMor2 R1)).
    use mk_Roof.
    - exact LS2.
    - exact ((LocSqr2Mor2 LS2) ;; (RoofMor1 R1)).
    - exact ((LocSqr2Mor1 LS2) ;; (RoofMor2 R2)).
    - use (isLocClassComp iLC).
      + exact (LocSqr2Mor2Is LS2).
      + exact (RoofMor1Is R1).
  Defined.

  (** ** Composition of roofs *)
  Local Lemma SOM_eq {x y : ob C} (f g : x --> y) (e : f = g) (H : SOM x y f) :
    SOM x y g.
  Proof.
    induction e. exact H.
  Qed.

  (** Construct a "commutative coroof" from RoofTop *)
  Definition RoofTopToCoroof {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) :
    Σ CR : Coroof x y, (RoofMor1 R1 ;; CoroofMor1 CR = RoofMor2 R1 ;; CoroofMor2 CR)
                         × (RoofMor1 R2 ;; CoroofMor1 CR = RoofMor2 R2 ;; CoroofMor2 CR).
  Proof.
    set (sqr1 := isLocClassSqr1 iLC _ _ _ (RoofMor1 R1) (RoofMor1Is R1) (RoofMor2 R1)).
    set (sqr2 := isLocClassSqr1 iLC _ _ _ (RoofMor1 R2) (RoofMor1Is R2) (RoofMor2 R2)).
    set (sqr3 := isLocClassSqr1 iLC _ _ _ (LocSqr1Mor2 sqr1) (LocSqr1Mor2Is sqr1)
                                (LocSqr1Mor2 sqr2)).
    set (mor1 := RoofTopMor1 T ;; RoofMor1 R1 ;; LocSqr1Mor1 sqr1 ;; LocSqr1Mor1 sqr3).
    set (mor2 := RoofTopMor1 T ;; RoofMor1 R1 ;; LocSqr1Mor1 sqr2 ;; LocSqr1Mor2 sqr3).

    assert (H : RoofTopMor1 T ;; RoofMor1 R1 ;; (LocSqr1Mor1 sqr1 ;; LocSqr1Mor1 sqr3)
                = RoofTopMor1 T ;; RoofMor1 R1 ;; (LocSqr1Mor1 sqr2 ;; LocSqr1Mor2 sqr3)).
    {
      set (tmp1 := LocSqr1Comm sqr1).
      set (tmp2 := LocSqr1Comm sqr2).
      set (tmp3 := LocSqr1Comm sqr3).
      rewrite assoc. rewrite <- (assoc _ (RoofMor1 R1)). rewrite tmp1.
      rewrite assoc. rewrite <- assoc. rewrite tmp3.
      rewrite assoc. rewrite (RoofTopEq2 T).
      rewrite <- (assoc _ (RoofMor2 R2)). rewrite <- tmp2.
      rewrite assoc. rewrite (RoofTopEq1 T). rewrite assoc.
      apply idpath.
    }
    set (PreS := isLocClassPre iLC _ _ _ (RoofTopMor1 T ;; RoofMor1 R1) (RoofTopMor1Is T)
                               (LocSqr1Mor1 sqr1 ;; LocSqr1Mor1 sqr3)
                               (LocSqr1Mor1 sqr2 ;; LocSqr1Mor2 sqr3) H).
    use tpair.
    - use mk_Coroof.
      + exact PreS.
      + exact (LocSqr1Mor1 sqr1 ;; LocSqr1Mor1 sqr3 ;; PreSwitchMor PreS).
      + exact (LocSqr1Mor2 sqr2 ;; LocSqr1Mor2 sqr3 ;; PreSwitchMor PreS).
      + use (isLocClassComp iLC).
        * use (isLocClassComp iLC).
          -- exact (LocSqr1Mor2Is sqr2).
          -- exact (LocSqr1Mor2Is sqr3).
        * exact (PreSwitchMorIs PreS).
    - cbn. split.
      + rewrite <- (LocSqr1Comm sqr3).
        rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
        apply cancel_postcomposition. apply cancel_postcomposition.
        apply (LocSqr1Comm sqr1).
      + rewrite (PreSwitchEq PreS).
        rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
        apply cancel_postcomposition. apply cancel_postcomposition.
        apply (LocSqr1Comm sqr2).
  Defined.
  Opaque RoofTopToCoroof.

  (** Precomposition with equivalent roofs yield equivalent roofs. *)
  Lemma roof_pre_comp {x y z : ob C} (R1 R2 : Roof x y)
        (e : (eqrelpair (RoofHrel x y) (RoofEqrel x y)) R1 R2) (R3 : Roof y z) :
    (eqrelpair (RoofHrel x z) (RoofEqrel x z)) (roof_comp R1 R3) (roof_comp R2 R3).
  Proof.
    use (squash_to_prop e). apply propproperty. intros T.
    set (T' := RoofTopToCoroof T). induction T' as [CR eq].
    intros P X. apply X. clear X P.
    set (R4 := roof_comp R1 R3). set (R5 := roof_comp R2 R3).
    unfold roof_comp in R4. unfold roof_comp in R5.
    set (sqr4 := isLocClassSqr2 iLC R3 R1 y (RoofMor1 R3) (RoofMor1Is R3) (RoofMor2 R1)).
    set (sqr5 := isLocClassSqr2 iLC R3 R2 y (RoofMor1 R3) (RoofMor1Is R3) (RoofMor2 R2)).
    fold sqr4 in R4. fold sqr5 in R5.
    set (sqr6 := isLocClassSqr2 iLC R5 R4 x (LocSqr2Mor2 sqr5 ;; RoofMor1 R2) (RoofMor1Is R5)
                                (LocSqr2Mor2 sqr4 ;; RoofMor1 R1)).
    assert (s : SOM R3 CR (RoofMor1 R3 ;; CoroofMor2 CR)).
    {
      use (isLocClassComp iLC).
      - exact (RoofMor1Is R3).
      - exact (CoroofMor2Is CR).
    }
    assert (H : LocSqr2Mor1 sqr6 ;; LocSqr2Mor1 sqr5 ;; (RoofMor1 R3 ;; CoroofMor2 CR) =
                LocSqr2Mor2 sqr6 ;; LocSqr2Mor1 sqr4 ;; (RoofMor1 R3 ;; CoroofMor2 CR)).
    {
      rewrite assoc. rewrite assoc.
      rewrite <- (assoc _ (LocSqr2Mor1 sqr5)). rewrite (LocSqr2Comm sqr5).
      rewrite <- (assoc _ (LocSqr2Mor1 sqr4)). rewrite (LocSqr2Comm sqr4).
      rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
      rewrite <- (dirprod_pr1 eq). rewrite <- (dirprod_pr2 eq).
      rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
      apply cancel_postcomposition.
      set (tmp := LocSqr2Comm sqr6). rewrite assoc in tmp. rewrite assoc in tmp.
      apply tmp.
    }
    set (PostS := isLocClassPost iLC _ _ _
                                 (LocSqr2Mor1 sqr6 ;; LocSqr2Mor1 sqr5)
                                 (LocSqr2Mor2 sqr6 ;; LocSqr2Mor1 sqr4)
                                 (RoofMor1 R3 ;; CoroofMor2 CR) s H).
    use mk_RoofTop.
    - exact PostS.
    - exact (PostSwitchMor PostS ;; LocSqr2Mor2 sqr6).
    - exact (PostSwitchMor PostS ;; LocSqr2Mor1 sqr6).
    - use (isLocClassComp iLC).
      + use (isLocClassComp iLC).
        * exact (PostSwitchMorIs PostS).
        * exact (LocSqr2Mor2Is sqr6).
      + exact (RoofMor1Is R4).
    - cbn.
      rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
      apply (! (LocSqr2Comm sqr6)).
    - cbn.
      rewrite assoc. rewrite assoc.
      set (tmp := ! (PostSwitchEq PostS)). rewrite assoc in tmp. rewrite assoc in tmp.
      apply (maponpaths (fun f : _ => f ;; RoofMor2 R3)) in tmp.
      apply tmp.
  Qed.

  (** Postcomposition with equivalent roofs yield equivalent roofs. *)
  Lemma roof_post_comp {x y z : ob C} (R1 : Roof x y) (R2 R3 : Roof y z)
        (e : (eqrelpair (RoofHrel y z) (RoofEqrel y z)) R2 R3) :
    (eqrelpair (RoofHrel x z) (RoofEqrel x z)) (roof_comp R1 R2) (roof_comp R1 R3).
  Proof.
    use (squash_to_prop e). apply propproperty. intros T. clear e.
    set (T' := RoofTopToCoroof T). induction T' as [CR eq].
    intros P X. apply X. clear X P.
    set (R4 := roof_comp R1 R2). set (R5 := roof_comp R1 R3).
    unfold roof_comp in R4. unfold roof_comp in R5.
    set (sqr4 := isLocClassSqr2 iLC R2 R1 y (RoofMor1 R2) (RoofMor1Is R2) (RoofMor2 R1)).
    set (sqr5 := isLocClassSqr2 iLC R3 R1 y (RoofMor1 R3) (RoofMor1Is R3) (RoofMor2 R1)).
    fold sqr4 in R4. fold sqr5 in R5.
    set (sqr6 := isLocClassSqr2 iLC R5 R4 R1 (LocSqr2Mor2 sqr5) (LocSqr2Mor2Is sqr5)
                                (LocSqr2Mor2 sqr4)).
    assert (H : LocSqr2Mor1 sqr6 ;; LocSqr2Mor1 sqr5 ;; RoofMor2 R3 ;; CoroofMor2 CR =
                LocSqr2Mor2 sqr6 ;; LocSqr2Mor1 sqr4 ;; RoofMor2 R2 ;; CoroofMor2 CR).
    {
      rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
      rewrite <- (dirprod_pr1 eq). rewrite <- (dirprod_pr2 eq).
      rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
      rewrite <- (assoc _ (LocSqr2Mor1 sqr4)). rewrite (LocSqr2Comm sqr4).
      rewrite <- (assoc _ (LocSqr2Mor1 sqr5)). rewrite (LocSqr2Comm sqr5).
      rewrite assoc. rewrite assoc.
      apply cancel_postcomposition. apply cancel_postcomposition.
      apply (LocSqr2Comm sqr6).
    }
    set (PostS := isLocClassPost iLC _ _ _
                               (LocSqr2Mor1 sqr6 ;; LocSqr2Mor1 sqr5 ;; RoofMor2 R3)
                               (LocSqr2Mor2 sqr6 ;; LocSqr2Mor1 sqr4 ;; RoofMor2 R2)
                               (CoroofMor2 CR) (CoroofMor2Is CR) H).
    use mk_RoofTop.
    - exact PostS.
    - exact (PostSwitchMor PostS ;; LocSqr2Mor2 sqr6).
    - exact (PostSwitchMor PostS ;; LocSqr2Mor1 sqr6).
    - use (isLocClassComp iLC).
      + use (isLocClassComp iLC).
        * exact (PostSwitchMorIs PostS).
        * exact (LocSqr2Mor2Is sqr6).
      + exact (RoofMor1Is R4).
    - cbn. rewrite assoc. rewrite assoc. apply cancel_postcomposition.
      set (tmp := ! (LocSqr2Comm sqr6)).
      apply (maponpaths (fun f : _ => PostSwitchMor PostS ;; f)) in tmp.
      rewrite assoc in tmp. rewrite assoc in tmp. apply tmp.
    - cbn. apply pathsinv0.
      rewrite assoc. rewrite assoc.
      set (tmp := PostSwitchEq PostS).
      rewrite assoc in tmp. rewrite assoc in tmp. rewrite assoc in tmp. rewrite assoc in tmp.
      apply tmp.
  Qed.

  Lemma roof_comp_iscontr (x y z : ob C) (e1 : RoofEqclass x y) (e2 : RoofEqclass y z) :
    iscontr (Σ e3 : RoofEqclass x z,
                    Π (f : Roof x y) (s1 : (RoofEqclassIn e1) f)
                      (g : Roof y z) (s2 : (RoofEqclassIn e2) g),
                    (RoofEqclassIn e3) (roof_comp f g)).
  Proof.
    induction e1 as [e1 e1eq]. induction e2 as [e2 e2eq].
    use (squash_to_prop (dirprod_pr1 e1eq)). apply isapropiscontr. intros R1.
    induction R1 as [R1 R1'].
    use (squash_to_prop (dirprod_pr1 e2eq)). apply isapropiscontr. intros R2.
    induction R2 as [R2 R2'].
    use tpair.
    - use tpair.
      + use mk_RoofEqclass.
        * exact (fun RR : (Roof x z) => (eqrelpair _ (RoofEqrel x z)) RR (roof_comp R1 R2)).
        * use iseqclassconstr.
          -- intros P X. apply X. clear X P.
             use tpair.
             ++ exact (roof_comp R1 R2).
             ++ use eqrelrefl.
          -- intros R3 R4 H1 H2. cbn beta in H2. cbn beta.
             use (squash_to_prop H1). apply propproperty. intros T1.
             use (squash_to_prop H2). apply propproperty. intros T2.
             apply eqrelsymm in H1.
             use eqreltrans.
             ++ exact R3.
             ++ exact H1.
             ++ exact H2.
          -- intros R3 R4 H1 H2. cbn beta in H1, H2.
             apply eqrelsymm in H2.
             use eqreltrans.
             ++ exact (roof_comp R1 R2).
             ++ exact H1.
             ++ exact H2.
      + cbn. intros R3 R3' R4 R4'.
        set (tmp1 := eqax2 e1eq R1 R3 R1' R3').
        set (tmp2 := eqax2 e2eq R2 R4 R2' R4').
        set (tmp_pre := roof_pre_comp R1 R3 tmp1 R4).
        set (tmp_post := roof_post_comp R1 R2 R4 tmp2).
        assert (X : (eqrelpair (RoofHrel x z) (RoofEqrel x z)) (roof_comp R3 R4) (roof_comp R1 R2)).
        {
          apply eqrelsymm.
          use eqreltrans.
          - exact (roof_comp R1 R4).
          - exact tmp_post.
          - exact tmp_pre.
        }
        exact X.
    (* Uniqueness *)
    - intros t.
      use total2_paths.
      + use RoofEqclassEq.
        * intros R HR. cbn.
          set (tmp1 := eqax2 (pr2 (pr1 t))). apply tmp1.
          -- exact HR.
          -- apply (pr2 t).
             ++ cbn. exact R1'.
             ++ cbn. exact R2'.
        * intros R HR. cbn in HR.
          set (tmp1 := eqax1 (pr2 (pr1 t))). apply (tmp1 (roof_comp R1 R2)).
          -- apply eqrelsymm. apply HR.
          -- apply (pr2 t).
             ++ cbn. exact R1'.
             ++ cbn. exact R2'.
      + apply proofirrelevance.
        apply impred_isaprop. intros t0.
        apply impred_isaprop. intros t1.
        apply impred_isaprop. intros t2.
        apply impred_isaprop. intros t3.
        apply impred_isaprop. intros t4.
        apply impred_isaprop. intros t5.
        apply propproperty.
  Qed.

  Local Lemma roof_comp_iscontr_in (x y z : ob C) (R1 : Roof x y) (R2 : Roof y z) :
    RoofEqclassIn (pr1 (pr1 (roof_comp_iscontr _ _ _ (RoofEqclassFromRoof R1)
                                               (RoofEqclassFromRoof R2))))
                  (roof_comp R1 R2).
  Proof.
    use (pr2 (pr1 (roof_comp_iscontr x y z (RoofEqclassFromRoof R1) (RoofEqclassFromRoof R2)))).
    - apply RoofEqclassFromRoofIn.
    - apply RoofEqclassFromRoofIn.
  Qed.

  (** ** Definition of the localization *)
  Definition loc_precategory_ob_mor : precategory_ob_mor :=
    tpair (fun ob : UU => ob -> ob -> UU) (ob C) (fun x y : ob C => RoofEqclass x y).

  Definition IdRoof (x : ob C) : Roof x x.
  Proof.
    use mk_Roof.
    - exact x.
    - exact (identity x).
    - exact (identity x).
    - exact (isLocClassIs iLC x).
  Defined.

  Lemma IdRoofEqrel_left {x y : ob C} (R1 : Roof x y) :
    (eqrelpair (RoofHrel x y) (RoofEqrel x y)) R1 (roof_comp (IdRoof x) R1).
  Proof.
    set (comp := roof_comp (IdRoof x) R1). unfold roof_comp in comp.
    set (sqr := isLocClassSqr2 iLC R1 (IdRoof x) x (RoofMor1 R1) (RoofMor1Is R1)
                               (RoofMor2 (IdRoof x))).
    fold sqr in comp. apply eqrelsymm.
    intros P X. apply X. clear X P.
    use mk_RoofTop.
    - exact comp.
    - exact (identity comp).
    - exact (LocSqr2Mor1 sqr).
    - use (isLocClassComp iLC).
      + apply (isLocClassIs iLC).
      + apply (RoofMor1Is comp).
    - rewrite id_left. cbn. apply (! (LocSqr2Comm sqr)).
    - cbn. rewrite id_left. apply idpath.
  Qed.

  Lemma IdRoofEqrel_right {x y : ob C} (R1 : Roof x y) :
    (eqrelpair (RoofHrel x y) (RoofEqrel x y)) R1 (roof_comp R1 (IdRoof y)).
  Proof.
    set (comp := roof_comp R1 (IdRoof y)). unfold roof_comp in comp.
    set (sqr := isLocClassSqr2 iLC (IdRoof y) R1 y (RoofMor1 (IdRoof y))
                               (RoofMor1Is (IdRoof y)) (RoofMor2 R1)).
    fold sqr in comp. apply eqrelsymm.
    intros P X. apply X. clear X P.
    use mk_RoofTop.
    - exact comp.
    - exact (identity comp).
    - exact (LocSqr2Mor2 sqr).
    - use (isLocClassComp iLC).
      + apply (isLocClassIs iLC).
      + apply (RoofMor1Is comp).
    - rewrite id_left. cbn. apply idpath.
    - rewrite id_left. cbn. apply (LocSqr2Comm sqr).
  Qed.

  Definition IdRoofEqclass (x : ob C) : RoofEqclass x x.
  Proof.
    exact (RoofEqclassFromRoof (mk_Roof x x x (identity x) (identity x) (isLocClassIs iLC x))).
  Defined.

  Definition loc_precategory_data : precategory_data :=
    precategory_data_pair
      loc_precategory_ob_mor
      (fun (x : ob C) => IdRoofEqclass x)
      (fun (x y z : ob C) (f : RoofEqclass x y) (g : RoofEqclass y z) =>
         pr1 (pr1 (roof_comp_iscontr x y z f g))).

  Lemma loc_id_left_in {x y : loc_precategory_data} (f : loc_precategory_data⟦x, y⟧)
    (R1 : Roof x y) (H1 : RoofEqclassIn f R1) :
    pr1 (identity x ;; f) (roof_comp (IdRoof x) R1).
  Proof.
    apply (pr2 (pr1 (roof_comp_iscontr x x y (IdRoofEqclass x) f))).
    - apply RoofEqclassFromRoofIn.
    - apply H1.
  Qed.

  Local Lemma loc_id_left {x y : loc_precategory_data} (f : loc_precategory_data⟦x, y⟧) :
    identity x ;; f = f.
  Proof.
    use (squash_to_prop (pr1 (RoofEqclassIs f))). apply isasetRoofEqclass. intros f'.
    induction f' as [f1 f2].
    use RoofEqclassEq.
    - intros R HR.
      set (tmp := IdRoofEqrel_left R).
      set (e1 := eqax1 (RoofEqclassIs (identity x ;; f)) _ _ tmp HR).
      (* Need to show that eqrel f1 R *)
      assert (X : RoofEqclassIn (identity x ;; f) (roof_comp (IdRoof x) f1)).
      {
        cbn.
        apply (pr2 (pr1 (roof_comp_iscontr x x y (IdRoofEqclass x) f)) (IdRoof x)).
        - apply RoofEqclassFromRoofIn.
        - apply f2.
      }
      set (e2 := eqax2 (RoofEqclassIs (identity x ;; f)) _ _ e1 X).
      set (e3 := IdRoofEqrel_left R).
      use (eqax1 (RoofEqclassIs f)).
      + exact (roof_comp (IdRoof x) f1).
      + use eqreltrans.
        * exact (roof_comp (IdRoof x) R).
        * apply eqrelsymm. apply e2.
        * apply eqrelsymm. apply e3.
      + set (e4 := IdRoofEqrel_left f1).
        use (eqax1 (RoofEqclassIs f)).
        -- exact f1.
        -- exact e4.
        -- exact f2.
    - intros R HR.
      set (tmp := IdRoofEqrel_left R).
      use (eqax1 (RoofEqclassIs (identity x ;; f))).
      + exact (roof_comp (IdRoof x) R).
      + apply eqrelsymm. apply tmp.
      + apply (pr2 (pr1 (roof_comp_iscontr x x y (IdRoofEqclass x) f))).
        * apply RoofEqclassFromRoofIn.
        * apply HR.
  Qed.

  Local Lemma loc_id_right {x y : loc_precategory_data} (f : loc_precategory_data⟦x, y⟧) :
    f ;; identity y = f.
  Proof.
    use (squash_to_prop (pr1 (RoofEqclassIs f))). apply isasetRoofEqclass. intros f'.
    induction f' as [f1 f2].
    use RoofEqclassEq.
    - intros R HR.
      set (tmp := IdRoofEqrel_right R).
      set (e1 := eqax1 (RoofEqclassIs (f ;; identity y)) _ _ tmp HR).
      (* Need to show (eqrel ...) f1 R *)
      assert (X : RoofEqclassIn (f ;; identity y) (roof_comp f1 (IdRoof y))).
      {
        cbn.
        apply (pr2 (pr1 (roof_comp_iscontr x y y f (IdRoofEqclass y)))).
        - apply f2.
        - apply RoofEqclassFromRoofIn.
      }
      set (e2 := eqax2 (RoofEqclassIs (f ;; identity y)) _ _ e1 X).
      use (eqax1 (RoofEqclassIs f)).
      + exact (roof_comp f1 (IdRoof y)).
      + use eqreltrans.
        * exact (roof_comp R (IdRoof y)).
        * apply eqrelsymm. apply e2.
        * apply eqrelsymm. apply tmp.
      + set (e4 := IdRoofEqrel_right f1).
        use (eqax1 (RoofEqclassIs f)).
        -- exact f1.
        -- exact e4.
        -- exact f2.
    - intros R HR.
      set (tmp := IdRoofEqrel_right R).
      use (eqax1 (RoofEqclassIs (f ;; identity y))).
      + exact (roof_comp R (IdRoof y)).
      + apply eqrelsymm. apply tmp.
      + apply (pr2 (pr1 (roof_comp_iscontr x y y f (IdRoofEqclass y)))).
        * apply HR.
        * apply RoofEqclassFromRoofIn.
  Qed.

  Local Definition loc_precategory_assoc_Roof (x y z w : loc_precategory_data) (R1 : Roof x y)
        (R2 : Roof y z) (R3 : Roof z w) : Roof x w.
  Proof.
    set (sqr1 := isLocClassSqr2 iLC _ _ _ (RoofMor1 R2) (RoofMor1Is R2) (RoofMor2 R1)).
    set (sqr2 := isLocClassSqr2 iLC _ _ _ (RoofMor1 R3) (RoofMor1Is R3) (RoofMor2 R2)).
    set (sqr3 := isLocClassSqr2 iLC _ _ _ (LocSqr2Mor2 sqr2) (LocSqr2Mor2Is sqr2)
                                (LocSqr2Mor1 sqr1)).
    use mk_Roof.
    - exact sqr3.
    - exact (LocSqr2Mor2 sqr3 ;; LocSqr2Mor2 sqr1 ;; RoofMor1 R1).
    - exact (LocSqr2Mor1 sqr3 ;; LocSqr2Mor1 sqr2 ;; RoofMor2 R3).
    - use (isLocClassComp iLC).
      + use (isLocClassComp iLC).
        * exact (LocSqr2Mor2Is sqr3).
        * exact (LocSqr2Mor2Is sqr1).
      + exact (RoofMor1Is R1).
  Defined.

  Local Lemma loc_precategory_assoc_eqrel1 {x y z w : loc_precategory_data} (R1 : Roof x y)
        (R2 : Roof y z) (R3 : Roof z w) :
    (eqrelpair (RoofHrel x w) (RoofEqrel x w)) (roof_comp (roof_comp R1 R2) R3)
                                               (loc_precategory_assoc_Roof x y z w R1 R2 R3).
  Proof.
    set (R4 := roof_comp R1 R2).
    set (R5 := roof_comp R2 R3).
    set (R6 := loc_precategory_assoc_Roof x y z w R1 R2 R3).
    set (R6' := roof_comp R4 R3).
    set (CR := RoofToCoroof R3).
    set (sqrop := isLocClassSqr1 iLC R3 z w (RoofMor1 R3) (RoofMor1Is R3) (RoofMor2 R3)).
    set (sqr1 := isLocClassSqr2 iLC R2 R1 y (RoofMor1 R2) (RoofMor1Is R2) (RoofMor2 R1)).
    set (sqr2 := isLocClassSqr2 iLC R3 R2 z (RoofMor1 R3) (RoofMor1Is R3) (RoofMor2 R2)).
    set (sqr3 := isLocClassSqr2 iLC sqr2 sqr1 R2 (LocSqr2Mor2 sqr2) (LocSqr2Mor2Is sqr2)
                                (LocSqr2Mor1 sqr1)).
    set (sqr4 := isLocClassSqr2 iLC R3 sqr1 z (RoofMor1 R3) (RoofMor1Is R3)
                                (LocSqr2Mor1 sqr1 ;; RoofMor2 R2)).
    set (sqr := isLocClassSqr2 iLC _ _ _ (LocSqr2Mor2 sqr3) (LocSqr2Mor2Is sqr3)
                               (LocSqr2Mor2 sqr4)).
    assert (H : LocSqr2Mor2 sqr ;; RoofMor2 R6' ;; CoroofMor2 CR =
                LocSqr2Mor1 sqr ;; RoofMor2 R6 ;; CoroofMor2 CR).
    {
      cbn. fold sqrop. fold sqr1. fold sqr2. fold sqr3. fold sqr4.
      rewrite assoc. rewrite assoc. rewrite assoc.
      rewrite <- assoc. rewrite <- (LocSqr1Comm sqrop).
      rewrite <- (assoc _ (RoofMor2 R3)). rewrite <- (LocSqr1Comm sqrop).
      rewrite assoc. rewrite assoc.
      rewrite <- (assoc _ (LocSqr2Mor1 sqr4)). rewrite (LocSqr2Comm sqr4).
      rewrite assoc. rewrite assoc.
      rewrite <- (assoc _ (LocSqr2Mor1 sqr2)). rewrite (LocSqr2Comm sqr2).
      rewrite assoc.
      apply cancel_postcomposition. apply cancel_postcomposition.
      rewrite <- (LocSqr2Comm sqr). rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition.
      apply (! (LocSqr2Comm sqr3)).
    }
    set (PostS := isLocClassPost iLC _ _ _ (LocSqr2Mor2 sqr ;; RoofMor2 R6')
                                 (LocSqr2Mor1 sqr ;;  RoofMor2 R6)
                                 (CoroofMor2 CR) (CoroofMor2Is CR) H).
    intros P X. apply X. clear X P.
    use mk_RoofTop.
    - exact (PostS).
    - exact (PostSwitchMor PostS ;; LocSqr2Mor2 sqr).
    - exact (PostSwitchMor PostS ;; LocSqr2Mor1 sqr).
    - use (isLocClassComp iLC).
      + use (isLocClassComp iLC).
        * exact (PostSwitchMorIs PostS).
        * exact (LocSqr2Mor2Is sqr).
      + exact (RoofMor1Is R6').
    - rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. cbn. fold sqr1. fold sqr2. fold sqr3. fold sqr4.
      rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
      apply cancel_postcomposition. apply cancel_postcomposition.
      exact (! (LocSqr2Comm sqr)).
    - rewrite <- assoc. rewrite <- assoc.
      exact (PostSwitchEq PostS).
  Qed.

  Local Lemma loc_precategory_assoc_eqrel2 (x y z w : loc_precategory_data) (R1 : Roof x y)
        (R2 : Roof y z) (R3 : Roof z w) :
    (eqrelpair (RoofHrel x w) (RoofEqrel x w)) (roof_comp R1 (roof_comp R2 R3))
                                               (loc_precategory_assoc_Roof x y z w R1 R2 R3).
  Proof.
    set (R4 := roof_comp R1 R2).
    set (R5 := roof_comp R2 R3).
    set (R6 := loc_precategory_assoc_Roof x y z w R1 R2 R3).
    set (R6' := roof_comp R1 R5).
    set (CR := RoofToCoroof R2).
    set (sqrop := isLocClassSqr1 iLC R2 y z (RoofMor1 R2) (RoofMor1Is R2) (RoofMor2 R2)).
    set (sqr1 := isLocClassSqr2 iLC R2 R1 y (RoofMor1 R2) (RoofMor1Is R2) (RoofMor2 R1)).
    set (sqr2 := isLocClassSqr2 iLC R3 R2 z (RoofMor1 R3) (RoofMor1Is R3) (RoofMor2 R2)).
    set (sqr3 := isLocClassSqr2 iLC sqr2 sqr1 R2 (LocSqr2Mor2 sqr2) (LocSqr2Mor2Is sqr2)
                                (LocSqr2Mor1 sqr1)).
    set (sqr4 := isLocClassSqr2 iLC sqr2 R1 y (LocSqr2Mor2 sqr2 ;; RoofMor1 R2)
                                (isLocClassComp iLC sqr2 R2 y (LocSqr2Mor2 sqr2)
                                                (LocSqr2Mor2Is sqr2)
                                                (RoofMor1 R2) (RoofMor1Is R2)) (RoofMor2 R1)).
    assert (e0 : SOM _ _ (LocSqr2Mor2 sqr3 ;; LocSqr2Mor2 sqr1)).
    {
      use (isLocClassComp iLC).
      - exact (LocSqr2Mor2Is sqr3).
      - exact (LocSqr2Mor2Is sqr1).
    }
    set (sqr := isLocClassSqr2 iLC _ _ _ (LocSqr2Mor2 sqr3 ;; LocSqr2Mor2 sqr1) e0
                               (LocSqr2Mor2 sqr4)).
    assert (e : SOM R3 CR (RoofMor1 R3 ;; CoroofMor2 CR)).
    {
      use (isLocClassComp iLC).
      - exact (RoofMor1Is R3).
      - exact (CoroofMor2Is CR).
    }
    assert (H : LocSqr2Mor2 sqr ;; LocSqr2Mor1 sqr4 ;; LocSqr2Mor1 sqr2 ;;
                            (RoofMor1 R3 ;; LocSqr1Mor2 sqrop) =
                LocSqr2Mor1 sqr ;; LocSqr2Mor1 sqr3 ;; LocSqr2Mor1 sqr2 ;;
                            (RoofMor1 R3 ;; LocSqr1Mor2 sqrop)).
    {
      rewrite assoc. rewrite assoc.
      rewrite <- (assoc _ (LocSqr2Mor1 sqr2)). rewrite (LocSqr2Comm sqr2). rewrite assoc.
      rewrite <- (assoc _ (LocSqr2Mor1 sqr2)). rewrite (LocSqr2Comm sqr2). rewrite assoc.
      rewrite <- assoc. rewrite <- (LocSqr1Comm sqrop). rewrite assoc.
      rewrite <- (assoc _ _ (LocSqr1Mor2 sqrop)). rewrite <- (LocSqr1Comm sqrop). rewrite assoc.
      apply cancel_postcomposition.
      rewrite <- (assoc _ (LocSqr2Mor1 sqr3)). rewrite (LocSqr2Comm sqr3). rewrite assoc.

      rewrite <- assoc. rewrite <- assoc. rewrite (LocSqr2Comm sqr4). rewrite assoc.
      rewrite <- (LocSqr2Comm sqr).
      rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. apply cancel_precomposition.
      apply (! (LocSqr2Comm sqr1)).
    }
    set (PostS := isLocClassPost iLC _ _ _ (LocSqr2Mor2 sqr ;; LocSqr2Mor1 sqr4 ;; LocSqr2Mor1 sqr2)
                                 (LocSqr2Mor1 sqr ;; LocSqr2Mor1 sqr3 ;; LocSqr2Mor1 sqr2)
                                 (RoofMor1 R3 ;; CoroofMor2 CR) e H).
    intros P X. apply X. clear X P.
    use mk_RoofTop.
    - exact PostS.
    - exact (PostSwitchMor PostS ;; LocSqr2Mor2 sqr).
    - exact (PostSwitchMor PostS ;; LocSqr2Mor1 sqr).
    - use (isLocClassComp iLC).
      + use (isLocClassComp iLC).
        * exact (PostSwitchMorIs PostS).
        * exact (LocSqr2Mor2Is sqr).
      + exact (RoofMor1Is R6').
    - cbn. fold sqr1. fold sqr2. fold sqr3. fold sqr4.
      rewrite <- assoc. apply pathsinv0. rewrite <- assoc. apply cancel_precomposition.
      rewrite assoc. rewrite assoc. rewrite assoc. apply cancel_postcomposition.
      rewrite <- assoc. apply (LocSqr2Comm sqr).
    - cbn. fold sqr1. fold sqr2. fold sqr3. fold sqr4.
      rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
      apply cancel_postcomposition.
      set (tmp := PostSwitchEq PostS). rewrite assoc in tmp. rewrite assoc in tmp.
      rewrite assoc in tmp. rewrite assoc in tmp.
      exact tmp.
  Qed.

  Local Lemma loc_precategory_assoc_eqrel (x y z w : loc_precategory_data) (R1 : Roof x y)
        (R2 : Roof y z) (R3 : Roof z w) :
    (eqrelpair (RoofHrel x w) (RoofEqrel x w)) (roof_comp R1 (roof_comp R2 R3))
                                               (roof_comp (roof_comp R1 R2) R3).
  Proof.
    use eqreltrans.
    - exact (loc_precategory_assoc_Roof x y z w R1 R2 R3).
    - exact (loc_precategory_assoc_eqrel2 x y z w R1 R2 R3).
    - apply eqrelsymm.
      exact (loc_precategory_assoc_eqrel1 R1 R2 R3).
  Qed.

  Local Lemma loc_precategory_assoc (a b c d : loc_precategory_data)
        (f : loc_precategory_data ⟦a, b⟧) (g : loc_precategory_data ⟦b, c⟧)
        (h : loc_precategory_data ⟦c, d⟧) : f ;; (g ;; h) = f ;; g ;; h.
  Proof.
    use (squash_to_prop (pr1 (RoofEqclassIs f))). apply isasetRoofEqclass. intros f'.
    use (squash_to_prop (pr1 (RoofEqclassIs g))). apply isasetRoofEqclass. intros g'.
    use (squash_to_prop (pr1 (RoofEqclassIs h))). apply isasetRoofEqclass. intros h'.
    induction f' as [f1 f2]. induction g' as [g1 g2]. induction h' as [h1 h2].
    use RoofEqclassEq.
    - intros R HR.
      assert (X1 : pr1 (f ;; (g ;; h)) (roof_comp f1 (roof_comp g1 h1))).
      {
        apply (pr2 (pr1 (roof_comp_iscontr a b d f (pr1 (pr1 (roof_comp_iscontr b c d g h)))))).
        - apply f2.
        - apply (pr2 (pr1 (roof_comp_iscontr b c d g h))).
          + apply g2.
          + apply h2.
      }
      assert (X2 : pr1 (f ;; g ;; h) (roof_comp (roof_comp f1 g1) h1)).
      {
        apply (pr2 (pr1 (roof_comp_iscontr a c d (pr1 (pr1 (roof_comp_iscontr a b c f g))) h))).
        - apply (pr2 (pr1 (roof_comp_iscontr a b c f g))).
          + apply f2.
          + apply g2.
        - apply h2.
      }
      set (X3 := loc_precategory_assoc_eqrel a b c d f1 g1 h1).
      use (eqax1 (RoofEqclassIs (f ;; g ;; h))).
      + exact (roof_comp f1 (roof_comp g1 h1)).
      + use (eqax2 (RoofEqclassIs (f ;; (g ;; h)))).
        * exact X1.
        * exact HR.
      + use (eqax1 (RoofEqclassIs (f ;; g ;; h))).
        * exact (roof_comp (roof_comp f1 g1) h1).
        * apply eqrelsymm. exact X3.
        * exact X2.
    - intros R HR.
      assert (X1 : pr1 (f ;; (g ;; h)) (roof_comp f1 (roof_comp g1 h1))).
      {
        apply (pr2 (pr1 (roof_comp_iscontr a b d f (pr1 (pr1 (roof_comp_iscontr b c d g h)))))).
        - apply f2.
        - apply (pr2 (pr1 (roof_comp_iscontr b c d g h))).
          + apply g2.
          + apply h2.
      }
      assert (X2 : pr1 (f ;; g ;; h) (roof_comp (roof_comp f1 g1) h1)).
      {
        apply (pr2 (pr1 (roof_comp_iscontr a c d (pr1 (pr1 (roof_comp_iscontr a b c f g))) h))).
        - apply (pr2 (pr1 (roof_comp_iscontr a b c f g))).
          + apply f2.
          + apply g2.
        - apply h2.
      }
      set (X3 := loc_precategory_assoc_eqrel a b c d f1 g1 h1).
      use (eqax1 (RoofEqclassIs (f ;; (g ;; h)))).
      + exact (roof_comp f1 (roof_comp g1 h1)).
      + use eqreltrans.
        * exact (roof_comp (roof_comp f1 g1) h1).
        * exact X3.
        * use (eqax2 (RoofEqclassIs (f ;; g ;; h))).
          -- exact X2.
          -- exact HR.
      + exact X1.
  Qed.

  Lemma is_precategory_loc_precategory_data : is_precategory loc_precategory_data.
  Proof.
    split.
    - split.
      + intros a b f.
        apply loc_id_left.
      + intros a b f.
        apply loc_id_right.
    - intros a b c d f g h.
      apply loc_precategory_assoc.
  Qed.

  (** This is the category C[S^{-1}] . I have not yet formalized the universal property. *)
  Definition loc_precategory : precategory := tpair _ _ is_precategory_loc_precategory_data.

  Lemma has_homsets_loc_precategory : has_homsets loc_precategory.
  Proof.
    intros R1 R2. apply isasetRoofEqclass.
  Qed.

End def_roofs.
