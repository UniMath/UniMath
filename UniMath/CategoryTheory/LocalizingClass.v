(** * Localizing class *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.functor_categories.

(** * Localizing class and localization of categories.
    In this section we define localization of categories when the collection of morphisms forms
    so called localizing class. The axioms of localizing class S are the following
    - every identity morphism must be in the collection
    - if f and g are in S, then so is f · g
    - Suppose we morphisms s : X --> Y and f : Z --> Y such that s in in S. Then we can find a
      square, that is morphisms, s' : W --> Z and f' : W --> X, such that s' in in S and we have
      s' · f = f' · s.
    - Dual version of the previous. Suppose s : X --> Y and f : X --> Z such that s in in S. Then
      we can find a square, that is morphisms, s' : Z --> W and f' : Y --> W, such that s' is in S
      and we have s' · f = f' · s.
    - Suppose we have a morphism s : X --> Y contained in S and two morphisms f g : Y --> Z such
      that s · f = s · g. Then S contains a morphism s' such that f · s' = f · s'.
    - Dual of the above. Suppose we have a morphism s : Z --> W in S and two morphisms
      f g : Y --> Z such that f · s = g · s. Then we can find a morphism s' in S such that
      s' · f = s' · g.
*)

Section def_roofs.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Definition SubsetsOfMors : UU := ∏ (x y : ob C), hsubtype (hSetpair (C⟦x, y⟧) (hs x y)).

  (** ** Localizing classes *)

  (** *** Identities and compositions are in the subset of morphisms *)
  Definition isLocalizingClass1 (SOM : SubsetsOfMors) : UU :=
    (∏ (x : ob C), SOM x x (identity x))
      × (∏ (x y z : ob C) (f : x --> y) (e1 : SOM x y f) (g : y --> z) (e2 : SOM y z g),
         SOM x z (f · g)).

  Definition isLocClassIs {SOM : SubsetsOfMors} (H : isLocalizingClass1 SOM) :
    ∏ (x : ob C), SOM x x (identity x) := pr1 H.

  Definition isLocClassComp {SOM : SubsetsOfMors} (H : isLocalizingClass1 SOM) :
    ∏ (x y z : ob C) (f : x --> y) (e1 : SOM x y f) (g : y --> z) (e2 : SOM y z g),
    SOM x z (f · g) := pr2 H.

  (** **** Squares *)
  Definition LocSqr1 (SOM : SubsetsOfMors) {x y z : ob C} (s : x --> y) (e1 : SOM x y s)
             (f : x --> z) : UU :=
    ∑ D : (∑ (w : ob C), C⟦y, w⟧ × C⟦z, w⟧),
          (SOM z (pr1 D) (dirprod_pr2 (pr2 D)))
            × (s · (dirprod_pr1 (pr2 D)) = f · (dirprod_pr2 (pr2 D))).

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
    s · (LocSqr1Mor1 LS1) = f · (LocSqr1Mor2 LS1) := dirprod_pr2 (pr2 LS1).

  Definition LocSqr2 (SOM : SubsetsOfMors) {y z w : ob C} (s : y --> w) (e1 : SOM y w s)
             (f : z --> w) : UU :=
    ∑ D : (∑ (x : ob C), C⟦x, y⟧ × C⟦x, z⟧),
          (SOM (pr1 D) z (dirprod_pr2 (pr2 D)))
            × ((dirprod_pr1 (pr2 D)) · s = (dirprod_pr2 (pr2 D)) · f).

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
    (LocSqr2Mor1 LS2) · s = (LocSqr2Mor2 LS2) · f := dirprod_pr2 (pr2 LS2).

  (** *** Completion to squares *)
  Definition isLocalizingClass2 (SOM : SubsetsOfMors) : UU :=
    (∏ (x y z : ob C) (s : x --> y) (e1 : SOM x y s) (f : x --> z), (LocSqr1 SOM s e1 f))
      × (∏ (y z w : ob C) (s : y --> w) (e1 : SOM y w s) (f : z --> w), (LocSqr2 SOM s e1 f)).

  Definition isLocClassSqr1 {SOM : SubsetsOfMors} (H : isLocalizingClass2 SOM) :
    ∏ (x y z : ob C) (s : x --> y) (e1 : SOM x y s) (f : x --> z), LocSqr1 SOM s e1 f :=
    dirprod_pr1 H.

  Definition isLocClassSqr2 {SOM : SubsetsOfMors} (H : isLocalizingClass2 SOM) :
    ∏ (y z w : ob C) (s : y --> w) (e1 : SOM y w s) (f : z --> w), LocSqr2 SOM s e1 f :=
    dirprod_pr2 H.

  (** **** Pre- and post switch *)
  Definition PreSwitch (SOM : SubsetsOfMors) {x y z : ob C} (s : x --> y) (e : SOM x y s)
             (f g : y --> z) (H : s · f = s · g) : UU :=
    ∑ D : (∑ (w : ob C), C⟦z, w⟧), (SOM z (pr1 D) (pr2 D)) × (f · (pr2 D) = g · (pr2 D)).

  Definition PreSwitchOb {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e : SOM x y s}
             {f g : y --> z} {H : s · f = s · g} (PreS : PreSwitch SOM s e f g H) : ob C :=
    pr1 (pr1 PreS).
  Coercion PreSwitchOb : PreSwitch >-> ob.

  Definition PreSwitchMor {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e : SOM x y s}
             {f g : y --> z} {H : s · f = s · g} (PreS : PreSwitch SOM s e f g H) :
    C⟦z, PreS⟧ := pr2 (pr1 PreS).

  Definition PreSwitchMorIs {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e : SOM x y s}
             {f g : y --> z} {H : s · f = s · g} (PreS : PreSwitch SOM s e f g H) :
    SOM z PreS (PreSwitchMor PreS) := dirprod_pr1 (pr2 PreS).

  Definition PreSwitchEq {SOM : SubsetsOfMors} {x y z : ob C} {s : x --> y} {e : SOM x y s}
             {f g : y --> z} {H : s · f = s · g} (PreS : PreSwitch SOM s e f g H) :
    f · (PreSwitchMor PreS) = g · (PreSwitchMor PreS) := dirprod_pr2 (pr2 PreS).

  (** **** Post switch *)

  Definition PostSwitch (SOM : SubsetsOfMors) {y z w : ob C} (f g : y --> z) (s : z --> w)
             (e : SOM z w s) (H : f · s = g · s) : UU :=
    ∑ D : (∑ (x : ob C), C⟦x, y⟧), (SOM (pr1 D) y (pr2 D)) × ((pr2 D) · f = (pr2 D) · g).

  Definition PostSwitchOb {SOM : SubsetsOfMors} {y z w : ob C} {f g : y --> z} {s : z --> w}
             {e : SOM z w s} {H : f · s = g · s} (PostS : PostSwitch SOM f g s e H) : ob C :=
    pr1 (pr1 PostS).
  Coercion PostSwitchOb : PostSwitch >-> ob.

  Definition PostSwitchMor {SOM : SubsetsOfMors} {y z w : ob C} {f g : y --> z} {s : z --> w}
             {e : SOM z w s} {H : f · s = g · s} (PostS : PostSwitch SOM f g s e H) :
    C⟦PostS, y⟧ := pr2 (pr1 PostS).

  Definition PostSwitchMorIs {SOM : SubsetsOfMors} {y z w : ob C} {f g : y --> z} {s : z --> w}
             {e : SOM z w s} {H : f · s = g · s} (PostS : PostSwitch SOM f g s e H) :
    SOM PostS y (PostSwitchMor PostS) := dirprod_pr1 (pr2 PostS).

  Definition PostSwitchEq {SOM : SubsetsOfMors} {y z w : ob C} {f g : y --> z} {s : z --> w}
             {e : SOM z w s} {H : f · s = g · s} (PostS : PostSwitch SOM f g s e H) :
    (PostSwitchMor PostS) · f = (PostSwitchMor PostS) · g := dirprod_pr2 (pr2 PostS).

  (** *** Pre- and postcomposition with morphisms in the subset *)
  Definition isLocalizingClass3 (SOM : SubsetsOfMors) : UU :=
    (∏ (x y z : ob C) (s : x --> y) (e : SOM x y s) (f g : y --> z) (H : s · f = s · g),
     PreSwitch SOM s e f g H)
      × (∏ (y z w : ob C) (f g : y --> z) (s : z --> w) (e : SOM z w s) (H : f · s = g · s),
         PostSwitch SOM f g s e H).

  Definition isLocClassPre {SOM : SubsetsOfMors} (H : isLocalizingClass3 SOM) :
    ∏ (x y z : ob C) (s : x --> y) (e : SOM x y s) (f g : y --> z) (H : s · f = s · g),
    PreSwitch SOM s e f g H := dirprod_pr1 H.

  Definition isLocClassPost {SOM : SubsetsOfMors} (H : isLocalizingClass3 SOM) :
    ∏ (y z w : ob C) (f g : y --> z) (s : z --> w) (e : SOM z w s) (H : f · s = g · s),
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
    ∑ D : (∑ z : ob C, C⟦z, x⟧ × C⟦z, y⟧), (SOM (pr1 D) x (dirprod_pr1 (pr2 D))).

  Definition mk_Roof (x y z : ob C) (s : z --> x) (f : z --> y) (e : SOM z x s) : Roof x y :=
    tpair _ (tpair _ z (s,,f)) e.

  Definition RoofOb {x y : ob C} (R : Roof x y) : ob C := pr1 (pr1 R).
  Coercion RoofOb : Roof >-> ob.

  Definition RoofMor1 {x y : ob C} (R : Roof x y) : C⟦R, x⟧ := dirprod_pr1 (pr2 (pr1 R)).

  Definition RoofMor1Is {x y : ob C} (R : Roof x y) : SOM R x (RoofMor1 R) := pr2 R.

  Definition RoofMor2 {x y : ob C} (R : Roof x y) : C⟦R, y⟧ := dirprod_pr2 (pr2 (pr1 R)).

  (** ** Coroofs *)
  Definition Coroof (x y : ob C) : UU :=
    ∑ D : (∑ z : ob C, C⟦x, z⟧ × C⟦y, z⟧), (SOM y (pr1 D) (dirprod_pr2 (pr2 D))).

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
    ∑ D : (∑ w : ob C, C⟦w, R1⟧ × C⟦w, R2⟧),
          (SOM (pr1 D) x ((dirprod_pr1 (pr2 D)) · (RoofMor1 R1)))
            × ((dirprod_pr1 (pr2 D)) · (RoofMor1 R1) = (dirprod_pr2 (pr2 D)) · (RoofMor1 R2))
            × ((dirprod_pr1 (pr2 D)) · (RoofMor2 R1) = (dirprod_pr2 (pr2 D)) · (RoofMor2 R2)).

  Definition mk_RoofTop {x y : ob C} {R1 R2 : Roof x y} (w : ob C) (s : w --> R1) (f : w --> R2)
             (e : SOM w x (s · RoofMor1 R1))
             (H1 : s · (RoofMor1 R1) = f · (RoofMor1 R2))
             (H2 : s · (RoofMor2 R1) = f · (RoofMor2 R2)) : RoofTop R1 R2 :=
    tpair _ (tpair _ w (s,,f)) (e,,(H1,,H2)).

  Definition RoofTopOb {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) : ob C := pr1 (pr1 T).
  Coercion RoofTopOb : RoofTop >-> ob.

  Definition RoofTopMor1 {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) : C⟦T, R1⟧ :=
    dirprod_pr1 (pr2 (pr1 T)).

  Definition RoofTopMor1Is {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) :
    (SOM T x ((RoofTopMor1 T) · (RoofMor1 R1))) := (dirprod_pr1 (pr2 T)).

  Definition RoofTopMor2 {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) : C⟦T, R2⟧ :=
    dirprod_pr2 (pr2 (pr1 T)).

  Definition RoofTopEq1 {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) :
    (RoofTopMor1 T) · (RoofMor1 R1) = (RoofTopMor2 T) · (RoofMor1 R2) :=
    dirprod_pr1 (dirprod_pr2 (pr2 T)).

  Definition RoofTopEq2 {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) :
    (RoofTopMor1 T) · (RoofMor2 R1) = (RoofTopMor2 T) · (RoofMor2 R2) :=
    dirprod_pr2 (dirprod_pr2 (pr2 T)).

  (** We define an equivalence relation between the roofs *)
  Definition RoofHrel' {x y : ob C} (R1 R2 : Roof x y) : hProp := ishinh (RoofTop R1 R2).

  Definition RoofHrel (x y : ob C) : hrel (Roof x y) :=
    (λ R1 : Roof x y, λ R2 : Roof x y, RoofHrel' R1 R2).

  Lemma RoofEqrel (x y : ob C) : iseqrel (RoofHrel x y).
  Proof.
    use iseqrelconstr.
    (* is trans *)
    - intros R1 R2 R3 T1' T2'.
      use (squash_to_prop T1'). apply isapropishinh. intros T1. clear T1'.
      use (squash_to_prop T2'). apply isapropishinh. intros T2. clear T2'.
      set (tmp := isLocClassSqr2 iLC T2 T1 x (RoofTopMor1 T2 · RoofMor1 R2) (RoofTopMor1Is T2)
                                 (RoofTopMor2 T1 · RoofMor1 R2)).
      induction tmp as [D1 D2]. induction D1 as [w m]. induction m as [m1 m2].
      induction D2 as [D1 D2]. cbn in D1, D2. repeat rewrite assoc in D2.
      set (tmp := isLocClassPost iLC w R2 x (m1 · RoofTopMor1 T2) (m2 · RoofTopMor2 T1)
                                 (RoofMor1 R2) (RoofMor1Is R2) D2).
      induction tmp as [t p].
      intros P X. apply X. clear X P.
      use mk_RoofTop.
      + exact (pr1 t).
      + exact ((pr2 t) · m2 · RoofTopMor1 T1).
      + exact ((pr2 t) · m1 · RoofTopMor2 T2).
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
  (* Definition eqclass {X : UU} {r : eqrel X} : UU := ∑ A : hsubtype X, iseqclass r A. *)

  Definition RoofEqclass (x y : ob C) : UU :=
    ∑ A : hsubtype (Roof x y), iseqclass (eqrelpair _ (RoofEqrel x y)) A.

  Lemma isasetRoofEqclass (x y : ob C) : isaset (RoofEqclass x y).
  Proof.
    apply isaset_total2.
    - apply isasethsubtype.
    - intros x0.
      apply isasetaprop.
      apply isapropiseqclass.
  Defined.

  Definition mk_RoofEqclass {x y : ob C} (A : hsubtype (Roof x y))
             (H : iseqclass (eqrelpair _ (RoofEqrel x y)) A) : RoofEqclass x y := tpair _ A H.

  Definition RoofEqclassIn {x y : ob C} (RE : RoofEqclass x y) : hsubtype (Roof x y) := pr1 RE.

  Definition RoofEqclassIs {x y : ob C} (RE : RoofEqclass x y) :
    iseqclass (eqrelpair _ (RoofEqrel x y)) (RoofEqclassIn RE) := pr2 RE.

  Definition RoofEqclassEq {x y : ob C} (RE1 RE2 : RoofEqclass x y)
             (H1 : ∏ (R : Roof x y) (H : (pr1 RE1) R), (pr1 RE2) R)
             (H2 : ∏ (R : Roof x y) (H : (pr1 RE2) R), (pr1 RE1) R) : RE1 = RE2.
  Proof.
    use total2_paths_f.
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
    - exact (λ RR : Roof x y, (eqrelpair _ (RoofEqrel x y)) RR R).
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

  Definition RoofEqclassEqRoof {x y : ob C} (RE : RoofEqclass x y)
             (R : Roof x y) (HR : RoofEqclassIn RE R) : RE = RoofEqclassFromRoof R.
  Proof.
    use RoofEqclassEq.
    - intros R0 HR0.
      use (eqax1 (RoofEqclassIs (RoofEqclassFromRoof R))).
      + exact R.
      + use (eqax2 (RoofEqclassIs RE)).
        * exact HR.
        * exact HR0.
      + apply RoofEqclassFromRoofIn.
    - intros R0 HR0.
      use (eqax1 (RoofEqclassIs RE)).
      + exact R.
      + use (eqax2 (RoofEqclassIs (RoofEqclassFromRoof R))).
        * apply RoofEqclassFromRoofIn.
        * exact HR0.
      + exact HR.
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
    - exact ((LocSqr2Mor2 LS2) · (RoofMor1 R1)).
    - exact ((LocSqr2Mor1 LS2) · (RoofMor2 R2)).
    - use (isLocClassComp iLC).
      + exact (LocSqr2Mor2Is LS2).
      + exact (RoofMor1Is R1).
  Defined.


  (** ** Composition of roofs *)

  (** Construct a "commutative coroof" from RoofTop *)
  Definition RoofTopToCoroof {x y : ob C} {R1 R2 : Roof x y} (T : RoofTop R1 R2) :
    ∑ CR : Coroof x y, (RoofMor1 R1 · CoroofMor1 CR = RoofMor2 R1 · CoroofMor2 CR)
                         × (RoofMor1 R2 · CoroofMor1 CR = RoofMor2 R2 · CoroofMor2 CR).
  Proof.
    set (sqr1 := isLocClassSqr1 iLC _ _ _ (RoofMor1 R1) (RoofMor1Is R1) (RoofMor2 R1)).
    set (sqr2 := isLocClassSqr1 iLC _ _ _ (RoofMor1 R2) (RoofMor1Is R2) (RoofMor2 R2)).
    set (sqr3 := isLocClassSqr1 iLC _ _ _ (LocSqr1Mor2 sqr1) (LocSqr1Mor2Is sqr1)
                                (LocSqr1Mor2 sqr2)).
    set (mor1 := RoofTopMor1 T · RoofMor1 R1 · LocSqr1Mor1 sqr1 · LocSqr1Mor1 sqr3).
    set (mor2 := RoofTopMor1 T · RoofMor1 R1 · LocSqr1Mor1 sqr2 · LocSqr1Mor2 sqr3).

    assert (H : RoofTopMor1 T · RoofMor1 R1 · (LocSqr1Mor1 sqr1 · LocSqr1Mor1 sqr3)
                = RoofTopMor1 T · RoofMor1 R1 · (LocSqr1Mor1 sqr2 · LocSqr1Mor2 sqr3)).
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
    set (PreS := isLocClassPre iLC _ _ _ (RoofTopMor1 T · RoofMor1 R1) (RoofTopMor1Is T)
                               (LocSqr1Mor1 sqr1 · LocSqr1Mor1 sqr3)
                               (LocSqr1Mor1 sqr2 · LocSqr1Mor2 sqr3) H).
    use tpair.
    - use mk_Coroof.
      + exact PreS.
      + exact (LocSqr1Mor1 sqr1 · LocSqr1Mor1 sqr3 · PreSwitchMor PreS).
      + exact (LocSqr1Mor2 sqr2 · LocSqr1Mor2 sqr3 · PreSwitchMor PreS).
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
    set (sqr6 := isLocClassSqr2 iLC R5 R4 x (LocSqr2Mor2 sqr5 · RoofMor1 R2) (RoofMor1Is R5)
                                (LocSqr2Mor2 sqr4 · RoofMor1 R1)).
    assert (s : SOM R3 CR (RoofMor1 R3 · CoroofMor2 CR)).
    {
      use (isLocClassComp iLC).
      - exact (RoofMor1Is R3).
      - exact (CoroofMor2Is CR).
    }
    assert (H : LocSqr2Mor1 sqr6 · LocSqr2Mor1 sqr5 · (RoofMor1 R3 · CoroofMor2 CR) =
                LocSqr2Mor2 sqr6 · LocSqr2Mor1 sqr4 · (RoofMor1 R3 · CoroofMor2 CR)).
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
                                 (LocSqr2Mor1 sqr6 · LocSqr2Mor1 sqr5)
                                 (LocSqr2Mor2 sqr6 · LocSqr2Mor1 sqr4)
                                 (RoofMor1 R3 · CoroofMor2 CR) s H).
    use mk_RoofTop.
    - exact PostS.
    - exact (PostSwitchMor PostS · LocSqr2Mor2 sqr6).
    - exact (PostSwitchMor PostS · LocSqr2Mor1 sqr6).
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
      apply (maponpaths (λ f : _, f · RoofMor2 R3)) in tmp.
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
    assert (H : LocSqr2Mor1 sqr6 · LocSqr2Mor1 sqr5 · RoofMor2 R3 · CoroofMor2 CR =
                LocSqr2Mor2 sqr6 · LocSqr2Mor1 sqr4 · RoofMor2 R2 · CoroofMor2 CR).
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
                               (LocSqr2Mor1 sqr6 · LocSqr2Mor1 sqr5 · RoofMor2 R3)
                               (LocSqr2Mor2 sqr6 · LocSqr2Mor1 sqr4 · RoofMor2 R2)
                               (CoroofMor2 CR) (CoroofMor2Is CR) H).
    use mk_RoofTop.
    - exact PostS.
    - exact (PostSwitchMor PostS · LocSqr2Mor2 sqr6).
    - exact (PostSwitchMor PostS · LocSqr2Mor1 sqr6).
    - use (isLocClassComp iLC).
      + use (isLocClassComp iLC).
        * exact (PostSwitchMorIs PostS).
        * exact (LocSqr2Mor2Is sqr6).
      + exact (RoofMor1Is R4).
    - cbn. rewrite assoc. rewrite assoc. apply cancel_postcomposition.
      set (tmp := ! (LocSqr2Comm sqr6)).
      apply (maponpaths (λ f : _, PostSwitchMor PostS · f)) in tmp.
      rewrite assoc in tmp. rewrite assoc in tmp. apply tmp.
    - cbn. apply pathsinv0.
      rewrite assoc. rewrite assoc.
      set (tmp := PostSwitchEq PostS).
      rewrite assoc in tmp. rewrite assoc in tmp. rewrite assoc in tmp. rewrite assoc in tmp.
      apply tmp.
  Qed.

  Lemma roof_comp_iscontr (x y z : ob C) (e1 : RoofEqclass x y) (e2 : RoofEqclass y z) :
    iscontr (∑ e3 : RoofEqclass x z,
                    ∏ (f : Roof x y) (s1 : (RoofEqclassIn e1) f)
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
        * exact (λ RR : (Roof x z), (eqrelpair _ (RoofEqrel x z)) RR (roof_comp R1 R2)).
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
      use total2_paths_f.
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
    tpair (λ ob : UU, ob -> ob -> UU) (ob C) (λ x y : ob C, RoofEqclass x y).

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
      (λ (x : ob C), IdRoofEqclass x)
      (fun (x y z : ob C) (f : RoofEqclass x y) (g : RoofEqclass y z) =>
         pr1 (pr1 (roof_comp_iscontr x y z f g))).

  Lemma loc_id_left_in {x y : loc_precategory_data} (f : loc_precategory_data⟦x, y⟧)
    (R1 : Roof x y) (H1 : RoofEqclassIn f R1) :
    pr1 (identity x · f) (roof_comp (IdRoof x) R1).
  Proof.
    apply (pr2 (pr1 (roof_comp_iscontr x x y (IdRoofEqclass x) f))).
    - apply RoofEqclassFromRoofIn.
    - apply H1.
  Qed.

  Local Lemma loc_id_left {x y : loc_precategory_data} (f : loc_precategory_data⟦x, y⟧) :
    identity x · f = f.
  Proof.
    use (squash_to_prop (pr1 (RoofEqclassIs f))). apply isasetRoofEqclass. intros f'.
    induction f' as [f1 f2].
    use RoofEqclassEq.
    - intros R HR.
      set (tmp := IdRoofEqrel_left R).
      set (e1 := eqax1 (RoofEqclassIs (identity x · f)) _ _ tmp HR).
      (* Need to show that eqrel f1 R *)
      assert (X : RoofEqclassIn (identity x · f) (roof_comp (IdRoof x) f1)).
      {
        cbn.
        apply (pr2 (pr1 (roof_comp_iscontr x x y (IdRoofEqclass x) f)) (IdRoof x)).
        - apply RoofEqclassFromRoofIn.
        - apply f2.
      }
      set (e2 := eqax2 (RoofEqclassIs (identity x · f)) _ _ e1 X).
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
      use (eqax1 (RoofEqclassIs (identity x · f))).
      + exact (roof_comp (IdRoof x) R).
      + apply eqrelsymm. apply tmp.
      + apply (pr2 (pr1 (roof_comp_iscontr x x y (IdRoofEqclass x) f))).
        * apply RoofEqclassFromRoofIn.
        * apply HR.
  Qed.

  Local Lemma loc_id_right {x y : loc_precategory_data} (f : loc_precategory_data⟦x, y⟧) :
    f · identity y = f.
  Proof.
    use (squash_to_prop (pr1 (RoofEqclassIs f))). apply isasetRoofEqclass. intros f'.
    induction f' as [f1 f2].
    use RoofEqclassEq.
    - intros R HR.
      set (tmp := IdRoofEqrel_right R).
      set (e1 := eqax1 (RoofEqclassIs (f · identity y)) _ _ tmp HR).
      (* Need to show (eqrel ...) f1 R *)
      assert (X : RoofEqclassIn (f · identity y) (roof_comp f1 (IdRoof y))).
      {
        cbn.
        apply (pr2 (pr1 (roof_comp_iscontr x y y f (IdRoofEqclass y)))).
        - apply f2.
        - apply RoofEqclassFromRoofIn.
      }
      set (e2 := eqax2 (RoofEqclassIs (f · identity y)) _ _ e1 X).
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
      use (eqax1 (RoofEqclassIs (f · identity y))).
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
    - exact (LocSqr2Mor2 sqr3 · LocSqr2Mor2 sqr1 · RoofMor1 R1).
    - exact (LocSqr2Mor1 sqr3 · LocSqr2Mor1 sqr2 · RoofMor2 R3).
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
                                (LocSqr2Mor1 sqr1 · RoofMor2 R2)).
    set (sqr := isLocClassSqr2 iLC _ _ _ (LocSqr2Mor2 sqr3) (LocSqr2Mor2Is sqr3)
                               (LocSqr2Mor2 sqr4)).
    assert (H : LocSqr2Mor2 sqr · RoofMor2 R6' · CoroofMor2 CR =
                LocSqr2Mor1 sqr · RoofMor2 R6 · CoroofMor2 CR).
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
    set (PostS := isLocClassPost iLC _ _ _ (LocSqr2Mor2 sqr · RoofMor2 R6')
                                 (LocSqr2Mor1 sqr ·  RoofMor2 R6)
                                 (CoroofMor2 CR) (CoroofMor2Is CR) H).
    intros P X. apply X. clear X P.
    use mk_RoofTop.
    - exact (PostS).
    - exact (PostSwitchMor PostS · LocSqr2Mor2 sqr).
    - exact (PostSwitchMor PostS · LocSqr2Mor1 sqr).
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
    set (sqr4 := isLocClassSqr2 iLC sqr2 R1 y (LocSqr2Mor2 sqr2 · RoofMor1 R2)
                                (isLocClassComp iLC sqr2 R2 y (LocSqr2Mor2 sqr2)
                                                (LocSqr2Mor2Is sqr2)
                                                (RoofMor1 R2) (RoofMor1Is R2)) (RoofMor2 R1)).
    assert (e0 : SOM _ _ (LocSqr2Mor2 sqr3 · LocSqr2Mor2 sqr1)).
    {
      use (isLocClassComp iLC).
      - exact (LocSqr2Mor2Is sqr3).
      - exact (LocSqr2Mor2Is sqr1).
    }
    set (sqr := isLocClassSqr2 iLC _ _ _ (LocSqr2Mor2 sqr3 · LocSqr2Mor2 sqr1) e0
                               (LocSqr2Mor2 sqr4)).
    assert (e : SOM R3 CR (RoofMor1 R3 · CoroofMor2 CR)).
    {
      use (isLocClassComp iLC).
      - exact (RoofMor1Is R3).
      - exact (CoroofMor2Is CR).
    }
    assert (H : LocSqr2Mor2 sqr · LocSqr2Mor1 sqr4 · LocSqr2Mor1 sqr2 ·
                            (RoofMor1 R3 · LocSqr1Mor2 sqrop) =
                LocSqr2Mor1 sqr · LocSqr2Mor1 sqr3 · LocSqr2Mor1 sqr2 ·
                            (RoofMor1 R3 · LocSqr1Mor2 sqrop)).
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
    set (PostS := isLocClassPost iLC _ _ _ (LocSqr2Mor2 sqr · LocSqr2Mor1 sqr4 · LocSqr2Mor1 sqr2)
                                 (LocSqr2Mor1 sqr · LocSqr2Mor1 sqr3 · LocSqr2Mor1 sqr2)
                                 (RoofMor1 R3 · CoroofMor2 CR) e H).
    intros P X. apply X. clear X P.
    use mk_RoofTop.
    - exact PostS.
    - exact (PostSwitchMor PostS · LocSqr2Mor2 sqr).
    - exact (PostSwitchMor PostS · LocSqr2Mor1 sqr).
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
        (h : loc_precategory_data ⟦c, d⟧) : f · (g · h) = f · g · h.
  Proof.
    use (squash_to_prop (pr1 (RoofEqclassIs f))). apply isasetRoofEqclass. intros f'.
    use (squash_to_prop (pr1 (RoofEqclassIs g))). apply isasetRoofEqclass. intros g'.
    use (squash_to_prop (pr1 (RoofEqclassIs h))). apply isasetRoofEqclass. intros h'.
    induction f' as [f1 f2]. induction g' as [g1 g2]. induction h' as [h1 h2].
    use RoofEqclassEq.
    - intros R HR.
      assert (X1 : pr1 (f · (g · h)) (roof_comp f1 (roof_comp g1 h1))).
      {
        apply (pr2 (pr1 (roof_comp_iscontr a b d f (pr1 (pr1 (roof_comp_iscontr b c d g h)))))).
        - apply f2.
        - apply (pr2 (pr1 (roof_comp_iscontr b c d g h))).
          + apply g2.
          + apply h2.
      }
      assert (X2 : pr1 (f · g · h) (roof_comp (roof_comp f1 g1) h1)).
      {
        apply (pr2 (pr1 (roof_comp_iscontr a c d (pr1 (pr1 (roof_comp_iscontr a b c f g))) h))).
        - apply (pr2 (pr1 (roof_comp_iscontr a b c f g))).
          + apply f2.
          + apply g2.
        - apply h2.
      }
      set (X3 := loc_precategory_assoc_eqrel a b c d f1 g1 h1).
      use (eqax1 (RoofEqclassIs (f · g · h))).
      + exact (roof_comp f1 (roof_comp g1 h1)).
      + use (eqax2 (RoofEqclassIs (f · (g · h)))).
        * exact X1.
        * exact HR.
      + use (eqax1 (RoofEqclassIs (f · g · h))).
        * exact (roof_comp (roof_comp f1 g1) h1).
        * apply eqrelsymm. exact X3.
        * exact X2.
    - intros R HR.
      assert (X1 : pr1 (f · (g · h)) (roof_comp f1 (roof_comp g1 h1))).
      {
        apply (pr2 (pr1 (roof_comp_iscontr a b d f (pr1 (pr1 (roof_comp_iscontr b c d g h)))))).
        - apply f2.
        - apply (pr2 (pr1 (roof_comp_iscontr b c d g h))).
          + apply g2.
          + apply h2.
      }
      assert (X2 : pr1 (f · g · h) (roof_comp (roof_comp f1 g1) h1)).
      {
        apply (pr2 (pr1 (roof_comp_iscontr a c d (pr1 (pr1 (roof_comp_iscontr a b c f g))) h))).
        - apply (pr2 (pr1 (roof_comp_iscontr a b c f g))).
          + apply f2.
          + apply g2.
        - apply h2.
      }
      set (X3 := loc_precategory_assoc_eqrel a b c d f1 g1 h1).
      use (eqax1 (RoofEqclassIs (f · (g · h)))).
      + exact (roof_comp f1 (roof_comp g1 h1)).
      + use eqreltrans.
        * exact (roof_comp (roof_comp f1 g1) h1).
        * exact X3.
        * use (eqax2 (RoofEqclassIs (f · g · h))).
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

  (** The category of roofs under the correct equivalence relation *)
  Definition loc_precategory : precategory := tpair _ _ is_precategory_loc_precategory_data.

  (** In particular, loc_precategory has homsets. *)
  Lemma has_homsets_loc_precategory : has_homsets loc_precategory.
  Proof.
    intros R1 R2. apply isasetRoofEqclass.
  Qed.


  (** ** Universal property *)
  (** We verify that loc_precategory satisfies the universal property required for localization
      of categories. Universal property: Suppose F : C -> D is a functor which maps the
      morphisms in SOM to isomorphisms in D. Then there exists a unique functor H : loc_precategory
      -> D such that functor_composite [FunctorToLocalization] H = F, where FunctorToLocalization
      is the natural inclusion functor C -> loc_precategory.

      The unique functor H is constructed in [LocalizationUniversalFunctor], commutativity is
      proved in [LocalizationUniversalFunctorComm], and uniqueness of the functor is proved in
      [LocalizationUniversalFunctorUnique]. In case the objects of D satisfy isaset, then we also
      show that commutativity is unique. This means that the type
      "functor_composite [FunctorToLocalization] H = F" has only one term.
   *)

  (** Maps a morphism to roofs *)
  Definition MorToRoof {x y : ob C} (f : x --> y) : Roof x y.
  Proof.
    use mk_Roof.
    - exact x.
    - exact (identity x).
    - exact f.
    - exact (isLocClassIs iLC x).
  Defined.

  (** MorToRoof is linear with respect to composition in C. *)
  Lemma MorphismCompEqrel {x y z : ob C} (f : x --> y) (g : y --> z) :
    (eqrelpair _ (RoofEqrel x z)) (MorToRoof (f · g)) (roof_comp (MorToRoof f) (MorToRoof g)).
  Proof.
    set (Rf := MorToRoof f).
    set (Rg := MorToRoof g).
    set (Rfg := MorToRoof (f · g)).
    unfold roof_comp.
    set (sqr1 := isLocClassSqr2 iLC Rg Rf y (RoofMor1 Rg) (RoofMor1Is Rg) (RoofMor2 Rf)).
    set (CR := RoofToCoroof (MorToRoof g)).
    set (sqrop := isLocClassSqr1 iLC y y z (identity y) (isLocClassIs iLC y) g).
    assert (H : LocSqr2Mor1 sqr1 · RoofMor2 Rg · CoroofMor2 CR =
                LocSqr2Mor2 sqr1 · f · g · CoroofMor2 CR).
    {
      cbn. fold sqrop.
      rewrite <- assoc. rewrite <- (LocSqr1Comm sqrop). rewrite id_left.
      rewrite <- assoc. rewrite <- (LocSqr1Comm sqrop). rewrite id_left.
      apply cancel_postcomposition.
      set (tmp := LocSqr2Comm sqr1). cbn in tmp. rewrite id_right in tmp.
      exact tmp.
    }
    set (PostS := isLocClassPost iLC _ _ _ (LocSqr2Mor1 sqr1 · RoofMor2 Rg)
                                 (LocSqr2Mor2 sqr1 · f · g)
                                 (CoroofMor2 CR) (CoroofMor2Is CR) H).
    intros P X. apply X. clear X P.
    use mk_RoofTop.
    - exact PostS.
    - exact (PostSwitchMor PostS · (LocSqr2Mor2 sqr1)).
    - exact (PostSwitchMor PostS).
    - use (isLocClassComp iLC).
      + use (isLocClassComp iLC).
        * exact (PostSwitchMorIs PostS).
        * exact (LocSqr2Mor2Is sqr1).
      + exact (RoofMor1Is Rfg).
    - cbn. rewrite assoc. apply idpath.
    - cbn.
      set (tmp := PostSwitchEq PostS). cbn in tmp.
      rewrite assoc in tmp. rewrite assoc in tmp. rewrite assoc in tmp.
      rewrite assoc. rewrite assoc.
      exact (! (tmp)).
  Qed.

  (** This is used to show that the natural inclusion functor C --> loc_precategory
      respects composition. See [FunctorToLocalization]. *)
  Lemma FunctorToLocalization_comp {x y z : ob C} (f : x --> y) (g : y --> z) :
    RoofEqclassFromRoof (MorToRoof (f · g)) =
    pr1 (pr1 (roof_comp_iscontr x y z (RoofEqclassFromRoof (MorToRoof f))
                                (RoofEqclassFromRoof (MorToRoof g)))).
  Proof.
    set (tmpp := roof_comp_iscontr_in x y z (MorToRoof f) (MorToRoof g)).
    set (eqclass := pr1 (pr1 (roof_comp_iscontr x y z (RoofEqclassFromRoof (MorToRoof f))
                                                (RoofEqclassFromRoof (MorToRoof g))))).
    fold eqclass in tmpp.
    set (cont := pr1 (roof_comp_iscontr x y z (RoofEqclassFromRoof (MorToRoof f))
                                        (RoofEqclassFromRoof (MorToRoof g)))).
    set (cont' := pr2 cont). cbn in cont, cont'.
    use RoofEqclassEq.
    - intros R HR.
      unfold RoofEqclassIn in tmpp.
      use (eqax1 (RoofEqclassIs eqclass)).
      + exact (roof_comp (MorToRoof f) (MorToRoof g)).
      + use eqreltrans.
        * exact (MorToRoof (f · g)).
        * apply eqrelsymm. apply MorphismCompEqrel.
        * set (HR' := RoofEqclassFromRoofIn (MorToRoof (f · g))).
          use (eqax2 (RoofEqclassIs (RoofEqclassFromRoof (MorToRoof (f · g))))).
          -- exact HR'.
          -- exact HR.
      + exact tmpp.
    - intros R HR.
      use (eqax1 (RoofEqclassIs (RoofEqclassFromRoof (MorToRoof (f · g))))).
      + exact (MorToRoof (f · g)).
      + use eqreltrans.
        * exact (roof_comp (MorToRoof f) (MorToRoof g)).
        * apply MorphismCompEqrel.
        * use (eqax2 (RoofEqclassIs eqclass)).
          -- exact tmpp.
          -- exact HR.
      + apply RoofEqclassFromRoofIn.
  Qed.

  (** This is the natural inclusion functor from C to loc_precategory. It is identity on objects
      and sends a morphisms f : X --> Y to a roof (id_X, f). *)
  Definition FunctorToLocalization : functor C loc_precategory.
  Proof.
    use tpair.
    - use functor_data_constr.
      + intros x. exact x.
      + intros x y f. exact (RoofEqclassFromRoof (MorToRoof f)).
    - split.
      + intros x. apply idpath.
      + intros x y z f g. exact (FunctorToLocalization_comp f g).
  Defined.

  (** This definition is the map used by the unique localization functor to map morphisms.
      It sends a roof (s, f) to the composite (# F s)^{-1} · (# F f). *)
  Definition MorMap (D : precategory) (hsD : has_homsets D) (F : functor C D) (x y : ob C)
             (H : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# F f)) :
    Roof x y -> D⟦F x, F y⟧.
  Proof.
    intros R.
    exact (inv_from_iso (isopair _ (H _ _(RoofMor1 R) (RoofMor1Is R))) · (# F (RoofMor2 R))).
  Defined.

  (** One of the 2-out-of-3 properties for isomorphisms. *)
  Lemma is_iso_pre {D : precategory} {x y z : D} (f : x --> y) (g : y --> z)
        (H1 : is_iso (f · g)) (H2 : is_iso g) : is_iso f.
  Proof.
    set (iso1 := isopair _ H1).
    set (iso2 := isopair _ H2).
    set (inv1 := inv_from_iso iso1).
    set (inv2 := inv_from_iso iso2).
    use is_iso_qinv.
    - exact (g · inv1).
    - split.
      + rewrite assoc. unfold inv1.
        set (tmp := iso_inv_after_iso iso1). cbn in tmp.
        apply tmp.
      + set (tmp := iso_inv_after_iso iso2). cbn in tmp. rewrite <- tmp. clear tmp.
        rewrite <- assoc. apply cancel_precomposition.
        apply (post_comp_with_iso_is_inj _ _ _ g H2).
        set (tmp := iso_after_iso_inv iso2). cbn in tmp. rewrite tmp. clear tmp.
        rewrite <- assoc. set (tmp := iso_after_iso_inv iso1). cbn in tmp. exact tmp.
  Qed.

  (** These two lemmas are used in the proof of [MorMap_iscomprelfun]. *)
  Lemma MorMap_top_mor1_is_iso (D : precategory) (hsD : has_homsets D) (F : functor C D)
        (x y : ob C) (H : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# F f))
        (R1 R2 : Roof x y) (T : RoofTop R1 R2) : is_iso (# F (RoofTopMor1 T)).
  Proof.
    use (@is_iso_pre D).
    - exact (F x).
    - exact (# F (RoofMor1 R1)).
    - rewrite <- functor_comp. apply H. apply (RoofTopMor1Is T).
    - apply H. apply (RoofMor1Is R1).
  Qed.

  Lemma MorMap_top_mor2_is_iso (D : precategory) (hsD : has_homsets D) (F : functor C D)
        (x y : ob C) (H : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# F f))
        (R1 R2 : Roof x y) (T : RoofTop R1 R2) : is_iso (# F (RoofTopMor2 T)).
  Proof.
    use (@is_iso_pre D).
    - exact (F x).
    - exact (# F (RoofMor1 R2)).
    - rewrite <- functor_comp. rewrite <- (RoofTopEq1 T). apply H. apply (RoofTopMor1Is T).
    - apply H. apply (RoofMor1Is R2).
  Qed.

  (** Equation for compositions of inverses *)
  Lemma inv_from_iso_comp {D : precategory} {x y z : D} (f : iso x y) (g : iso y z) :
    inv_from_iso (iso_comp f g) = inv_from_iso g · inv_from_iso f.
  Proof.
    apply pathsinv0. apply inv_iso_unique'. unfold precomp_with. unfold iso_comp. cbn.
    rewrite assoc. rewrite <- (assoc _ g). rewrite iso_inv_after_iso. rewrite id_right.
    apply iso_inv_after_iso.
  Qed.

  (** MorMap is compatible with equivalence relation of roofs when one assumes that all the
      morpsisms in SOM are mapped to isomorphisms. *)
  Lemma MorMap_iscomprelfun (D : precategory) (hsD : has_homsets D) (F : functor C D) (x y : ob C)
             (H : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# F f)) :
    iscomprelfun (eqrelpair _ (RoofEqrel x y)) (MorMap D hsD F x y H).
  Proof.
    intros R1 R2 T'.
    use (squash_to_prop T'). apply hsD. intros T. clear T'.
    set (iso1 := isopair _ (H _ _ _ (RoofMor1Is R1))).
    set (iso2 := isopair _ (H _ _ _ (RoofMor1Is R2))).
    set (iso3 := isopair _ (MorMap_top_mor1_is_iso D hsD F x y H R1 R2 T)).
    set (iso4 := isopair _ (MorMap_top_mor2_is_iso D hsD F x y H R1 R2 T)).
    unfold MorMap.
    rewrite <- (id_left (# F (RoofMor2 R1))).
    rewrite <- (iso_after_iso_inv (iso3)). cbn.
    rewrite <- assoc. rewrite <- functor_comp. rewrite assoc.
    rewrite <- inv_from_iso_comp.
    rewrite (RoofTopEq2 T). rewrite functor_comp.
    fold iso1 iso2 iso3 iso4.
    assert (X : iso_comp iso3 iso1 = iso_comp iso4 iso2).
    {
      apply eq_iso. cbn.
      rewrite <- functor_comp. rewrite <- functor_comp. apply maponpaths.
      apply (RoofTopEq1 T).
    }
    rewrite X.
    rewrite inv_from_iso_comp. rewrite <- assoc.
    apply cancel_precomposition.
    rewrite assoc.
    set (tmp := iso_after_iso_inv iso4). cbn in tmp. rewrite tmp. clear tmp.
    apply id_left.
  Qed.

  (** There is a unique morphism in D such that all the roofs R which are in equivalence class
      eqclass are mapped to. This uses the assumption H' which says that all morphisms in SOM
      are mapped to isomorphisms in D. *)
  Lemma MorMap_iscontr (D : precategory) (hsD : has_homsets D) (F : functor C D)
        (H' : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# F f))
        (x y : C) (eqclass : RoofEqclass x y) :
    iscontr (∑ g : D⟦F x, F y⟧,
                   ∏ (R : Roof x y) (H1 : RoofEqclassIn (eqclass) R), g = MorMap D hsD F x y H' R).
  Proof.
    use (squash_to_prop (pr1 (RoofEqclassIs eqclass))). apply isapropiscontr. intros R.
    induction R as [R1 R2].
    set (tmp := MorMap_iscomprelfun D hsD F x y H'). unfold iscomprelfun in tmp.
    use unique_exists.
    - exact (MorMap D hsD F x y H' R1).
    - cbn. intros R' HR'. apply tmp.
      use (eqax2 (RoofEqclassIs eqclass)).
      + exact R2.
      + exact HR'.
    - intros y0.
      apply impred_isaprop. intros t.
      apply impred_isaprop. intros t0.
      apply hsD.
    - intros y0 T. cbn beta in T. exact (T R1 R2).
  Qed.

  (** MorMap equality from MorMap_iscontr *)
  Lemma MorMap_iscontr_eq (D : precategory) (hsD : has_homsets D) (F : functor C D)
        (H' : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# F f))
        (x y : C) (eqclass : RoofEqclass x y) (R : Roof x y) (H1 : RoofEqclassIn eqclass R) :
    pr1 (pr1 (MorMap_iscontr D hsD F H' x y eqclass)) = MorMap D hsD F x y H' R.
  Proof.
    apply (pr2 (pr1 (MorMap_iscontr D hsD F H' x y eqclass))).
    exact H1.
  Qed.

  (** Equivalence class equality of roof_comp_iscontr with roof_comp's using R1'' and R2'' *)
  Lemma roof_comp_iscontr_eqclass {x y z : ob C} (R1 : RoofEqclass x y) (R2 : RoofEqclass y z)
        (R1' : Roof x y) (R1'' : RoofEqclassIn R1 R1')
        (R2' : Roof y z) (R2'' : RoofEqclassIn R2 R2') :
    pr1 (pr1 (roof_comp_iscontr x y z R1 R2)) = RoofEqclassFromRoof (roof_comp R1' R2').
  Proof.
    set (tmp := pr2 (pr1 (roof_comp_iscontr x y z R1 R2)) R1' R1'' R2' R2'').
    use RoofEqclassEq.
    - intros R3 HR3.
      use (eqax1 (RoofEqclassIs (RoofEqclassFromRoof (roof_comp R1' R2')))).
      + exact (roof_comp R1' R2').
      + use (eqax2 (RoofEqclassIs (pr1 (pr1 (roof_comp_iscontr x y z R1 R2))))).
        * exact tmp.
        * exact HR3.
      + apply RoofEqclassFromRoofIn.
    - intros R3 HR3.
      use (eqax1 (RoofEqclassIs (pr1 (pr1 (roof_comp_iscontr x y z R1 R2))))).
      + exact (roof_comp R1' R2').
      + use (eqax2 (RoofEqclassIs (RoofEqclassFromRoof (roof_comp R1' R2')))).
        * apply RoofEqclassFromRoofIn.
        * exact HR3.
      + apply tmp.
  Qed.

  (** MorMap is linear with respect to composition in D *)
  Lemma MorMap_compose (D : precategory) (hsD : has_homsets D) (F : functor C D)
        (H' : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# F f))
        {x y z : ob C} (R1 : Roof x y) (R2 : Roof y z) :
    MorMap D hsD F x z H' (roof_comp R1 R2) = MorMap D hsD F x y H' R1 · MorMap D hsD F y z H' R2.
  Proof.
    set (sqr := isLocClassSqr2 iLC R2 R1 y (RoofMor1 R2) (RoofMor1Is R2) (RoofMor2 R1)).
    unfold roof_comp. fold sqr. unfold MorMap at 1. cbn.
    set (iso1 := isopair
                   (# F (LocSqr2Mor2 sqr · RoofMor1 R1))
                   (H' sqr x (LocSqr2Mor2 sqr · RoofMor1 R1)
                       (isLocClassComp iLC sqr R1 x (LocSqr2Mor2 sqr) (LocSqr2Mor2Is sqr)
                                       (RoofMor1 R1) (RoofMor1Is R1)))).
    set (iso2 := isopair _ (H' sqr R1 (LocSqr2Mor2 sqr) (LocSqr2Mor2Is sqr))).
    set (iso3 := isopair _ (H' R1 x (RoofMor1 R1) (RoofMor1Is R1))).
    set (iso4 := isopair _ (H' R2 y (RoofMor1 R2) (RoofMor1Is R2))).
    assert (X : iso1 = iso_comp iso2 iso3).
    {
      use eq_iso. cbn.
      rewrite functor_comp.
      apply idpath.
    }
    rewrite X. rewrite inv_from_iso_comp. rewrite functor_comp. rewrite assoc.
    unfold MorMap. rewrite assoc. fold iso3 iso4.
    apply cancel_postcomposition.
    rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    set (tmp := LocSqr2Comm sqr).
    apply (pre_comp_with_iso_is_inj D _ _ _ _ (pr2 iso2)). rewrite assoc.
    set (tmp2 := iso_inv_after_iso iso2). cbn in tmp2. cbn. rewrite tmp2. clear tmp2.
    rewrite id_left.
    apply (post_comp_with_iso_is_inj D _ _ _ (pr2 iso4)). cbn. rewrite <- functor_comp.
    rewrite tmp. clear tmp. rewrite functor_comp. rewrite <- assoc.
    apply cancel_precomposition.
    rewrite <- assoc.
    set (tmp2 := iso_after_iso_inv iso4). cbn in tmp2. rewrite tmp2. rewrite id_right.
    apply idpath.
  Qed.

  (** Construct a roof representing s^{-1} from a morphism s in SOM *)
  Definition InvRoofFromMorInSom {x y : C} (s : y --> x) (S : SOM y x s) : Roof x y.
  Proof.
    use mk_Roof.
    - exact y.
    - exact s.
    - exact (identity y).
    - exact S.
  Defined.

  (** Roof is equivalent to composition of its "components". *)
  Definition RoofDecomposeEqrel {x y : C} (R : Roof x y) :
    (eqrelpair _ (RoofEqrel x y)) R (roof_comp (InvRoofFromMorInSom (RoofMor1 R) (RoofMor1Is R))
                                               (MorToRoof (RoofMor2 R))).
  Proof.
    unfold roof_comp.
    set (sqr := isLocClassSqr2 iLC (MorToRoof (RoofMor2 R))
                               (InvRoofFromMorInSom (RoofMor1 R) (RoofMor1Is R)) R
                               (RoofMor1 (MorToRoof (RoofMor2 R)))
                               (RoofMor1Is (MorToRoof (RoofMor2 R)))
                               (RoofMor2 (InvRoofFromMorInSom (RoofMor1 R) (RoofMor1Is R)))).
    fold sqr.
    intros P X. apply X. clear X P.
    use mk_RoofTop.
    - exact sqr.
    - exact (LocSqr2Mor2 sqr).
    - exact (identity (sqr)).
    - use (isLocClassComp iLC).
      + exact (LocSqr2Mor2Is sqr).
      + exact (RoofMor1Is R).
    - rewrite id_left. cbn. apply idpath.
    - cbn. set (tmp := LocSqr2Comm sqr). cbn in tmp.
      rewrite id_right in tmp. rewrite id_right in tmp.
      rewrite id_left. rewrite tmp. apply idpath.
  Qed.

  (** Composition of RoofEqclasses is the same as the equivalence class of composition of the
      roofs. *)
  Lemma RoofEqclassCompToRoofComp {x y z : C} (R1 : Roof x y) (R2 : Roof y z) :
    @compose loc_precategory x y z (RoofEqclassFromRoof R1) (RoofEqclassFromRoof R2) =
    (RoofEqclassFromRoof (roof_comp R1 R2)).
  Proof.
    apply RoofEqclassEqRoof.
    apply (pr2 (pr1 (roof_comp_iscontr x y z (RoofEqclassFromRoof R1) (RoofEqclassFromRoof R2)))).
    - apply RoofEqclassFromRoofIn.
    - apply RoofEqclassFromRoofIn.
  Qed.

  (** Equivalent roofs give rise to the same equivalence class. *)
  Lemma RoofEqClassEq1 {x y : ob C} (R1 R2 : Roof x y) (H : (eqrelpair _ (RoofEqrel x y)) R1 R2) :
    (RoofEqclassFromRoof R1) = (RoofEqclassFromRoof R2).
  Proof.
    use RoofEqclassEq.
    - intros R HR.
      use (eqax1 (RoofEqclassIs (RoofEqclassFromRoof R2))).
      + exact R1.
      + use (eqax2 (RoofEqclassIs (RoofEqclassFromRoof R1))).
        * exact (RoofEqclassFromRoofIn R1).
        * exact HR.
      + use (eqax2 (RoofEqclassIs (RoofEqclassFromRoof R2))).
        * exact H.
        * exact (RoofEqclassFromRoofIn R2).
    - intros R HR.
      use (eqax1 (RoofEqclassIs (RoofEqclassFromRoof R1))).
      + exact R2.
      + use (eqax2 (RoofEqclassIs (RoofEqclassFromRoof R2))).
        * exact (RoofEqclassFromRoofIn R2).
        * exact HR.
      + use (eqax1 (RoofEqclassIs (RoofEqclassFromRoof R1))).
        * exact R1.
        * exact H.
        * exact (RoofEqclassFromRoofIn R1).
  Qed.

  (** This lemma is used to show that inverse roof composed with roof gives the same equivalence
      class as the IdRoof. *)
  Lemma RoofEqclassCompInvRToId {x y : ob C} (f1 : Roof x y) :
    @compose loc_precategory _ _ _
             (RoofEqclassFromRoof (InvRoofFromMorInSom (RoofMor1 f1) (RoofMor1Is f1)))
             (RoofEqclassFromRoof (MorToRoof (RoofMor1 f1))) = (RoofEqclassFromRoof (IdRoof x)).
  Proof.
    set (R1 := (InvRoofFromMorInSom (RoofMor1 f1) (RoofMor1Is f1))).
    set (R2 := (MorToRoof (RoofMor1 f1))).
    set (tmp := pr2 (pr1 (roof_comp_iscontr x f1 x (RoofEqclassFromRoof R1)
                                            (RoofEqclassFromRoof R2)))).
    cbn in tmp.
    use pathscomp0.
    - exact (RoofEqclassFromRoof (roof_comp R1 R2)).
    - use RoofEqclassEqRoof.
      apply tmp.
      + apply RoofEqclassFromRoofIn.
      + apply RoofEqclassFromRoofIn.
    - apply RoofEqClassEq1.
      intros P X. apply X. clear X P. clear tmp.
      unfold roof_comp.
      set (sqr := (isLocClassSqr2 iLC R2 R1 f1 (RoofMor1 R2) (RoofMor1Is R2) (RoofMor2 R1))).
      use mk_RoofTop.
      + exact sqr.
      + cbn. exact (identity sqr).
      + exact (LocSqr2Mor2 sqr · (RoofMor1 f1)).
      + use (isLocClassComp iLC).
        * exact (isLocClassIs iLC _).
        * exact (RoofMor1Is _).
      + rewrite id_left. cbn. rewrite id_right. apply idpath.
      + rewrite id_left. rewrite id_right. cbn.
        set (tmp := LocSqr2Comm sqr). cbn in tmp. rewrite id_right in tmp. rewrite id_right in tmp.
        rewrite tmp. apply idpath.
  Qed.

  (** This lemma shows that the equivalence class of roofs induced by a roof R is equal to the
      equivalence class of roofs induced by composition of roofs (InvRoof (RoofMor1 R)) and
      (MorToRoof (RoofMor2 R)) *)
  Lemma RoofEqclassToRoofComp {x y : ob C} (R : Roof x y) :
    RoofEqclassFromRoof R =
    RoofEqclassFromRoof
      (roof_comp (InvRoofFromMorInSom (RoofMor1 R) (RoofMor1Is R)) (MorToRoof (RoofMor2 R))).
  Proof.
    use RoofEqclassEqRoof.
    use (eqax1 (RoofEqclassIs (RoofEqclassFromRoof R))).
    - exact R.
    - exact (RoofDecomposeEqrel R).
    - apply RoofEqclassFromRoofIn.
  Defined.
  Opaque RoofEqclassToRoofComp.

  (** This lemma is used to show that the localization functor [LocalizationUniversalFunctor] is
      indeed a functor. *)
  Lemma LocalizationUniversalFunctor_isfunctor
    (D : precategory) (hsD : has_homsets D) (F : functor C D)
    (H' : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# F f)) :
    @is_functor loc_precategory_data D
      (functor_data_constr
         loc_precategory_ob_mor D (λ x : C, F x)
         (λ (x y : C) (eqclass : RoofEqclass x y),
          pr1 (pr1 (MorMap_iscontr D hsD F H' x y eqclass)))).
  Proof.
    split.
    - intros x. cbn. cbn in *.
      set (tmp := pr2 (pr1 (MorMap_iscontr D hsD F H' x x (IdRoofEqclass x))) (IdRoof x)).
      assert (H2 : MorMap D hsD F x x H' (IdRoof x) = identity (F x)).
      {
        unfold MorMap. cbn.
        set (iso := isopair _ (H' x x (identity x) (isLocClassIs iLC x))).
        set (tmpp := iso_after_iso_inv iso). cbn in tmpp. apply tmpp.
      }
      use (pathscomp0 _ H2).
      apply tmp.
      apply RoofEqclassFromRoofIn.
    - intros x y z R1 R2. cbn.
      use (squash_to_prop (pr1 (RoofEqclassIs R1))). apply hsD. intros R1'.
      induction R1' as [R1' R1''].
      use (squash_to_prop (pr1 (RoofEqclassIs R2))). apply hsD. intros R2'.
      induction R2' as [R2' R2''].
      rewrite (MorMap_iscontr_eq D hsD F H' x y R1 R1' R1'').
      rewrite (MorMap_iscontr_eq D hsD F H' y z R2 R2' R2'').
      rewrite (roof_comp_iscontr_eqclass R1 R2 R1' R1'' R2' R2'').
      set (tmp := pr2 (pr1 (MorMap_iscontr
                              D hsD F H' x z (RoofEqclassFromRoof (roof_comp R1' R2'))))
                      (roof_comp R1' R2') (RoofEqclassFromRoofIn (roof_comp R1' R2'))).
      rewrite tmp. clear tmp.
      apply MorMap_compose.
  Qed.

  (** The universal functor which we use to factor F through loc_precategory *)
  Definition LocalizationUniversalFunctor (D : precategory) (hsD : has_homsets D) (F : functor C D)
             (H' : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# F f)) :
    functor loc_precategory D.
  Proof.
    use mk_functor.
    - use functor_data_constr.
      + intros x. exact (F x).
      + intros x y eqclass. apply (pr1 (pr1 (MorMap_iscontr D hsD F H' x y eqclass))).
    - exact (LocalizationUniversalFunctor_isfunctor D hsD F H').
  Defined.

  (** We show that LocalizationUniversalFunctor satisfies the commutativity required for the
      universal functor. *)
  Definition LocalizationUniversalFunctorComm (D : precategory) (hsD : has_homsets D)
             (F : functor C D) (H' : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# F f)) :
    functor_composite FunctorToLocalization (LocalizationUniversalFunctor D hsD F H') = F.
  Proof.
    use (functor_eq _ _ hsD).
    use total2_paths_f.
    - apply idpath.
    - cbn.
      use funextsec. intros a.
      use funextsec. intros b.
      use funextsec. intros f.
      use (pathscomp0 (MorMap_iscontr_eq D hsD F H' a b (RoofEqclassFromRoof (MorToRoof f))
                                         (MorToRoof f) (RoofEqclassFromRoofIn _))).
      unfold MorToRoof. unfold MorMap. cbn.
      set (iso := (isopair (# F (identity a)) (H' a a (identity a) (isLocClassIs iLC a)))).
      assert (X : iso = identity_iso (F a)).
      {
        use eq_iso. cbn.
        rewrite functor_id.
        apply idpath.
      }
      rewrite X. cbn. apply id_left.
  Qed.

  (** This lemma shows uniqueness of the functor LocalizationUniversalFunctor *)
  Lemma LocalizationUniversalFunctorUnique (D : precategory) (hsD : has_homsets D) (F : functor C D)
        (H' : ∏ (x y : C) (f : C ⟦ x, y ⟧), SOM x y f → is_iso (# F f))
        (y : functor loc_precategory D) (T : functor_composite FunctorToLocalization y = F) :
    y = (LocalizationUniversalFunctor D hsD F H').
  Proof.
    use (functor_eq _ _ hsD).
    use total2_paths_f.
    - induction T. apply idpath.
    - use funextsec. intros a.
      use funextsec. intros b.
      use funextsec. intros f.
      induction T. cbn. unfold idfun.
      use (squash_to_prop (pr1 (RoofEqclassIs f))). apply hsD. intros f'. induction f' as [f1 f2].
      rewrite (RoofEqclassEqRoof f f1 f2).
      use (pathscomp0 _ (! (pr2 (pr1 (MorMap_iscontr
                                        D hsD (functor_composite FunctorToLocalization y)
                                        H' a b (RoofEqclassFromRoof f1)))
                                f1 (RoofEqclassFromRoofIn f1)))).
      rewrite (RoofEqclassToRoofComp f1).
      rewrite <- (RoofEqclassCompToRoofComp (InvRoofFromMorInSom (RoofMor1 f1) (RoofMor1Is f1))
                                           (MorToRoof (RoofMor2 f1))).
      use (pathscomp0 (@functor_comp
                         loc_precategory D y
                         _ _ _
                         (RoofEqclassFromRoof (InvRoofFromMorInSom (RoofMor1 f1) (RoofMor1Is f1)))
                         (RoofEqclassFromRoof (MorToRoof (RoofMor2 f1))))).
      unfold functor_composite. cbn. apply cancel_postcomposition.
      set (iso1 := isopair _ (H' f1 a (RoofMor1 f1) (RoofMor1Is f1))).
      apply (post_comp_with_iso_is_inj _ _ _ _ (pr2 iso1)).
      use (pathscomp0 _ (! (iso_after_iso_inv iso1))).
      unfold iso1. clear iso1. cbn.
      set (tmp := @functor_comp
                    loc_precategory D y
                    _ _ _
                    (RoofEqclassFromRoof (InvRoofFromMorInSom (RoofMor1 f1) (RoofMor1Is f1)))
                    (RoofEqclassFromRoof (MorToRoof (RoofMor1 f1)))).
      unfold functor_on_morphisms in tmp. apply pathsinv0 in tmp. use (pathscomp0 tmp). clear tmp.
      rewrite RoofEqclassCompInvRToId.
      apply (@functor_id loc_precategory D y).
  Qed.

  (** The following lemma only applies when the objects of D satisfy isaset. *)
  Lemma LocalizationUniversalProperty (D : precategory) (hsD : has_homsets D) (hssD : isaset D)
        (F : functor C D) (H' : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# F f)) :
    iscontr (∑ H : functor loc_precategory D, functor_composite FunctorToLocalization H = F).
  Proof.
    use unique_exists.
    (* The functor *)
    - exact (LocalizationUniversalFunctor D hsD F H').
    (* Commutativity of the functor *)
    - exact (LocalizationUniversalFunctorComm D hsD F H').
    (* Uniqueness of commutativity *)
    - intros y. apply (functor_isaset _ _ hsD hssD).
    (* Uniqueness of the functor *)
    - exact (LocalizationUniversalFunctorUnique D hsD F H').
  Defined.
  Opaque LocalizationUniversalProperty.

  (** The functor FunctorToLocalization maps morphisms in SOM to isomorphisms *)
  Definition FunctorToLocalization_is_iso :
    ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# FunctorToLocalization f).
  Proof.
    intros x y f s. cbn.
    use (@is_iso_qinv loc_precategory).
    - exact (RoofEqclassFromRoof (InvRoofFromMorInSom f s)).
    - split.
      + set (sqr := isLocClassSqr2 iLC (InvRoofFromMorInSom f s) (MorToRoof f) y
                                   (RoofMor1 (InvRoofFromMorInSom f s))
                                   (RoofMor1Is (InvRoofFromMorInSom f s))
                                   (RoofMor2 (MorToRoof f))).
        set (PostS := isLocClassPost iLC sqr x y (LocSqr2Mor2 sqr) (LocSqr2Mor1 sqr) f s
                                     (! (LocSqr2Comm sqr))).
        rewrite RoofEqclassCompToRoofComp.
        use RoofEqClassEq1.
        intros P X. apply X. clear X P.
        unfold roof_comp. fold sqr.
        use mk_RoofTop.
        * exact PostS.
        * exact (PostSwitchMor PostS).
        * exact (PostSwitchMor PostS · LocSqr2Mor2 sqr).
        * use (isLocClassComp iLC).
          -- exact (PostSwitchMorIs PostS).
          -- use (isLocClassComp iLC).
             ++ exact (LocSqr2Mor2Is sqr).
             ++ exact (isLocClassIs iLC x).
        * cbn. rewrite assoc. apply idpath.
        * cbn. rewrite assoc. rewrite id_right. rewrite id_right.
          exact (! (PostSwitchEq PostS)).
      + set (sqr := isLocClassSqr2 iLC (MorToRoof f) (InvRoofFromMorInSom f s) x
                                   (RoofMor1 (MorToRoof f)) (RoofMor1Is (MorToRoof f))
                                   (RoofMor2 (InvRoofFromMorInSom f s))).
        rewrite RoofEqclassCompToRoofComp.
        use RoofEqClassEq1.
        intros P X. apply X. clear X P.
        unfold roof_comp. fold sqr.
        use mk_RoofTop.
        * exact sqr.
        * exact (identity sqr).
        * exact (LocSqr2Mor2 sqr · f).
        * use (isLocClassComp iLC).
          -- exact (isLocClassIs iLC sqr).
          -- use (isLocClassComp iLC).
             ++ exact (LocSqr2Mor2Is sqr).
             ++ exact s.
        * rewrite id_left. cbn. rewrite id_right. apply idpath.
        * rewrite id_left. cbn. rewrite id_right.
          set (tmp := LocSqr2Comm sqr). cbn in tmp.
          rewrite id_right in tmp. rewrite id_right in tmp. rewrite tmp.
          apply idpath.
  Qed.

  (** Localization of categories is unique up to isomorphism of categories and loc_precategory is
      one such precategory. *)
  Lemma LocalizationUniversalCategory (CC : precategory) (hss : has_homsets CC)
        (In : functor C CC) (H' : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# In f))
        (HH : ∏ (D : precategory) (hsD : has_homsets D)
                (F : functor C D) (H' : ∏ (x y : C) (f : x --> y) (s : SOM x y f), is_iso (# F f)),
              ∑ HH : functor CC D, (functor_composite In HH = F)
                                     × (∏ (yy : functor CC D) (comm : functor_composite In yy = F),
                                        yy = HH)) :
    ∑ D : (functor CC loc_precategory × functor loc_precategory CC),
          (functor_composite (dirprod_pr1 D) (dirprod_pr2 D) = (functor_identity _))
            × (functor_composite (dirprod_pr2 D) (dirprod_pr1 D) = (functor_identity _)).
  Proof.
    set (comm1 := LocalizationUniversalFunctorComm CC hss In H').
    set (tmp := HH loc_precategory has_homsets_loc_precategory FunctorToLocalization
                   FunctorToLocalization_is_iso).
    induction tmp as [inv1 p]. induction p as [comm2 unique2].
    set (inv2 := (LocalizationUniversalFunctor CC hss In H')).
    use tpair.
    - use dirprodpair.
      + exact inv1.
      + exact inv2.
    - use dirprodpair.
      + cbn.
        rewrite <- comm2 in comm1. rewrite functor_assoc in comm1.
        set (tmp := HH CC hss In H').
        induction tmp as [F' CC2]. induction CC2 as [comm3 unique3].
        set (tmp1 := unique3 (functor_identity CC) (functor_identity_right _ _ _)).
        set (tmp2 := unique3 (functor_composite inv1 (LocalizationUniversalFunctor CC hss In H'))
                             comm1).
        rewrite <- tmp1 in tmp2. exact tmp2.
      + cbn.
        rewrite <- comm1 in comm2. rewrite functor_assoc in comm2.
        set (tmp := LocalizationUniversalFunctorUnique
                      loc_precategory has_homsets_loc_precategory FunctorToLocalization
                      FunctorToLocalization_is_iso).
        set (tmp1 := tmp _ comm2). fold inv2 in tmp1.
        set (tmp2 := tmp (functor_identity _) (functor_identity_right _ _ _)).
        rewrite <- tmp2 in tmp1.
        exact tmp1.
  Defined.
  Opaque LocalizationUniversalCategory.

End def_roofs.
