Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Core.Isos.

Open Scope cat.
Open Scope mor_disp_scope.

Section DisplayedBifunctor.

  Import Notations.

  Definition disp_bifunctor_data {A B C : category} (F : bifunctor A B C) (DA : disp_cat A) (DB : disp_cat B) (DC : disp_cat C)
    := ∑ (Fob : ∏ (x : A) (y : B), DA x -> DB y -> DC (x ⊗_{F} y)),
      (∏ (x : A) (y1 y2 : B) (g : B⟦y1,y2⟧) (xx : DA x) (yy1 : DB y1) (yy2 : DB y2),
       (yy1 -->[g] yy2) -> ((Fob _ _ xx yy1) -->[x ⊗^{F}_{l} g] (Fob _ _ xx yy2)))
                                          ×
      (∏ (x1 x2 : A) (y : B) (f : A⟦x1,x2⟧) (xx1 : DA x1) (xx2 : DA x2) (yy : DB y),
          (xx1 -->[f] xx2) -> ((Fob _ _ xx1 yy) -->[f ⊗^{F}_{r} y] (Fob _ _ xx2 yy))).

  Definition make_disp_bifunctor_data {A B C : category} (F : bifunctor A B C) (DA : disp_cat A) (DB : disp_cat B) (DC : disp_cat C)
    (Fob : ∏ (x : A) (y : B), DA x -> DB y -> DC (x ⊗_{F} y))
    (dlw : ∏ (x : A) (y1 y2 : B) (g : B⟦y1,y2⟧) (xx : DA x) (yy1 : DB y1) (yy2 : DB y2), (yy1 -->[g] yy2) -> ((Fob _ _ xx yy1) -->[x ⊗^{F}_{l} g] (Fob _ _ xx yy2)))
    (drw : ∏ (x1 x2 : A) (y : B) (f : A⟦x1,x2⟧) (xx1 : DA x1) (xx2 : DA x2) (yy : DB y), (xx1 -->[f] xx2) -> ((Fob _ _ xx1 yy) -->[f ⊗^{F}_{r} y] (Fob _ _ xx2 yy)))
      : disp_bifunctor_data F DA DB DC := (Fob,,dlw,,drw).

  Definition disp_bifunctor_on_objects {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) : ∏ (x : A) (y : B), DA x -> DB y -> DC (x ⊗_{F} y) := pr1 DF.
  Local Notation "xx ⊗⊗_{ DF } yy" := (disp_bifunctor_on_objects DF _ _ xx yy) (at level 31).

  Definition disp_leftwhiskering_on_morphisms {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) :
     ∏ (x : A) (y1 y2 : B) (g : B⟦y1,y2⟧) (xx : DA x) (yy1 : DB y1) (yy2 : DB y2), (yy1 -->[g] yy2) -> ((pr1 DF _ _ xx yy1) -->[x ⊗^{F}_{l} g] (pr1 DF _ _ xx yy2)) := pr1 (pr2 DF).
  Local Notation "xx ⊗⊗^{ DF }_{l} gg" := (disp_leftwhiskering_on_morphisms DF _ _ _ _ xx _ _ gg) (at level 31).

  Definition disp_rightwhiskering_on_morphisms {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) :
     ∏ (x1 x2 : A) (y : B) (f : A⟦x1,x2⟧) (xx1 : DA x1) (xx2 : DA x2) (yy : DB y), (xx1 -->[f] xx2) -> ((pr1 DF _ _ xx1 yy) -->[f ⊗^{F}_{r} y] (pr1 DF _ _ xx2 yy)) := pr2 (pr2 DF).
  Local Notation "ff ⊗⊗^{ DF }_{r} yy" := (disp_rightwhiskering_on_morphisms DF _ _ _ _ _ _ yy ff) (at level 31).

  Definition disp_bifunctor_leftidax {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) :=
    ∏ (x : A) (y : B) (xx : DA x) (yy : DB y),
      xx ⊗⊗^{DF}_{l} (id_disp yy) = transportb _ (bifunctor_leftid F x y) (id_disp (xx ⊗⊗_{DF} yy)).

  Definition disp_bifunctor_rightidax {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) :=
    ∏ (x : A) (y : B) (xx : DA x) (yy : DB y), (id_disp xx) ⊗⊗^{DF}_{r} yy = transportb _ (bifunctor_rightid F y x) (id_disp (xx ⊗⊗_{DF} yy)).

  Definition disp_bifunctor_leftcompax {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) :=
    ∏ (x : A) (y1 y2 y3 : B) (g1 : B⟦y1,y2⟧) (g2 : B⟦y2,y3⟧)
      (xx : DA x) (yy1 : DB y1) (yy2 : DB y2) (yy3 : DB y3) (gg1 : yy1 -->[g1] yy2) (gg2 : yy2 -->[g2] yy3),
      (xx ⊗⊗^{DF}_{l} (gg1 ;; gg2)  = transportb _ (bifunctor_leftcomp F _ _ _ _ g1 g2)  ((xx ⊗⊗^{DF}_{l} gg1) ;; (xx ⊗⊗^{DF}_{l} gg2)) ).

  Definition disp_bifunctor_rightcompax {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) :=
    ∏ (x1 x2 x3 : A) (y : B) (f1 : A⟦x1,x2⟧) (f2 : A⟦x2,x3⟧)
      (xx1 : DA x1) (xx2 : DA x2) (xx3 : DA x3) (yy : DB y) (ff1 : xx1 -->[f1] xx2) (ff2 : xx2 -->[f2] xx3),
      ((ff1 ;; ff2) ⊗⊗^{DF}_{r} yy  = transportb _ (bifunctor_rightcomp F _ _ _ _ f1 f2)  ((ff1 ⊗⊗^{DF}_{r} yy) ;; (ff2 ⊗⊗^{DF}_{r} yy)) ).


  (** Remark:: No make_disp_functor exists in Displayedcats.Functors **)
  Lemma leftwhiskering_dispfunctor {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) (dbli : disp_bifunctor_leftidax DF) (dblc : disp_bifunctor_leftcompax DF) :
    ∏ (x : A) (xx : DA x), disp_functor (leftwhiskering_functor F (bifunctor_leftid F) (bifunctor_leftcomp F) x) DB DC.
  Proof.
    intros x xx.
    (* use make_disp_functor. *)
    use tpair.
    - use tpair.
      + intros y yy.
        exact (xx ⊗⊗_{DF} yy).
      + intros y1 y2 yy1 yy2 g gg.
        exact (xx ⊗⊗^{DF}_{l} gg).
    - use tpair.
      + intros y yy.
        exact (dbli x y xx yy).
      + intros y1 y2 y3 yy1 yy2 yy3 g1 g2 gg1 gg2.
        cbn.
        exact (dblc x y1 y2 y3 g1 g2 xx yy1 yy2 yy3 gg1 gg2).
  Defined.

  Lemma rightwhiskering_dispfunctor {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) (dbri : disp_bifunctor_rightidax DF) (dbrc : disp_bifunctor_rightcompax DF) :
    ∏ (y : B) (yy : DB y), disp_functor (rightwhiskering_functor F (bifunctor_rightid F) (bifunctor_rightcomp F) y) DA DC.
  Proof.
    intros y yy.
    (* use make_disp_functor. *)
    use tpair.
    - use tpair.
      + intros x xx.
        exact (xx ⊗⊗_{DF} yy).
      + intros x1 x2 xx1 xx2 f ff.
        exact (ff ⊗⊗^{DF}_{r} yy).
    - use tpair.
      + intros x xx.
        exact (dbri x y xx yy).
      + intros x1 x2 x3 xx1 xx2 xx3 f1 f2 ff1 ff2.
        cbn.
        exact (dbrc x1 x2 x3 y f1 f2 xx1 xx2 xx3 yy ff1 ff2).
  Defined.


  Definition dispfunctoronmorphisms1 {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) {x1 x2 : A} {y1 y2 : B} {f : A⟦x1,x2⟧} {g : B⟦y1,y2⟧} {xx1 : DA x1} {xx2 : DA x2} {yy1 : DB y1} {yy2 : DB y2} (ff : xx1 -->[f] xx2) (gg : yy1 -->[g] yy2) : xx1 ⊗⊗_{DF} yy1 -->[f ⊗^{F} g] xx2 ⊗⊗_{DF} yy2 :=
    (ff ⊗⊗^{DF}_{r} yy1) ;; (xx2 ⊗⊗^{DF}_{l} gg).
  Local Notation "ff ⊗⊗^{ DF } gg" := (dispfunctoronmorphisms1 DF ff gg) (at level 31).

  Definition dispfunctoronmorphisms2 {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) {x1 x2 : A} {y1 y2 : B} {f : A⟦x1,x2⟧} {g : B⟦y1,y2⟧} {xx1 : DA x1} {xx2 : DA x2} {yy1 : DB y1} {yy2 : DB y2} (ff : xx1 -->[f] xx2) (gg : yy1 -->[g] yy2) : xx1 ⊗⊗_{DF} yy1 -->[functoronmorphisms2 F f g] xx2 ⊗⊗_{DF} yy2 :=
    (xx1 ⊗⊗^{DF}_{l} gg) ;; (ff ⊗⊗^{DF}_{r} yy2).
  Local Notation "ff ⊗⊗^{ DF }_{2} gg" := (dispfunctoronmorphisms2 DF ff gg) (at level 31).

  Definition dispfunctoronmorphisms_are_equal {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) := ∏ (x1 x2 : A) (y1 y2 : B) (f : A⟦x1,x2⟧) (g : B⟦y1,y2⟧) (xx1 : DA x1) (xx2 : DA x2) (yy1 : DB y1) (yy2 : DB y2) (ff : xx1 -->[f] xx2) (gg : yy1 -->[g] yy2),  ff ⊗⊗^{DF} gg = transportb _ (bifunctor_equalwhiskers F _ _ _ _ f g) (ff ⊗⊗^{DF}_{2} gg).

  Lemma dispwhiskerscommutes {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} {DF : disp_bifunctor_data F DA DB DC} (dfmae : dispfunctoronmorphisms_are_equal DF) :
    ∏ (x1 x2 : A) (y1 y2 : B) (f : A⟦x1,x2⟧) (g : B⟦y1,y2⟧) (xx1 : DA x1) (xx2 : DA x2) (yy1 : DB y1) (yy2 : DB y2) (ff : xx1 -->[f] xx2) (gg : yy1 -->[g] yy2),
      ((ff ⊗⊗^{ DF}_{r} yy1) ;; (xx2 ⊗⊗^{ DF}_{l} gg) = transportb _ (bifunctor_equalwhiskers F x1 x2 y1 y2 f g) ((xx1 ⊗⊗^{ DF}_{l} gg) ;; (ff ⊗⊗^{ DF}_{r} yy2))).
  Proof.
    intros.
    apply dfmae.
  Qed.

  Definition is_disp_bifunctor {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) : UU :=
    (disp_bifunctor_leftidax DF) ×
    (disp_bifunctor_rightidax DF) ×
    (disp_bifunctor_leftcompax DF) ×
    (disp_bifunctor_rightcompax DF) ×
    (dispfunctoronmorphisms_are_equal DF).

  Definition disp_bifunctor {A B C : category} (F : bifunctor A B C) (DA : disp_cat A) (DB : disp_cat B) (DC : disp_cat C) : UU :=
    ∑ (DF : disp_bifunctor_data F DA DB DC), is_disp_bifunctor DF.

  Definition make_disp_bifunctor {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor_data F DA DB DC) (H : is_disp_bifunctor DF)
    : disp_bifunctor F DA DB DC := (DF,,H).

  Definition disp_bifunctordata_from_disp_bifunctor {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor F DA DB DC) : disp_bifunctor_data F DA DB DC := pr1 DF.
  Coercion disp_bifunctordata_from_disp_bifunctor : disp_bifunctor >-> disp_bifunctor_data.

  Definition is_disp_bifunctordata_from_disp_bifunctor {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor F DA DB DC) : is_disp_bifunctor DF := pr2 DF.

  Definition disp_bifunctor_leftid {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor F DA DB DC) : disp_bifunctor_leftidax DF := pr1 (is_disp_bifunctordata_from_disp_bifunctor DF).

   Definition disp_bifunctor_rightid {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor F DA DB DC) : disp_bifunctor_rightidax DF := pr1 (pr2 (is_disp_bifunctordata_from_disp_bifunctor DF)).

  Definition disp_bifunctor_leftcomp {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor F DA DB DC) : disp_bifunctor_leftcompax DF := pr1 (pr2 (pr2 (is_disp_bifunctordata_from_disp_bifunctor DF))).

  Definition disp_bifunctor_rightcomp {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor F DA DB DC) : disp_bifunctor_rightcompax DF := pr1 (pr2 (pr2 (pr2 (is_disp_bifunctordata_from_disp_bifunctor DF)))).

  Definition disp_bifunctor_equalwhiskers {A B C : category} {F : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (DF : disp_bifunctor F DA DB DC) : dispfunctoronmorphisms_are_equal DF := pr2 (pr2 (pr2 (pr2 (is_disp_bifunctordata_from_disp_bifunctor DF)))).

End DisplayedBifunctor.

Module DisplayedBifunctorNotations.
  Notation "xx ⊗⊗_{ DF } yy" := (disp_bifunctor_on_objects DF _ _ xx yy) (at level 31).
  Notation "xx ⊗⊗^{ DF }_{l} gg" := (disp_leftwhiskering_on_morphisms DF _ _ _ _ xx _ _ gg) (at level 31).
  Notation "ff ⊗⊗^{ DF }_{r} yy" := (disp_rightwhiskering_on_morphisms DF _ _ _ _ _ _ yy ff) (at level 31).
  Notation "ff ⊗⊗^{ DF } gg" := (dispfunctoronmorphisms1 DF ff gg) (at level 31).
End DisplayedBifunctorNotations.


Section DisplayedWhiskeredBinaturaltransformation.

  Import DisplayedBifunctorNotations.

  Definition disp_binat_trans_data {A B C : category} {F : bifunctor A B C} {G : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (α : binat_trans_data F G) (DF : disp_bifunctor F DA DB DC) (DG : disp_bifunctor G DA DB DC) : UU :=
    ∏ (x : A) (y : B) (xx : DA x) (yy : DB y), xx ⊗⊗_{DF} yy -->[α x y] xx ⊗⊗_{DG} yy.

  Definition make_disp_binat_trans_data {A B C : category} {F : bifunctor A B C} {G : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} {α : binat_trans_data F G} {DF : disp_bifunctor F DA DB DC} {DG : disp_bifunctor G DA DB DC} (dα :  ∏ (x : A) (y : B) (xx : DA x) (yy : DB y), xx ⊗⊗_{DF} yy -->[α x y] xx ⊗⊗_{DG} yy) : disp_binat_trans_data α DF DG := dα.

  Definition is_disp_binat_trans {A B C : category} {F : bifunctor A B C} {G : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} {α : binat_trans F G} {DF : disp_bifunctor F DA DB DC} {DG : disp_bifunctor G DA DB DC} (dα : disp_binat_trans_data α DF DG) : UU :=
    (∏ (x : A) (y1 y2 : B) (g : B⟦y1,y2⟧) (xx : DA x) (yy1 : DB y1) (yy2 : DB y2) (gg : yy1 -->[g] yy2),
      ((xx ⊗⊗^{DF}_{l} gg) ;; (dα _ _ xx yy2) = transportb _ (pr1 (pr2 α) x y1 y2 _) ((dα _ _ xx yy1) ;; (xx ⊗⊗^{DG}_{l} gg)))) ×                                                                                                                                            (∏ (x1 x2 : A) (y : B) (f : A⟦x1,x2⟧) (xx1 : DA x1) (xx2 : DA x2) (yy : DB y) (ff : xx1 -->[f] xx2),
    ((ff ⊗⊗^{DF}_{r} yy) ;; (dα _ _ xx2 yy) = transportb _ (pr2 (pr2 α) x1 x2 y _) ((dα _ _ xx1 yy) ;; (ff ⊗⊗^{DG}_{r} yy))) ).

  (* The following lemma is something we should, but I'm really stuck trying to prove because transportations jump in everywhere everytime I want to do something.. *)
  Lemma full_disp_naturality_condition {A B C : category} {F : bifunctor A B C} {G : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} {α : binat_trans F G} {DF : disp_bifunctor F DA DB DC} {DG : disp_bifunctor G DA DB DC} {dα : disp_binat_trans_data α DF DG} (dαn : is_disp_binat_trans dα) (x1 x2 : A) (y1 y2 : B) (f : A⟦x1,x2⟧) (g : B⟦y1,y2⟧) (xx1 : DA x1) (xx2 : DA x2) (yy1 : DB y1) (yy2 : DB y2) (ff : xx1 -->[f] xx2) (gg : yy1 -->[g] yy2) :
    (ff ⊗⊗^{DF} gg) ;; (dα _ _ xx2 yy2) = transportb _ (full_naturality_condition (pr2 α) f g) ((dα _ _ xx1 yy1) ;; (ff ⊗⊗^{DG} gg)).
  Proof.
    unfold dispfunctoronmorphisms1.

    (*
    etrans.
    {
      apply (assoc_disp_var ( ff ⊗⊗^{ DF}_{r} yy1) ( xx2 ⊗⊗^{ DF}_{l} gg) ( dα x2 y2 xx2 yy2)).
    }
    rewrite (pr1 dαn).
    apply transportb_transpose_right.
    apply pathsinv0.
    etrans. {
      apply assoc_disp.
    }
    apply transportb_transpose_left.



    assert (pf: dα x1 y1 xx1 yy1 ;; ff ⊗⊗^{ DG}_{r} yy1 ;; xx2 ⊗⊗^{ DG}_{l} gg = ( transportb _ (! (pr22 α) x1 x2 y1 f) (ff ⊗⊗^{ DF}_{r} yy1 ;; dα x2 y1 xx2 yy1)) ;; xx2 ⊗⊗^{ DG}_{l} gg).
    {
      rewrite (pathsinv0 (transportb_transpose_left (pr2 dαn x1 x2 y1  f xx1 xx2 yy1 ff))).
      apply idpath.
    }
    etrans. { apply pf. }
    Search (transportf _ _ (transportf _ _ _)).
    rewrite transport_f_f.
    rewrite transport_f_f.



    etrans. {

      apply (cancel_precomposition_disp (pr2 dα x1 x2 y1)).



    }

    etrans. { apply transport_b_b. }
    (* Remains to show: transportb _ p1 (dα x1 y1 xx1 yy1 ;;  (ff ⊗⊗^{ DG}_{r} yy1 ;; xx2 ⊗⊗^{ DG}_{l} gg))
                           =
                ff ⊗⊗^{ DF}_{r} yy1 ;; transportb _ p2 (dα x2 y1 xx2 yy1 ;; xx2 ⊗⊗^{ DG}_{l} gg)
       for some p1 ̸= p2
     *)

    apply transportb_transpose_left.
    etrans.
    {
      apply assoc_disp.
    }
    etrans.
    {
      Check (pr2 dαn x1 x2 y1 f xx1 xx2 yy1 ff).
      rewrite (pr1 dαn x2 y1 y2 g xx2 yy1 yy2 gg).



    rewrite transport_b_b.
    Search (_ ;; transportb _ _ _).


    apply pathsinv0.
    rewrite (pathsinv0 (pr1 dαn _ _ _ _ _ _ _ _)).
    apply transportf_transpose_right.
    apply pathsinv0.
    etrans.
    {
      rewrite (pr1 dαn x2 y1 y2 g xx2 yy1 yy2 gg).
      apply idpath.
    }



    apply pathsinv0.
    (* rewrite transport_f_f. *)
    Search (transportf _ _ _ = _ -> _ transportb _ _ _).

    Search (_ ;; transportf _ _ _).

    Check (transport_b_b _ (pr2 dαn _ _ _ _ _ _ _ _) _).

    Check ((pr1 dαn) x1 x2 y1 y _ xx1 yy1 yy2 gg).

    rewrite ((pr1 dαn) x2 y1 y2 g xx2 yy1 yy2 gg).

    rewrite mor_disp_transportf_postwhisker.


    rewrite assoc.
    rewrite ((pr2 αn) a1 a2 b1 f).
    rewrite assoc.
    apply idpath.
  Qed. *)
  Abort.


  Definition disp_binat_trans {A B C : category} {F : bifunctor A B C} {G : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} (α : binat_trans F G) (DF : disp_bifunctor F DA DB DC) (DG : disp_bifunctor G DA DB DC) : UU :=
    ∑ (dα : disp_binat_trans_data α DF DG), is_disp_binat_trans dα.

  Definition make_disp_binat_trans {A B C : category} {F : bifunctor A B C} {G : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} {α : binat_trans F G} {DF : disp_bifunctor F DA DB DC} {DG : disp_bifunctor G DA DB DC} (dα : disp_binat_trans_data α DF DG) (H : is_disp_binat_trans dα) : disp_binat_trans α DF DG := (dα,,H).

  Check is_iso_disp.

  Definition is_dispbinatiso {A B C : category} {F : bifunctor A B C} {G : bifunctor A B C} {DA : disp_cat A} {DB : disp_cat B} {DC : disp_cat C} {α : binat_trans F G} (αiso : is_binatiso α) {DF : disp_bifunctor F DA DB DC} {DG : disp_bifunctor G DA DB DC} (dα : disp_binat_trans α DF DG)
    := ∏ (x : A) (y : B) (xx : DA x) (yy : DB y), is_iso_disp (z_iso_to_iso ((α x y ),,(αiso x y ))) (pr1 dα x y xx yy).


End DisplayedWhiskeredBinaturaltransformation.
