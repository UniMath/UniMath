(****************************************************
  Benedikt Ahrens and Anders Mörtberg, October 2015
*****************************************************)

Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
(* Local Notation "F ⟶ G" := (nat_trans F G) (at level 39). *)
Local Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (at level 50).

Section move_upstream.

Lemma path_to_ctr (A : UU) (B : A -> UU) (isc : iscontr (total2 (fun a => B a)))
           (a : A) (p : B a) : a = pr1 (pr1 isc).
Proof.
exact (maponpaths pr1 (pr2 isc (tpair _ a p))).
Defined.

Lemma uniqueExists (A : UU) (P : A -> UU)
  (Hexists : iscontr (total2 (fun a => P a)))
  (a b : A) (Ha : P a) (Hb : P b) : a = b.
Proof.
assert (H : tpair _ _ Ha = tpair _ _ Hb).
  now apply proofirrelevance, isapropifcontr.
exact (base_paths _ _ H).
Defined.

End move_upstream.

Section diagram_def.

Definition graph := Σ (D : UU) , D -> D -> UU.

Definition vertex : graph -> UU := pr1.
Definition edge {g : graph} : vertex g -> vertex g -> UU := pr2 g.

Definition diagram (g : graph) (C : precategory) : UU :=
  Σ (f : vertex g -> C), ∀ (a b : vertex g), edge a b -> C⟦f a, f b⟧.

Definition dob {g : graph} {C : precategory} (d : diagram g C) : vertex g -> C :=
  pr1 d.

Definition dmor {g : graph} {C : precategory} (d : diagram g C) :
  ∀ {a b}, edge a b -> C⟦dob d a,dob d b⟧ := pr2 d.

Section diagram_from_functor.

Variables (J C : precategory).
Variable (F : functor J C).

Definition graph_from_precategory : graph := pr1 (pr1 J).
Definition diagram_from_functor : diagram graph_from_precategory C :=
  tpair _ _ (pr2 (pr1 F)).

End diagram_from_functor.

End diagram_def.

Section colim_def.

Variables (C : precategory) (hsC : has_homsets C).

(* TODO: Maybe package cocones again? *)
Definition isColimCocone {g : graph} (d : diagram g C) (c0 : C)
  (f : ∀ (v : vertex g), C⟦dob d v,c0⟧)
  (H : ∀ (u v : vertex g) (e : edge u v), dmor d e ;; f v = f u) : UU :=
  ∀ (c : C) (fc : ∀ (v : vertex g), C⟦dob d v,c⟧)
    (Hc : ∀ (u v : vertex g) (e : edge u v), dmor d e ;; fc v = fc u),
  iscontr (Σ x : C⟦c0,c⟧, ∀ (v : vertex g), f v ;; x = fc v).

Definition ColimCocone {g : graph} (d : diagram g C) : UU :=
  Σ (A : Σ c0f : (Σ c0 : C, ∀ (v : vertex g), C⟦dob d v,c0⟧),
   ∀ (u v : vertex g) (e : edge u v), dmor d e ;; (pr2 c0f) v = (pr2 c0f) u),
    isColimCocone d (pr1 (pr1 A)) (pr2 (pr1 A)) (pr2 A).

Definition mk_ColimCocone {g : graph} (d : diagram g C)
  (c : C) (f : ∀ (v : vertex g), C⟦dob d v,c⟧)
  (H : ∀ (u v : vertex g) (e : edge u v), dmor d e ;; f v = f u)
  (isCC : isColimCocone d c f H) : ColimCocone d :=
    tpair _ (tpair _ (tpair _ c f) H) isCC.

Definition Colims : UU := ∀ {g : graph} (d : diagram g C), ColimCocone d.
Definition hasColims : UU  :=
  ∀ {g : graph} (d : diagram g C), ishinh (ColimCocone d).

Definition colim {g : graph} {d : diagram g C}
  (CC : ColimCocone d) : C := pr1 (pr1 (pr1 CC)).

Definition colimIn {g : graph} {d : diagram g C} (CC : ColimCocone d) :
  ∀ (v : vertex g), C⟦dob d v,colim CC⟧ :=
    pr2 (pr1 (pr1 CC)).

Definition colimInCommutes {g : graph} {d : diagram g C}
  (CC : ColimCocone d) : ∀ (u v : vertex g) (e : edge u v),
   dmor d e ;; colimIn CC v = colimIn CC u :=
     pr2 (pr1 CC).

Definition isColimCocone_ColimCocone {g : graph} {d : diagram g C}
  (CC : ColimCocone d) :
  isColimCocone d (colim CC) (colimIn CC) (colimInCommutes CC) :=
   pr2 CC.

Definition colimArrow {g : graph} {d : diagram g C} (CC : ColimCocone d)
  (c : C) (fc : ∀ (v : vertex g), C⟦dob d v,c⟧)
  (Hc : ∀ (u v : vertex g) (e : edge u v), dmor d e ;; fc v = fc u) :
  C⟦colim CC,c⟧ := pr1 (pr1 (isColimCocone_ColimCocone CC c fc Hc)).

Lemma colimArrowCommutes {g : graph} {d : diagram g C} (CC : ColimCocone d)
  (c : C) (fc : ∀ (v : vertex g), C⟦dob d v,c⟧)
  (Hc : ∀ (u v : vertex g) (e : edge u v), dmor d e ;; fc v = fc u)
  (u : vertex g) :
  colimIn CC u ;; colimArrow CC c fc Hc = fc u.
Proof.
exact ((pr2 (pr1 (isColimCocone_ColimCocone CC _ fc Hc))) u).
Qed.

Lemma colimArrowUnique {g : graph} {d : diagram g C} (CC : ColimCocone d)
  (c : C) (fc : ∀ (v : vertex g), C⟦dob d v,c⟧)
  (Hc : ∀ (u v : vertex g) (e : edge u v), dmor d e ;; fc v = fc u)
  (k : C⟦colim CC,c⟧)
  (Hk : ∀ (u : vertex g), colimIn CC u ;; k = fc u) :
  k = colimArrow CC c fc Hc.
Proof.
now apply path_to_ctr, Hk.
Qed.

Lemma Cocone_postcompose {g : graph} {d : diagram g C}
  (c : C) (fc : ∀ (v : vertex g), C⟦dob d v,c⟧)
  (Hc : ∀ (u v : vertex g) (e : edge u v), dmor d e ;; fc v = fc u)
  (x : C) (f : C⟦c,x⟧) : ∀ u v (e : edge u v), (dmor d e ;; (fc v ;; f) = fc u ;; f).
Proof.
now intros u v e; rewrite assoc, Hc.
Qed.

Lemma colimArrowEta {g : graph} {d : diagram g C} (CC : ColimCocone d)
  (c : C) (f : C⟦colim CC,c⟧) :
    f = colimArrow CC c (λ u, colimIn CC u ;; f)
          (Cocone_postcompose _ _ (colimInCommutes CC) c f).
Proof.
now apply colimArrowUnique.
Qed.

Definition colimOfArrows {g : graph} {d1 d2 : diagram g C}
  (CC1 : ColimCocone d1) (CC2 : ColimCocone d2)
  (f : ∀ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∀ u v (e : edge u v), dmor d1 e ;; f v = f u ;; dmor d2 e) :
  C⟦colim CC1,colim CC2⟧.
Proof.
refine (colimArrow _ _ _ _).
- now intro u; apply (f u ;; colimIn CC2 u).
- abstract (intros u v e; simpl;
            now rewrite assoc, fNat, <- assoc, colimInCommutes).
Defined.

Lemma colimOfArrowsIn {g : graph} (d1 d2 : diagram g C)
  (CC1 : ColimCocone d1) (CC2 : ColimCocone d2)
  (f : ∀ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∀ u v (e : edge u v), dmor d1 e ;; f v = f u ;; dmor d2 e) :
    ∀ u, colimIn CC1 u ;; colimOfArrows CC1 CC2 f fNat =
         f u ;; colimIn CC2 u.
Proof.
now unfold colimOfArrows; intro u; rewrite colimArrowCommutes.
Qed.

Lemma preCompWithColimOfArrows_subproof {g : graph} {d1 d2 : diagram g C}
  (CC1 : ColimCocone d1) (CC2 : ColimCocone d2)
  (f : ∀ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∀ u v (e : edge u v), dmor d1 e ;; f v = f u ;; dmor d2 e)
  (x : C) (k : ∀ (u : vertex g), C⟦dob d2 u,x⟧)
  (Hx : ∀ (u v : vertex g) (e : edge u v), dmor d2 e ;; k v = k u) :
    ∀ (u v : vertex g) (e : edge u v),
      dmor d1 e;; (λ u0 : vertex g, f u0;; k u0) v =
      (λ u0 : vertex g, f u0;; k u0) u.
Proof.
intros u v e; simpl.
now rewrite <- (Hx u v e), !assoc, fNat.
Qed.

Lemma precompWithColimOfArrows {g : graph} (d1 d2 : diagram g C)
  (CC1 : ColimCocone d1) (CC2 : ColimCocone d2)
  (f : ∀ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∀ u v (e : edge u v), dmor d1 e ;; f v = f u ;; dmor d2 e)
  (x : C) (k : ∀ (u : vertex g), C⟦dob d2 u,x⟧)
  (Hx : ∀ (u v : vertex g) (e : edge u v), dmor d2 e ;; k v = k u) :
  colimOfArrows CC1 CC2 f fNat ;; colimArrow CC2 x k Hx =
  colimArrow CC1 x (λ u, f u ;; k u)
     (preCompWithColimOfArrows_subproof CC1 CC2 f fNat x k Hx).
Proof.
apply colimArrowUnique.
now intro u; rewrite assoc, colimOfArrowsIn, <- assoc, colimArrowCommutes.
Qed.

Lemma postcompWithColimArrow {g : graph} (D : diagram g C)
 (CC : ColimCocone D)
 (c : C) (fc : ∀ u, C⟦dob D u,c⟧)
 (Hc : ∀ (u v : vertex g) (e : edge u v), dmor D e ;; fc v = fc u)
 (d : C) (k : C⟦c,d⟧) :
   colimArrow CC c fc Hc ;; k =
   colimArrow CC d (λ u, fc u ;; k) (Cocone_postcompose c fc Hc d k).
Proof.
apply colimArrowUnique.
now intro u; rewrite assoc, colimArrowCommutes.
Qed.

Lemma colim_endo_is_identity {g : graph} (D : diagram g C)
  (CC : ColimCocone D)
  (k : colim CC ⇒ colim CC)
  (H : ∀ u, colimIn CC u ;; k = colimIn CC u) :
  identity _ = k.
Proof.
unfold ColimCocone in CC.
refine (uniqueExists _ _ ((pr2 CC) _ _ _) _ _ _ _).
- intros v.
  exact (pr2 (pr1 (pr1 CC)) v).
- intros u v e; simpl.
  now apply colimInCommutes.
- intros v; simpl.
  now apply id_right.
- intros v; simpl.
  now apply H.
Qed.

Definition Cocone_by_postcompose {g : graph} (D : diagram g C)
 (c : C) (fc : ∀ u, C⟦dob D u,c⟧)
 (Hc : ∀ (u v : vertex g) (e : edge u v), dmor D e ;; fc v = fc u) :
 ∀ (d : C) (k : C⟦c,d⟧),
 Σ (μ : ∀ (u : vertex g), C⟦dob D u,d⟧), ∀ (u v : vertex g) (e : edge u v), dmor D e ;; μ v = μ u.
Proof.
intros d k.
exists (λ u, fc u ;; k).
now apply Cocone_postcompose.
Defined.

Lemma isColim_weq_subproof1 {g : graph} (D : diagram g C)
  (c : C) (fc : ∀ u, C⟦dob D u,c⟧)
  (Hc : ∀ (u v : vertex g) (e : edge u v), dmor D e ;; fc v = fc u)
  (d : C) (k : C⟦c,d⟧) :
  ∀ u, fc u ;; k = pr1 (Cocone_by_postcompose D c fc Hc d k) u.
Proof.
now intro u.
Qed.

Lemma isColim_weq_subproof2 (g : graph) (D : diagram g C)
  (c : C) (fc : ∀ u, C⟦dob D u,c⟧) (Hc : ∀ u v e, dmor D e ;; fc v = fc u)
  (H : ∀ d, isweq (Cocone_by_postcompose D c fc Hc d))
  (d : C) (fd : ∀ u, C⟦dob D u,d⟧) (Hd : ∀ u v e, dmor D e ;; fd v = fd u)
  (u : vertex g) :
    fc u ;; invmap (weqpair _ (H d)) (tpair _ fd Hd) = fd u.
Proof.
rewrite (isColim_weq_subproof1 D c fc Hc d (invmap (weqpair _ (H d)) _) u).
set (p := homotweqinvweq (weqpair _ (H d)) (tpair _ fd Hd)); simpl in p.
now rewrite p.
Qed.

Lemma isColim_weq {g : graph} (D : diagram g C)
  (c : C) (fc : ∀ u, C⟦dob D u,c⟧)
  (Hc : ∀ (u v : vertex g) (e : edge u v), dmor D e ;; fc v = fc u) :
    isColimCocone D c fc Hc <-> ∀ d, isweq (Cocone_by_postcompose D c fc Hc d).
Proof.
split.
- intros H d.
  refine (gradth _ _ _ _).
  + intros k.
    exact (colimArrow (mk_ColimCocone D c fc Hc H) _ (pr1 k) (pr2 k)).
  + intro k; simpl.
    now apply pathsinv0, (colimArrowEta (mk_ColimCocone D c fc Hc H)).
  + simpl; intro k.
    apply total2_paths_second_isaprop.
    * now repeat (apply impred; intro); apply hsC.
    * destruct k as [k Hk]; simpl.
      apply funextsec; intro u.
      now apply (colimArrowCommutes (mk_ColimCocone D c fc Hc H)).
- intros H d fd Hd.
  refine (tpair _ _ _).
  + exists (invmap (weqpair _ (H d)) (tpair _ fd Hd)); intro u.
    now apply isColim_weq_subproof2.
  + intro t; apply total2_paths_second_isaprop;
      [ now apply impred; intro; apply hsC | ].
    destruct t as [t Ht]; simpl.
    apply (invmaponpathsweq (weqpair _ (H d))); simpl.
    apply total2_paths_second_isaprop;
      [ now repeat (apply impred; intro); apply hsC | simpl ].
    apply pathsinv0, funextsec; intro u; rewrite Ht.
    now apply isColim_weq_subproof2.
Defined.

End colim_def.

Section ColimFunctor.

Variable A C : precategory.
Variable HC : Colims C.
Variable hsC : has_homsets C.
Variable g : graph.
Variable D : diagram g [A, C, hsC].

Definition diagram_pointwise (a : A) : diagram g C.
Proof.
exists (fun v => pr1 (dob D v) a); intros u v e.
now apply (pr1 (dmor D e) a).
Defined.

Let HCg a := HC g (diagram_pointwise a).

Definition ColimFunctor_ob (a : A) : C := colim _ (HCg a).

Definition ColimFunctor_mor (a a' : A) (f : A⟦a, a'⟧)
  : ColimFunctor_ob a ⇒ ColimFunctor_ob a'.
Proof.
refine (colimOfArrows _ _ _ _ _).
- now intro u; apply (# (pr1 (dob D u)) f).
- abstract (now intros u v e; simpl; apply pathsinv0, (nat_trans_ax (dmor D e))).
Defined.

Definition ColimFunctor_data : functor_data A C :=
  tpair _ _ ColimFunctor_mor.

Lemma is_functor_ColimFunctor_data : is_functor ColimFunctor_data.
Proof.
split.
- intro a; simpl.
  apply pathsinv0, colim_endo_is_identity; intro u.
  unfold ColimFunctor_mor.
  now rewrite colimOfArrowsIn, (functor_id (dob D u)), id_left.
- intros a b c fab fbc; simpl; unfold ColimFunctor_mor.
  apply pathsinv0.
  eapply pathscomp0; [now apply precompWithColimOfArrows|].
  apply pathsinv0, colimArrowUnique; intro u.
  now rewrite colimOfArrowsIn, (functor_comp (dob D u)), assoc.
Qed.

Definition ColimFunctor : functor A C :=
  tpair _ _ is_functor_ColimFunctor_data.

Definition colim_nat_trans_in_data v : [A, C, hsC] ⟦ dob D v, ColimFunctor ⟧.
Proof.
refine (tpair _ _ _).
- intro a; exact (colimIn C (HCg a) v).
- intros a a' f.
  now apply pathsinv0, (colimOfArrowsIn _ _ _ (HCg a) (HCg a')).
Defined.

Lemma ColimFunctor_unique (F : [A, C, hsC])
  (Fc : ∀ v : vertex g, [A, C, hsC] ⟦ dob D v, F ⟧)
  (Hc : ∀ (u v : vertex g) (e : edge u v), dmor D e ;; Fc v = Fc u) :
   iscontr (Σ x : [A, C, hsC] ⟦ ColimFunctor, F ⟧,
            ∀ v : vertex g, colim_nat_trans_in_data v ;; x = Fc v).
Proof.
refine (tpair _ _ _).
- refine (tpair _ _ _).
  + refine (tpair _ _ _).
    * intro a.
      apply (colimArrow _ (HCg a) _ (λ v, pr1 (Fc v) a)).
      intros u v e.
      now apply (nat_trans_eq_pointwise (Hc u v e)).
    * intros a a' f; simpl.
      eapply pathscomp0; [now apply precompWithColimOfArrows|].
      apply pathsinv0.
      eapply pathscomp0; [now apply postcompWithColimArrow|].
      apply colimArrowUnique; intro u.
      eapply pathscomp0; [now apply colimArrowCommutes|].
      now apply pathsinv0, nat_trans_ax.
  + intro u.
    apply (nat_trans_eq hsC); simpl; intro a.
    now apply (colimArrowCommutes _ (HCg a)).
- intro t; destruct t as [t1 t2].
  apply (total2_paths_second_isaprop); simpl.
  + apply impred; intro u.
    now apply functor_category_has_homsets.
  + apply (nat_trans_eq hsC); simpl; intro a.
    apply colimArrowUnique; intro u.
    now rewrite <- (t2 u).
Qed.

Lemma ColimFunctorCocone : ColimCocone [A,C,hsC] D.
Proof.
refine (tpair _ _ _).
- refine (tpair _ _ _).
  + exists ColimFunctor.
    now apply colim_nat_trans_in_data.
  + abstract (now intros u v e; apply (nat_trans_eq hsC);
                  intro a; apply (colimInCommutes C (HCg a))).
- now intros F Fc Hc; simpl; apply (ColimFunctor_unique _ _ Hc).
Defined.

End ColimFunctor.

Lemma ColimsFunctorCategory (A C : precategory) (hsC : has_homsets C)
  (HC : Colims C) : Colims [A,C,hsC].
Proof.
now intros g d; apply ColimFunctorCocone.
Qed.

