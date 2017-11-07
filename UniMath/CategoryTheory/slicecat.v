(** **********************************************************

Anders Mörtberg, Benedikt Ahrens, 2015-2016

*************************************************************)

(** **********************************************************

Contents:

- Definition of slice precategories, C/x (assumes that C has homsets)

- Proof that the forgetful functor [slicecat_to_cat] : C/x → C is
  a left adjoint if C has binary products ([is_left_adjoint_slicecat_to_cat])

- Proof that C/x is a univalent_category if C is

- Proof that any morphism C[x,y] induces a functor from C/x to C/y
  ([slicecat_functor])

- Colimits in slice categories ([slice_precat_colims])

- Binary products in slice categories of categories with pullbacks
  ([BinProducts_slice_precat])

- Binary coproducts in slice categories of categories with binary
  coproducts ([BinCoproducts_slice_precat])

- Coproducts in slice categories of categories with coproducts
  ([Coproducts_slice_precat])

- Initial object in slice categories with initial object
  ([Initial_slice_precat])

- Terminal object in slice categories ([Terminal_slice_precat])

- Base change functor ([base_change_functor]) and proof that
  it is right adjoint to slicecat_functor

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.exponentials.

Local Open Scope cat.

(** * Definition of slice categories *)
(** Given a category C and x : obj C. The slice category C/x is given by:

- obj C/x: pairs (a,f) where f : a -> x

- morphism (a,f) -> (b,g): morphism h : a -> b with
<<
           h
       a - - -> b
       |       /
       |     /
     f |   / g
       | /
       v
       x
>>
    where h · g = f

*)
Section slice_precat_def.

Context (C : precategory) (x : C).

(* Accessor functions *)
Definition slicecat_ob := total2 (λ a, C⟦a,x⟧).
Definition slicecat_mor (f g : slicecat_ob) := total2 (λ h, pr2 f = h · pr2 g).

Definition slicecat_ob_object (f : slicecat_ob) : ob C := pr1 f.

Definition slicecat_ob_morphism (f : slicecat_ob) : C⟦slicecat_ob_object f, x⟧ := pr2 f.

(* Accessor functions *)
Definition slicecat_mor_morphism {f g : slicecat_ob} (h : slicecat_mor f g) :
  C⟦slicecat_ob_object f, slicecat_ob_object g⟧ := pr1 h.

Definition slicecat_mor_comm {f g : slicecat_ob} (h : slicecat_mor f g) :
  (slicecat_ob_morphism f) = (slicecat_mor_morphism h) · (slicecat_ob_morphism g) := pr2 h.

Definition slice_precat_ob_mor : precategory_ob_mor := (slicecat_ob,,slicecat_mor).

Definition id_slice_precat (c : slice_precat_ob_mor) : c --> c :=
  tpair _ _ (!(id_left (pr2 c))).

Definition comp_slice_precat_subproof {a b c : slice_precat_ob_mor}
  (f : a --> b) (g : b --> c) : pr2 a = (pr1 f · pr1 g) · pr2 c.
Proof.
  rewrite <- assoc, (!(pr2 g)).
  exact (pr2 f).
Qed.

Definition comp_slice_precat (a b c : slice_precat_ob_mor)
                             (f : a --> b) (g : b --> c) : a --> c :=
  (pr1 f · pr1 g,,comp_slice_precat_subproof _ _).

Definition slice_precat_data : precategory_data :=
  precategory_data_pair _ id_slice_precat comp_slice_precat.

Lemma is_precategory_slice_precat_data (hsC : has_homsets C) :
  is_precategory slice_precat_data.
Proof.
repeat split; simpl.
* intros a b f.
  case f; clear f; intros h hP.
  apply subtypePairEquality; [ intro; apply hsC | apply id_left ].
* intros a b f.
  case f; clear f; intros h hP.
  apply subtypePairEquality; [ intro; apply hsC | apply id_right ].
* intros a b c d f g h.
  apply subtypePairEquality; [ intro; apply hsC | apply assoc ].
Qed.

Definition slice_precat (hsC : has_homsets C) : precategory :=
  (_,,is_precategory_slice_precat_data hsC).


End slice_precat_def.

Section slice_precat_theory.

Context {C : precategory} (hsC : has_homsets C) (x : C).

Local Notation "C / X" := (slice_precat C X hsC).

Lemma has_homsets_slice_precat : has_homsets (C / x).
Proof.
intros a b.
case a; clear a; intros a f; case b; clear b; intros b g; simpl.
apply (isofhleveltotal2 2); [ apply hsC | intro h].
now apply isasetaprop; apply hsC.
Qed.

Lemma eq_mor_slicecat (af bg : C / x) (f g : C/x⟦af,bg⟧) : pr1 f = pr1 g -> f = g.
Proof.
now intro heq; apply (total2_paths_f heq); apply hsC.
Qed.

Lemma eq_iso_slicecat (af bg : C / x) (f g : iso af bg) : pr1 f = pr1 g -> f = g.
Proof.
case g; case f; clear f g; simpl; intros f fP g gP eq.
refine (subtypePairEquality _ eq).
now intro; apply isaprop_is_iso.
Qed.

(** It suffices that the underlying morphism is an iso to get an iso in
    the slice category *)
Lemma iso_to_slice_precat_iso (af bg : C / x) (h : af --> bg)
  (isoh : is_iso (pr1 h)) : is_iso h.
Proof.
case (is_z_iso_from_is_iso _ isoh); intros hinv [h1 h2].
assert (pinv : hinv · pr2 af = pr2 bg).
{ now rewrite <- id_left, <- h2, <- assoc, (!(pr2 h)). }
apply is_iso_from_is_z_iso.
exists (hinv,,!pinv).
now split; (apply subtypePairEquality; [ intro; apply hsC |]).
Qed.

(** An iso in the slice category gives an iso in the base category *)
Lemma slice_precat_iso_to_iso  (af bg : C / x) (h : af --> bg)
  (p : is_iso h) : is_iso (pr1 h).
Proof.
case (is_z_iso_from_is_iso _ p); intros hinv [h1 h2].
apply is_iso_from_is_z_iso.
exists (pr1 hinv); split.
- apply (maponpaths pr1 h1).
- apply (maponpaths pr1 h2).
Qed.

Lemma iso_weq (af bg : C / x) :
  weq (iso af bg) (total2 (fun h : iso (pr1 af) (pr1 bg) => pr2 af = h · pr2 bg)).
Proof.
apply (weqcomp (weqtotal2asstor _ _)).
apply invweq.
apply (weqcomp (weqtotal2asstor _ _)).
apply weqfibtototal; intro h; simpl.
apply (weqcomp (weqdirprodcomm _ _)).
apply weqfibtototal; intro p.
apply weqimplimpl; try apply isaprop_is_iso.
- now intro hp; apply iso_to_slice_precat_iso.
- now intro hp; apply (slice_precat_iso_to_iso _ _ _ hp).
Defined.

(** The forgetful functor from C/x to C *)
Definition slicecat_to_cat : functor (C / x) C.
Proof.
use mk_functor.
+ use tpair.
  - apply pr1.
  - intros a b; apply pr1.
+ now split.
Defined.

(** Right adjoint to slicecat_to_cat *)
Definition cat_to_slicecat (BPC : BinProducts C) : functor C (C / x).
Proof.
use mk_functor.
+ use tpair.
  * intro y.
    exists (BinProductObject _ (BPC x y)).
    apply BinProductPr1.
  * intros A B f; cbn.
    use tpair.
    - apply (BinProductOfArrows _ _ _ (identity x) f).
    - abstract (cbn; now rewrite BinProductOfArrowsPr1, id_right).
+ split.
  * intros A; apply eq_mor_slicecat;
    now apply pathsinv0, BinProductArrowUnique; rewrite id_left, id_right.
  * intros a1 a2 a3 f1 f2; apply eq_mor_slicecat; simpl;
    now rewrite BinProductOfArrows_comp, id_right.
Defined.

Lemma is_left_adjoint_slicecat_to_cat (BPC : BinProducts C) :
  is_left_adjoint slicecat_to_cat.
Proof.
exists (cat_to_slicecat BPC).
use mk_are_adjoints.
+ use mk_nat_trans.
  * simpl; intros F.
    exists (BinProductArrow _ _ (pr2 F) (identity _)); simpl.
    abstract (now rewrite BinProductPr1Commutes).
  * intros Y Z F; apply eq_mor_slicecat; simpl.
    rewrite postcompWithBinProductArrow.
    apply BinProductArrowUnique.
    - now rewrite <- assoc, BinProductPr1Commutes, id_right, (pr2 F).
    - now rewrite <- assoc, BinProductPr2Commutes, id_left, id_right.
+ use mk_nat_trans.
  * intros Y.
    apply BinProductPr2.
  * now intros Y Z f; apply BinProductOfArrowsPr2.
+ split.
  * intros Y; cbn.
    now rewrite BinProductPr2Commutes.
  * intros Y; apply eq_mor_slicecat; cbn.
    rewrite postcompWithBinProductArrow.
    apply pathsinv0, BinProductArrowUnique; trivial.
    now rewrite id_right, id_left.
Defined.

End slice_precat_theory.

(** * Proof that C/x is a univalent_category if C is. *)
(** This is exercise 9.1 in the HoTT book *)
Section slicecat_theory.

Context {C : precategory} (is_catC : is_univalent C) (x : C).

Local Notation "C / x" := (slice_precat C x (pr2 is_catC)).

Lemma id_weq_iso_slicecat (af bg : C / x) : (af = bg) ≃ (iso af bg).
Proof.
set (a := pr1 af); set (f := pr2 af); set (b := pr1 bg); set (g := pr2 bg).

assert (weq1 : weq (af = bg)
                   (total2 (fun (p : a = b) => transportf _ p (pr2 af) = g))).
  apply (total2_paths_equiv _ af bg).

assert (weq2 : weq (total2 (fun (p : a = b) => transportf _ p (pr2 af) = g))
                   (total2 (fun (p : a = b) => idtoiso (! p) · f = g))).
  apply weqfibtototal; intro p.
  rewrite idtoiso_precompose.
  apply idweq.

assert (weq3 : weq (total2 (fun (p : a = b) => idtoiso (! p) · f = g))
                   (total2 (λ h : iso a b, f = h · g))).
  apply (weqbandf (weqpair _ ((pr1 is_catC) a b))); intro p.
  rewrite idtoiso_inv; simpl.
  apply weqimplimpl; simpl; try apply (pr2 is_catC); intro Hp.
    rewrite <- Hp, assoc, iso_inv_after_iso, id_left; apply idpath.
  rewrite Hp, assoc, iso_after_iso_inv, id_left; apply idpath.

assert (weq4 : weq (total2 (λ h : iso a b, f = h · g)) (iso af bg)).
  apply invweq; apply iso_weq.

apply (weqcomp weq1 (weqcomp weq2 (weqcomp weq3 weq4))).
Defined.

Lemma is_univalent_slicecat : is_univalent (C / x).
Proof.
split; [| apply has_homsets_slice_precat]; simpl; intros a b.
set (h := id_weq_iso_slicecat a b).
apply (isweqhomot h); [intro p|case h; trivial].
destruct p.
now apply eq_iso, eq_mor_slicecat.
Qed.

End slicecat_theory.

(** * A morphism x --> y in the base category induces a functor between C/x and C/y *)
Section slicecat_functor_def.

Context {C : precategory} (hsC : has_homsets C) {x y : C} (f : C⟦x,y⟧).

Local Notation "C / X" := (slice_precat C X hsC).

Definition slicecat_functor_ob (af : C / x) : C / y :=
  (pr1 af,,pr2 af · f).

Lemma slicecat_functor_subproof (af bg : C / x) (h : C/x⟦af,bg⟧) :
  pr2 af · f = pr1 h · (pr2 bg · f).
Proof.
now rewrite assoc, <- (pr2 h).
Qed.

Definition slicecat_functor_data : functor_data (C / x) (C / y) :=
  tpair (λ F, ∏ a b, C/x⟦a,b⟧ → C/y⟦F a,F b⟧) slicecat_functor_ob
        (λ a b h, (pr1 h,,slicecat_functor_subproof _ _ h)).

Lemma is_functor_slicecat_functor : is_functor slicecat_functor_data.
Proof.
split.
- now intros a; apply eq_mor_slicecat.
- now intros a b c g h; apply eq_mor_slicecat.
Qed.

Definition slicecat_functor : functor (C / x) (C / y) :=
  (slicecat_functor_data,,is_functor_slicecat_functor).

End slicecat_functor_def.

Section slicecat_functor_theory.

Context {C : precategory} (hsC : has_homsets C).

Local Notation "C / X" := (slice_precat C X hsC).

Lemma slicecat_functor_identity_ob (x : C) :
  slicecat_functor_ob hsC (identity x) = functor_identity (C / x).
Proof.
apply funextsec; intro af.
unfold slicecat_functor_ob.
now rewrite id_right.
Defined.

Lemma slicecat_functor_identity (x : C) :
  slicecat_functor _ (identity x) = functor_identity (C / x).
Proof.
apply (functor_eq _ _ (has_homsets_slice_precat _ _)); simpl.
apply (two_arg_paths_f (slicecat_functor_identity_ob _)).
apply funextsec; intros [a f].
apply funextsec; intros [b g].
apply funextsec; intros [h hh].
rewrite transport_of_functor_map_is_pointwise; simpl in *.
unfold slicecat_mor.
rewrite transportf_total2.
apply subtypePairEquality; [intro; apply hsC | ].
rewrite transportf_total2; simpl.
unfold slicecat_functor_identity_ob.
rewrite toforallpaths_funextsec; simpl.
case (id_right f).
now case (id_right g).
Qed.

Lemma slicecat_functor_comp_ob {x y z : C} (f : C⟦x,y⟧) (g : C⟦y,z⟧) :
  slicecat_functor_ob hsC (f · g) =
  (λ a, slicecat_functor_ob hsC g (slicecat_functor_ob hsC f a)).
Proof.
apply funextsec; intro af.
now unfold slicecat_functor_ob; rewrite assoc.
Defined.

(* This proof is not so nice... *)
Lemma slicecat_functor_comp {x y z : C} (f : C⟦x,y⟧) (g : C⟦y,z⟧) :
  slicecat_functor hsC (f · g) =
  functor_composite (slicecat_functor _ f) (slicecat_functor _ g).
Proof.
apply (functor_eq _ _ (has_homsets_slice_precat _ _)); simpl.
unfold slicecat_functor_data; simpl.
unfold functor_composite_data; simpl.
apply (two_arg_paths_f (slicecat_functor_comp_ob _ _)).
apply funextsec; intros [a fax].
apply funextsec; intros [b fbx].
apply funextsec; intros [h hh].
rewrite transport_of_functor_map_is_pointwise; simpl in *.
unfold slicecat_mor.
rewrite transportf_total2.
apply subtypePairEquality; [intro; apply hsC | ].
rewrite transportf_total2; simpl.
unfold slicecat_functor_comp_ob.
rewrite toforallpaths_funextsec; simpl.
assert (H1 : transportf (fun x : C / z => pr1 x --> b)
               (Foundations.PartA.internal_paths_rew_r _ _ _
                 (λ p, tpair _ a p = tpair _ a _) (idpath (tpair _ a _))
                 (assoc fax f g)) h = h).
  case (assoc fax f g); apply idpath.
assert (H2 : ∏ h', h' = h ->
             transportf (fun x : C / z => a --> pr1 x)
                        (Foundations.PartA.internal_paths_rew_r _ _ _
                           (λ p, tpair _ b p = tpair _ b _) (idpath _)
                           (assoc fbx f g)) h' = h).
  intros h' eq.
  case (assoc fbx f g); rewrite eq; apply idpath.
now apply H2.
Qed.

End slicecat_functor_theory.

(** * Colimits in slice categories *)
Section slicecat_colimits.

Context (g : graph) {C : precategory} (hsC : has_homsets C) (x : C).

Local Notation "C / X" := (slice_precat C X hsC).

Let U : functor (C / x) C := slicecat_to_cat hsC x.

Lemma slice_precat_isColimCocone (d : diagram g (C / x)) (a : C / x)
  (cc : cocone d a)
  (H : isColimCocone (mapdiagram U d) (U a) (mapcocone U d cc)) :
  isColimCocone d a cc.
Proof.
set (CC := mk_ColimCocone _ _ _ H).
intros y ccy.
use unique_exists.
+ use tpair; simpl.
  * apply (colimArrow CC), (mapcocone U _ ccy).
  * abstract (apply pathsinv0;
              eapply pathscomp0; [apply (postcompWithColimArrow _ CC (pr1 y) (mapcocone U d ccy))|];
              apply pathsinv0, (colimArrowUnique CC); intros u; simpl;
              eapply pathscomp0; [apply (!(pr2 (coconeIn cc u)))|];
              apply (pr2 (coconeIn ccy u))).
+ abstract (intros u; apply subtypeEquality; [intros xx; apply hsC|]; simpl;
            apply (colimArrowCommutes CC)).
+ abstract (intros f; simpl; apply impred; intro u; apply has_homsets_slice_precat).
+ abstract (intros f; simpl; intros Hf;
            apply eq_mor_slicecat; simpl;
            apply (colimArrowUnique CC); intro u; cbn;
            now rewrite <- (Hf u)).
Defined.

Lemma slice_precat_ColimCocone (d : diagram g (C / x))
  (H : ColimCocone (mapdiagram U d)) :
  ColimCocone d.
Proof.
use mk_ColimCocone.
- use tpair.
  + apply (colim H).
  + apply colimArrow.
    use mk_cocone.
    * intro v; apply (pr2 (dob d v)).
    * abstract (intros u v e; apply (! pr2 (dmor d e))).
- use mk_cocone.
  + intro v; simpl.
    use tpair; simpl.
    * apply (colimIn H v).
    * abstract (apply pathsinv0, (colimArrowCommutes H)).
  + abstract (intros u v e; apply eq_mor_slicecat, (coconeInCommutes (colimCocone H))).
- intros y ccy.
  use unique_exists.
  + use tpair; simpl.
    * apply colimArrow, (mapcocone U _ ccy).
    * abstract (apply pathsinv0, colimArrowUnique; intros v; simpl; rewrite assoc;
                eapply pathscomp0;
                  [apply cancel_postcomposition,
                        (colimArrowCommutes H _ (mapcocone U _ ccy) v)|];
                destruct ccy as [f Hf]; simpl; apply (! pr2 (f v))).
  + abstract (intro v; apply eq_mor_slicecat; simpl;
              apply (colimArrowCommutes _ _ (mapcocone U d ccy))).
  + abstract (simpl; intros f; apply impred; intro v; apply has_homsets_slice_precat).
  + abstract (intros f Hf; apply eq_mor_slicecat; simpl in *; apply colimArrowUnique;
              intros v; apply (maponpaths pr1 (Hf v))).
Defined.

End slicecat_colimits.

Lemma slice_precat_colims_of_shape {C : precategory} (hsC : has_homsets C)
  {g : graph} (x : C) (CC : Colims_of_shape g C) :
  Colims_of_shape g (slice_precat C x hsC).
Proof.
now intros y; apply slice_precat_ColimCocone, CC.
Defined.

Lemma slice_precat_colims {C : precategory} (hsC : has_homsets C) (x : C) (CC : Colims C) :
  Colims (slice_precat C x hsC).
Proof.
now intros g d; apply slice_precat_ColimCocone, CC.
Defined.

(** * Moving between Binary products in slice categories and Pullbacks in base category *)
Section slicecat_binproducts.

Context {C : precategory} (hsC : has_homsets C).

Local Notation "C / X" := (slice_precat C X hsC).

Definition pullback_to_slice_binprod {A B Z : C} {f : A --> Z} {g : B --> Z} :
  Pullback f g -> BinProductCone (C / Z) (A ,, f) (B ,, g).
Proof.
  intros P.
  refine (((PullbackObject P ,, (PullbackPr1 P) · f) ,, (((PullbackPr1 P) ,, idpath _) ,, (((PullbackPr2 P) ,, (PullbackSqrCommutes P))))) ,, _).
  intros Y [j jeq] [k keq]; simpl in jeq , keq.
  use unique_exists.
  + use tpair.
    ++ apply (PullbackArrow P _ j k).
       abstract (now rewrite <- jeq , keq).
    ++ abstract (cbn; now rewrite assoc, PullbackArrow_PullbackPr1, <- jeq).
  + abstract (split; apply eq_mor_slicecat; simpl;
              [ apply PullbackArrow_PullbackPr1 | apply PullbackArrow_PullbackPr2 ]).
  + abstract (now intros h; apply isapropdirprod; apply has_homsets_slice_precat).
  + abstract (intros h [H1 H2]; apply eq_mor_slicecat, PullbackArrowUnique;
             [ apply (maponpaths pr1 H1) | apply (maponpaths pr1 H2) ]).
Defined.

Definition BinProducts_slice_precat (PC : Pullbacks C) : ∏ x, BinProducts (C / x) :=
 λ x a b, pullback_to_slice_binprod (PC _ _ _ (pr2 a) (pr2 b)).

Definition slice_binprod_to_pullback {Z : C} {AZ BZ : C / Z} :
  BinProductCone (C / Z) AZ BZ → Pullback (pr2 AZ) (pr2 BZ).
Proof.
  induction AZ as [A f].
  induction BZ as [B g].
  intros [[[P h] [[l leq] [r req]]] PisProd].
  refine ((P ,, l ,, r) ,, (! leq @ req) ,, _).
  intros Y j k Yeq. simpl in *.
  use unique_exists.
  + exact (pr1 (pr1 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))).
  + abstract (exact (maponpaths pr1 (pr1 (pr2 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))) ,,
                                maponpaths pr1 (pr2 (pr2 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))))).
  + abstract (intros x; apply isofhleveldirprod; apply (hsC _ _)).
  + intros t teqs.
    refine (maponpaths pr1 (maponpaths pr1 (pr2 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq)) ((t ,, (maponpaths (λ x, x · f) (!(pr1 teqs)) @ !(assoc _ _ _) @ maponpaths (λ x, t · x) (!leq))) ,, _)))).
    abstract (split; apply eq_mor_slicecat; [exact (pr1 teqs) | exact (pr2 teqs)]).
Defined.

Definition Pullbacks_from_slice_BinProducts (BP : ∏ x, BinProducts (C / x)) : Pullbacks C :=
  λ x a b f g, slice_binprod_to_pullback (BP x (a ,, f) (b ,, g)).

End slicecat_binproducts.

(** * Binary coproducts in slice categories of categories with binary coproducts *)
Section slicecat_bincoproducts.

Context {C : precategory} (hsC : has_homsets C) (BC : BinCoproducts C).

Local Notation "C / X" := (slice_precat C X hsC).

Lemma BinCoproducts_slice_precat (x : C) : BinCoproducts (C / x).
Proof.
intros a b.
use mk_BinCoproductCocone.
+ exists (BinCoproductObject _ (BC (pr1 a) (pr1 b))).
  apply (BinCoproductArrow _ _ (pr2 a) (pr2 b)).
+ use tpair.
  - apply BinCoproductIn1.
  - abstract (cbn; now rewrite BinCoproductIn1Commutes).
+ use tpair.
  - apply BinCoproductIn2.
  - abstract (cbn; now rewrite BinCoproductIn2Commutes).
+ intros c f g.
  use unique_exists.
  - exists (BinCoproductArrow _ _ (pr1 f) (pr1 g)).
    abstract (apply pathsinv0, BinCoproductArrowUnique;
      [ now rewrite assoc, (BinCoproductIn1Commutes C _ _ (BC (pr1 a) (pr1 b))), (pr2 f)
      | now rewrite assoc, (BinCoproductIn2Commutes C _ _ (BC (pr1 a) (pr1 b))), (pr2 g)]).
  - abstract (split; apply eq_mor_slicecat; simpl;
             [ apply BinCoproductIn1Commutes | apply BinCoproductIn2Commutes ]).
  - abstract (intros y; apply isapropdirprod; apply has_homsets_slice_precat).
  - abstract (now intros y [<- <-]; apply eq_mor_slicecat, BinCoproductArrowUnique).
Defined.

End slicecat_bincoproducts.

(** * Coproducts in slice categories of categories with coproducts *)
Section slicecat_coproducts.

Context {C : precategory} (hsC : has_homsets C) (I : UU) (BC : Coproducts I C).

Local Notation "C / X" := (slice_precat C X hsC).

Lemma Coproducts_slice_precat (x : C) : Coproducts I (C / x).
Proof.
intros a.
use mk_CoproductCocone.
+ exists (CoproductObject _ _ (BC (λ i, pr1 (a i)))).
  apply CoproductArrow; intro i; apply (pr2 (a i)).
+ intro i; use tpair; simpl.
  - apply (CoproductIn I C (BC (λ i, pr1 (a i))) i).
  - abstract (now rewrite (CoproductInCommutes I C _ (BC (λ i, pr1 (a i))))).
+ intros c f.
  use unique_exists.
  - exists (CoproductArrow _ _ _ (λ i, pr1 (f i))).
    abstract (simpl; apply pathsinv0, CoproductArrowUnique; intro i;
              now rewrite assoc, (CoproductInCommutes _ _ _ (BC (λ i, pr1 (a i)))), (pr2 (f i))).
  - abstract (now intros i;
              apply eq_mor_slicecat, (CoproductInCommutes _ _ _ (BC (λ i0 : I, pr1 (a i0))))).
  - abstract (now intros y; apply impred; intro i; apply has_homsets_slice_precat).
  - abstract (simpl; intros y Hy;
              apply eq_mor_slicecat, CoproductArrowUnique;
              intros i; apply (maponpaths pr1 (Hy i))).
Defined.

End slicecat_coproducts.

Section slicecat_initial.

Context {C : precategory} (hsC : has_homsets C) (IC : Initial C).

Local Notation "C / X" := (slice_precat C X hsC).

Lemma Initial_slice_precat (x : C) : Initial (C / x).
Proof.
use mk_Initial.
- use tpair.
  + apply (InitialObject IC).
  + apply InitialArrow.
- intros y.
  use unique_exists; simpl.
  * apply InitialArrow.
  * abstract (now apply pathsinv0, InitialArrowUnique).
  * abstract (now intros f; apply hsC).
  * abstract (now intros f Hf; apply InitialArrowUnique).
Defined.

End slicecat_initial.

Section slicecat_terminal.

Context {C : precategory} (hsC : has_homsets C).

Local Notation "C / X" := (slice_precat C X hsC).

Lemma Terminal_slice_precat (x : C) : Terminal (C / x).
Proof.
use mk_Terminal.
- use tpair.
  + apply x.
  + apply (identity x).
- intros y.
  use unique_exists; simpl.
  * apply (pr2 y).
  * abstract (now rewrite id_right).
  * abstract (now intros f; apply hsC).
  * abstract (now intros f ->; rewrite id_right).
Defined.

End slicecat_terminal.

(** Base change functor: https://ncatlab.org/nlab/show/base+change *)
Section base_change.

Context {C : precategory} (hsC : has_homsets C) (PC : Pullbacks C).

Local Notation "C / X" := (slice_precat C X hsC).

Definition base_change_functor_data {c c' : C} (g : C⟦c,c'⟧) : functor_data (C / c') (C / c).
Proof.
use tpair.
- intros Af'.
  exists (PullbackObject (PC _ _ _ g (pr2 Af'))).
  apply PullbackPr1.
- intros a b f.
  use tpair; simpl.
  + use PullbackArrow.
    * apply PullbackPr1.
    * apply (PullbackPr2 _ · pr1 f).
    * abstract (now rewrite <- assoc, <- (pr2 f), PullbackSqrCommutes).
  + abstract (now rewrite PullbackArrow_PullbackPr1).
Defined.

Lemma is_functor_base_change_functor {c c' : C} (g : C⟦c,c'⟧) :
 is_functor (base_change_functor_data g).
Proof.
split.
- intros x; apply (eq_mor_slicecat hsC); simpl.
  now apply pathsinv0, PullbackArrowUnique; rewrite id_left, ?id_right.
- intros x y z f1 f2; apply (eq_mor_slicecat hsC); simpl.
  apply pathsinv0, PullbackArrowUnique.
  + now rewrite <- assoc, !PullbackArrow_PullbackPr1.
  + now rewrite <- assoc, PullbackArrow_PullbackPr2, !assoc,
            PullbackArrow_PullbackPr2.
Qed.

Definition base_change_functor {c c' : C} (g : C⟦c,c'⟧) : functor (C / c') (C / c) :=
  (base_change_functor_data g,,is_functor_base_change_functor g).

Local Definition eta {c c' : C} (g : C⟦c,c'⟧) :
  nat_trans (functor_identity (C / c))
            (functor_composite (slicecat_functor hsC g) (base_change_functor g)).
Proof.
use mk_nat_trans.
- intros x.
  use tpair; simpl.
  + use (PullbackArrow _ _ (pr2 x) (identity _)).
    abstract (now rewrite id_left).
  + abstract (now rewrite PullbackArrow_PullbackPr1).
- intros x y f; apply eq_mor_slicecat; simpl.
  eapply pathscomp0; [apply postCompWithPullbackArrow|].
  apply pathsinv0, PullbackArrowUnique.
  + now rewrite <- assoc, !PullbackArrow_PullbackPr1, <- (pr2 f).
  + now rewrite <- assoc, PullbackArrow_PullbackPr2, assoc,
                PullbackArrow_PullbackPr2, id_right, id_left.
Defined.

Local Definition eps {c c' : C} (g : C⟦c,c'⟧) :
  nat_trans (functor_composite (base_change_functor g) (slicecat_functor hsC g))
            (functor_identity (C / c')).
Proof.
use mk_nat_trans.
- intros x.
  exists (PullbackPr2 _); simpl.
  abstract (now apply PullbackSqrCommutes).
- intros x  y f; apply eq_mor_slicecat; simpl.
  now rewrite PullbackArrow_PullbackPr2.
Defined.

Local Lemma form_adjunction_eta_eps {c c' : C} (g : C⟦c,c'⟧) :
  form_adjunction (slicecat_functor hsC g) (base_change_functor g) (eta g) (eps g).
Proof.
use tpair.
- now intros x; apply eq_mor_slicecat; simpl; rewrite PullbackArrow_PullbackPr2.
- intros x; apply (eq_mor_slicecat hsC); simpl.
  apply pathsinv0, PullbackEndo_is_identity.
  + now rewrite <- assoc, !PullbackArrow_PullbackPr1.
  + now rewrite <- assoc, PullbackArrow_PullbackPr2, assoc,
                PullbackArrow_PullbackPr2, id_left.
Qed.

Lemma are_adjoints_slicecat_functor_base_change {c c' : C} (g : C⟦c,c'⟧) :
  are_adjoints (slicecat_functor hsC g) (base_change_functor g).
Proof.
exists (eta g,,eps g).
exact (form_adjunction_eta_eps g).
Defined.

(** If the base change functor has a right adjoint, called dependent product, then C / c has
    exponentials. The formal proof is inspired by Proposition 2.1 from:
    https://ncatlab.org/nlab/show/locally+cartesian+closed+category#in_category_theory
*)
Section dependent_product.

Context (H : ∏ {c c' : C} (g : C⟦c,c'⟧), is_left_adjoint (base_change_functor g)).

Let dependent_product_functor {c c' : C} (g : C⟦c,c'⟧) :
  functor (C / c) (C / c') := right_adjoint (H c c' g).

Let BPC c : BinProducts (C / c) := @BinProducts_slice_precat C hsC PC c.

Lemma const_prod_functor1_slicecat c (Af : C / c) :
  constprod_functor1 (BPC c) Af =
  functor_composite (base_change_functor (pr2 Af)) (slicecat_functor hsC (pr2 Af)).
Proof.
apply functor_eq; try apply has_homsets_slice_precat.
use functor_data_eq; try trivial.
intros x y f; apply (eq_mor_slicecat hsC); simpl.
apply PullbackArrowUnique.
- now rewrite PullbackArrow_PullbackPr1, id_right.
- now rewrite PullbackArrow_PullbackPr2.
Defined.

Lemma dependent_product_to_exponentials c : has_exponentials (BPC c).
Proof.
intros Af.
use tpair.
+ apply (functor_composite (base_change_functor (pr2 Af))
                           (dependent_product_functor (pr2 Af))).
+ rewrite const_prod_functor1_slicecat.
  apply are_adjoints_functor_composite.
  - apply (pr2 (H _ _ _)).
  - apply are_adjoints_slicecat_functor_base_change.
Defined.

End dependent_product.
End base_change.