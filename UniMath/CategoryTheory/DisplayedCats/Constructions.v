
(** Some important constructions on displayed categories

Partial contents:

- Full subcategory as total category of a displayed category
- Displayed category given by a structure on objects and a proposition
   on morphisms of the base category
- Direct products of displayed categories (and their projections)
  - [dirprod_cat D1 D2]
  - [dirprodpr1_functor], [dirprodpr2_functor]
- Sigmas of displayed categories
- Displayed functor cat
- Fiber cats
*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Open Scope cat.
Local Open Scope mor_disp_scope.

Section Auxiliary.

(* TODO: perhaps upstream; consider name *)
Lemma total2_reassoc_paths {A} {B : A → UU} {C : (∑ a, B a) -> UU}
    (BC : A -> UU := λ a, ∑ b, C (a,,b))
    {a1 a2 : A} (bc1 : BC a1) (bc2 : BC a2)
    (ea : a1 = a2)
    (eb : transportf _ ea (pr1 bc1) = pr1 bc2)
    (ec : transportf C (two_arg_paths_f (*was total2_paths2*) ea eb) (pr2 bc1) = pr2 bc2)
  : transportf _ ea bc1 = bc2.
Proof.
  destruct ea, bc1 as [b1 c1], bc2 as [b2 c2].
  cbn in *; destruct eb, ec.
  apply idpath.
Defined.

(* TODO: as for non-primed version above *)
Lemma total2_reassoc_paths' {A} {B : A → UU} {C : (∑ a, B a) -> UU}
    (BC : A -> UU := λ a, ∑ b, C (a,,b))
    {a1 a2 : A} (bc1 : BC a1) (bc2 : BC a2)
    (ea : a1 = a2)
    (eb : pr1 bc1 = transportb _ ea (pr1 bc2))
    (ec : pr2 bc1 = transportb C (total2_paths2_b ea eb) (pr2 bc2))
  : bc1 = transportb _ ea bc2.
Proof.
  destruct ea, bc1 as [b1 c1], bc2 as [b2 c2].
  cbn in eb; destruct eb; cbn in ec; destruct ec.
  apply idpath.
Defined.

Lemma transportf_pathsinv0_var :
∏ {X : UU} {P : X → UU} {x y : X} {p : x = y} {u : P x}
{v : P y}, transportf P p u = v → transportf P (!p) v = u.
Proof.
  intros. induction p. apply (!X0).
Defined.

End Auxiliary.


(** * Full subcategories *)

Section full_subcat.
Variable C : category.
Variable P : C -> UU.

Definition disp_full_sub_ob_mor : disp_cat_ob_mor C.
Proof.
  exists P.
  intros. exact unit.
Defined.

Definition disp_full_sub_id_comp : disp_cat_id_comp C disp_full_sub_ob_mor.
Proof.
  split; intros; apply tt.
Qed.

Definition disp_full_sub_data : disp_cat_data C
  :=  disp_full_sub_ob_mor,, disp_full_sub_id_comp.

Definition disp_full_sub_axioms : disp_cat_axioms _ disp_full_sub_data.
Proof.
  repeat split; intros; try (apply proofirrelevance; apply isapropunit).
  apply isasetaprop; apply isapropunit.
Qed.

Definition disp_full_sub : disp_cat C := _ ,, disp_full_sub_axioms.

End full_subcat.

(** * Displayed category from structure on objects and compatibility on morphisms *)

Section struct_hom.

Variable C : category.
Variable univC : is_univalent C.
Variable P : ob C -> UU.
(* Variable Pisset : ∏ x, isaset (P x). *)
Variable H : ∏ (x y : C), P x → P y → C⟦x,y⟧ → UU.
Arguments H {_ _} _ _ _ .
Variable Hisprop : ∏ x y a b (f : C⟦x,y⟧), isaprop (H a b f).
Variable Hid : ∏ (x : C) (a : P x), H a a (identity _ ).
Variable Hcomp : ∏ (x y z : C) a b c (f : C⟦x,y⟧) (g : C⟦y,z⟧),
                 H a b f → H b c g → H a c (f · g).

Definition disp_struct_ob_mor : disp_cat_ob_mor C.
Proof.
  exists P.
  intros ? ? f a b; exact (H f a b ).
Defined.

Definition disp_struct_id_comp : disp_cat_id_comp _ disp_struct_ob_mor.
Proof.
  split; cbn; intros.
  - apply Hid.
  - eapply Hcomp. apply X. apply X0.
Qed.

Definition disp_struct_data : disp_cat_data C := _ ,, disp_struct_id_comp.

Definition disp_struct_axioms : disp_cat_axioms _ disp_struct_data.
Proof.
  repeat split; intros; try (apply proofirrelevance; apply Hisprop).
  apply isasetaprop; apply Hisprop.
Qed.

Definition disp_struct : disp_cat C := _ ,, disp_struct_axioms.

End struct_hom.

(** * Products of displayed (pre)categories

We directly define direct products of displayed categories over a base.

An alternative would be to define the direct product as the [sigma_disp_cat] of the pullback to either factor.  *)
Section Dirprod.

Context {C : category} (D1 D2 : disp_cat C).

Definition dirprod_disp_cat_ob_mor : disp_cat_ob_mor C.
Proof.
  exists (λ c, D1 c × D2 c).
  intros x y xx yy f.
  exact (pr1 xx -->[f] pr1 yy × pr2 xx -->[f] pr2 yy).
Defined.

Definition dirprod_disp_cat_id_comp
  : disp_cat_id_comp _ dirprod_disp_cat_ob_mor.
Proof.
  apply tpair.
  - intros x xx. exact (id_disp _,, id_disp _).
  - intros x y z f g xx yy zz ff gg.
    exact ((pr1 ff ;; pr1 gg),, (pr2 ff ;; pr2 gg)).
Defined.

Definition dirprod_disp_cat_data : disp_cat_data C
  := (_ ,, dirprod_disp_cat_id_comp).

Definition dirprod_disp_cat_axioms
  : disp_cat_axioms _ dirprod_disp_cat_data.
Proof.
  repeat apply tpair.
  - intros. apply dirprod_paths; refine (id_left_disp @ !_).
    + refine (pr1_transportf _ _ _ _ _ _ _).
    + apply pr2_transportf.
  - intros. apply dirprod_paths; refine (id_right_disp @ !_).
    + refine (pr1_transportf _ _ _ _ _ _ _).
    + apply pr2_transportf.
  - intros. apply dirprod_paths; refine (assoc_disp @ !_).
    + refine (pr1_transportf _ _ _ _ _ _ _).
    + apply pr2_transportf.
  - intros. apply isaset_dirprod; apply homsets_disp.
Qed.

Definition dirprod_disp_cat : disp_cat C
  := (_ ,, dirprod_disp_cat_axioms).

Definition dirprodpr1_disp_functor_data
  : disp_functor_data (functor_identity C) dirprod_disp_cat (D1).
Proof.
  mkpair.
  - intros x xx; exact (pr1 xx).
  - intros x y xx yy f ff; exact (pr1 ff).
Defined.

Definition dirprodpr1_disp_functor_axioms
  : disp_functor_axioms dirprodpr1_disp_functor_data.
Proof.
  split.
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition dirprodpr1_disp_functor
  : disp_functor (functor_identity C) dirprod_disp_cat (D1)
:= (dirprodpr1_disp_functor_data,, dirprodpr1_disp_functor_axioms).


Definition dirprodpr2_disp_functor_data
  : disp_functor_data (functor_identity C) dirprod_disp_cat (D2).
Proof.
  mkpair.
  - intros x xx; exact (pr2 xx).
  - intros x y xx yy f ff; exact (pr2 ff).
Defined.

Definition dirprodpr2_disp_functor_axioms
  : disp_functor_axioms dirprodpr2_disp_functor_data.
Proof.
  split.
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition dirprodpr2_disp_functor
  : disp_functor (functor_identity C) dirprod_disp_cat (D2)
:= (dirprodpr2_disp_functor_data,, dirprodpr2_disp_functor_axioms).

End Dirprod.

Notation "D1 × D2" := (dirprod_disp_cat D1 D2) : disp_cat_scope.
Delimit Scope disp_cat_scope with disp_cat.
Bind Scope disp_cat_scope with disp_cat.

(** * Sigmas of displayed (pre)categories *)
Section Sigma.

Context {C : category}
        {D : disp_cat C}
        (E : disp_cat (total_category D)).

Definition sigma_disp_cat_ob_mor : disp_cat_ob_mor C.
Proof.
  exists (λ c, ∑ (d : D c), (E (c,,d))).
  intros x y xx yy f.
  exact (∑ (fD : pr1 xx -->[f] pr1 yy),
                (pr2 xx -->[f,,fD] pr2 yy)).
Defined.

Definition sigma_disp_cat_id_comp
  : disp_cat_id_comp _ sigma_disp_cat_ob_mor.
Proof.
  apply tpair.
  - intros x xx.
    exists (id_disp _). exact (id_disp (pr2 xx)).
  - intros x y z f g xx yy zz ff gg.
    exists (pr1 ff ;; pr1 gg). exact (pr2 ff ;; pr2 gg).
Defined.

Definition sigma_disp_cat_data : disp_cat_data C
  := (_ ,, sigma_disp_cat_id_comp).


Definition sigma_disp_cat_axioms
  : disp_cat_axioms _ sigma_disp_cat_data.
Proof.
  repeat apply tpair.
  - intros. use total2_reassoc_paths'.
    + apply id_left_disp.
    + etrans. exact (@id_left_disp _ _ _ _ _ _ _ (pr2 ff)).
      apply maponpaths_2, homset_property.
  - intros. use total2_reassoc_paths'.
    + apply id_right_disp.
    + etrans. exact (@id_right_disp _ _ _ _ _ _ _ (pr2 ff)).
      apply maponpaths_2, homset_property.
  - intros. use total2_reassoc_paths'.
    + apply assoc_disp.
    + etrans.
        exact (@assoc_disp _ _
                 _ _ _ _  _ _ _
                 _ _ _ _  (pr2 ff) (pr2 gg) (pr2 hh)).
      apply maponpaths_2, homset_property.
  - intros. apply isaset_total2; intros; apply homsets_disp.
Qed.

Definition sigma_disp_cat : disp_cat C
  := (_ ,, sigma_disp_cat_axioms).

Definition sigmapr1_disp_functor_data
  : disp_functor_data (functor_identity C) sigma_disp_cat D.
Proof.
  mkpair.
  - intros x xx; exact (pr1 xx).
  - intros x y xx yy f ff; exact (pr1 ff).
Defined.

Definition sigmapr1_disp_functor_axioms
  : disp_functor_axioms sigmapr1_disp_functor_data.
Proof.
  split.
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition sigmapr1_disp_functor
  : disp_functor (functor_identity C) sigma_disp_cat D
:= (sigmapr1_disp_functor_data,, sigmapr1_disp_functor_axioms).

(* TODO: complete [sigmapr2_disp]; will be a [functor_lifting], not a [disp_functor]. *)

(** ** Transport and isomorphism lemmas *)

Lemma pr1_transportf_sigma_disp {x y : C} {f f' : x --> y} (e : f = f')
    {xxx : sigma_disp_cat x} {yyy} (fff : xxx -->[f] yyy)
  : pr1 (transportf _ e fff) = transportf _ e (pr1 fff).
Proof.
  destruct e; apply idpath.
Qed.

Lemma pr2_transportf_sigma_disp {x y : C} {f f' : x --> y} (e : f = f')
    {xxx : sigma_disp_cat x} {yyy} (fff : xxx -->[f] yyy)
  : pr2 (transportf _ e fff)
  = transportf (λ ff, pr2 xxx -->[ff] _ ) (two_arg_paths_f (*total2_paths2*) e (! pr1_transportf_sigma_disp e fff))
      (pr2 fff).
Proof.
  destruct e. apply pathsinv0.
  etrans. apply maponpaths_2, maponpaths, maponpaths.
  apply (homsets_disp _ _ _ (idpath _)).
  apply idpath.
Qed.


(** ** Univalence *)

Local Open Scope hide_transport_scope.

Definition is_iso_sigma_disp_aux1
    {x y} {xxx : sigma_disp_cat x} {yyy : sigma_disp_cat y}
    {f : iso x y} (fff : xxx -->[f] yyy)
    (ii : is_iso_disp f (pr1 fff))
    (ffi := (_,, ii) : iso_disp f (pr1 xxx) (pr1 yyy))
    (iii : is_iso_disp (@total_iso _ _ (_,,_) (_,,_) f ffi) (pr2 fff))
  : yyy -->[inv_from_iso f] xxx.
Proof.
  exists (inv_mor_disp_from_iso ii).
  set (ggg := inv_mor_disp_from_iso iii).
  exact (transportf _ (inv_mor_total_iso _ _ _) ggg).
Defined.

Lemma is_iso_sigma_disp_aux2
    {x y} {xxx : sigma_disp_cat x} {yyy : sigma_disp_cat y}
    {f : iso x y} (fff : xxx -->[f] yyy)
    (ii : is_iso_disp f (pr1 fff))
    (ffi := (_,, ii) : iso_disp f (pr1 xxx) (pr1 yyy))
    (iii : is_iso_disp (@total_iso _ _ (_,,_) (_,,_) f ffi) (pr2 fff))
  :   (is_iso_sigma_disp_aux1 fff ii iii) ;; fff
    = transportb _ (iso_after_iso_inv f) (id_disp yyy)
  ×
      fff ;; (is_iso_sigma_disp_aux1 fff ii iii)
    = transportb _ (iso_inv_after_iso f) (id_disp xxx).
Proof.
  split.
  - use total2_paths_f.
    + abstract ( etrans;
        [ apply iso_disp_after_inv_mor
        | apply pathsinv0, pr1_transportf_sigma_disp]).
    + etrans. Focus 2. apply @pathsinv0, pr2_transportf_sigma_disp.
      etrans. apply maponpaths.
        refine (mor_disp_transportf_postwhisker
          (@inv_mor_total_iso _ _ (_,,_) (_,,_) f ffi) _ (pr2 fff)).
      etrans. apply functtransportf.
      etrans. apply transport_f_f.
      etrans. eapply transportf_bind.
        apply (iso_disp_after_inv_mor iii).
      apply maponpaths_2, (@homset_property (total_category D)).
  - use total2_paths_f; cbn.
    + abstract ( etrans;
        [ apply inv_mor_after_iso_disp
        | apply pathsinv0, pr1_transportf_sigma_disp ]).
    + etrans. Focus 2. apply @pathsinv0, pr2_transportf_sigma_disp.
      etrans. apply maponpaths.
      refine (mor_disp_transportf_prewhisker
        (@inv_mor_total_iso _ _ (_,,_) (_,,_) f ffi) (pr2 fff) _).
      etrans. apply functtransportf.
      etrans. apply transport_f_f.
      etrans. eapply transportf_bind.
        apply (inv_mor_after_iso_disp iii).
      apply maponpaths_2, (@homset_property (total_category D)).
Time Qed. (* TODO: try to speed this up? *)

Lemma is_iso_sigma_disp
    {x y} {xxx : sigma_disp_cat x} {yyy : sigma_disp_cat y}
    {f : iso x y} (fff : xxx -->[f] yyy)
    (ii : is_iso_disp f (pr1 fff))
    (ffi := (_,, ii) : iso_disp f (pr1 xxx) (pr1 yyy))
    (iii : is_iso_disp (@total_iso _ _ (_,,_) (_,,_) f ffi) (pr2 fff))
  : is_iso_disp f fff.
Proof.
  exists (is_iso_sigma_disp_aux1 fff ii iii).
  apply is_iso_sigma_disp_aux2.
Defined.

Definition sigma_disp_iso
    {x y} (xx : sigma_disp_cat x) (yy : sigma_disp_cat y)
    {f : iso x y} (ff : iso_disp f (pr1 xx) (pr1 yy))
    (fff : iso_disp (@total_iso _ _ (_,,_) (_,,_) f ff) (pr2 xx) (pr2 yy))
  : iso_disp f xx yy.
Proof.
  exists (pr1 ff,, pr1 fff). use is_iso_sigma_disp; cbn.
  - exact (pr2 ff).
  - exact (pr2 fff).
Defined.

Definition sigma_disp_iso_map
    {x y} (xx : sigma_disp_cat x) (yy : sigma_disp_cat y)
    (f : iso x y)
  : (∑ ff : iso_disp f (pr1 xx) (pr1 yy),
       iso_disp (@total_iso _ _ (_,,_) (_,,_) f ff) (pr2 xx) (pr2 yy))
  -> iso_disp f xx yy
:= λ ff, sigma_disp_iso _ _ (pr1 ff) (pr2 ff).

Lemma sigma_disp_iso_isweq
    {x y} (xx : sigma_disp_cat x) (yy : sigma_disp_cat y)
    (f : iso x y)
  : isweq (sigma_disp_iso_map xx yy f).
Proof.
Abort.

(*
Definition sigma_disp_iso_equiv
    {x y} (xx : sigma_disp_cat x) (yy : sigma_disp_cat y)
    (f : iso x y)
:= weqpair _ (sigma_disp_iso_isweq xx yy f).
*)

(*
Lemma is_univalent_sigma_disp (DD : is_univalent_disp D) (EE : is_univalent_disp E)
  : is_univalent_disp sigma_disp_cat.
Proof.
  apply is_univalent_disp_from_fibers.
  intros x xx yy.
  use weqhomot.
  - destruct xx as [xx xxx], yy as [yy yyy].
     use (@weqcomp _ (∑ ee : xx = yy, transportf (λ r, E (x,,r)) ee xxx = yyy) _ _ _).
      refine (total2_paths_equiv _ _ _).
    set (i := fun (ee : xx = yy) => (total2_paths2 (idpath _) ee)).
    apply @weqcomp with
        (∑ ee : xx = yy, transportf _ (i ee) xxx = yyy).
      apply weqfibtototal; intros ee.
      refine (_ ,, isweqpathscomp0l _ _).
      (* TODO: a pure transport lemma; maybe break out? *)
      destruct ee; apply idpath.
    apply @weqcomp with (∑ ee : xx = yy,
             iso_disp (@idtoiso (total_category _) (_,,_) (_,,_) (i ee)) xxx yyy).
      apply weqfibtototal; intros ee.
      exists (fun (eee : transportf _ (i ee) xxx = yyy) => idtoiso_disp _ eee).
      apply EE.
    apply @weqcomp with (∑ ee : xx = yy, iso_disp
         (@total_iso _ D (_,,_) (_,,_) _ (idtoiso_disp (idpath _) ee)) xxx yyy).
      apply weqfibtototal; intros ee.
      mkpair.
        refine (transportf (λ I, iso_disp I xxx yyy) _).
        unfold i.
      (* TODO: maybe break out this lemma on [idtoiso]? *)
      (* Note: [abstract] here is to speed up a [cbn] below. *)
        destruct ee. abstract (apply eq_iso, idpath).
      exact (isweqtransportf (λ I, iso_disp I xxx yyy) _).
    apply (@weqcomp _ (∑ f : iso_disp (identity_iso x) xx yy,
                      (iso_disp (@total_iso _ D (_,,_) (_,,_) _ f) xxx yyy)) _).
      refine (weqfp (weqpair _ _) _). refine (DD _ _ (idpath _) _ _).
    apply (sigma_disp_iso_equiv (_,,_) (_,,_) _).
  - assert (lemma2 : forall i i' (e : i = i') ii,
                 pr1 (transportf (λ i, iso_disp i (pr2 xx) (pr2 yy)) e ii)
                 = transportf _ (maponpaths pr1 e) (pr1 ii)).
      intros; destruct e; apply idpath.
    intros ee; apply eq_iso_disp.
    destruct ee, xx as [xx xxx]; cbn.
    apply maponpaths.
    etrans. cbn in lemma2.
    (* This [match] is to supply the 3rd argument of [lemma2], without referring to the identifier auto-generated by [abstract] above. *)
    match goal with |[ |- pr1 (transportf _ ?H _) = _ ]
      => apply (lemma2 _ _ H _) end.
    refine (@maponpaths_2 _ _ _ _ _ (idpath _) _ _).
    etrans. use maponpaths. apply eq_iso, idpath.
      apply isaset_iso, homset_property.
   apply (@homset_property (total_category _) (_,,_) (_,,_)).
Qed.
*)

End Sigma.

(** * Displayed functor category

Displayed functors and natural transformations form a displayed category over the ordinary functor category between the bases. *)

Section Functor.
(* TODO: clean up this section a bit. *)

Variables C' C : category.
Variable D' : disp_cat C'.
Variable D : disp_cat C.

Let FunctorsC'C := functor_category C' C.

Lemma foo
  (F' F : functor C' C)
  (a' a : nat_trans F' F)
  (p : a' = a )
  (FF' : disp_functor F' D' D)
  (FF : disp_functor F D' D)
  (b : disp_nat_trans a' FF' FF)
  (c' : C')
  (xx' : D' c')
  :
  pr1 (transportf (λ x, disp_nat_trans x FF' FF) p b) c' xx' =
      transportf (mor_disp (FF' c' xx') (FF c' xx'))
           (nat_trans_eq_pointwise p _ )  (b c' xx').
Proof.
  induction p.
  assert (XR : nat_trans_eq_pointwise (idpath a') c' = idpath _ ).
  { apply homset_property. }
  rewrite XR.
  apply idpath.
Qed.

Lemma disp_nat_trans_id_left
  (F' F : functor C' C)
  (a : nat_trans F' F)
  (FF' : disp_functor F' D' D)
  (FF : disp_functor F D' D)
  (b : disp_nat_trans a FF' FF)
  :
   disp_nat_trans_comp (disp_nat_trans_id FF') b =
   transportb (λ f : nat_trans F' F, disp_nat_trans f FF' FF)
              (id_left (a : FunctorsC'C ⟦ _ , _ ⟧))
              b.
Proof.
  apply subtypeEquality.
  { intro. apply isaprop_disp_nat_trans_axioms. }
  apply funextsec; intro c'.
  apply funextsec; intro xx'.
  apply pathsinv0.
  etrans. apply foo.
  apply pathsinv0.
  etrans. apply id_left_disp.
  unfold transportb.
  apply maponpaths_2, homset_property.
Qed.

Lemma disp_nat_trans_id_right
  (F' F : functor C' C)
  (a : nat_trans F' F)
  (FF' : disp_functor F' D' D)
  (FF : disp_functor F D' D)
  (b : disp_nat_trans a FF' FF)
  :
   disp_nat_trans_comp b (disp_nat_trans_id FF) =
   transportb (λ f : nat_trans F' F, disp_nat_trans f FF' FF)
              (id_right (a : FunctorsC'C ⟦ _ , _ ⟧))
              b.
Proof.
  apply subtypeEquality.
  { intro. apply isaprop_disp_nat_trans_axioms. }
  apply funextsec; intro c'.
  apply funextsec; intro xx'.
  apply pathsinv0.
  etrans. apply foo.
  apply pathsinv0.
  etrans. apply id_right_disp.
  unfold transportb.
  apply maponpaths_2, homset_property.
Qed.

Lemma disp_nat_trans_assoc
  (x y z w : functor C' C)
  (f : nat_trans x y)
  (g : nat_trans y z)
  (h : nat_trans z w)
  (xx : disp_functor x D' D)
  (yy : disp_functor y D' D)
  (zz : disp_functor z D' D)
  (ww : disp_functor w D' D)
  (ff : disp_nat_trans f xx yy)
  (gg : disp_nat_trans g yy zz)
  (hh : disp_nat_trans h zz ww)
  :
   disp_nat_trans_comp ff (disp_nat_trans_comp gg hh) =
   transportb (λ f0 : nat_trans x w, disp_nat_trans f0 xx ww)
     (assoc (f : FunctorsC'C⟦_,_⟧) g h)
     (disp_nat_trans_comp (disp_nat_trans_comp ff gg) hh).
Proof.
  apply subtypeEquality.
  { intro. apply isaprop_disp_nat_trans_axioms. }
  apply funextsec; intro c'.
  apply funextsec; intro xx'.
  apply pathsinv0.
  etrans. apply foo.
  apply pathsinv0.
  etrans. apply assoc_disp.
  unfold transportb.
  apply maponpaths_2.
  apply homset_property.
Qed.

Lemma isaset_disp_nat_trans
  (x y : functor C' C)
  (f : nat_trans x y)
  (xx : disp_functor x D' D)
  (yy : disp_functor y D' D)
  :
   isaset (disp_nat_trans f xx yy).
Proof.
  intros. simpl in *.
  apply (isofhleveltotal2 2).
  * do 2 (apply impred; intro).
    apply homsets_disp.
  * intro d.
    do 6 (apply impred; intro).
    apply hlevelntosn. apply homsets_disp.
Qed.

Definition disp_functor_cat :
  disp_cat (FunctorsC'C).
Proof.
  mkpair.
  - mkpair.
    + mkpair.
      * intro F.
        apply (disp_functor F D' D).
      * simpl. intros F' F FF' FF a.
        apply (disp_nat_trans a FF' FF).
    + mkpair.
      * intros x xx.
        apply disp_nat_trans_id.
      * intros ? ? ? ? ? ? ? ? X X0. apply (disp_nat_trans_comp X X0 ).
  - repeat split.
    + apply disp_nat_trans_id_left.
    + apply disp_nat_trans_id_right.
    + apply disp_nat_trans_assoc.
    + apply isaset_disp_nat_trans.
Defined.

(** TODO : characterize isos in the displayed functor cat *)

(** TODO: integrate [has_homsets] assumptions below! *)
Definition pointwise_iso_from_nat_iso {A X : precategory} {hsX : has_homsets X}
  {F G : functor_precategory A X hsX}
  (b : iso F G) (a : A) : iso (pr1 F a) (pr1 G a)
  :=
  functor_iso_pointwise_if_iso _ _ _ _ _ b (pr2 b)_ .


Definition pointwise_inv_is_inv_on {A X : precategory} {hsX : has_homsets X}
  {F G : functor_precategory A X hsX}
  (b : iso F G) (a : A) :

  inv_from_iso (pointwise_iso_from_nat_iso b a) =
                                       pr1 (inv_from_iso b) a.
Proof.
  apply id_right.
Defined.

(** TODO : write a few lemmas about isos in
    the disp functor precat,
    to make the following sane

    However: it seems to be better to work on
    https://github.com/UniMath/UniMath/issues/362
    first.
*)

Definition is_pointwise_iso_if_is_disp_functor_cat_iso
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f ] yy)
  (H : is_iso_disp f FF)
  :
  forall x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ).
Proof.
  intros x' xx'.
  mkpair.
  - set (X:= pr1 H). simpl in X.
    apply (transportb _ (pointwise_inv_is_inv_on f _ ) (X x' xx')).
  - simpl. repeat split.
    + etrans. apply mor_disp_transportf_postwhisker.
      apply pathsinv0.
      apply transportf_comp_lemma.
      assert (XR:= pr1 (pr2 H)).
      assert (XRT :=  (maponpaths pr1 XR)).
      assert (XRT' :=  toforallpaths _ _ _  (toforallpaths _ _ _ XRT x')).
      apply pathsinv0.
      etrans. apply XRT'.
      clear XRT' XRT XR.
      assert (XR := foo).
      specialize (XR _ _ _ _ (! iso_after_iso_inv f)).
      etrans. apply XR.
      apply maponpaths_2, homset_property.
    + etrans. apply mor_disp_transportf_prewhisker.
      apply pathsinv0.
      apply transportf_comp_lemma.
      assert (XR:= inv_mor_after_iso_disp H).
      assert (XRT :=  (maponpaths pr1 XR)).
      assert (XRT' :=  toforallpaths _ _ _  (toforallpaths _ _ _ XRT x')).
      apply pathsinv0.
      etrans. apply XRT'.
      clear XRT' XRT XR.
      assert (XR := foo).
      specialize (XR _ _ _ _ (! iso_inv_after_iso f)).
      etrans. apply XR.
      apply maponpaths_2, homset_property.
Defined.

Lemma is_disp_nat_trans_pointwise_inv
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f] yy)
  (H : ∏ (x' : C') (xx' : D' x'),
      is_iso_disp (pointwise_iso_from_nat_iso f x') (pr1 FF x' xx'))
  (x' x0 : C')
  (f0 : x' --> x0)
  (xx' : D' x')
  (xx0 : D' x0)
  (ff : xx' -->[ f0] xx0)
  :
   # (yy : disp_functor _ _ _)  ff ;; (let RT := pr1 (H x0 xx0) in
               transportf (mor_disp (pr1 yy x0 xx0) (pr1 xx x0 xx0))
                 (id_right (pr1 (inv_from_iso f) x0)) RT) =
   transportb (mor_disp (pr1 yy x' xx') (pr1 xx x0 xx0))
     (nat_trans_ax (inv_from_iso f) x' x0 f0)
     ((let RT := pr1 (H x' xx') in
       transportf (mor_disp (pr1 yy x' xx') (pr1 xx x' xx'))
         (id_right (pr1 (inv_from_iso f) x')) RT) ;;
      # (xx : disp_functor _ _ _) ff).
Proof.
 etrans. apply mor_disp_transportf_prewhisker.
    apply pathsinv0.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
(*    Search (transportf _ _ _ = transportf _ _ _ ). *)
(*    Search (?e = ?e' -> ?w = ?w' -> _ ?e ?w = _ ?e' ?w'). *)
    etrans. apply transport_f_f.
(*    Search (transportf _ _ _ = transportf _ _ _ ). *)
    apply transportf_comp_lemma.
    set (Hx := H x' xx').
    assert (Hx1 := pr2 (pr2 Hx)).
    set (XR:= iso_disp_precomp (pointwise_iso_from_nat_iso f x' ) (_ ,,Hx)).
(*    Check (# (pr1 yy) ff ;; pr1 (H x0 xx0)). *)
    specialize (XR _
       (
        ((# (y : functor _ _ ))%cat f0 · inv_from_iso (pointwise_iso_from_nat_iso f x0))

         )
       ).
    specialize (XR ((xx : disp_functor _ _ _  ) x0 xx0)).
    set (Xweq := weqpair _ XR).
    apply (invmaponpathsweq Xweq).
    unfold Xweq. clear Xweq.
    etrans.  apply mor_disp_transportf_prewhisker.
    etrans. apply maponpaths. apply assoc_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths_2. apply Hx1.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply assoc_disp.
    assert (XRO := @disp_nat_trans_ax _ _ _ _ _ _ _ _ _ FF).
    specialize (XRO _ _ _ xx'  _ ff).
    assert (XR' := ! (transportf_pathsinv0 _ _ _ _  (!XRO))).
    clear XRO.
    clear XR. clear Hx1.
    etrans. apply maponpaths. apply maponpaths_2.
            apply XR'.
    etrans. apply maponpaths.  apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    apply pathsinv0.

    etrans. apply maponpaths.
            apply assoc_disp_var.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply maponpaths.
            apply (inv_mor_after_iso_disp (H _ _ )).
    etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
    etrans. apply maponpaths. apply maponpaths.
            apply id_right_disp.
    etrans. apply transport_f_f.
    etrans. apply transport_f_f.
    apply maponpaths_2. apply homset_property.
Qed.

Definition inv_disp_from_pointwise_iso
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f ] yy)
  (H : forall x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ))
  :
       yy -->[ inv_from_iso f] xx.
Proof.
  mkpair.
  + intros x' xx'.
    simpl in xx. simpl in yy.
    assert (XR : inv_from_iso (pointwise_iso_from_nat_iso f x') =
                                       pr1 (inv_from_iso f) x').
    { apply id_right. }
    set (RT := pr1 (H x' xx')).
    apply (transportf _ XR RT).
  + intros x' x0 f0 xx' xx0 ff.
    apply is_disp_nat_trans_pointwise_inv.
Defined.



Definition is_disp_functor_cat_iso_if_pointwise_iso
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f ] yy)
  (H : forall x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ))
  : is_iso_disp f FF.
Proof.
  mkpair.
  - apply (inv_disp_from_pointwise_iso _ _ _ _ _ FF H).
  - split.
    + apply subtypeEquality.
      { intro. apply isaprop_disp_nat_trans_axioms. }
      apply funextsec; intro c'.
      apply funextsec; intro xx'.
      apply pathsinv0.
      etrans. apply foo.
      cbn.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_postwhisker.
      etrans. apply maponpaths. apply (iso_disp_after_inv_mor (H c' xx')).
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property.
    + apply subtypeEquality.
      { intro. apply isaprop_disp_nat_trans_axioms. }
      apply funextsec; intro c'.
      apply funextsec; intro xx'.
      apply pathsinv0.
      etrans. apply foo.
      cbn.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_prewhisker.
      etrans. apply maponpaths. apply (inv_mor_after_iso_disp (H c' xx')).
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property.
Defined.

Definition is_disp_functor_cat_iso_iff_pointwise_iso
  (x y : FunctorsC'C)
  (f : iso x y)
  (xx : disp_functor_cat x)
  (yy : disp_functor_cat y)
  (FF : xx -->[ f ] yy)
  :
  (∏ x' (xx' : D' x') , is_iso_disp (pointwise_iso_from_nat_iso f _ )
                          (pr1 FF _ xx' ))
    <->
    is_iso_disp f FF.
Proof.
  split.
  - apply is_disp_functor_cat_iso_if_pointwise_iso.
  - apply is_pointwise_iso_if_is_disp_functor_cat_iso.
Defined.


End Functor.

(** * Fiber categories *)

(** A displayed category gives a _fiber_ category over each object of the base.  These are most interesting in the case where the displayed category is an isofibration. *)
Section Fiber.

Context {C : category}
        (D : disp_cat C)
        (c : C).

Definition fiber_category_data : precategory_data.
Proof.
  mkpair.
  - mkpair.
    + apply (ob_disp D c).
    + intros xx xx'. apply (mor_disp xx xx' (identity c)).
  - mkpair.
    + intros. apply id_disp.
    + intros. apply (transportf _ (id_right _ ) (comp_disp X X0)).
Defined.

Lemma fiber_is_precategory : is_precategory fiber_category_data.
Proof.
  repeat split; intros; cbn.
  - etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f. apply transportf_comp_lemma_hset.
    apply (homset_property). apply idpath.
  - etrans. apply maponpaths. apply id_right_disp.
    etrans. apply transport_f_f. apply transportf_comp_lemma_hset.
    apply (homset_property). apply idpath.
  - etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply assoc_disp.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply maponpaths.  apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    apply maponpaths_2. apply homset_property.
Qed.

Definition fiber_precategory : precategory := ( _ ,, fiber_is_precategory).

Lemma has_homsets_fiber_category : has_homsets fiber_precategory.
Proof.
  intros x y. apply homsets_disp.
Qed.

Definition fiber_category : category
  := ( fiber_precategory ,, has_homsets_fiber_category).


Definition iso_disp_from_iso_fiber (a b : fiber_category) :
  iso a b -> iso_disp (identity_iso c) a b.
Proof.
 intro i.
 mkpair.
 + apply (pr1 i).
 + cbn.
   mkpair.
   * apply (inv_from_iso i).
   * abstract (  split;
       [ assert (XR := iso_after_iso_inv i);
        cbn in *;
        assert (XR' := transportf_pathsinv0_var XR);
        etrans; [ apply (!XR') |];
        unfold transportb;
        apply maponpaths_2; apply homset_property
       |assert (XR := iso_inv_after_iso i);
        cbn in *;
        assert (XR' := transportf_pathsinv0_var XR);
        etrans; [ apply (!XR') | ];
        unfold transportb;
        apply maponpaths_2; apply homset_property ] ).
Defined.

Definition iso_fiber_from_iso_disp (a b : fiber_category) :
  iso a b <- iso_disp (identity_iso c) a b.
Proof.
  intro i.
  mkpair.
  + apply (pr1 i).
  + cbn in *.
    apply (@is_iso_from_is_z_iso fiber_category).
    mkpair.
    apply (inv_mor_disp_from_iso i).
    abstract (split; cbn;
              [
                assert (XR := inv_mor_after_iso_disp i);
                etrans; [ apply maponpaths , XR |];
                etrans; [ apply transport_f_f |];
                apply transportf_comp_lemma_hset;
                  try apply homset_property; apply idpath
              | assert (XR := iso_disp_after_inv_mor i);
                etrans; [ apply maponpaths , XR |] ;
                etrans; [ apply transport_f_f |];
                apply transportf_comp_lemma_hset;
                try apply homset_property; apply idpath
              ]).
Defined.

Lemma iso_disp_iso_fiber (a b : fiber_category) :
  iso a b ≃ iso_disp (identity_iso c) a b.
Proof.
  exists (iso_disp_from_iso_fiber a b).
  use (gradth _ (iso_fiber_from_iso_disp _ _ )).
  - intro. apply eq_iso. apply idpath.
  - intro. apply eq_iso_disp. apply idpath.
Defined.

(** ** Univalence *)
Variable H : is_univalent_disp D.

Let idto1 (a b : fiber_category) : a = b ≃ iso_disp (identity_iso c) a b
  :=
  weqpair (@idtoiso_fiber_disp _ _ _ a b) (H _ _ (idpath _ ) a b).

Let idto2 (a b : fiber_category) : a = b -> iso_disp (identity_iso c) a b
  :=
  funcomp (λ p : a = b, idtoiso p) (iso_disp_iso_fiber a b).

Lemma eq_idto1_idto2 (a b : fiber_category)
  : ∏ p : a = b, idto1 _ _ p = idto2 _ _ p.
Proof.
  intro p. induction p.
  apply eq_iso_disp.
  apply idpath.
Qed.

Lemma is_univalent_fiber_cat
  (a b : fiber_category)
  :
  isweq (λ p : a = b, idtoiso p).
Proof.
  use (twooutof3a _ (iso_disp_iso_fiber a b)).
  - use (isweqhomot (idto1 a b)).
    + intro p.
      apply eq_idto1_idto2.
    + apply weqproperty.
  - apply weqproperty.
Defined.


Lemma is_univalent_fiber : is_univalent fiber_category.
Proof.
  split.
  - apply is_univalent_fiber_cat.
  - apply has_homsets_fiber_category.
Defined.

End Fiber.

Arguments fiber_precategory {_} _ _ .
Arguments fiber_category {_} _ _ .

(* TODO: is this a terrible notation?  Probably. *)
Notation "D [{ x }]" := (fiber_category D x)(at level 3,format "D [{ x }]").


Lemma is_univalent_disp_from_is_univalent_fiber {C : category} (D : disp_cat C)
  : (∏ (c : C), is_univalent D[{c}]) → is_univalent_disp D.
Proof.
  intro H.
  apply is_univalent_disp_from_fibers.
  intros c xx xx'.
  specialize (H c).
  set (w := weqpair _ (pr1 H xx xx')).
  set (w' := weqcomp w (iso_disp_iso_fiber D _ xx xx')).
  apply (weqhomot _ w').
  intro e. induction e.
  apply eq_iso_disp. apply idpath.
Defined.

Definition is_univalent_disp_iff_fibers_are_univalent {C : category} (D : disp_cat C)
  : is_univalent_disp D <-> (∏ (c : C), is_univalent D[{c}]).
Proof.
  split; intro H.
  - intro. apply is_univalent_fiber. apply H.
  - apply is_univalent_disp_from_is_univalent_fiber.
    apply H.
Defined.


(** ** Fiber functors

Functors between displayed categories induce functors between their fibers. *)
Section Fiber_Functors.

Section fix_context.

Context {C C' : category} {D} {D'}
        {F : functor C C'} (FF : disp_functor F D D')
        (x : C).

Definition fiber_functor_data : functor_data D[{x}] D'[{F x}].
Proof.
  mkpair.
  - apply (λ xx', FF xx').
  - intros xx' xx ff.
    apply (transportf _ (functor_id _ _ ) (# FF ff)).
Defined.

Lemma is_functor_fiber_functor : is_functor fiber_functor_data.
Proof.
  split; unfold functor_idax, functor_compax; cbn.
  - intros.
    apply transportf_pathsinv0.
    apply pathsinv0. apply disp_functor_id.
  - intros.
    etrans. apply maponpaths. apply disp_functor_transportf.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply disp_functor_comp.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply maponpaths. apply mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    apply maponpaths_2, homset_property.
Qed.

Definition fiber_functor : functor D[{x}] D'[{F x}]
  := ( _ ,, is_functor_fiber_functor).

End fix_context.

(* TODO: consider lemma organisation in this file *)

Definition is_iso_fiber_from_is_iso_disp
  {C : category} {D : disp_cat C}
  {c : C} {d d' : D c} (ff : d -->[identity c] d')
  (Hff : is_iso_disp (identity_iso c) ff)
: @is_iso (fiber_category D c) _ _ ff.
Proof.
  apply is_iso_from_is_z_iso.
  exists (pr1 Hff).
  mkpair; cbn.
  + set (H := pr2 (pr2 Hff)).
    etrans. apply maponpaths, H.
    etrans. apply transport_f_b.
    refine (@maponpaths_2 _ _ _ _ _ (paths_refl _) _ _).
    apply homset_property.
  + set (H := pr1 (pr2 Hff)).
    etrans. apply maponpaths, H.
    etrans. apply transport_f_b.
    refine (@maponpaths_2 _ _ _ _ _ (paths_refl _) _ _).
    apply homset_property.
Qed.

Definition fiber_nat_trans {C C' : category}
  {F : functor C C'}
  {D D'} {FF FF' : disp_functor F D D'}
  (α : disp_nat_trans (nat_trans_id F) FF FF')
  (c : C)
: nat_trans (fiber_functor FF c) (fiber_functor FF' c).
Proof.
  use tpair; simpl.
  - intro d. exact (α c d).
  - unfold is_nat_trans; intros d d' ff; simpl.
    set (αff := pr2 α _ _ _ _ _ ff); simpl in αff.
    cbn.
    etrans. apply maponpaths, mor_disp_transportf_postwhisker.
    etrans. apply transport_f_f.
    etrans. apply maponpaths, αff.
    etrans. apply transport_f_b.
    apply @pathsinv0.
    etrans. apply maponpaths, mor_disp_transportf_prewhisker.
    etrans. apply transport_f_f.
    apply maponpaths_2, homset_property.
Defined.

Lemma fiber_functor_ff
    {C C' : category} {D} {D'}
    {F : functor C C'} (FF : disp_functor F D D')
    (H : disp_functor_ff FF)
    (c : C)
: fully_faithful (fiber_functor FF c).
Proof.
  intros xx yy; cbn.
  set (XR := H _ _ xx yy (identity _ )).
  apply twooutof3c.
  - apply XR.
  - apply isweqtransportf.
Defined.

End Fiber_Functors.
