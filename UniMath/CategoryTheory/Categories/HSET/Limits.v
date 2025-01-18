(** * Limits in [HSET] *)

(** ** Contents

  - General limits ([LimsHSET])
    - Alternate definition using cats/limits
  - Binary products ([BinProductsHSET])
  - General indexed products ([ProductsHSET])
  - Terminal object ([TerminalHSET])
    - Terminal object from general limits ([TerminalHSET_from_Lims])
  - Pullbacks ([PullbacksHSET])
    - Pullbacks from general limits ([PullbacksHSET_from_Lims])
    - Pullbacks of arrows from [unit] as inverse images
  - Equalizers from general limits ([EqualizersHSET_from_Lims])

Written by: Benedikt Ahrens, Anders Mörtberg

October 2015 - January 2016

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.PartA. (* flip *)
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.WeakEquivalences.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Graphs.Equalizers.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.

Local Open Scope cat.

(** ** General limits *)

Section limits.

Variable g : graph.
Variable D : diagram g HSET.

Definition limset_UU : UU :=
  ∑ (f : ∏ u : vertex g, pr1hSet (dob D u)),
    ∏ u v (e : edge u v), dmor D e (f u) = f v.

Definition limset : HSET.
Proof.
  exists limset_UU.
  apply (isofhleveltotal2 2);
            [ apply impred; intro; apply pr2
            | intro f; repeat (apply impred; intro);
              apply isasetaprop, setproperty ].
Defined.

Lemma LimConeHSET : LimCone D.
Proof.
use make_LimCone.
- apply limset.
- exists (λ u f, pr1 f u).
  abstract (intros u v e; simpl; apply funextfun; intro f; simpl; apply (pr2 f)).
- intros X CC.
  use tpair.
  + use tpair.
    * intro x; exists (λ u, coneOut CC u x).
      abstract (intros u v e; apply (toforallpaths _ _ _ (coneOutCommutes CC _ _ e))).
    * abstract (intro v; apply idpath).
  + abstract (intros [t p]; apply subtypePath;
              [ intro; apply impred; intro; apply isaset_set_fun_space
              | apply funextfun; intro; apply subtypePath];
                [ intro; repeat (apply impred; intro); apply setproperty
                | apply funextsec; intro u; apply (toforallpaths _ _ _ (p u))]).
Defined.

End limits.

Lemma LimsHSET : Lims HSET.
Proof.
now intros g d; apply LimConeHSET.
Defined.

Lemma LimsHSET_of_shape (g : graph) : Lims_of_shape g HSET.
Proof.
now intros d; apply LimConeHSET.
Defined.

(** *** Alternate definition using cats/limits  *)

Require UniMath.CategoryTheory.Limits.Cats.Limits.

Section cats_limits.

Variable J : precategory.
Variable D : functor J HSET.

Definition cats_limset_UU : UU :=
  ∑ (f : ∏ u, pr1hSet (D u)),
    ∏ u v (e : J⟦u,v⟧), # D e (f u) = f v.

Definition cats_limset : HSET.
Proof.
  exists cats_limset_UU.
  apply (isofhleveltotal2 2);
            [ apply impred; intro; apply pr2
            | intro f; repeat (apply impred; intro);
              apply isasetaprop, setproperty ].
Defined.

Lemma cats_LimConeHSET : Cats.Limits.LimCone D.
Proof.
use make_LimCone.
- apply cats_limset.
- exists (λ u f, pr1 f u).
  abstract (intros u v e; apply funextfun; intro f; apply (pr2 f)).
- intros X CC.
  use tpair.
  + use tpair.
    * intro x; exists (λ u, coneOut CC u x).
      abstract (intros u v e; apply (toforallpaths _ _ _ (coneOutCommutes CC _ _ e))).
    * abstract (intro v; apply idpath).
  + abstract (intros [t p]; apply subtypePath;
     [ intro; apply impred; intro; apply isaset_set_fun_space
     | apply funextfun; intro x; apply subtypePath];
       [ intro; repeat (apply impred; intro); apply setproperty
       | simpl; apply funextsec; intro u; apply (toforallpaths _ _ _ (p u))]).
Defined.

End cats_limits.

Lemma cats_LimsHSET : Cats.Limits.Lims HSET.
Proof.
now intros g d; apply cats_LimConeHSET.
Defined.

Lemma cats_LimsHSET_of_shape (g : category) : Cats.Limits.Lims_of_shape g HSET.
Proof.
now intros d; apply cats_LimConeHSET.
Defined.

(** ** Binary products ([BinProductsHSET]) *)

Lemma BinProductsHSET : BinProducts HSET.
Proof.
intros A B.
use make_BinProduct.
- apply (A × B)%set.
- simpl in *; apply pr1.
- simpl in *; intros x; apply (pr2 x).
- apply make_isBinProduct.
  intros C f g; use tpair.
  * exists (prodtofuntoprod (f,,g)); abstract (split; apply idpath).
  * abstract (intros [t [ht1 ht2]]; apply subtypePath;
             [ intros x; apply isapropdirprod; apply has_homsets_HSET
             | now apply funextfun; intro x; rewrite <- ht2, <- ht1 ]).
Defined.

Require UniMath.CategoryTheory.Limits.Graphs.BinProducts.

(** *** Binary products from limits ([BinProductsHSET_from_Lims]) *)

Lemma BinProductsHSET_from_Lims : Graphs.BinProducts.BinProducts HSET.
Proof.
  now apply BinProducts.BinProducts_from_Lims, LimsHSET_of_shape.
Defined.

(** ** General indexed products ([ProductsHSET]) *)

Lemma ProductsHSET (I : UU) : Products I HSET.
Proof.
intros A.
use make_Product.
- exists (∏ i, pr1 (A i)); apply isaset_forall_hSet.
- simpl; intros i f; apply (f i).
- apply make_isProduct; try apply homset_property.
  intros C f; simpl in *.
  use tpair.
  * exists (λ c i, f i c); intro i; apply idpath.
   * abstract (intros h; apply subtypePath; simpl;
       [ intro; apply impred; intro; apply has_homsets_HSET
       | destruct h as [t ht]; simpl; apply funextfun; intro x;
         apply funextsec; intro i; rewrite <- ht; apply idpath ]).
Defined.

(** ** Terminal object [TerminalHSET] *)

Lemma TerminalHSET : Terminal HSET.
Proof.
  apply (make_Terminal unitHSET).
  apply make_isTerminal; intro a.
  exists (λ _, tt).
  abstract (simpl; intro f; apply funextfun; intro x; case (f x); apply idpath).
Defined.

(** *** Terminal object from general limits [TerminalHSET_from_Lims] *)

Require UniMath.CategoryTheory.Limits.Graphs.Terminal.

Lemma TerminalHSET_from_Lims : Graphs.Terminal.Terminal HSET.
Proof.
  now apply Terminal.Terminal_from_Lims, LimsHSET_of_shape.
Defined.

(** ** Pullbacks [PullbacksHSET] *)

Definition PullbackHSET_ob {A B C : HSET} (f : HSET⟦B,A⟧) (g : HSET⟦C,A⟧) : HSET.
Proof.
  exists (∑ (xy : setdirprod B C), f (pr1 xy) = g (pr2 xy)).
  abstract (apply isaset_total2; [ apply isasetdirprod; apply setproperty
                                 | intros xy; apply isasetaprop, setproperty ]).
Defined.

Lemma PullbacksHSET : Pullbacks HSET.
Proof.
intros A B C f g.
use make_Pullback.
  + apply (PullbackHSET_ob f g).
  + intros xy; apply (pr1 (pr1 xy)).
  + intros xy; apply (pr2 (pr1 xy)).
  + abstract (apply funextsec; intros [[x y] Hxy]; apply Hxy).
  + use make_isPullback.
    intros X f1 f2 Hf12; cbn.
    use unique_exists.
    - intros x.
      exists (f1 x,,f2 x); abstract (apply (toforallpaths _ _ _ Hf12)).
    - abstract (now split).
    - abstract (now intros h; apply isapropdirprod; apply has_homsets_HSET).
    - abstract (intros h [H1 H2]; apply funextsec; intro x;
      apply subtypePath; [intros H; apply setproperty|]; simpl;
      now rewrite <- (toforallpaths _ _ _ H1 x), <- (toforallpaths _ _ _ H2 x)).
Defined.

(** * Elements of pullbacks of sets *)
Definition el_pullback_set
           {X₁ X₂ Y₁ Y₂ : hSet}
           {f₁ : Y₁ → Y₂}
           {f₂ : X₂ → Y₂}
           {g₁ : X₁ → X₂}
           {g₂ : X₁ → Y₁}
           {p : (λ x, f₁(g₂ x)) = (λ x, f₂(g₁ x))}
           (Hp : isPullback (C := SET) p)
           (y : Y₁)
           (x : X₂)
           (q : f₁ y = f₂ x)
  : X₁.
Proof.
  pose (P := make_Pullback _ Hp).
  simple refine (PullbackArrow P unitset _ _ _ tt).
  - exact (λ _, y).
  - exact (λ _, x).
  - abstract
      (use funextsec ; intro ;
       exact q).
Defined.

Proposition el_pullback_set_pr1
            {X₁ X₂ Y₁ Y₂ : hSet}
            {f₁ : Y₁ → Y₂}
            {f₂ : X₂ → Y₂}
            {g₁ : X₁ → X₂}
            {g₂ : X₁ → Y₁}
            {p : (λ x, f₁(g₂ x)) = (λ x, f₂(g₁ x))}
            (Hp : isPullback (C := SET) p)
            (y : Y₁)
            (x : X₂)
            (q : f₁ y = f₂ x)
  : g₂ (el_pullback_set Hp y x q) = y.
Proof.
  pose (P := make_Pullback _ Hp).
  use (eqtohomot (PullbackArrow_PullbackPr1 P _ _ _ _)).
Qed.

Proposition el_pullback_set_pr2
            {X₁ X₂ Y₁ Y₂ : hSet}
            {f₁ : Y₁ → Y₂}
            {f₂ : X₂ → Y₂}
            {g₁ : X₁ → X₂}
            {g₂ : X₁ → Y₁}
            {p : (λ x, f₁(g₂ x)) = (λ x, f₂(g₁ x))}
            (Hp : isPullback (C := SET) p)
            (y : Y₁)
            (x : X₂)
            (q : f₁ y = f₂ x)
  : g₁ (el_pullback_set Hp y x q) = x.
Proof.
  pose (P := make_Pullback _ Hp).
  use (eqtohomot (PullbackArrow_PullbackPr2 P _ _ _ _)).
Qed.

(** *** Pullbacks from general limits [PullbacksHSET_from_Lims] *)

Require UniMath.CategoryTheory.Limits.Graphs.Pullbacks.

Lemma PullbacksHSET_from_Lims : Graphs.Pullbacks.Pullbacks HSET.
Proof.
  apply (Graphs.Pullbacks.Pullbacks_from_Lims HSET LimsHSET).
Defined.

(** *** Pullbacks of arrows from [unit] as inverse images *)

(** The set [hfiber f y] is a pullback of a diagram involving an arrow
    from [TerminalHSET], i.e. [unit].

    In particular, A pullback diagram of shape
<<
      Z --- ! --> unit
      |            |
      |            | y
      V            V
      X --- f -->  Y
>>
    makes [Z] (isomorphic to) the inverse image of a point [y : Y] under [f].
 *)

(** A translation of [weqfunfromunit] into the language of category theory,
    to make the statement of the next lemmas more concise. *)
Lemma weqfunfromunit_HSET (X : hSet) : HSET⟦TerminalHSET, X⟧ ≃ X.
Proof.
  apply weqfunfromunit.
Defined.

Local Lemma tosecoverunit_compute {X : UU} {x : X} :
  ∏ t, tosecoverunit (λ _ : unit, X) x t = x.
Proof.
  abstract (induction t; reflexivity).
Qed.

Lemma hfiber_is_pullback {X Y : hSet} (f : HSET⟦X, Y⟧)
      (y : Y) (y' := invweq (weqfunfromunit_HSET _) y) :
  ∑ H, @isPullback _ _ _ _ _ f y' (hfiberpr1 f y : HSET⟦hfiber_hSet f y , X⟧)
                       (TerminalArrow TerminalHSET _) H.
Proof.
  use tpair.
  - apply funextfun; intro.
    apply hfiberpr2.
  - intros pb pbpr1 pbpr2 pbH.

    (** First, simplify what we have to prove.
        Part of the condition is trivial. *)
    use iscontrweqb.
    + exact (∑ hk : HSET ⟦ pb, hfiber_hSet f y ⟧,
              hk · hfiberpr1 f y = pbpr1).
    + apply weqfibtototal; intro.
      apply invweq.
      apply dirprod_with_contr_r.
      use make_iscontr.
      * apply isapropifcontr.
        apply TerminalHSET.
      * intro; apply proofirrelevance; apply homset_property.
    + unfold hfiber_hSet, hfiber; cbn.
      use make_iscontr.
      * use tpair.
        intros pb0.
        use tpair.
        -- exact (pbpr1 pb0).
        -- cbn.
           apply toforallpaths in pbH.
           specialize (pbH pb0); cbn in pbH.
           refine (pbH @ _).
           apply tosecoverunit_compute.
        -- apply idpath.
      * intros t.
        apply subtypePath.
        -- intro; apply has_homsets_HSET.
        -- cbn.
           apply funextfun; intro; cbn.
           apply subtypePath.
           ++ intro; apply setproperty.
           ++ apply (toforallpaths _ _ _ (pr2 t)).
Defined.

(** ** Equalizers from general limits [EqualizersHSET_from_Lims] *)

Require UniMath.CategoryTheory.Limits.Graphs.Equalizers.

Lemma EqualizersHSET_from_Lims : Graphs.Equalizers.Equalizers HSET.
Proof.
  apply (Graphs.Equalizers.Equalizers_from_Lims HSET LimsHSET).
Defined.

(** HSET Pullbacks and Equalizers from limits to direct definition *)
Section HSET_Structures.

  Definition HSET_Pullbacks : @Limits.Pullbacks.Pullbacks HSET :=
    equiv_Pullbacks_2 HSET PullbacksHSET_from_Lims.

  Definition HSET_Equalizers: @Limits.Equalizers.Equalizers HSET :=
    equiv_Equalizers2 HSET EqualizersHSET_from_Lims.

End HSET_Structures.

(**
 Concrete construction of equalizers of sets
 *)
Definition Equalizers_in_HSET
  : Equalizers HSET.
Proof.
  intros X Y f g ; cbn in *.
  simple refine ((_ ,, _) ,, _ ,, _).
  - exact (∑ (x : X), hProp_to_hSet (eqset (f x) (g x)))%set.
  - exact (λ x, pr1 x).
  - abstract
      (use funextsec ;
       intro z ; cbn ;
       exact (pr2 z)).
  - intros W h p.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use funextsec ;
         intro w ;
         use subtypePath ; [ intro ; apply setproperty | ] ;
         exact (eqtohomot (pr2 φ₁ @ !(pr2 φ₂)) w)).
    + simple refine (_ ,, _).
      * exact (λ w, h w ,, eqtohomot p w).
      * apply idpath.
Defined.
