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
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.limits.graphs.equalizers.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Require Import UniMath.CategoryTheory.categories.HSET.Core.

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

Require UniMath.CategoryTheory.limits.cats.limits.

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

Lemma cats_LimConeHSET : cats.limits.LimCone D.
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

Lemma cats_LimsHSET : cats.limits.Lims HSET.
Proof.
now intros g d; apply cats_LimConeHSET.
Defined.

Lemma cats_LimsHSET_of_shape (g : category) : cats.limits.Lims_of_shape g HSET.
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

Require UniMath.CategoryTheory.limits.graphs.binproducts.

(** *** Binary products from limits ([BinProductsHSET_from_Lims]) *)

Lemma BinProductsHSET_from_Lims : graphs.binproducts.BinProducts HSET.
Proof.
  now apply binproducts.BinProducts_from_Lims, LimsHSET_of_shape.
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

Lemma TerminalSET : Terminal HSET.
Proof.
  apply (make_Terminal unitHSET).
  apply make_isTerminal; intro a.
  exists (λ _, tt).
  abstract (simpl; intro f; apply funextfun; intro x; case (f x); apply idpath).
Defined.

(** *** Terminal object from general limits [TerminalHSET_from_Lims] *)

Require UniMath.CategoryTheory.limits.graphs.terminal.

Lemma TerminalHSET_from_Lims : graphs.terminal.Terminal HSET.
Proof.
  now apply terminal.Terminal_from_Lims, LimsHSET_of_shape.
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

(** *** Pullbacks from general limits [PullbacksHSET_from_Lims] *)

Require UniMath.CategoryTheory.limits.graphs.pullbacks.

Lemma PullbacksHSET_from_Lims : graphs.pullbacks.Pullbacks HSET.
Proof.
  apply (graphs.pullbacks.Pullbacks_from_Lims HSET LimsHSET).
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
Lemma weqfunfromunit_HSET (X : hSet) : HSET⟦TerminalSET, X⟧ ≃ X.
Proof.
  apply weqfunfromunit.
Defined.

(** The [hfiber] of a function between sets is also a set. *)
Definition hfiber_hSet {X Y : hSet} (f : HSET⟦X, Y⟧) (y : Y) : hSet.
Proof.
  use make_hSet.
  - exact (hfiber f y).
  - apply isaset_hfiber; apply setproperty.
Defined.

Local Lemma tosecoverunit_compute {X : UU} {x : X} :
  ∏ t, tosecoverunit (λ _ : unit, X) x t = x.
Proof.
  abstract (induction t; reflexivity).
Qed.

Local Definition hfiber_hSet_pr1 {X Y : hSet} (f : HSET⟦X, Y⟧) (y : Y) :
    HSET⟦hfiber_hSet f y, X⟧ := hfiberpr1 f y.

Lemma hfiber_is_pullback {X Y : hSet} (f : HSET⟦X, Y⟧)
      (y : Y) (y' := invweq (weqfunfromunit_HSET _) y) :
  ∑ H, @isPullback _ _ _ _ _ f y' (hfiber_hSet_pr1 f y)
                       (TerminalArrow TerminalSET _) H.
Proof.
  use tpair.
  - apply funextfun; intro.
    apply hfiberpr2.
  - intros pb pbpr1 pbpr2 pbH.

    (** First, simplify what we have to prove.
        Part of the condition is trivial. *)
    use iscontrweqb.
    + exact (∑ hk : HSET ⟦ pb, hfiber_hSet f y ⟧,
              hk · hfiber_hSet_pr1 f y = pbpr1).
    + apply weqfibtototal; intro.
      apply invweq.
      apply dirprod_with_contr_r.
      use make_iscontr.
      * apply proofirrelevance.
        apply hlevelntosn.
        apply (pr2 TerminalSET). (** TODO: should be an accessor *)
      * intro; apply proofirrelevance; apply setproperty.
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
        -- apply funextfun; intro; apply idpath.
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

Require UniMath.CategoryTheory.limits.graphs.equalizers.

Lemma EqualizersHSET_from_Lims : graphs.equalizers.Equalizers HSET.
Proof.
  apply (graphs.equalizers.Equalizers_from_Lims HSET LimsHSET).
Defined.

(** HSET Pullbacks and Equalizers from limits to direct definition *)
Section HSET_Structures.

  Definition HSET_Pullbacks : @limits.pullbacks.Pullbacks HSET :=
    equiv_Pullbacks_2 HSET PullbacksHSET_from_Lims.

  Definition HSET_Equalizers: @limits.equalizers.Equalizers HSET :=
    equiv_Equalizers2 HSET EqualizersHSET_from_Lims.

End HSET_Structures.
