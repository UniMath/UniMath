(** ** Refinement of M-types

    M-types can be refined to satisfy the right definitional equalities.
    This idea is from Felix Rech's Bachelor's thesis, and Felix
    Rech also developed together with Luis Scoccola a first formalization
    in UniMath as project work of the UniMath 2017 school. The present
    formalization was obtained as project work of the UniMath 2019 school
    and is heavily inspired by that former formalization.

    Author: Dominik Kirst (@dominik-kirst) and Ralph Matthes (@rmatthes)

    massive overhaul by Ralph Matthes (May to July 2025):
    - clearer mathematical display of what the refinement brings w.r.t.
      the supposed final coalgebra
    - computable elements are now called purely coiterative elements, and
      their property is isolated
    - more typing information given
    - better use of documentation facilities
    - new lemma destrM'_aux to encapsulate the equational part of destrM'
    - more readable proof of eq_corecM0
    - the crucial element of the overhaul is the total rewrite of the proof
      of Lemma P_isaprop that now tries to generate the new goals as much as
      possible, while the previous version announced the intermediate goals
      through intermediate_weq with formulas conceived in the UniMath 2017
      school formalization

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Induction.FunctorCoalgebras_legacy.
Require Import UniMath.CategoryTheory.Categories.Type.Core.

Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.M.Core.
Require Import UniMath.Induction.M.Uniqueness.

(**
    The construction is called a refinement: as input we take any final coalgebra
    for the respective polynomial functor describing an M-type  (hence, with the
    provable coiteration rule), the output is the refined final coalgebra with the
    equational rule of coiteration holding definitionally: Lemma [corec_computation]
    is proved merely by [idpath]. Of course, both coalgebras are equal - provably
    (Lemma [coalgebras_eq]).
 *)
Local Open Scope cat.

Section Refinement.

  Context (A : UU).
  Context (B : A → UU).

  Local Definition F : type_precat ⟶ type_precat
    := polynomial_functor A B.

  Variable M0 : coalgebra F.
  Local Definition carrierM0 : type_precat := coalgebra_ob F M0.
  Local Definition destrM0 : type_precat ⟦ carrierM0, F carrierM0 ⟧
    := coalgebra_mor F M0.

  Variable finalM0 : is_final M0.
  Local Definition corecM0 (C : coalgebra F) : type_precat ⟦ coalgebra_ob F C, carrierM0 ⟧
    := pr1 (iscontrpr1 (finalM0 C)).

  Lemma corec_equational_aux (C : coalgebra F) (c : coalgebra_ob F C) : is_coalgebra_homo F (corecM0 C).
  Proof.
    exact (pr2 (iscontrpr1 (finalM0 C))).
  Defined. (* defined because the target of the morphisms is a precategory only *)

  (** recall the provable equation governing corec *)
  Lemma corec_equational (C : coalgebra F) (c : coalgebra_ob F C) :
    destrM0 (corecM0 C c) = # F (corecM0 C) (coalgebra_mor F C c).
  Proof.
    set (aux := toforallpaths _ _ _ (corec_equational_aux C c)).
    apply pathsinv0, aux.
  Defined.

  Local Open Scope functions.

  (** refinement of the final coalgebra to purely coiterative elements *)
  Definition is_purelycoiterativeM0 (m0 : carrierM0) : UU := ∃ (C : coalgebra F) (c : coalgebra_ob F C), corecM0 C c = m0.

  Definition carrierM : UU := total2 is_purelycoiterativeM0.

  (* Check (carrierM = ∑ m0 : carrierM0, ∃ (C : coalgebra F) (c : coalgebra_ob F C), corecM0 C c = m0). *)

  (** definition of the corecursor *)
  Definition corecM (C : coalgebra F) (c : coalgebra_ob F C) : carrierM.
  Proof.
    exists (corecM0 C c). apply hinhpr. exists C, c. apply idpath.
  Defined.

  (** a form of functoriality of [F] w.r.t. convertibility *)
  Lemma corecM_corecM0 (C : coalgebra F) (cf: F (coalgebra_ob F C)) :
    #F pr1 (#F (corecM C) cf) = #F (corecM0 C) cf.
  Proof.
    apply idpath.
  Defined.

  (** definition of a proposition we factor the computation through *)
  Local Definition P (m0 : carrierM0) : UU
    := ∑ af : F carrierM, destrM0 m0 = # F pr1 af.

  (** in order to show [P] to be a proposition, a not obviously equivalent
    formulation is given for which it is easy to show [isaprop] *)
  Local Definition P' (m0 : carrierM0) : UU :=
    ∑ ap : (∑ a : A, pr1 (destrM0 m0) = a),
                 ∏ b : B (pr1 ap),
                 ∑ mp : (∑ m0' : carrierM0,
                                transportf (λ a : A, B a  -> carrierM0)
                                           (pr2 ap)
                                           (pr2 (destrM0 m0)) b =
                                m0'),
                                is_purelycoiterativeM0 (pr1 mp).

  (** the easy auxiliary lemma *)
  Local Lemma P'_isaprop (m0 : carrierM0) : isaprop (P' m0).
  Proof.
    apply isofhleveltotal2.
    - apply isofhlevelcontr.
      apply iscontrcoconusfromt.
    - intro ap; induction ap as [a p].
      apply impred; intros b.
      apply isofhleveltotal2.
      + apply isofhlevelcontr.
        apply iscontrcoconusfromt.
      + intro mp; induction mp as [m0' q].
        apply isapropishinh.
  Defined.

  (** the crucial lemma *)
  Local Lemma P_isaprop (m0 : carrierM0) : isaprop (P m0).
  Proof.
    use (@isofhlevelweqb _ _ (P' m0) _ (P'_isaprop m0)).
    eapply weqcomp.
    { apply weqtotal2asstor. }
    (* working on the right end: *)
    eapply weqcomp.
    2: { apply invweq.
         apply weqtotal2asstor. }
    (* reducing the problem: *)
    apply weqfibtototal; intro a.
    eapply weqcomp.
    { apply weqfibtototal; intro f.
      apply total2_paths_equiv.
    }
    unfold PathPair. simpl.
    eapply weqcomp.
    { apply weqtotal2comm. }
    (* reducing the problem: *)
    apply weqfibtototal; intro p.
    (* the next line serves to illustrate the the right-hand side will not be touched during the next five transformations *)
    match goal with |[ |- _ ≃ ?rhs] => set (therhs := rhs) end.
    eapply weqcomp.
    { set (H1 := weqfuntototaltototal (B a) is_purelycoiterativeM0).
      apply (weqbandf H1 _ (fun fg => transportf (λ a : A, B a -> carrierM0) p (pr2 (destrM0 m0)) = pr1 fg)). (* the second argument to [weqbandf] is [fun f => transportf (λ x : A, B x → carrierM0) p (pr2 (destrM0 m0)) = pr1 ∘ f] *)
      (* solving a trivial subproblem: *)
      cbn.
      intro f.
      apply idweq.
    }
    simpl.
    eapply weqcomp.
    { apply weqtotal2asstor. }
    simpl.
    eapply weqcomp.
    { apply weqfibtototal; intro f.
      apply weqfibtototal; intro Hyp.
      apply weqtoforallpaths.
    }
    simpl.
    unfold homot.
    eapply weqcomp.
    { apply weqfibtototal; intro f.
      apply invweq.
      apply (weqforalltototal _ (fun x _ => transportf (λ a0 : A, B a0 → carrierM0) p (pr2 (destrM0 m0)) x = f x)). (* the first argument to [weqforalltototal] is [fun x => is_computableM0 (f x)] *)
    }
    simpl.
    eapply weqcomp.
    { apply invweq.
      apply (weqforalltototal _ (fun b y => ∑ _ : is_purelycoiterativeM0 y, transportf (λ a0 : A, B a0 → carrierM0) p (pr2 (destrM0 m0)) b = y)). (* the first argument to [weqforalltototal] is [fun _ => carrierM0] *)
    }
    (* reducing the problem: *)
    apply weqonsecfibers; intro b.
    (* no longer need to illustrate the fixed right-hand side: *)
    clear therhs.
    eapply weqcomp.
    { apply weqfibtototal; intro m0'.
      apply weqdirprodcomm.
    }
    simpl.
    (* the final step is on the current right-hand side: *)
    apply invweq.
    apply weqtotal2asstor. (* the first argument to [weqtotal2asstor] is [fun x => transportf (λ a0 : A, B a0 → carrierM0) p (pr2 (destrM0 m0)) b = x], the second is [fun y => is_computableM0 (pr1 y)] *)
  Defined.

  (* Now the destructor of M can be defined *)

  Local Lemma destrM'_aux (m0 : carrierM0) (C : coalgebra F) (c : coalgebra_ob F C) (H1 : corecM0 C c = m0) :
    destrM0 m0 = # F pr1 ((# F (corecM C) ∘ coalgebra_mor F C) c).
  Proof.
    etrans.
    { rewrite <- H1. apply corec_equational. }
    apply pathsinv0, corecM_corecM0.
  Defined.

  Local Definition destrM' (m : carrierM) : P (pr1 m).
  Proof.
    induction m as [m0 H]. apply (squash_to_prop H); [apply P_isaprop|].
    intros [C [c H1]].
    exists ((# F (corecM C) ∘ (coalgebra_mor F C)) c).
    cbn [pr1].
    apply destrM'_aux.
    assumption.
  Defined.

  Definition destrM (m : carrierM) : F carrierM :=
    pr1 (destrM' m).

  Definition M : coalgebra F :=
    (carrierM,, destrM).

  (** the destructor satisfies the corecursion equation definitionally *)
  Lemma corec_computation (C : coalgebra F) (c : coalgebra_ob F C) :
    destrM (corecM C c) = # F (corecM C) (coalgebra_mor F C c).
  Proof.
    apply idpath.
  Defined.

  (** for the moment only an experiment *)
  Lemma truth_of_P (m0 : carrierM0) : P m0 -> is_purelycoiterativeM0 m0.
  Proof.
    intros [[a f] Hyp].
    simpl in Hyp.
    unfold polynomial_functor_arr in Hyp.
    simpl in Hyp.
  Abort. (* there should be a notion of computable element that is wider than purely coiterative *)

  (** the two carriers are equal *)
  Lemma eq_corecM0 (m0 : carrierM0) :
    corecM0 M0 m0 = m0.
  Proof.
    apply pathsinv0.
    assert (aux := path_to_ctr _ _ (finalM0 M0) (pr1 (coalgebra_homo_id F M0)) (pr2 (coalgebra_homo_id F M0))).
    apply toforallpaths in aux.
    apply aux.
  Defined.

  Definition injectM0 (m0 : carrierM0) :
    ∃ C c, corecM0 C c = m0.
  Proof.
    apply hinhpr. exists M0, m0. apply eq_corecM0.
  Defined.

  Lemma carriers_weq :
    carrierM ≃ carrierM0.
  Proof.
    apply (weq_iso pr1 (λ m0, m0,, injectM0 m0)).
    - intros [m H]. cbn. apply maponpaths, ishinh_irrel.
    - intros x. cbn. apply idpath.
  Defined.

  Lemma carriers_eq :
    carrierM = carrierM0.
  Proof.
    apply weqtopaths, carriers_weq.
  Defined. (** needs to be transparent *)

  (* The two coalgebras are equal *)

  Local Lemma eq1 (m0 : carrierM0) :
    transportf (λ X, X → F X) carriers_eq destrM m0
    = transportf (λ X, F X) carriers_eq (destrM (transportf (λ X, X) (!carriers_eq) m0)).
  Proof.
    destruct carriers_eq. apply idpath.
  Defined.

  Local Lemma eq2 (m0 : carrierM0) :
    transportf (λ X, X) (!carriers_eq) m0 = m0,, injectM0 m0.
  Proof.
    apply (transportf_pathsinv0' (idfun UU) carriers_eq).
    unfold carriers_eq. rewrite weqpath_transport. apply idpath.
  Defined.

  Local Lemma eq3 (m0 : carrierM0) :
    destrM (m0,, injectM0 m0) = pr1 (destrM0 m0),, corecM M0 ∘ pr2 (destrM0 m0).
  Proof.
    apply idpath.
  Defined.

  Lemma coalgebras_eq :
    M = M0.
  Proof.
    use total2_paths_f; [apply carriers_eq|].
    apply funextfun. intro m0.
    rewrite eq1. rewrite eq2. rewrite eq3.
    cbn. unfold polynomial_functor_obj.
    rewrite transportf_total2_const.
    use total2_paths_f; [apply idpath|].
    cbn. apply funextsec. intros b. rewrite <- UniMath.MoreFoundations.PartA.helper_A.
    unfold carriers_eq. rewrite weqpath_transport.
    cbn. rewrite eq_corecM0. apply idpath.
  Defined.

  (* Thus M is final *)

  Lemma finalM : is_final M.
  Proof.
    rewrite coalgebras_eq. apply finalM0.
  Defined.

End Refinement.
