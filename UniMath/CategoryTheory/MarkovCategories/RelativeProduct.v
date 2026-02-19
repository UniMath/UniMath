(*********************************************
Relative Product

In this file, we develop dagger-categorical results about the 
dagger categories [prob_space C] of probability spaces and [couplings C] of couplings.
As these categories are dagger equivalent, it suffices to develop the theory for one of them;
we choose couplings as working with probability spaces involves quotients.

The core results are 
* almost surely deterministic maps can be identified with coisometries
* the relative product construction on probability spaces has the universal property of a dilator

Table of Contents
1. Results relating Coisometries and Almost-Sure Determinism 
2. Relative Product and Dilators in Couplings [couplings C]
3. Relative Product and Dilators in Probability Spaces [prob_space C]

References
- Matthew Di Meglio, Chris Heunen, Jean-Simon Pacaud Lemay, Paolo Perrone, Dario Stein:
  'Dagger categories of relations: the equivalence of dilatory dagger categories
                                   and epi-regular independence categories'
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Categories.Quotient.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.
Require Import UniMath.CategoryTheory.MarkovCategories.Determinism.
Require Import UniMath.CategoryTheory.MarkovCategories.State.
Require Import UniMath.CategoryTheory.MarkovCategories.InformationFlowAxioms.
Require Import UniMath.CategoryTheory.MarkovCategories.AlmostSurely.
Require Import UniMath.CategoryTheory.MarkovCategories.Conditionals.
Require Import UniMath.CategoryTheory.MarkovCategories.Couplings.
Require Import UniMath.CategoryTheory.MarkovCategories.ProbabilitySpaces.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.DaggerCategories.Isometry.
Require Import UniMath.CategoryTheory.DaggerCategories.Dilators.
Require Import UniMath.CategoryTheory.DaggerCategories.Univalence.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope markov.

(** * 1. Results relating Coisometries and Almost-Sure Determinism *)

Section DaggerLemmas.
  Context {C : markov_category_with_conditionals}.

  Proposition ase_determinism_coisometry {x y : C} (p : I_{C} --> x) (f : x --> y) :
       is_deterministic_ase p f 
    -> (bayesian_inverse p f) · f =_{p·f} identity y.
  Proof.
    intros det_ase.
    apply make_equal_almost_surely_r.
    
    etrans. {
      rewrite <- pairing_tensor_r, assoc.
      rewrite bayesian_inverse_eq_r, assoc'.
      rewrite pairing_tensor_r, id_left.
      reflexivity. }

    rewrite pairing_id.
    rewrite pairing_eq.
    rewrite assoc'.
    
    use ase_precomp.
    apply ase_symm.
    exact det_ase.
  Qed.

  Proposition coisometry_ase_deterministic {x y : C} (p : I_{C} --> x) (f : x --> y) :
    (bayesian_inverse p f) · f =_{p·f} identity y -> is_deterministic_ase p f.
  Proof.
    intros e.
    use relpos_coisometry_lemma.
    - apply conditionals_imply_relative_positivity.
    - exact (bayesian_inverse p f).
    - apply bayesian_inverse_eq.
    - exact e.
  Qed.

End DaggerLemmas.

Section DaggerPropositions.
  Context {C : markov_category_with_conditionals}.

  Let C_is_causal : is_causal C := conditionals_imply_causality. 
  Let PS := prob_space (C_is_causal).

  Let dag : dagger PS := prob_space_dagger C.

  Local Lemma isos_coisometry_aux {x y : PS} :
    ∏ (ff : x --> y) (gg : y --> x)
    (inv_ffgg : ff · gg = identity _) (inv_ggff : gg · ff = identity _), is_coisometry dag ff.
  Proof.
    destruct x as [x p], y as [y q].

    use setquotunivprop'. { do 3 (intro; use impred). intro. apply homset_property. }
    intros [f presf].  
    use setquotunivprop'. { do 2 (intro; use impred). intro. apply homset_property. }
    intros [g presg] inv_fg inv_gf.
    apply iscompsetquotpr.
    cbn. 
    pose(ase_fg := setquotpreq _ _ _ inv_fg).
    cbn in ase_fg.

    do 2 cbn in presf.
    rewrite <- presf.
    apply ase_determinism_coisometry.
    use relpos_coisometry_lemma.
    - apply conditionals_imply_relative_positivity.
    - exact g.
    - apply splitting_to_bayesian_inverse.
      * apply conditionals_imply_relative_positivity.
      * exact ase_fg.
    - pose(ase_gf := setquotpreq _ _ _ inv_gf).
      cbn in ase_gf.
      rewrite presf.
      exact ase_gf.
  Qed.

  Proposition isos_coisometry {x y : PS} (phi : z_iso x y) : is_coisometry dag phi.
  Proof.
    use isos_coisometry_aux.
    - apply z_iso_inv.
      exact phi.
    - apply z_iso_inv_after_z_iso.
    - apply z_iso_after_z_iso_inv.
  Qed.  

  Proposition isos_unitary {x y : PS} (f : z_iso x y) : is_unitary dag f.
  Proof.
    apply z_iso_coisometry_unitary.
    apply isos_coisometry.
  Qed.

End DaggerPropositions.

(** * 2. Relative Product and Dilators in Couplings [couplings C] *)

(* Some lemmas about coisometries in couplings *)

Section CouplingCoisometries.
  Context {C : markov_category_with_conditionals}.
  Let krn := couplings_dagger_cat C.

 Proposition bloom_coupling_coiso {p q : state C} {γ : coupling p q}
    (f : state_ob p --> state_ob q)
    (e : coupling_to_state γ = bloom_coupling p f)
    (det_ase : is_deterministic_ase p f)
    : is_coisometry krn γ.
  Proof.
    apply coupling_ext.
    cbn.
    rewrite e.
    rewrite bloom_dilation_composition.
    unfold dilation_coupling, identity_coupling.
    assert (cod : p · f = q). { 
      rewrite <- bloom_coupling_cod.
      rewrite <- e.
      apply coupling_cod.
    }
    rewrite <- cod, assoc'.
    apply ase_precomp.
    apply ase_symm.
    exact det_ase.
  Qed.

  Proposition det_ase_from_coiso {p q : state C} {γ : coupling p q}
    (f : state_ob p --> state_ob q)
    (e : coupling_to_state γ = bloom_coupling p f)
    (coisom : is_coisometry krn γ)
    : is_deterministic_ase p f.
  Proof.
    use coisometry_ase_deterministic.
    apply make_equal_almost_surely_r.
    etrans. {
      rewrite <- pairing_tensor_r, assoc.
      rewrite bayesian_inverse_eq_r.
      rewrite assoc', pairing_tensor_r, id_left.
      reflexivity.
    }
    unfold is_coisometry in coisom.
    assert(c := maponpaths coupling_to_state coisom).
    cbn in c.
    rewrite e in c.
    rewrite bloom_dilation_composition in c.
    unfold dilation_coupling, identity_coupling in c.
    rewrite c.
    rewrite pairing_id.
    apply maponpaths_2.
    rewrite <- bloom_coupling_cod.
    rewrite <- e.
    rewrite coupling_cod.
    reflexivity.
  Qed.  
  
  Definition make_bloom_coisometry {p q : state C}
    (f : state_ob p --> state_ob q)
    (e : p · f = q)
    (det_ase : is_deterministic_ase p f)
    : coisometry krn p q.
  Proof.
    use make_coisometry.
    - use make_coupling.
      * exact (bloom_coupling p f).
      * abstract (rewrite bloom_coupling_dom; reflexivity).
      * abstract (rewrite bloom_coupling_cod; exact e).
    - use bloom_coupling_coiso.
      * exact f.
      * reflexivity.
      * exact det_ase.
  Defined.

End CouplingCoisometries.

(* Relative products and dilators in couplings *)
Section CouplingDilators.
  Context {C : markov_category_with_conditionals}.
  Let krn := couplings_dagger_cat C.

  Definition relprod {p q : krn} (γ : p --> q) : krn.
  Proof.
    destruct p as [x p], q as [y q], γ as [γ [domγ codγ]].
    exact (x ⊗ y ,, γ).
  Defined.

  Definition p1 {p q : krn} (γ : p --> q) : coisometry krn (relprod γ) p.
  Proof.
    use make_bloom_coisometry.
    - exact proj1.
    - apply coupling_dom.
    - apply deterministic_implies_determinstic_ase.
      apply is_deterministic_proj1.
  Defined.
  
  Definition p2 {p q : krn} (γ : p --> q) : coisometry krn (relprod γ) q.
  Proof.
    use make_bloom_coisometry.
    - exact proj2.
    - apply coupling_cod.
    - apply deterministic_implies_determinstic_ase.
      apply is_deterministic_proj2.
  Defined.

  Proposition relprod_dilation_eq {p q : krn} (γ : p --> q) :
    {p1 γ}_krn^† · (p2 γ) = γ.
  Proof.
    apply coupling_ext.
    unfold p1, p2.
    cbn.
    rewrite bloom_dilation_composition.
    unfold dilation_coupling.
    rewrite pairing_proj_id, id_right.
    reflexivity.
  Qed.

  Definition relprod_dilation {p q : krn} (γ : p --> q) : dilation krn γ.
  Proof.
    destruct p as [x p], q as [y q].
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (relprod γ).
    - apply p1.
    - apply p2.
    - apply relprod_dilation_eq. 
  Defined.

  (* Show that [relprod_dilation] is a dilator, i.e. a terminal dilation *)
  Section Terminal.
    Context {p q : krn}
            (γ : p --> q)
            (d : dilation krn γ).

    Let x : C := state_ob p.
    Let y : C := state_ob q. 
    Let w : C := state_ob (apex d).
    Let r : I_{C} --> w := state_dist (apex d).

    Let left_coupling := (coisometry_to_mor (left_leg d)).
    Let right_coupling := (coisometry_to_mor (right_leg d)).

    Let left := coupling_to_state left_coupling.
    Let right := coupling_to_state right_coupling.

    Let f : w --> x := coupling_cond left_coupling.
    Let g : w --> y := coupling_cond right_coupling.

    Local Lemma d_dil : r · ⟨f,g⟩ = coupling_to_state γ.
    Proof.
      rewrite <- (dilation_eq _ d).
      cbn.

      (* `rewrite` fails here, so we need to do rewriting manually *)
      symmetry.
      etrans. {
        apply maponpaths_2.
        apply maponpaths.
        assert (xx : coupling_to_state (coisometry_to_mor (left_leg d)) = left). { reflexivity. }
        exact xx.
      }
      etrans. {
        apply maponpaths.
        assert (xx : coupling_to_state (coisometry_to_mor (right_leg d)) = right). { reflexivity. }
        exact xx.
      }
      
      rewrite (coupling_is_bloom_coupling left).
      rewrite (coupling_is_bloom_coupling right).

      assert(e1 : left · proj1 = r). { apply coupling_dom. }
      assert(e2 : right · proj1 = r). { apply coupling_dom. }
      rewrite e1, e2.

      rewrite bloom_dilation_composition.
      reflexivity.
    Qed.
    
    (** Existence: Construct the required mediating map [h] *)

    Definition h : krn ⟦ d, relprod_dilation γ ⟧.
    Proof.
      use make_coupling.
      - exact (bloom_coupling r ⟨f,g⟩).
      - abstract (apply bloom_coupling_dom).
      - abstract (rewrite bloom_coupling_cod; exact d_dil).
    Defined.       
    
    Local Lemma f_det : is_deterministic_ase r f.
    Proof.
      use det_ase_from_coiso.
      - exact left_coupling.
      - apply coupling_is_bloom_cond.     
      - apply coisometry_property.
    Qed.   

    Local Lemma g_det : is_deterministic_ase r g.
    Proof.
      use det_ase_from_coiso.
      - exact right_coupling.
      - apply coupling_is_bloom_cond.
      - apply coisometry_property.
    Qed.  

    Definition h_is_coisometry : is_coisometry krn h.
    Proof.
      use bloom_coupling_coiso.
      - exact ⟨f,g⟩.
      - reflexivity.
      - use is_deterministic_ase_pairing.
        * exact f_det.
        * exact g_det.
    Qed.   
      
    Definition h_coisometry : coisometry krn d (relprod_dilation γ).
    Proof.
      use make_coisometry.
      - exact h.
      - exact h_is_coisometry.
    Defined.  

    Proposition h_left : h_coisometry · left_leg (relprod_dilation γ) = left_leg d.
    Proof.
      apply coupling_ext.
      cbn.
      etrans. {
        apply maponpaths.
        apply maponpaths_2.
        symmetry.
        apply d_dil.
      } 
      rewrite bloom_coupling_composition.
      rewrite pairing_proj1.
      rewrite coupling_is_bloom_coupling.
      rewrite coupling_dom.
      reflexivity.
    Qed.

    Proposition h_right : h_coisometry · right_leg (relprod_dilation γ) = right_leg d.
    Proof.
      apply coupling_ext.
      cbn.
      etrans. {
        apply maponpaths.
        apply maponpaths_2.
        symmetry.
        apply d_dil.
      } 
      rewrite bloom_coupling_composition.
      rewrite pairing_proj2.
      rewrite coupling_is_bloom_coupling.
      rewrite coupling_dom.
      reflexivity.
    Qed.
    
    Proposition relprod_dilation_factorization 
      : dilation_map krn d (relprod_dilation γ).
    Proof.
      use make_dilation_map_from_coisometries.
      - exact h_coisometry.
      - apply h_left.
      - apply h_right.
    Defined.     

    (** Uniqueness: Show that any other dilation map is equal to the one constructed *)

    Context (other : dilation_map krn d (relprod_dilation γ)).

    Let σ := coupling_to_state (coisometry_to_mor other).
    Let s : w --> x ⊗ y := coupling_cond other.

    (* We claim that s = h *)

    Local Lemma σ_pi1 : other · p1 γ = left_coupling.
    Proof.
      apply dilation_map_eq_left.
    Qed.
    
    Local Lemma σ_pi2 : other · p2 γ = right_coupling.
    Proof.
      apply dilation_map_eq_right.
    Qed.

    Local Lemma σ_is_bloom : σ = bloom_coupling r s.
    Proof.
      rewrite (coupling_is_bloom_coupling σ).
      apply maponpaths_2.
      apply coupling_dom.
    Qed. 

    Local Lemma rs : r · s = coupling_to_state γ.
    Proof.
      rewrite <- bloom_coupling_cod.
      rewrite <- σ_is_bloom.
      apply coupling_cod.
    Qed.

    Local Lemma s1 : bloom_coupling r (s · proj1) = coupling_to_state left_coupling.
    Proof.
      rewrite <- σ_pi1.
      cbn. 
      symmetry.
      etrans. {
        apply maponpaths_2.
        assert(tmp : coupling_to_state (coisometry_to_mor (dilation_map_to_coisom krn other)) = σ).
        { reflexivity. }
        exact tmp.
      }
      rewrite σ_is_bloom.
      etrans. {
        apply maponpaths.
        apply maponpaths_2.
        exact (!rs).
      }
      rewrite bloom_coupling_composition.
      reflexivity.
    Qed.

    Local Lemma s2 : bloom_coupling r (s · proj2) = coupling_to_state right_coupling.
    Proof.
      rewrite <- σ_pi2.
      cbn. 
      symmetry.
      etrans. {
        apply maponpaths_2.
        assert(tmp : coupling_to_state (coisometry_to_mor (dilation_map_to_coisom krn other)) = σ).
        { reflexivity. }
        exact tmp.
      }
      rewrite σ_is_bloom.
      etrans. {
        apply maponpaths.
        apply maponpaths_2.
        exact (!rs).
      }
      rewrite bloom_coupling_composition.
      reflexivity.
    Qed.

    Local Lemma s1_ase_f : (s · proj1) =_{r} f.
    Proof.
      apply make_ase_from_bloom_coupling.
      rewrite s1.
      etrans. { apply coupling_is_bloom_coupling. }
      apply maponpaths_2.
      apply coupling_dom.
    Qed.

    Local Lemma s2_ase_g : (s · proj2) =_{r} g.
    Proof.
      apply make_ase_from_bloom_coupling.
      rewrite s2.
      etrans. { apply coupling_is_bloom_coupling. }
      apply maponpaths_2.
      apply coupling_dom.
    Qed.

    Local Lemma s_ase : s =_{r} ⟨f,g⟩.
    Proof.
      (* by relative positivity, s is the pairing of its marginals *)
      apply ase_trans with (⟨s · proj1, s · proj2⟩). {
        use deterministic_marginal_independence_ase_1.
        - apply conditionals_imply_relative_positivity.
        - apply is_deterministic_ase_stable with f.
          * apply ase_symm; exact s1_ase_f.
          * exact f_det.   
      }
      (* but those marginals are f ... *)
      apply ase_trans with (⟨f, s · proj2⟩). {
        apply ase_pairing_l.
        exact s1_ase_f.
      }
      (* ... and g respectively *)
      apply ase_pairing_r.
      exact s2_ase_g.
    Qed.     

    Proposition uniqueness : σ = coupling_to_state h.
    Proof.
      rewrite σ_is_bloom.
      cbn.
      apply bloom_coupling_eq_from_ase. 
      exact s_ase.
    Qed.

    Proposition relprod_dilation_factorization_uniqueness
      : other = relprod_dilation_factorization.
    Proof.
      apply dilation_map_ext.
      apply coisometry_ext.
      apply coupling_ext.
      cbn.
      transitivity σ. { reflexivity. }
      apply uniqueness.
    Qed.
    
  End Terminal.

  Proposition coupling_dilator_is_dilator {p q : krn} (γ : p --> q) : 
    is_dilator krn (relprod_dilation γ).
  Proof.
    intros d.
    use make_iscontr.
    - apply relprod_dilation_factorization.
    - apply relprod_dilation_factorization_uniqueness. 
  Qed.

  Definition coupling_dilator {p q : krn} (γ : p --> q) : dilator krn γ.
  Proof.
    exists (relprod_dilation γ).
    apply coupling_dilator_is_dilator.
  Defined.

  Definition couplings_have_dilators : with_dilators krn.
  Proof.
    intros p q γ.
    exact (coupling_dilator γ).
  Defined.

End CouplingDilators.


(** * 3. Relative Product and Dilators in Probability Spaces [prob_space C] *)

Section Dilators.
  Context {C : markov_category_with_conditionals}.
  Let PS := prob_space_dagger_cat C.

  (* Transfer the dilators from couplings to probability spaces *)
  Definition ps_have_dilators : with_dilators PS.
  Proof.
    unfold PS.
    rewrite <- couplings_equals_ps_dagger.
    apply couplings_have_dilators.
  Defined.

  (* TODO: be more explicit here. 
    e.g. manually construct the bloom dilation and 
    show that it fixed by the equivalence *)
  
  Definition hProj {X : UU} (i : isaset X) (x : make_hSet X i) : X.
  Proof.
    exact x.
  Defined.

  Definition bloom_space {p q : PS} (f : p --> q) : PS.
  Proof.
    destruct p as [x p], q as [y q].
    refine (x ⊗ y ,, _).
    use hProj. { apply homset_property. } 
    revert f.
    use setquotuniv.
    - intros [f e].
      exact (bloom_coupling p f).
    - intros [f e] [g h] ase.
      unfold bloom_coupling.
      apply equal_almost_surely_r.
      exact ase.
  Defined.

  Definition bloom_space_proj1 {p q : PS} (f : p --> q) : (bloom_space f) --> p.
  Proof.
    use hProj. { apply homset_property. } 
    revert f.
    (* TODO *)
  Abort.

End Dilators.