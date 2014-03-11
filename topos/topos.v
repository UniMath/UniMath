Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.

Require Import RezkCompletion.limits.terminal.
Require Import RezkCompletion.limits.pullbacks.

Require Import RezkCompletion.topos.epis_monos.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).


Section subobject_classifier.

Variable C : precategory.

(* it seems that in order to state the subobject classifier axiom
   i need to ask C to have a terminal object sigma-wise 
   the basic instances of toposes (Set, presheaves) are univalent, however,
   so it doesn't make a difference
*)

Variable T : Terminal C.

Definition isSubobjectClassifier (Omega : C) (TrueArrow : mono C T Omega) :=
    forall (s b : C) (m : mono C s b), iscontr (total2 
         (fun phiH : total2 (fun phi : b --> Omega => 
                   m ;; phi == TerminalArrow s ;; TrueArrow) =>
                isPullback C (pr1 phiH) TrueArrow m (TerminalArrow s) (pr2 phiH))).

Definition SubobjectClassifier :=  
    total2 (fun OmegaTrueArrow : total2 (fun b => mono C T b) =>
           isSubobjectClassifier (pr1 OmegaTrueArrow) (pr2 OmegaTrueArrow)).

Section var_defs.

Hypothesis S : SubobjectClassifier.

Definition Omega : C := pr1 (pr1 S).
Definition TrueArrow : mono C T Omega := pr2 (pr1 S).

Definition isSubobjectClassifier_SubobjectClassifier :
     isSubobjectClassifier Omega TrueArrow := pr2 S.

Definition CharMap {s b : C} (m : mono C s b) : b --> Omega :=
      pr1 (pr1 (pr1 (isSubobjectClassifier_SubobjectClassifier s b m))).

Definition CharMapMakesCommute {s b : C} (m : mono C s b) : 
     m ;; CharMap m == TerminalArrow s ;; TrueArrow.
Proof.
  exact (pr2 (pr1 (pr1 (isSubobjectClassifier_SubobjectClassifier s b m)))).
Qed.

Definition CharMapPullback {s b : C} (m : mono C s b) : 
    isPullback _ (CharMap m) TrueArrow m (TerminalArrow s)
           (CharMapMakesCommute m).
Proof.
  exact (pr2 (pr1 (isSubobjectClassifier_SubobjectClassifier s b m))).
Qed.

Lemma CharMapUnique (s b : C) (m : mono C s b) (f : b --> Omega)
    (H : m ;; f == TerminalArrow s ;; TrueArrow) :
   isPullback _ f TrueArrow m (TerminalArrow s) H -> 
    f == CharMap m.
Proof.
  intro H'.
  set (H'' := isSubobjectClassifier_SubobjectClassifier s b m).
  set (H1 := tpair (fun phi : b --> Omega => m;; phi == TerminalArrow s;; TrueArrow) f H).
  set (H2 := tpair (fun phi : b --> Omega => m;; phi == TerminalArrow s;; TrueArrow) 
                    (CharMap m) (CharMapMakesCommute m)).
  set (H1' := tpair (fun phiH : total2 (fun phi : b --> Omega => 
                   m ;; phi == TerminalArrow s ;; TrueArrow) =>
                isPullback C (pr1 phiH) TrueArrow m (TerminalArrow s) (pr2 phiH))
                 H1 H').
  set (H2' := tpair (fun phiH : total2 (fun phi : b --> Omega => 
                   m ;; phi == TerminalArrow s ;; TrueArrow) =>
                isPullback C (pr1 phiH) TrueArrow m (TerminalArrow s) (pr2 phiH))
            H2 (CharMapPullback m)).
  assert (ex : H1' == H2').
  - apply proofirrelevance.
    apply isapropifcontr.
    apply H''.
  - apply (base_paths _ _ (base_paths _ _ ex)).
Qed.

End var_defs.

Section SubobjectClassifiers_isomorphic.

Variables S S' : SubobjectClassifier.

Definition one_way : Omega S --> Omega S' := CharMap S' (TrueArrow S).
Definition or_another : Omega S' --> Omega S := CharMap S (TrueArrow S').


(* todo : prove unicity of subobject classifer *)

Section power_object.

Variable OMEGA : SubobjectClassifier.
Variable Pb : Pullbacks C.




Let Omega : C := pr1 OMEGA.

Definition is_power_object (b : C) (Pb : C)



End subobject_classifier.































