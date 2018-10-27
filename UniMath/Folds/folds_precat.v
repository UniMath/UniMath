
(** Univalent FOLDS

    Benedikt Ahrens, following notes by Michael Shulman

Contents of this file:

  - Definition of the type of FOLDS precategories [folds_precat]
  - Definition of functions [id_func] and [comp_func] from a FOLDS precategory
  - Proof of the usual axioms of categories for those functions

*)


Require Import UniMath.Folds.UnicodeNotations.

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.total2_paths.

(** * The definition of a FOLDS precategory *)

(** ** Objects and a dependent type of morphisms *)

Definition folds_ob_mor := ∑ a : UU, a → a → UU.
Definition folds_ob_mor_pair (ob : UU)(mor : ob → ob → UU) :
    folds_ob_mor := tpair _ ob mor.

Definition ob (C : folds_ob_mor) : UU := @pr1 _ _ C.
Coercion ob : folds_ob_mor >-> UU.

Definition folds_morphisms {C : folds_ob_mor} : C → C → UU := pr2 C.
Local Notation "a ⇒ b" := (folds_morphisms a b).

Definition has_folds_homsets (C : folds_ob_mor) : UU := ∏ a b: C, isaset (a ⇒ b).

(** ** Identity and composition, given through predicates *)

Definition folds_id_T := ∑ C : folds_ob_mor,
    (∏ a : C, a ⇒ a → hProp)
 ×  (∏ (a b c : C), (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → hProp).

Definition folds_ob_mor_from_folds_id_comp (C : folds_id_T) : folds_ob_mor := pr1 C.
Coercion folds_ob_mor_from_folds_id_comp : folds_id_T >-> folds_ob_mor.

Definition I {C : folds_id_T} : ∏ {a : C}, a ⇒ a → hProp
  := pr1 (pr2 C).
Definition T {C : folds_id_T} : ∏ {a b c : C}, (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → hProp
  := pr2 (pr2 C).

(** **  The axioms for identity *)

Definition folds_ax_I (C : folds_id_T) :=
     (∏ a : C, ∥ ∑ f : a ⇒ a, I f ∥ )  (* there is an id *)
  × ((∏ (a b : C) (f : a ⇒ b)(i : b ⇒ b), I i → T f i f) (* id is post neutral *)
   × (∏ (a b : C) (f : a ⇒ b)(i : a ⇒ a), I i → T i f f)). (* id is pre neutral *)

Lemma isaprop_folds_ax_id C : isaprop (folds_ax_I C).
Proof.
 repeat (apply isapropdirprod).
 - apply impred; intro; apply isapropishinh.
 - repeat (apply impred; intro). apply pr2.
 - repeat (apply impred; intro). apply pr2.
Qed.

Definition folds_ax_T (C : folds_id_T) :=
     (∏ {a b c : C} (f : a ⇒ b) (g : b ⇒ c), ∥ ∑ h : a ⇒ c, T f g h ∥ ) (* there is a composite *)
 ×  ((∏ {a b c : C} {f : a ⇒ b} {g : b ⇒ c} {h k : a ⇒ c},
                  T f g h → T f g k → h = k )       (* composite is unique *)
  ×  (∏ {a b c d : C} (f : a ⇒ b) (g : b ⇒ c) (h : c ⇒ d)
                  (fg : a ⇒ c) (gh : b ⇒ d) (fg_h : a ⇒ d) (f_gh : a ⇒ d),
               T f g fg → T g h gh →
                  T fg h fg_h → T f gh f_gh → f_gh = fg_h)). (* composition is assoc *)

Lemma isaprop_folds_ax_T (C:folds_id_T) (hs: has_folds_homsets C): isaprop (folds_ax_T C).
Proof.
 repeat (apply isapropdirprod).
 - do 5 (apply impred; intro). apply isapropishinh.
 - repeat (apply impred; intro). apply hs.
 - repeat (apply impred; intro). apply hs.
Qed.


Definition folds_precat := ∑ C : folds_id_T, folds_ax_I C × folds_ax_T C.

Definition folds_id_comp_from_folds_precat (C : folds_precat) : folds_id_T := pr1 C.
Coercion folds_id_comp_from_folds_precat : folds_precat >-> folds_id_T.

(** * Some lemmas about FOLDS precategories *)

(** used later to go to precategories; we define
  - identity as a function
  - composition as a function
*)

Section some_lemmas_about_folds_precats.

Variable C : folds_precat.

Lemma I_unique : ∏ (a : C) (i i' : a ⇒ a), I i → I i' → i = i'.
Proof.
  intros a i i' Hi Hi'.
  destruct C as [CC [Cid Ccomp]]; simpl in *.
  assert (H1 : T i i' i).
  { apply (pr1 (pr2 Cid) _ _ _ _  ).  assumption. }
  assert (H2 : T i i' i').
  { apply (pr2 (pr2 Cid) _ _ _ _ ) . assumption. }
  apply (pr1 (pr2 Ccomp) _ _ _ _ _ _ _ H1 H2).
Qed.

Lemma I_contr : ∏ a : C, iscontr (∑ f : a ⇒ a, I f).
Proof.
  intro a.
  set (H := pr1 (pr1 (pr2 C)) a).
  set (H' := hProppair (iscontr (∑ f : a ⇒ a, I f))
                      (isapropiscontr _ )).
  apply (H H'); simpl.
  intro t; exists t.
  intro t'.
  apply subtypeEquality.
  - intro b; apply pr2.
  - destruct t; destruct t';
    apply I_unique; assumption.
Defined.

Definition I_func (a : C) : a ⇒ a := pr1 (pr1 (I_contr a)).

Lemma I_func_I (a : C) : I (I_func a).
Proof.
  apply (pr2 (pr1 (I_contr a))).
Defined.

Lemma T_contr : ∏ (a b c : C) (f : a ⇒ b) (g : b ⇒ c), iscontr (∑ h, T f g h).
Proof.
  intros a b c f g.
  set (H' := hProppair (iscontr (∑ h : a ⇒ c, T f g h))
                      (isapropiscontr _ )).
  apply (pr1 (pr2 (pr2 C)) a b c f g H').
  simpl; intro t; exists t.
  intro t'.
  apply subtypeEquality.
  - intro; apply pr2.
  - destruct t as [t tp]; destruct t' as [t' tp']; simpl in *.
    apply (pr1 (pr2 (pr2 (pr2 C))) _ _ _ f g ); assumption.
Defined.

Definition T_func {a b c : C} (f : a ⇒ b) (g : b ⇒ c) : a ⇒ c :=
     pr1 (pr1 (T_contr a b c f g)).

Local Notation "f ∘ g" := (T_func f g).  (*at level 30*)

Lemma T_func_T {a b c : C} (f : a ⇒ b) (g : b ⇒ c) : T f g (f ∘ g).
Proof.
  apply (pr2 (pr1 (T_contr a b c f g))).
Defined.

Lemma T_I_l (a b : C) (f : a ⇒ b) : f ∘ (I_func b) = f.
Proof.
  assert (H : T f (I_func b) f).
  { apply (pr1 (pr2 (pr1 (pr2 C)))). apply I_func_I. }
  assert (H' : T f (I_func b) (T_func f (I_func b))).
  { apply T_func_T. }
  set (H2 := pr1 (pr2 (pr2 (pr2 C)))).
  apply (H2 _ _ _ _ _ _ _ H' H).
Defined.

Lemma T_I_r (a b : C) (f : a ⇒ b) : (I_func a) ∘ f = f.
Proof.
  assert (H : T (I_func a) f f).
  { apply (pr2 (pr2 (pr1 (pr2 C)))). apply I_func_I. }
  assert (H' : T (I_func a) f (T_func (I_func a) f)).
  { apply T_func_T. }
  set (H2 := pr1 (pr2 (pr2 (pr2 C)))).
  apply (H2 _ _ _ _ _ _ _ H' H).
Defined.

Lemma T_assoc (a b c d : C) (f : a ⇒ b) (g : b ⇒ c) (h : c ⇒ d) :
    f ∘ (g ∘ h) = (f ∘ g) ∘ h.
Proof.
  apply (pr2 (pr2 (pr2 (pr2 C))) a b c d f g h (f ∘ g) (g ∘ h)).
  - apply T_func_T.
  - apply T_func_T.
  - apply T_func_T.
  - apply T_func_T.
Defined.


End some_lemmas_about_folds_precats.
