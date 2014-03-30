
Require Import Utf8.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.
Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.

(** * The definition of a FOLDS precategory *)

(** ** Objects and a dependent type of morphisms *)

Definition folds_ob_mor := total2 (λ a : UU, a → a → hSet).
Definition folds_ob_mor_pair (ob : UU)(mor : ob → ob → hSet) :
    folds_ob_mor := tpair _ ob mor.

Definition ob (C : folds_ob_mor) : Type := @pr1 _ _ C.
Coercion ob : folds_ob_mor >-> Sortclass.

Definition folds_morphisms {C : folds_ob_mor} : C → C → hSet := pr2 C.
Local Notation "a ⇒ b" := (folds_morphisms a b)(at level 50).

(** ** Identity and composition, given through predicates *)

Definition folds_id_comp := total2 (λ C : folds_ob_mor,
    dirprod (∀ a : C, a ⇒ a → hProp) 
            (∀ (a b c : C), (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → hProp)).

Definition folds_ob_mor_from_folds_id_comp (C : folds_id_comp) : folds_ob_mor := pr1 C.
Coercion folds_ob_mor_from_folds_id_comp : folds_id_comp >-> folds_ob_mor.

Definition id {C : folds_id_comp} : ∀ {a : C}, a ⇒ a → hProp := pr1 (pr2 C).
Definition comp {C : folds_id_comp} :
      ∀ {a b c : C}, (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → hProp := pr2 (pr2 C).

(** **  The axioms for identity *)

Definition folds_ax_id (C : folds_id_comp) := 
    dirprod (∀ a : C, ishinh (total2 (λ f : a ⇒ a, id f)))  (* there is an id *)
     (dirprod (∀ (a b : C) (f : a ⇒ b)(i : b ⇒ b), id i → comp f i f) (* id is post neutral *)      
              (∀ (a b : C) (f : a ⇒ b)(i : a ⇒ a), id i → comp i f f)). (* id is pre neutral *)

Lemma isaprop_folds_ax_id C : isaprop (folds_ax_id C).
Proof.
 repeat (apply isapropdirprod).
 - apply impred; intro; apply isapropishinh.
 - repeat (apply impred; intro). apply pr2.  
 - repeat (apply impred; intro). apply pr2.
Qed.

Definition folds_ax_comp (C : folds_id_comp) :=
    dirprod (∀ {a b c : C} (f : a ⇒ b) (g : b ⇒ c), 
                ishinh (total2 (λ h : a ⇒ c, comp f g h))) (* there is a composite *)
     (dirprod (∀ {a b c : C} {f : a ⇒ b} {g : b ⇒ c} {h k : a ⇒ c},
                  comp f g h → comp f g k → h == k )       (* composite is unique *)
              (∀ {a b c d : C} (f : a ⇒ b) (g : b ⇒ c) (h : c ⇒ d)
                  (fg : a ⇒ c) (gh : b ⇒ d) (fg_h : a ⇒ d) (f_gh : a ⇒ d), 
               comp f g fg → comp g h gh → 
                  comp fg h fg_h → comp f gh f_gh → f_gh == fg_h)). (* composition is assoc *)

Lemma isaprop_folds_ax_comp C : isaprop (folds_ax_comp C).
Proof.
 repeat (apply isapropdirprod).
 - do 5 (apply impred; intro). apply isapropishinh.
 - repeat (apply impred; intro). apply (pr2 (_ ⇒ _)) .  
 - repeat (apply impred; intro). apply (pr2 (_ ⇒ _ )).
Qed.


Definition folds_precat := total2 (λ C : folds_id_comp,
    dirprod (folds_ax_id C) (folds_ax_comp C)).
Definition folds_id_comp_from_folds_precat (C : folds_precat) : folds_id_comp := pr1 C.
Coercion folds_id_comp_from_folds_precat : folds_precat >-> folds_id_comp.

(** * Some lemmas about FOLDS precategories *)

(** used later to go to precategories; we define
  - identity as a function
  - composition as a function
*)

Section some_lemmas_about_folds_precats.

Variable C : folds_precat.

Lemma id_unique : ∀ (a : C) (i i' : a ⇒ a), id i → id i' → i == i'.
Proof.
  intros a i i' Hi Hi'.
  destruct C as [CC [Cid Ccomp]]; simpl in *.
  assert (H1 : comp i i' i).
  { apply (pr1 (pr2 Cid) _ _ _ _  ).  assumption. }
  assert (H2 : comp i i' i').
  { apply (pr2 (pr2 Cid) _ _ _ _ ) . assumption. }
  apply (pr1 (pr2 Ccomp) _ _ _ _ _ _ _ H1 H2).
Qed.

Lemma id_contr : ∀ a : C, iscontr (total2 (λ f : a ⇒ a, id f)).  
Proof.
  intro a.
  set (H := pr1 (pr1 (pr2 C)) a).
  set (H' := hProppair (iscontr (total2 (λ f : a ⇒ a, id f)))
                      (isapropiscontr _ )).
  apply (H H'); simpl.
  intro t; exists t.
  intro t'.
  apply total2_paths_hProp.
  - intro b; apply pr2.
  - destruct t; destruct t';
    apply id_unique; assumption.
Defined.

Definition id_func (a : C) : a ⇒ a := pr1 (pr1 (id_contr a)).

Lemma id_func_id (a : C) : id (id_func a).
Proof.
  apply (pr2 (pr1 (id_contr a))).  
Defined.

Lemma comp_contr : ∀ (a b c : C) (f : a ⇒ b) (g : b ⇒ c), 
    iscontr (total2 (λ h, comp f g h)).
Proof.
  intros a b c f g.
  set (H' := hProppair (iscontr (total2 (λ h : a ⇒ c, comp f g h)))
                      (isapropiscontr _ )).
  apply (pr1 (pr2 (pr2 C)) a b c f g H').
  simpl; intro t; exists t.
  intro t'.
  apply total2_paths_hProp.
  - intro; apply pr2.
  - destruct t; destruct t'; simpl in *.
    apply (pr1 (pr2 (pr2 (pr2 C))) _ _ _ f g ); assumption.
Defined.

Definition comp_func {a b c : C} (f : a ⇒ b) (g : b ⇒ c) : a ⇒ c :=
     pr1 (pr1 (comp_contr a b c f g)).

Local Notation "f ∘ g" := (comp_func f g) (at level 30).

Lemma comp_func_comp {a b c : C} (f : a ⇒ b) (g : b ⇒ c) : 
   comp f g (f ∘ g).
Proof.
  apply (pr2 (pr1 (comp_contr a b c f g))).
Defined.

Lemma comp_id_l (a b : C) (f : a ⇒ b) : f ∘ (id_func b) == f.
Proof.
  assert (H : comp f (id_func b) f).  
  { apply (pr1 (pr2 (pr1 (pr2 C)))). apply id_func_id. }
  assert (H' : comp f (id_func b) (comp_func f (id_func b))).  
  { apply comp_func_comp. }
  set (H2 := pr1 (pr2 (pr2 (pr2 C)))).
  apply (H2 _ _ _ _ _ _ _ H' H).
Defined.

Lemma comp_id_r (a b : C) (f : a ⇒ b) : (id_func a) ∘ f == f.
Proof.
  assert (H : comp (id_func a) f f).  
  { apply (pr2 (pr2 (pr1 (pr2 C)))). apply id_func_id. }
  assert (H' : comp (id_func a) f (comp_func (id_func a) f)).  
  { apply comp_func_comp. }
  set (H2 := pr1 (pr2 (pr2 (pr2 C)))).
  apply (H2 _ _ _ _ _ _ _ H' H).
Defined.

Lemma comp_assoc (a b c d : C) (f : a ⇒ b) (g : b ⇒ c) (h : c ⇒ d) :
    f ∘ (g ∘ h) == (f ∘ g) ∘ h.
Proof.
  apply (pr2 (pr2 (pr2 (pr2 C))) a b c d f g h (f ∘ g) (g ∘ h)).
  - apply comp_func_comp.
  - apply comp_func_comp.
  - apply comp_func_comp.
  - apply comp_func_comp.
Defined.
 

End some_lemmas_about_folds_precats.

