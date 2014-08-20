
Require Import Utf8.

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.
Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
(* Require Import FOLDS.aux_lemmas. *)

Notation "p # a" := (transportf _ p a) (at level 3, only parsing).

(** * The definition of a FOLDS pre-3-category *)

(** ** Objects and a dependent type of morphisms *)

Definition folds_3_ob_mor := total2 (λ a : UU, a → a → UU).
Definition folds_3_ob_mor_pair (ob : UU)(mor : ob → ob → UU) :
    folds_3_ob_mor := tpair _ ob mor.

Definition ob (C : folds_3_ob_mor) : Type := @pr1 _ _ C.
Coercion ob : folds_3_ob_mor >-> Sortclass.

Definition folds_3_morphisms {C : folds_3_ob_mor} : C → C → UU := pr2 C.
Local Notation "a ⇒ b" := (folds_3_morphisms a b)(at level 50).

(** ** Identity, composition, and equality, given through predicates *)
(** We do not assume those to be propositions.  *)

Definition folds_3_id_comp_eq := total2 (λ C : folds_3_ob_mor,
  dirprod (  
    dirprod (∀ a : C, a ⇒ a → UU)   
            (∀ (a b c : C), (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → UU)
          )
          (∀ a b : C, a ⇒ b → a ⇒ b → UU) ).


Definition folds_ob_mor_from_folds_id_comp (C : folds_3_id_comp_eq) : folds_3_ob_mor := pr1 C.
Coercion folds_ob_mor_from_folds_id_comp : folds_3_id_comp_eq >-> folds_3_ob_mor.

Definition I {C : folds_3_id_comp_eq} : ∀ {a : C}, a ⇒ a → UU := pr1 (pr1 (pr2 C)).
Definition T {C : folds_3_id_comp_eq} :
      ∀ {a b c : C}, (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → UU := pr2 (pr1 (pr2 C)).
Definition E {C : folds_3_id_comp_eq} : 
      ∀ {a b : C}, a ⇒ b → a ⇒ b → UU := pr2 (pr2 C).

(** ** E is an "equality", i.e. a congruence and equivalence *)

Definition E_is_good_to_I_and_T (C : folds_3_id_comp_eq) : UU :=
  dirprod (
          dirprod (
            dirprod (∀ (a b : C) (f : a ⇒ b), E f f)  (* refl *)
                    (∀ (a b : C) (f g : a ⇒ b), E f g → E g f) (* sym *)
                  )
                  (∀ (a b : C) (f g h : a ⇒ b), E f g → E g h → E f h)
          )
          (
          dirprod (∀ (a : C) (f g : a ⇒ a), E f g → I f → I g)
                  (∀ (a b c : C) (f f' : a ⇒ b) (g g' : b ⇒ c) (h h' : a ⇒ c),
                      E f f' → E g g' → E h h' → T f g h → T f' g' h')
          ).


(** **  The axioms for identity *)

Definition folds_ax_id (C : folds_3_id_comp_eq) := 
    dirprod (∀ a : C, ishinh (total2 (λ f : a ⇒ a, I f)))  (* there is a thing satisfying I *)
     (dirprod (∀ (a b : C) (f : a ⇒ b)(i : b ⇒ b), I i → T f i f) (* I is post neutral *)      
              (∀ (a b : C) (f : a ⇒ b)(i : a ⇒ a), I i → T i f f)). (* I is pre neutral *)


(** this is no longer valid
Lemma isaprop_folds_ax_id C : isaprop (folds_ax_id C).
Proof.
 repeat (apply isapropdirprod).
 - apply impred; intro; apply isapropishinh.
 - repeat (apply impred; intro). apply pr2.  
 - repeat (apply impred; intro). apply pr2.
Qed.
*)

Definition folds_ax_comp (C : folds_3_id_comp_eq) :=
    dirprod (∀ {a b c : C} (f : a ⇒ b) (g : b ⇒ c), 
                ishinh (total2 (λ h : a ⇒ c, T f g h))) (* there is a composite *)
     (dirprod (∀ {a b c : C} {f : a ⇒ b} {g : b ⇒ c} {h k : a ⇒ c},
                  T f g h → T f g k → E h k )       (* composite is unique mod E *)
              (∀ {a b c d : C} (f : a ⇒ b) (g : b ⇒ c) (h : c ⇒ d)
                  (fg : a ⇒ c) (gh : b ⇒ d) (fg_h : a ⇒ d) (f_gh : a ⇒ d), 
               T f g fg → T g h gh → 
                  T fg h fg_h → T f gh f_gh → E f_gh fg_h)). (* composition is assoc mod E *)

(** not valid 
Lemma isaprop_folds_ax_comp C : isaprop (folds_ax_comp C).
Proof.
 repeat (apply isapropdirprod).
 - do 5 (apply impred; intro). apply isapropishinh.
 - repeat (apply impred; intro). apply (pr2 (_ ⇒ _)) .  
 - repeat (apply impred; intro). apply (pr2 (_ ⇒ _ )).
Qed.
*)

Definition folds_3_precat := total2 (λ C : folds_3_id_comp_eq,
    dirprod (dirprod (folds_ax_id C) (folds_ax_comp C))
             (E_is_good_to_I_and_T C)).
Definition folds_id_comp_from_folds_precat (C : folds_3_precat) : folds_3_id_comp_eq := pr1 C.
Coercion folds_id_comp_from_folds_precat : folds_3_precat >-> folds_3_id_comp_eq.

(** * Some lemmas about FOLDS precategories *)

(** used later to go to precategories; we define
  - identity as a function
  - composition as a function
*)

(** * FOLDS-2-precategories *)
(** they are 3-precategories such that T, I and E are hProps *)

Definition is_folds_2_precat (C : folds_3_precat) :=
   dirprod (
     dirprod (∀ (a : C) (i : a ⇒ a), isaprop (I i)) 
             (∀ (a b c : C) (f : a ⇒ b) (g : b ⇒ c) (h : a ⇒ c), isaprop (T f g h)))
           (∀ (a b : C) (f g : a ⇒ b), isaprop (E f g)).

Definition folds_2_precat : UU := total2 (λ C, is_folds_2_precat C).

Definition folds_3_from_folds_2 (C : folds_2_precat) : folds_3_precat := pr1 C.
Coercion folds_3_from_folds_2 : folds_2_precat >-> folds_3_precat.


(** * FOLDS-2-isomorphisms *)

Section FOLDS_2_isos.

Variable C : folds_2_precat.
Variables a b : C.
Variables f g : a ⇒ b.

Definition folds_2_iso : UU :=
  dirprod 
    (dirprod 
      (dirprod 
        (∀ (x : C) (u : x ⇒ a) (v : x ⇒ b), weq (T u f v) (T u g v))
        (∀ (x : C) (u : a ⇒ x) (v : x ⇒ b), weq (T u v f) (T u v g))
      )
      (∀ (x : C) (u : b ⇒ x) (v : a ⇒ x), weq (T f u v) (T g u v))
     )
    (dirprod
      (dirprod 
        (dirprod (∀ (u : a ⇒ b) (p : b == a), weq (T p # f f u) (T p # g g u)) 
                 (∀ (u : b ⇒ b) (p : a == a), weq (T (transportf (λ a, a ⇒ b) p f) u f) 
                                                  (T (transportf (λ a, a ⇒ b) p g) u g)) (*True*)) 
        (dirprod (∀ (u : a ⇒ a) (p : b == b), weq (T u p # f f) (T u p # g g)) (*True*) 
                 (True)))
      (dirprod 
        (dirprod (True) 
                 (True)) 
        (dirprod (True) 
                 (True)))
    ).
      

Print folds_2_iso.

End FOLDS_2_isos.

Section some_lemmas_about_folds_precats.

Variable C : folds_3_precat.

Lemma I_I_E : ∀ (a : C) (i i' : a ⇒ a), I i → I i' → E i i'.
Proof.
  intros a i i' Hi Hi'.
  destruct C as [CC [Cid Ccomp]]; simpl in *.
  assert (H1 : T i i' i).
  { apply (pr1 (pr2 Cid) _ _ _ _  ).  assumption. }
  assert (H2 : T i i' i').
  { apply (pr2 (pr2 Cid) _ _ _ _ ) . assumption. }
  apply (pr1 (pr2 Ccomp) _ _ _ _ _ _ _ H1 H2).
Qed.

(** not valid 
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
*)

(*
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
  - destruct t as [t tp]; destruct t' as [t' tp']; simpl in *.
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
*)

End some_lemmas_about_folds_precats.

