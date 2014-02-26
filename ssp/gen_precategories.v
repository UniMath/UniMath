(** **********************************************************

Benedikt Ahrens



************************************************************)


(** **********************************************************

Contents :  

  - generalization of precategories


************************************************************)

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Definition of a generalized precategory *)

Definition precategory_ob_mor := total2 (
  fun ob : UU => ob -> ob -> UU).

Definition precategory_ob_mor_pair (ob : UU)(mor : ob -> ob -> UU) :
    precategory_ob_mor := tpair _ ob mor.

Definition ob (C : precategory_ob_mor) : Type := @pr1 _ _ C.
Coercion ob : precategory_ob_mor >-> Sortclass.

Definition precategory_morphisms { C : precategory_ob_mor } : 
       C ->  C -> UU := pr2 C.

(** We introduce notation for morphisms *)
(** in order for this notation not to pollute subsequent files, 
    we define this notation locally *)

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

(** ** [precategory_data] *)
(** data of a precategory : 
    - objects
    - morphisms
    - identity morphisms
    - composition
*)

Definition precategory_id_comp (C : precategory_ob_mor) :=
     dirprod (forall c : C, c --> c) (* identities *) 
             (forall a b c : C,
                 a --> b -> b --> c -> a --> c).

Definition precategory_data := total2 precategory_id_comp.

Definition precategory_data_pair (C : precategory_ob_mor)
    (id : forall c : C, c --> c)
    (comp: forall a b c : C,
         a --> b -> b --> c -> a --> c) : precategory_data :=
   tpair _ C (dirprodpair id comp).

Definition precategory_ob_mor_from_precategory_data (C : precategory_data) :
     precategory_ob_mor := pr1 C.
Coercion precategory_ob_mor_from_precategory_data : 
  precategory_data >-> precategory_ob_mor.

Definition identity { C : precategory_data } :
    forall c : C, c --> c := 
         pr1 (pr2 C).

Definition compose { C : precategory_data } 
  { a b c : C } : 
    a --> b -> b --> c -> a --> c := pr2 (pr2 C) a b c.

Local Notation "f ;; g" := (compose f g)(at level 50).


(** ** Axioms of a precategory *)
(** 
        - identity is left and right neutral for composition 
        - composition is associative
*)

Definition is_precategory (C : precategory_data) := 
   dirprod (dirprod (forall (a b : C) (f : a --> b),
                         identity a ;; f == f)
                     (forall (a b : C) (f : a --> b),
                         f ;; identity b == f))
            (forall (a b c d : C) 
                    (f : a --> b)(g : b --> c) (h : c --> d),
                     f ;; (g ;; h) == (f ;; g) ;; h).

Definition precategory := total2 is_precategory.

Definition precategory_data_from_precategory (C : precategory) : 
       precategory_data := pr1 C.
Coercion precategory_data_from_precategory : precategory >-> precategory_data.

Definition id_left (C : precategory) : 
   forall (a b : C) (f : a --> b),
           identity a ;; f == f := pr1 (pr1 (pr2 C)).

Definition id_right (C : precategory) :
   forall (a b : C) (f : a --> b),
           f ;; identity b == f := pr2 (pr1 (pr2 C)).

Definition assoc (C : precategory) : 
   forall (a b c d : C) 
          (f : a --> b)(g : b --> c) (h : c --> d),
                     f ;; (g ;; h) == (f ;; g) ;; h := pr2 (pr2 C).

(** Any equality on objects a and b induces a morphism from a to b *)

Definition idtomor {C : precategory_data}
   (a b : C) (H : a == b) : a --> b.
Proof.
  destruct H.
  exact (identity a).
Defined.

Definition idtomor_inv {C : precategory}
    (a b : C) (H : a == b) : b --> a.
Proof.
  destruct H.
  exact (identity a).
Defined.


Lemma cancel_postcomposition (C : precategory_data) (a b c: C)
   (f f' : a --> b) (g : b --> c) : f == f' -> f ;; g == f' ;; g.
Proof.
  intro H.
  destruct H.
  apply idpath.
Defined.



(** * Equivalence in a generalized precategory *)

(** ** Definition of equivalences *)

Definition postcompose_with {C : precategory} {b c : ob C} (g : b --> c) : 
      forall {a}, a --> b -> a --> c :=
   fun a f =>  f ;; g.

Definition is_leq {C : precategory} {b c : ob C} (g : b --> c) :=
     forall a : ob C, isweq (postcompose_with g (a:=a)).

(** being a left equivalence is a proposition *)
Lemma isaprop_is_leq {C : precategory} {b c : ob C} (g : b --> c) :
   isaprop (is_leq g).
Proof.
  apply impred;
  intro t; apply isapropisweq.
Qed.

Definition leq {C : precategory} (b c : ob C) : UU :=
   total2 (fun g : b --> c => is_leq g).
Definition morphism_from_leq (C : precategory)(a b : ob C)
   (f : leq a b) : a --> b := pr1 f.
Coercion morphism_from_leq : leq >-> precategory_morphisms.

Lemma eq_leq {C : precategory} (b c : ob C) (f g : leq b c) :
   pr1 f == pr1 g -> f == g.
Proof.
  apply total2_paths_hProp.
  apply isaprop_is_leq.
Defined.

Lemma id_is_leq {C : precategory} (a : ob C) : is_leq (identity a).
Proof.
  intro b.
  apply (gradth _ (fun x => x)).
  - intro g; apply id_right.
  - intro g; apply id_right.
Qed.

Definition id_leq {C : precategory} (a : ob C) : leq a a := 
        tpair _ _ (id_is_leq a).

Lemma postcompose_with_composition_ext {C : precategory} (b c d: ob C)
   (f : b --> c) (g : c --> d) :
   forall a (h : a --> b), postcompose_with (f ;; g) h == 
        postcompose_with g (postcompose_with f h).
Proof.
  intros a h; apply assoc.
Defined.

Lemma postcompose_with_composition {C : precategory} (b c d: ob C)
   (f : b --> c) (g : c --> d) :
   forall a, postcompose_with (f ;; g) (a:=a) == 
        fun x => postcompose_with g (postcompose_with f x).
Proof.
  intro a. apply funextfun.
  apply postcompose_with_composition_ext.
Defined.


Lemma is_leq_composition {C : precategory} (b c d: ob C)
   (f : b --> c) (g : c --> d) :
   is_leq f -> is_leq g ->  is_leq (f ;; g).
Proof.
  intros Hf Hg a.
  rewrite postcompose_with_composition.
  apply twooutof3c; auto.
Qed.

Definition leq_comp {C : precategory} {b c d: ob C}
   (f : leq b c) (g : leq c d) : leq b d :=
  tpair _ (f ;; g) (is_leq_composition _ _ _ f g (pr2 f) (pr2 g)).

Definition idtoleq {C : precategory} {c d : ob C} (p : c == d) : leq c d.
Proof.
  destruct p; exact (id_leq _ ).
Defined.

Definition is_category (C : precategory) := forall (a b : ob C),
    isweq (fun p : a == b => idtoleq p).

Lemma isaprop_is_category (C : precategory) : isaprop (is_category C).
Proof.
  apply impred; intro a.
  apply impred; intro b.
  apply isapropisweq.
Qed.


(** ** Univalent categories *)

Definition leqtoid (C : precategory) (H : is_category C) {a b : ob C}:
      leq a b -> a == b := invmap (weqpair _ (H a b)).

Lemma idtoleq_leqtoid (C : precategory) (H : is_category C) (a b : ob C) (f : leq a b) : 
       idtoleq (leqtoid _ H f) == f.
Proof.
  apply (homotweqinvweq (weqpair idtoleq (H a b))).
Qed.

Lemma lefteqtoid_idtolefteq (C : precategory) (H : is_category C) (a b : ob C) (p : a == b) : 
   leqtoid _ H (idtoleq p) == p.
Proof.
  apply (homotinvweqweq (weqpair idtoleq (H a b))).
Qed.

(** more properties of leq *)

Lemma idtoleq_postcompose (C : precategory) (a b b' : ob C)
  (p : b == b') (f : a --> b) :
      f ;; idtoleq p == transportf (fun b => a --> b) p f.
Proof.
  destruct p.
  apply id_right.
Qed.

Lemma idtoiso_postcompose_iso (C : precategory) (a b b' : ob C)
  (p : b == b') (f : leq a b) :
    leq_comp f (idtoleq p) == transportf (fun b => leq a b) p f.
Proof.
  destruct p.
  apply eq_leq.
  simpl.
  apply id_right.
Qed.

Lemma idtoiso_precompose (C : precategory) (a a' b : ob C)
  (p : a == a') (f : a --> b) :
      (idtoiso (!p)) ;; f == transportf (fun a ⇒ a --> b) p f.
Proof.
  destruct p.
  apply id_left.
Qed.

Lemma idtoiso_precompose_iso (C : precategory) (a a' b : ob C)
  (p : a == a') (f : iso a b) :
      iso_comp (idtoiso (!p)) f == transportf (fun a ⇒ iso a b) p f.
Proof.
  destruct p.
  apply eq_iso.
  simpl.
  apply id_left.
Qed.

Lemma double_transport_idtoiso (C : precategory) (a a' b b' : ob C)
  (p : a == a') (q : b == b') (f : a --> b) :
  double_transport p q f == inv_from_iso (idtoiso p) ;; f ;; idtoiso q.
Proof.
  destruct p.
  destruct q.
  rewrite id_right.
  rewrite id_left.
  apply idpath.
Qed.

Lemma idtoiso_inv (C : precategory) (a a' : ob C)
  (p : a == a') : idtoiso (!p) == iso_inv_from_iso (idtoiso p).
Proof.
  destruct p.
  apply idpath.
Qed.

Lemma idtoiso_concat (C : precategory) (a a' a'' : ob C)
  (p : a == a') (q : a' == a'') :
  idtoiso (p @ q) == iso_comp (idtoiso p) (idtoiso q).
Proof.
  destruct p.
  destruct q.
  apply eq_iso.
  simpl;
  rewrite id_left.
  apply idpath.
Qed.

Lemma idtoiso_inj (C : precategory) (H : is_category C) (a a' : ob C)
   (p p' : a == a') : idtoiso p == idtoiso p' → p == p'.
Proof.
  apply invmaponpathsincl.
  apply isinclweq.
  apply H.
Qed.

Lemma isotoid_inj (C : precategory) (H : is_category C) (a a' : ob C)
   (f f' : iso a a') : isotoid _ H f == isotoid _ H f' → f == f'.
Proof.
  apply invmaponpathsincl.
  apply isinclweq.
  apply isweqinvmap.
Qed.

Lemma isotoid_comp (C : precategory) (H : is_category C) (a b c : ob C)
  (e : iso a b) (f : iso b c) :
  isotoid _ H (iso_comp e f) == isotoid _ H e @ isotoid _ H f.
Proof.
  apply idtoiso_inj.
    assumption.
  rewrite idtoiso_concat.
  repeat rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma isotoid_identity_iso (C : precategory) (H : is_category C) (a : C) :
  isotoid _ H (identity_iso a) == idpath _ .
Proof.
  apply idtoiso_inj; try assumption.
  rewrite idtoiso_isotoid;
  apply idpath.
Qed.

Lemma inv_isotoid (C : precategory) (H : is_category C) (a b : C)
    (f : iso a b) : ! isotoid _ H f == isotoid _ H (iso_inv_from_iso f).
Proof.
  apply idtoiso_inj; try assumption.
  rewrite idtoiso_isotoid.
  rewrite idtoiso_inv.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma transportf_isotoid (C : precategory) (H : is_category C)
   (a a' b : ob C) (p : iso a a') (f : a --> b) :
 transportf (fun a0 : C ⇒ a0 --> b) (isotoid C H p) f == inv_from_iso p ;; f.
Proof.
  rewrite <- idtoiso_precompose.
  rewrite idtoiso_inv.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma transportf_isotoid_dep (C : precategory)
   (a a' : C) (p : a == a') (f : ∀ c, a --> c) :
 transportf (fun x : C ⇒ ∀ c, x --> c) p f == fun c ⇒ idtoiso (!p) ;; f c.
Proof.
  destruct p.
  simpl.
  apply funextsec.
  intro.
  rewrite id_left.
  apply idpath.
Qed.

Lemma transportf_isotoid_dep' (J C : precategory)
  (F : J → C)
   (a a' : C) (p : a == a') (f : ∀ c, a --> F c) :
 transportf (fun x : C ⇒ ∀ c, x --> F c) p f == fun c ⇒ idtoiso (!p) ;; f c.
Proof.
  destruct p.
  apply funextsec.
  intro. simpl.
  apply (! id_left _ _ _ _).
Defined.


  
(** for producing the inverse, we seem to need that
 - a "natural transformation" alpha : F -> G : C -> UU
   which is pointwise an equiv, is a "natural iso".
 - a natural iso has an inverse
 - natural transformations are representable
*)


(** define the category UU *)

Definition UUcat_data : precategory_data.
  exists (tpair (fun x => x -> x -> UU) UU (fun A B : UU => A -> B)).
  split; simpl.
  intro c; exact (fun x => x).
  intros a b c f g ; exact (fun x => g (f x)).
Defined.

Lemma is_precategory_UUcat : is_precategory UUcat_data.
Proof.
  repeat split; simpl.
Qed.

Definition UUcat : precategory := tpair _ _ is_precategory_UUcat.
  
(** TODO: UUcat is univalent *)


(** ** Functors *)

Definition functor_data (C C' : precategory_ob_mor) := total2 (
    fun F : ob C -> ob C' => 
             forall a b : ob C, a --> b -> F a --> F b).

Definition mkfunctor_data (C C' : precategory_ob_mor) 
    a b : functor_data C C' := tpair _ a b.

Definition functor_on_objects {C C' : precategory_ob_mor}
     (F : functor_data C C') :  ob C -> ob C' := pr1 F.
Coercion functor_on_objects : functor_data >-> Funclass.


Definition functor_on_morphisms {C C' : precategory_ob_mor} (F : functor_data C C') 
  { a b : ob C} :  a --> b -> F a --> F b := pr2 F a b.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).


Definition is_functor {C C' : precategory_data} (F : functor_data C C') :=
     dirprod (forall a : ob C, #F (identity a) == identity (F a))
             (forall a b c : ob C, forall f : a --> b, forall g : b --> c, 
                #F (f ;; g) == #F f ;; #F g).

(*
Lemma isaprop_is_functor (C C' : precategory_data) 
       (F : functor_data C C'): isaprop (is_functor F).
Proof.
  apply isofhleveldirprod.
  apply impred; intro a.
  apply (pr2 (_ --> _)).
  repeat (apply impred; intro).
  apply (pr2 (_ --> _)).
Qed.
*)

Definition functor (C C' : precategory) := total2 (
   fun F : functor_data C C' => is_functor F).


Definition functor_data_from_functor (C C': precategory)
     (F : functor C C') : functor_data C C' := pr1 F.
Coercion functor_data_from_functor : functor >-> functor_data.


Definition functor_id {C C' : precategory}(F : functor C C'):
       forall a : ob C, #F (identity a) == identity (F a) := pr1 (pr2 F).

Definition functor_comp {C C' : precategory}
      (F : functor C C'):
       forall a b c : ob C, forall f : a --> b,
                 forall g : b --> c, 
                #F (f ;; g) == #F f ;; #F g := pr2 (pr2 F).


(** * Natural transformations *)


(** ** Definition of natural transformations *)

Definition is_nat_trans {C C' : precategory_data}
  (F F' : functor_data C C')
  (t : forall x : ob C, F x -->  F' x) := 
  forall (x x' : ob C)(f : x --> x'),
    #F f ;; t x' == t x ;; #F' f.



Definition nat_trans {C C' : precategory_data}
  (F F' : functor_data C C') := total2 (
   fun t : forall x : ob C, F x -->  F' x => is_nat_trans F F' t).


Definition nat_trans_data (C C' : precategory_data)
 (F F' : functor_data C C')(a : nat_trans F F') :
   forall x : ob C, F x --> F' x := pr1 a.
Coercion nat_trans_data : nat_trans >-> Funclass.

Definition nat_trans_ax {C C' : precategory_data}
  (F F' : functor_data C C') (a : nat_trans F F') :
  forall (x x' : ob C)(f : x --> x'),
    #F f ;; a x' == a x ;; #F' f := pr2 a.



Lemma nat_trans_eq {C D: precategory} {F G : functor C D}
   (a b : nat_trans F G) : 
  (forall x, a x == b x) -> a == b.
Proof.
  intro H.
  apply (total2_paths (funextsec _ _ _ H)).
  destruct a as [a aax];
  destruct b as [b bax]; simpl in *.
  unfold is_nat_trans in *; simpl in *.
  Check (funextsec (fun x : C => F x --> G x) a b H).
  Search (transportf _ == _ ).
*)
  


(** ** opposite category *)

Definition opp_precat_ob_mor (C : precategory_ob_mor) : precategory_ob_mor :=
   tpair (fun ob : UU => ob -> ob -> UU) (ob C) 
        (fun a b : ob C => b --> a  ).

Definition opp_precat_data (C : precategory_data) : precategory_data.
Proof.
  exists (opp_precat_ob_mor C).
  split.
  exact (fun c => identity c).
  simpl.
  intros a b c f g.
  exact (g ;; f).
Defined.

Hint Unfold identity.

Ltac unf := unfold identity, 
                   compose, 
                   precategory_morphisms;
                   simpl.

Lemma is_precat_opp_precat_data (C : precategory) : is_precategory (opp_precat_data C).
Proof.
  repeat split; simpl.
  intros. unf.
  apply id_right.
  intros; unf.
  apply id_left.
  intros; unf.
  rewrite assoc.
  apply idpath.
Qed.

Definition opp_precat (C : precategory) : precategory := 
  tpair _ (opp_precat_data C) (is_precat_opp_precat_data C).

Local Notation "C '^op'" := (opp_precat C) (at level 3).





