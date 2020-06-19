Require Import Basics Types -Coeq UnivalenceAxiom.

Local Open Scope path_scope.

Definition Quot (A : Type) (R : A -> A -> Type) :
  Type := @Coeq {b : A * A & R (fst b) (snd b)}
                A (fun x => fst (x.1))
                  (fun x => snd (x.1)).

Definition inj {A : Type} {R : A -> A -> Type}
               (a : A) : Quot A R := coeq a.

Notation "[ a ]" := (inj a).

Definition glue {A : Type} {R : A -> A -> Type}
  {a b : A} (s : R a b) : @inj A R a = @inj A R b
  := cp ((a,b);s).

Definition Quot_ind {A : Type} {R : A -> A -> Type}
  (P : Quot A R -> Type)
  (f : forall a, P [a])
  (g : forall a b (s : R a b),
     (glue s) # (f a) = f b) :
   forall x, P x
  := fun x => (Coeq_ind _ _ 
   (fun b => g (fst b.1) (snd b.1) b.2) _).

Definition Quot_ind_beta {A : Type}
  {R : A -> A -> Type}
  (P : Quot A R -> Type)
  (f : forall a, P [a])
  (g : forall a b (s : R a b),
     (glue s) # (f a) = f b) :
   forall a b (s : R a b), 
   apD (Quot_ind P f g) (glue s) = g a b s
  := fun a b s =>
     Coeq_ind_beta_cp _ _ _ ((a,b);s).

Theorem Quot_rec {A : Type} {R : A -> A -> Type}
  (P : Type)
  (f : A -> P)
  (g : forall a b (s : R a b), f a = f b) :
   Quot A R -> P.
Proof. 
  refine (Quot_ind (fun _ => P) f
         (fun a b s => 
         (transport_const _ _) @ g _ _ s)).
Defined.

Theorem Quot_rec_beta {A : Type}
  {R : A -> A -> Type}
  (P : Type)
  (f : A -> P)
  (g : forall a b (s : R a b), f a = f b) :
  forall a b (s : R a b), 
   ap (Quot_rec P f g) (glue s) = g a b s.
Proof.
  intros.
  apply (cancelL (transport_const (glue s) _)).
  refine ((apD_const (Quot_rec P f g) _)^ @_).
  refine (Quot_ind_beta _ _ _ _ _ _).
Defined.

Section Quot_path_ind.
  Context {A : Type} {R : A -> A -> Type}
  (a : A) 
  (P : forall {b : A}, @inj A R a = @inj A R b ->
   Type)
  (r : P 1)
  (e : forall {b c : A} (s : R b c) (q : [a] = [b]),
       P q <~> P (q @ glue s)).

Arguments P {b}.
Arguments e {b c}.

  Definition ind {b : A} :
    forall (q : [a] = [b]), P q.
  Proof. 
    admit.
  Admitted.

  Definition ind_beta {b c : A} (s : R b c)
    (q : [a] = [b]) :
    ind (q @ glue s) = e s q (ind q).
  Proof.
    admit.
  Admitted.
End Quot_path_ind.

Check @ind.

 






    
 




                     






  

       

