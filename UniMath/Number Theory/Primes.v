(** * Results about Number Theory *)
(** Author: Junstin Scarfy. Jun 2019 - *)
(** Based on Bourbaky *)

Require Import UniMath.Foundations.All.

(**  prime numbers *)

Definition nat_mult : nat → nat → nat :=
  nat_rect (λ _, nat → nat) (λ _, 0) (λ _ IHm n, nat_plus n (IHm n)).

Definition is_prime : nat → UU :=
  λ n, ∑ _:((n = 1) → empty), (∏ m1 m2, nat_mult m1 m2 = n → (m1 = 1) ⨿ (m2 = 1)).

Definition exercise_3_2 : UU := ∑ n, is_prime n.

(** 3. functions A → nat which attain zero *)

Definition exercise_3_3 (A : UU) : UU := ∑ f:A → nat, ∑ a, f a = 0.

(** 4. the "less than" relation on natural numbers *)

Definition lessb : nat → nat → bool :=
  nat_rect
    (λ _, nat → bool)
    (nat_rect (λ _, bool) false (λ _ _, true))
    (λ n IHn,
       nat_rect (λ _, bool) false
                (λ m _, IHn m)).

Definition exercise_3_4 (n m : nat) : UU := bool_to_rel (lessb n m).