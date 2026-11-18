Require Import Arith.

Theorem left_idendity_addition: 
    forall n : nat, (0 + n = n).
Proof.
    intros n.
    simpl.
    reflexivity.
Qed.

Theorem definition_of_successor:
 forall n : nat, 1 + n = S n.
Proof.
    intros n.
    reflexivity.
Qed.

Theorem two_equal_number_sum:
 forall n m : nat, (n = m -> n + n = m + m).

Proof.
 intros n m.
 intros H.
 rewrite <- H.
 reflexivity.
Qed.

Check mult_n_O.

Check mult_n_Sm.

Theorem mult_p_O_and_q_O:
  forall p q : nat, (p * 0) + (q * O) = 0.
Proof.
    intros p q.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    simpl.
    reflexivity.
Qed.

Infix "=?" := Nat.eqb (at level 70): nat_scope.

Compute 2 =? 4.

Compute 4 =? 4.


Theorem nat_plus_1_is_never_eq_to_O:
 forall n : nat, (n + 1 =? 0) = false.

Proof.
 intros n.
 destruct n as [| n'] eqn:E.
 - simpl.
   reflexivity.
 - simpl.
   reflexivity.
Qed.

Definition negation (b : bool) : bool :=
  if b then false
  else true.

Theorem double_negation_is_get_back:
 forall b: bool, negation (negation b) = b.

Proof.
  intros b.
  destruct b eqn: E.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.
  
Theorem left_sum_by_zero_is_idempotent:
 forall n : nat, 0 + n = n.
Proof.
 intros n.
 simpl.
 reflexivity.
Qed.

Theorem right_sum_by_zero_is_idempotent:
 forall n : nat, n + 0 = n.
Proof.
  intros n.
  rewrite <- plus_n_O.
  reflexivity. 
Qed.

Check plus_n_O.




Theorem mult_by_zero_is_always_zero:
 forall n : nat, 0 * n = 0.
Proof.
 intros n.
 simpl.
 reflexivity.
Qed.


Fixpoint plus (n m: nat) : nat :=
 match n with
  | O => m
  | S n' => S (plus n' m)
 end.

Compute plus 3 7.
Compute plus 13 7.

Fixpoint mult (n m: nat) : nat :=
 match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.


Fixpoint factorial (n: nat) : nat :=
 match n with
  | O => 1
  | S n' => mult n (factorial n')
 end.

Compute factorial 1.
Compute factorial 2.
Compute factorial 3.
Compute factorial 4.
Compute factorial 5.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.


Theorem identity_fn_applied_three_times :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f (f b)) = b.
Proof.
 intros f H b.
 rewrite H.
 rewrite H.
 rewrite H.
 reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negation x) ->
  forall b : bool, f (f b) = b.
Proof.
 intros f H b.
 rewrite -> H.
 rewrite -> H.
 destruct b.
 - simpl.
   reflexivity.
 - simpl.
   reflexivity.
Qed.


Theorem mult_same:
  forall n : nat, n + n = 2 * n.
Proof.
  intros n.
  destruct n as [|n'] eqn:E.
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- plus_n_O.
    reflexivity.
Qed.

Theorem sum_of_Successsor:
 forall n : nat, S n + S n = S (n + S n).
Proof.
 intro n.
 simpl.
 reflexivity.
Qed.


Theorem mult_same':
  forall n : nat, n + n + n = 3 * n.
Proof.
  intros n.
  destruct n as [|k] eqn:E.
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- plus_n_O.
    rewrite <- Nat.add_assoc.
    rewrite <- sum_of_Successsor.
    reflexivity.
Qed.
  
Theorem repeated_addition :
  forall k n : nat,
    (k * n) = (k * n).
Proof.
  intros k n.
  reflexivity.
Qed.