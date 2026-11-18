(* recall from src/proofs.v*)
Theorem left_addition_by_zero:
    forall n : nat, 0 + n = n.
Proof.
    intros n.
    simpl.
    reflexivity.
Qed.

Check plus_n_O.

Theorem right_addition_by_zero:
    forall n : nat, n + 0 = n.
Proof.
    intros n.
    rewrite <- plus_n_O.
    reflexivity.
Qed.

(* now induction of the recall above*)
(* the goal here is to correctly prove the plus_n_O *)
Theorem add_n_O:
    forall n : nat, n + 0 = n.
Proof.
    intros n.
    induction n as [|n' H].
    - simpl.
      reflexivity.
    - simpl.
      rewrite -> H.
      reflexivity.
Qed.

Theorem n_minus_n_is_identity:
    forall n : nat, n - n = 0.
Proof.
    intros n.
    induction n as [| n' H].
    - simpl.
      reflexivity.
    - simpl.
      rewrite -> H.
      reflexivity.
Qed.
Require Import Arith.
Check Nat.add_succ_comm.

Theorem addition_is_commutative_in_nat:
    forall n m : nat, n + m = m + n.
Proof.
    intros n m.
    induction n as [ | n' H].
    - simpl.
      apply plus_n_O.
    - simpl.
      rewrite <- Nat.add_succ_comm.
      simpl.
      rewrite H.
      reflexivity.
Qed. 

Theorem trivial_equality_for_human:
    forall n m : nat, (n + 0 + 0) * m = n * m.
Proof.
    intros n m.
    assert (H: n + 0 + 0 = n).
    {
      rewrite <- !plus_n_O.
      reflexivity.
    }
    rewrite H.
    reflexivity.
Qed.

Theorem isolated_commutativity_in_sum:
  forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  {
    rewrite addition_is_commutative_in_nat.
    reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

Check Nat.add_assoc.

Theorem add_shuffle3 :
    forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    assert (H: n + m = m + n).
    {
        rewrite addition_is_commutative_in_nat.
        reflexivity.
    }
    rewrite Nat.add_assoc.
    rewrite H.
    rewrite <- Nat.add_assoc.
    reflexivity.
Qed.


Check mult_n_O.


Check Nat.mul_succ_l.
Check Nat.mul_succ_r.

Theorem mul_comm : 
    forall m n : nat, m * n = n * m.
Proof.
    intros n m.
    induction n as [| n' H].
    - simpl.
      rewrite <- mult_n_O.
      reflexivity.
    - rewrite Nat.mul_succ_l.
      rewrite H.
      rewrite Nat.mul_succ_r.
      reflexivity.
Qed.

Check leb.

Theorem plus_leb_compat_l : 
    forall n m p : nat,
  (n <=? m = true) -> (p + n) <=? (p + m) = true.
Proof.
    intros n m p H.
    induction p as [| p' Hp].
    - simpl.
      rewrite H.
      reflexivity.
    - simpl.
      rewrite Hp.
      reflexivity.
Qed.

Theorem leb_refl :
    forall n:nat, (n <=? n) = true.
Proof.
    intros.
    induction n as [| n' H].
    - simpl.
      reflexivity.
    - simpl.
      rewrite H.
      reflexivity.
Qed.

Theorem zero_neqb_S:
    forall n : nat, 0 =? (S n) = false.
Proof.
    intros n.
    simpl.
    reflexivity.
Qed.

Theorem S_neqb_0 : 
    forall n : nat, (S n) =? 0 = false.
Proof.
    intros n.
    simpl.
    reflexivity.
Qed.

Theorem mult_1_l : 
    forall n : nat, 1 * n = n.
Proof.
    intros n.
    simpl.
    rewrite <- plus_n_O.
    reflexivity.
Qed.

